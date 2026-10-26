import V185TrunkScan23Chunk0084

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_505441 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_505441 : Nat := 118140960795 + 505441 * 2 ^ 59
def prefixEnd_505441 : Nat := 4983230072969 + 3 ^ 40 * 505441 * 2
def baseEnd_505441 : Nat := 86511391829754064487675

theorem tailTrace_505441 : CollatzResearch.WordTrace tailWord_505441 prefixEnd_505441 86511391829754064487675 := by
  unfold tailWord_505441
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434947761881054295428177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12289965174587369530285451 18434947761881054295428177)
  ·
    refine ⟨13826210821410790721571133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18434947761881054295428177 13826210821410790721571133)
    ·
      refine ⟨5184829058029046520589175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13826210821410790721571133 5184829058029046520589175)
      ·
        refine ⟨7777243587043569780883763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184829058029046520589175 7777243587043569780883763)
        ·
          refine ⟨11665865380565354671325645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777243587043569780883763 11665865380565354671325645)
          ·
            refine ⟨4374699517712008001747117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11665865380565354671325645 4374699517712008001747117)
            ·
              refine ⟨1640512319142003000655169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374699517712008001747117 1640512319142003000655169)
              ·
                refine ⟨1230384239356502250491377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640512319142003000655169 1230384239356502250491377)
                ·
                  refine ⟨922788179517376687868533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1230384239356502250491377 922788179517376687868533)
                  ·
                    refine ⟨86511391829754064487675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 922788179517376687868533 86511391829754064487675)
                    ·
                      rfl

theorem cell23_505441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_505441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505441 prefixEnd_505441 := by exact prefixLift 505441
  have htrace : WordTrace (prefixWord ++ tailWord_505441) baseStart_505441 baseEnd_505441 := by
    simpa [prefixWord, tailWord_505441, baseEnd_505441] using wordTrace_append hprefix tailTrace_505441
  have hstable : (prefixWord ++ tailWord_505441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505441).length < 2 ^ (prefixWord ++ tailWord_505441).sum := by decide
  have hdescent : baseEnd_505441 < baseStart_505441 := by decide
  rcases family_descends (prefixWord ++ tailWord_505441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505445 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 5]
def baseStart_505445 : Nat := 118140960795 + 505445 * 2 ^ 59
def prefixEnd_505445 : Nat := 4983230072969 + 3 ^ 40 * 505445 * 2
def baseEnd_505445 : Nat := 28837358823542241979223

theorem tailTrace_505445 : CollatzResearch.WordTrace tailWord_505445 prefixEnd_505445 28837358823542241979223 := by
  unfold tailWord_505445
  simp only [CollatzResearch.WordTrace]
  refine ⟨18435093653866562978573789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12290062435911041985715859 18435093653866562978573789)
  ·
    refine ⟨6913160120199961116965171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18435093653866562978573789 6913160120199961116965171)
    ·
      refine ⟨10369740180299941675447757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6913160120199961116965171 10369740180299941675447757)
      ·
        refine ⟨3888652567612478128292909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10369740180299941675447757 3888652567612478128292909)
        ·
          refine ⟨1458244712854679298109841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3888652567612478128292909 1458244712854679298109841)
          ·
            refine ⟨1093683534641009473582381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458244712854679298109841 1093683534641009473582381)
            ·
              refine ⟨410131325490378552593393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1093683534641009473582381 410131325490378552593393)
              ·
                refine ⟨307598494117783914445045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410131325490378552593393 307598494117783914445045)
                ·
                  refine ⟨28837358823542241979223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307598494117783914445045 28837358823542241979223)
                  ·
                    rfl

theorem cell23_505445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_505445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505445 prefixEnd_505445 := by exact prefixLift 505445
  have htrace : WordTrace (prefixWord ++ tailWord_505445) baseStart_505445 baseEnd_505445 := by
    simpa [prefixWord, tailWord_505445, baseEnd_505445] using wordTrace_append hprefix tailTrace_505445
  have hstable : (prefixWord ++ tailWord_505445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505445).length < 2 ^ (prefixWord ++ tailWord_505445).sum := by decide
  have hdescent : baseEnd_505445 < baseStart_505445 := by decide
  rcases family_descends (prefixWord ++ tailWord_505445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505481 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_505481 : Nat := 118140960795 + 505481 * 2 ^ 59
def prefixEnd_505481 : Nat := 4983230072969 + 3 ^ 40 * 505481 * 2
def baseEnd_505481 : Nat := 259554714715442036962841

theorem tailTrace_505481 : CollatzResearch.WordTrace tailWord_505481 prefixEnd_505481 259554714715442036962841 := by
  unfold tailWord_505481
  simp only [CollatzResearch.WordTrace]
  refine ⟨18436406681736141126884297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12290937787824094084589531 18436406681736141126884297)
  ·
    refine ⟨13827305011302105845163223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18436406681736141126884297 13827305011302105845163223)
    ·
      refine ⟨20740957516953158767744835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13827305011302105845163223 20740957516953158767744835)
      ·
        refine ⟨31111436275429738151617253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20740957516953158767744835 31111436275429738151617253)
        ·
          refine ⟨5833394301643075903428235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31111436275429738151617253 5833394301643075903428235)
          ·
            refine ⟨8750091452464613855142353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833394301643075903428235 8750091452464613855142353)
            ·
              refine ⟨6562568589348460391356765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8750091452464613855142353 6562568589348460391356765)
              ·
                refine ⟨2460963221005672646758787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6562568589348460391356765 2460963221005672646758787)
                ·
                  refine ⟨3691444831508508970138181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460963221005672646758787 3691444831508508970138181)
                  ·
                    refine ⟨692145905907845431900909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3691444831508508970138181 692145905907845431900909)
                    ·
                      refine ⟨259554714715442036962841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 692145905907845431900909 259554714715442036962841)
                      ·
                        rfl

theorem cell23_505481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_505481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505481 prefixEnd_505481 := by exact prefixLift 505481
  have htrace : WordTrace (prefixWord ++ tailWord_505481) baseStart_505481 baseEnd_505481 := by
    simpa [prefixWord, tailWord_505481, baseEnd_505481] using wordTrace_append hprefix tailTrace_505481
  have hstable : (prefixWord ++ tailWord_505481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505481).length < 2 ^ (prefixWord ++ tailWord_505481).sum := by decide
  have hdescent : baseEnd_505481 < baseStart_505481 := by decide
  rcases family_descends (prefixWord ++ tailWord_505481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505562 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3]
def baseStart_505562 : Nat := 118140960795 + 505562 * 2 ^ 59
def prefixEnd_505562 : Nat := 4983230072969 + 3 ^ 40 * 505562 * 2
def baseEnd_505562 : Nat := 259596306648456220049969

theorem tailTrace_505562 : CollatzResearch.WordTrace tailWord_505562 prefixEnd_505562 259596306648456220049969 := by
  unfold tailWord_505562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609840248610672990145735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12292907329628461307055293 4609840248610672990145735)
  ·
    refine ⟨6914760372916009485218603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4609840248610672990145735 6914760372916009485218603)
    ·
      refine ⟨10372140559374014227827905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6914760372916009485218603 10372140559374014227827905)
      ·
        refine ⟨7779105419530510670870929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10372140559374014227827905 7779105419530510670870929)
        ·
          refine ⟨5834329064647883003153197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7779105419530510670870929 5834329064647883003153197)
          ·
            refine ⟨2187873399242956126182449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5834329064647883003153197 2187873399242956126182449)
            ·
              refine ⟨1640905049432217094636837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187873399242956126182449 1640905049432217094636837)
              ·
                refine ⟨307669696768540705244407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1640905049432217094636837 307669696768540705244407)
                ·
                  refine ⟨461504545152811057866611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307669696768540705244407 461504545152811057866611)
                  ·
                    refine ⟨692256817729216586799917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 461504545152811057866611 692256817729216586799917)
                    ·
                      refine ⟨259596306648456220049969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 692256817729216586799917 259596306648456220049969)
                      ·
                        rfl

theorem cell23_505562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_505562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505562 prefixEnd_505562 := by exact prefixLift 505562
  have htrace : WordTrace (prefixWord ++ tailWord_505562) baseStart_505562 baseEnd_505562 := by
    simpa [prefixWord, tailWord_505562, baseEnd_505562] using wordTrace_append hprefix tailTrace_505562
  have hstable : (prefixWord ++ tailWord_505562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505562).length < 2 ^ (prefixWord ++ tailWord_505562).sum := by decide
  have hdescent : baseEnd_505562 < baseStart_505562 := by decide
  rcases family_descends (prefixWord ++ tailWord_505562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505578 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_505578 : Nat := 118140960795 + 505578 * 2 ^ 59
def prefixEnd_505578 : Nat := 4983230072969 + 3 ^ 40 * 505578 * 2
def baseEnd_505578 : Nat := 86534840779642719149965

theorem tailTrace_505578 : CollatzResearch.WordTrace tailWord_505578 prefixEnd_505578 86534840779642719149965 := by
  unfold tailWord_505578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609986140596181673291347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12293296374923151128776925 4609986140596181673291347)
  ·
    refine ⟨6914979210894272509937021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4609986140596181673291347 6914979210894272509937021)
    ·
      refine ⟨2593117204085352191226383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6914979210894272509937021 2593117204085352191226383)
      ·
        refine ⟨3889675806128028286839575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593117204085352191226383 3889675806128028286839575)
        ·
          refine ⟨5834513709192042430259363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889675806128028286839575 5834513709192042430259363)
          ·
            refine ⟨8751770563788063645389045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834513709192042430259363 8751770563788063645389045)
            ·
              refine ⟨820478490355130966755223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8751770563788063645389045 820478490355130966755223)
              ·
                refine ⟨1230717735532696450132835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820478490355130966755223 1230717735532696450132835)
                ·
                  refine ⟨1846076603299044675199253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230717735532696450132835 1846076603299044675199253)
                  ·
                    refine ⟨86534840779642719149965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1846076603299044675199253 86534840779642719149965)
                    ·
                      rfl

theorem cell23_505578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_505578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505578 prefixEnd_505578 := by exact prefixLift 505578
  have htrace : WordTrace (prefixWord ++ tailWord_505578) baseStart_505578 baseEnd_505578 := by
    simpa [prefixWord, tailWord_505578, baseEnd_505578] using wordTrace_append hprefix tailTrace_505578
  have hstable : (prefixWord ++ tailWord_505578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505578).length < 2 ^ (prefixWord ++ tailWord_505578).sum := by decide
  have hdescent : baseEnd_505578 < baseStart_505578 := by decide
  rcases family_descends (prefixWord ++ tailWord_505578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505585 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_505585 : Nat := 118140960795 + 505585 * 2 ^ 59
def prefixEnd_505585 : Nat := 4983230072969 + 3 ^ 40 * 505585 * 2
def baseEnd_505585 : Nat := 259608116703509630062363

theorem tailTrace_505585 : CollatzResearch.WordTrace tailWord_505585 prefixEnd_505585 259608116703509630062363 := by
  unfold tailWord_505585
  simp only [CollatzResearch.WordTrace]
  refine ⟨18440199873359366888670209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12293466582239577925780139 18440199873359366888670209)
  ·
    refine ⟨13830149905019525166502657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18440199873359366888670209 13830149905019525166502657)
    ·
      refine ⟨10372612428764643874876993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13830149905019525166502657 10372612428764643874876993)
      ·
        refine ⟨7779459321573482906157745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10372612428764643874876993 7779459321573482906157745)
        ·
          refine ⟨5834594491180112179618309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7779459321573482906157745 5834594491180112179618309)
          ·
            refine ⟨1093986467096271033678433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5834594491180112179618309 1093986467096271033678433)
            ·
              refine ⟨820489850322203275258825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093986467096271033678433 820489850322203275258825)
              ·
                refine ⟨615367387741652456444119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820489850322203275258825 615367387741652456444119)
                ·
                  refine ⟨923051081612478684666179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615367387741652456444119 923051081612478684666179)
                  ·
                    refine ⟨1384576622418718026999269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923051081612478684666179 1384576622418718026999269)
                    ·
                      refine ⟨259608116703509630062363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1384576622418718026999269 259608116703509630062363)
                      ·
                        rfl

theorem cell23_505585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_505585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505585 prefixEnd_505585 := by exact prefixLift 505585
  have htrace : WordTrace (prefixWord ++ tailWord_505585) baseStart_505585 baseEnd_505585 := by
    simpa [prefixWord, tailWord_505585, baseEnd_505585] using wordTrace_append hprefix tailTrace_505585
  have hstable : (prefixWord ++ tailWord_505585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505585).length < 2 ^ (prefixWord ++ tailWord_505585).sum := by decide
  have hdescent : baseEnd_505585 < baseStart_505585 := by decide
  rcases family_descends (prefixWord ++ tailWord_505585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505652 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_505652 : Nat := 118140960795 + 505652 * 2 ^ 59
def prefixEnd_505652 : Nat := 4983230072969 + 3 ^ 40 * 505652 * 2
def baseEnd_505652 : Nat := 259642519907360867924555

theorem tailTrace_505652 : CollatzResearch.WordTrace tailWord_505652 prefixEnd_505652 259642519907360867924555 := by
  unfold tailWord_505652
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221321782058318665679605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12295095709411091554239473 9221321782058318665679605)
  ·
    refine ⟨864498917067967374907463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9221321782058318665679605 864498917067967374907463)
    ·
      refine ⟨1296748375601951062361195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864498917067967374907463 1296748375601951062361195)
      ·
        refine ⟨1945122563402926593541793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296748375601951062361195 1945122563402926593541793)
        ·
          refine ⟨1458841922552194945156345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945122563402926593541793 1458841922552194945156345)
          ·
            refine ⟨1094131441914146208867259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458841922552194945156345 1094131441914146208867259)
            ·
              refine ⟨1641197162871219313300889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094131441914146208867259 1641197162871219313300889)
              ·
                refine ⟨1230897872153414484975667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641197162871219313300889 1230897872153414484975667)
                ·
                  refine ⟨1846346808230121727463501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230897872153414484975667 1846346808230121727463501)
                  ·
                    refine ⟨692380053086295647798813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846346808230121727463501 692380053086295647798813)
                    ·
                      refine ⟨259642519907360867924555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 692380053086295647798813 259642519907360867924555)
                      ·
                        rfl

theorem cell23_505652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_505652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505652 prefixEnd_505652 := by exact prefixLift 505652
  have htrace : WordTrace (prefixWord ++ tailWord_505652) baseStart_505652 baseEnd_505652 := by
    simpa [prefixWord, tailWord_505652, baseEnd_505652] using wordTrace_append hprefix tailTrace_505652
  have hstable : (prefixWord ++ tailWord_505652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505652).length < 2 ^ (prefixWord ++ tailWord_505652).sum := by decide
  have hdescent : baseEnd_505652 < baseStart_505652 := by decide
  rcases family_descends (prefixWord ++ tailWord_505652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505670 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_505670 : Nat := 118140960795 + 505670 * 2 ^ 59
def prefixEnd_505670 : Nat := 4983230072969 + 3 ^ 40 * 505670 * 2
def baseEnd_505670 : Nat := 259651762559141797499473

theorem tailTrace_505670 : CollatzResearch.WordTrace tailWord_505670 prefixEnd_505670 259651762559141797499473 := by
  unfold tailWord_505670
  simp only [CollatzResearch.WordTrace]
  refine ⟨576353127439107075172327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12295533385367617603676309 576353127439107075172327)
  ·
    refine ⟨864529691158660612758491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 576353127439107075172327 864529691158660612758491)
    ·
      refine ⟨1296794536737990919137737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864529691158660612758491 1296794536737990919137737)
      ·
        refine ⟨972595902553493189353303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1296794536737990919137737 972595902553493189353303)
        ·
          refine ⟨1458893853830239784029955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972595902553493189353303 1458893853830239784029955)
          ·
            refine ⟨2188340780745359676044933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458893853830239784029955 2188340780745359676044933)
            ·
              refine ⟨410313896389754939258425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2188340780745359676044933 410313896389754939258425)
              ·
                refine ⟨307735422292316204443819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410313896389754939258425 307735422292316204443819)
                ·
                  refine ⟨461603133438474306665729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307735422292316204443819 461603133438474306665729)
                  ·
                    refine ⟨346202350078855729999297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461603133438474306665729 346202350078855729999297)
                    ·
                      refine ⟨259651762559141797499473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346202350078855729999297 259651762559141797499473)
                      ·
                        rfl

theorem cell23_505670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_505670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505670 prefixEnd_505670 := by exact prefixLift 505670
  have htrace : WordTrace (prefixWord ++ tailWord_505670) baseStart_505670 baseEnd_505670 := by
    simpa [prefixWord, tailWord_505670, baseEnd_505670] using wordTrace_append hprefix tailTrace_505670
  have hstable : (prefixWord ++ tailWord_505670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505670).length < 2 ^ (prefixWord ++ tailWord_505670).sum := by decide
  have hdescent : baseEnd_505670 < baseStart_505670 := by decide
  rcases family_descends (prefixWord ++ tailWord_505670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505726 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_505726 : Nat := 118140960795 + 505726 * 2 ^ 59
def prefixEnd_505726 : Nat := 4983230072969 + 3 ^ 40 * 505726 * 2
def baseEnd_505726 : Nat := 259680517475793578399215

theorem tailTrace_505726 : CollatzResearch.WordTrace tailWord_505726 prefixEnd_505726 259680517475793578399215 := by
  unfold tailWord_505726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305667820731068496194129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12296895043899031979702021 2305667820731068496194129)
  ·
    refine ⟨1729250865548301372145597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2305667820731068496194129 1729250865548301372145597)
    ·
      refine ⟨648469074580613014554599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1729250865548301372145597 648469074580613014554599)
      ·
        refine ⟨972703611870919521831899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648469074580613014554599 972703611870919521831899)
        ·
          refine ⟨1459055417806379282747849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972703611870919521831899 1459055417806379282747849)
          ·
            refine ⟨1094291563354784462060887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1459055417806379282747849 1094291563354784462060887)
            ·
              refine ⟨1641437345032176693091331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094291563354784462060887 1641437345032176693091331)
              ·
                refine ⟨2462156017548265039636997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641437345032176693091331 2462156017548265039636997)
                ·
                  refine ⟨461654253290299694931937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2462156017548265039636997 461654253290299694931937)
                  ·
                    refine ⟨346240689967724771198953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461654253290299694931937 346240689967724771198953)
                    ·
                      refine ⟨259680517475793578399215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346240689967724771198953 259680517475793578399215)
                      ·
                        rfl

theorem cell23_505726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_505726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505726 prefixEnd_505726 := by exact prefixLift 505726
  have htrace : WordTrace (prefixWord ++ tailWord_505726) baseStart_505726 baseEnd_505726 := by
    simpa [prefixWord, tailWord_505726, baseEnd_505726] using wordTrace_append hprefix tailTrace_505726
  have hstable : (prefixWord ++ tailWord_505726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505726).length < 2 ^ (prefixWord ++ tailWord_505726).sum := by decide
  have hdescent : baseEnd_505726 < baseStart_505726 := by decide
  rcases family_descends (prefixWord ++ tailWord_505726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505728 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_505728 : Nat := 118140960795 + 505728 * 2 ^ 59
def prefixEnd_505728 : Nat := 4983230072969 + 3 ^ 40 * 505728 * 2
def baseEnd_505728 : Nat := 86560514812367523524735

theorem tailTrace_505728 : CollatzResearch.WordTrace tailWord_505728 prefixEnd_505728 86560514812367523524735 := by
  unfold tailWord_505728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9222707755920651155562919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12296943674560868207417225 9222707755920651155562919)
  ·
    refine ⟨13834061633880976733344379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9222707755920651155562919 13834061633880976733344379)
    ·
      refine ⟨20751092450821465100016569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13834061633880976733344379 20751092450821465100016569)
      ·
        refine ⟨15563319338116098825012427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20751092450821465100016569 15563319338116098825012427)
        ·
          refine ⟨23344979007174148237518641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15563319338116098825012427 23344979007174148237518641)
          ·
            refine ⟨17508734255380611178138981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23344979007174148237518641 17508734255380611178138981)
            ·
              refine ⟨3282887672883864595901059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17508734255380611178138981 3282887672883864595901059)
              ·
                refine ⟨4924331509325796893851589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282887672883864595901059 4924331509325796893851589)
                ·
                  refine ⟨923312157998586917597173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4924331509325796893851589 923312157998586917597173)
                  ·
                    refine ⟨86560514812367523524735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 923312157998586917597173 86560514812367523524735)
                    ·
                      rfl

theorem cell23_505728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_505728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505728 prefixEnd_505728 := by exact prefixLift 505728
  have htrace : WordTrace (prefixWord ++ tailWord_505728) baseStart_505728 baseEnd_505728 := by
    simpa [prefixWord, tailWord_505728, baseEnd_505728] using wordTrace_append hprefix tailTrace_505728
  have hstable : (prefixWord ++ tailWord_505728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505728).length < 2 ^ (prefixWord ++ tailWord_505728).sum := by decide
  have hdescent : baseEnd_505728 < baseStart_505728 := by decide
  rcases family_descends (prefixWord ++ tailWord_505728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505765 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_505765 : Nat := 118140960795 + 505765 * 2 ^ 59
def prefixEnd_505765 : Nat := 4983230072969 + 3 ^ 40 * 505765 * 2
def baseEnd_505765 : Nat := 259700543221318925811535

theorem tailTrace_505765 : CollatzResearch.WordTrace tailWord_505765 prefixEnd_505765 259700543221318925811535 := by
  unfold tailWord_505765
  simp only [CollatzResearch.WordTrace]
  refine ⟨18446765012707257630222749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12297843341804838420148499 18446765012707257630222749)
  ·
    refine ⟨6917536879765221611333531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18446765012707257630222749 6917536879765221611333531)
    ·
      refine ⟨10376305319647832417000297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917536879765221611333531 10376305319647832417000297)
      ·
        refine ⟨7782228989735874312750223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10376305319647832417000297 7782228989735874312750223)
        ·
          refine ⟨11673343484603811469125335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7782228989735874312750223 11673343484603811469125335)
          ·
            refine ⟨17510015226905717203688003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673343484603811469125335 17510015226905717203688003)
            ·
              refine ⟨26265022840358575805532005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510015226905717203688003 26265022840358575805532005)
              ·
                refine ⟨4924691782567232963537251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26265022840358575805532005 4924691782567232963537251)
                ·
                  refine ⟨7387037673850849445305877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924691782567232963537251 7387037673850849445305877)
                  ·
                    refine ⟨346267390961758567748713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7387037673850849445305877 346267390961758567748713)
                    ·
                      refine ⟨259700543221318925811535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346267390961758567748713 259700543221318925811535)
                      ·
                        rfl

theorem cell23_505765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_505765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505765 prefixEnd_505765 := by exact prefixLift 505765
  have htrace : WordTrace (prefixWord ++ tailWord_505765) baseStart_505765 baseEnd_505765 := by
    simpa [prefixWord, tailWord_505765, baseEnd_505765] using wordTrace_append hprefix tailTrace_505765
  have hstable : (prefixWord ++ tailWord_505765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505765).length < 2 ^ (prefixWord ++ tailWord_505765).sum := by decide
  have hdescent : baseEnd_505765 < baseStart_505765 := by decide
  rcases family_descends (prefixWord ++ tailWord_505765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505778 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_505778 : Nat := 118140960795 + 505778 * 2 ^ 59
def prefixEnd_505778 : Nat := 4983230072969 + 3 ^ 40 * 505778 * 2
def baseEnd_505778 : Nat := 259707218469827374948975

theorem tailTrace_505778 : CollatzResearch.WordTrace tailWord_505778 prefixEnd_505778 259707218469827374948975 := by
  unfold tailWord_505778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611809790415040212611497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12298159441106773900297325 4611809790415040212611497)
  ·
    refine ⟨3458857342811280159458623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4611809790415040212611497 3458857342811280159458623)
    ·
      refine ⟨5188286014216920239187935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3458857342811280159458623 5188286014216920239187935)
      ·
        refine ⟨7782429021325380358781903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188286014216920239187935 7782429021325380358781903)
        ·
          refine ⟨11673643531988070538172855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7782429021325380358781903 11673643531988070538172855)
          ·
            refine ⟨17510465297982105807259283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673643531988070538172855 17510465297982105807259283)
            ·
              refine ⟨26265697946973158710888925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510465297982105807259283 26265697946973158710888925)
              ·
                refine ⟨9849636730114934516583347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26265697946973158710888925 9849636730114934516583347)
                ·
                  refine ⟨14774455095172401774875021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9849636730114934516583347 14774455095172401774875021)
                  ·
                    refine ⟨5540420660689650665578133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14774455095172401774875021 5540420660689650665578133)
                    ·
                      refine ⟨259707218469827374948975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5540420660689650665578133 259707218469827374948975)
                      ·
                        rfl

theorem cell23_505778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_505778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505778 prefixEnd_505778 := by exact prefixLift 505778
  have htrace : WordTrace (prefixWord ++ tailWord_505778) baseStart_505778 baseEnd_505778 := by
    simpa [prefixWord, tailWord_505778, baseEnd_505778] using wordTrace_append hprefix tailTrace_505778
  have hstable : (prefixWord ++ tailWord_505778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505778).length < 2 ^ (prefixWord ++ tailWord_505778).sum := by decide
  have hdescent : baseEnd_505778 < baseStart_505778 := by decide
  rcases family_descends (prefixWord ++ tailWord_505778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505808 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_505808 : Nat := 118140960795 + 505808 * 2 ^ 59
def prefixEnd_505808 : Nat := 4983230072969 + 3 ^ 40 * 505808 * 2
def baseEnd_505808 : Nat := 259722622889462257573837

theorem tailTrace_505808 : CollatzResearch.WordTrace tailWord_505808 prefixEnd_505808 259722622889462257573837 := by
  unfold tailWord_505808
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224166675775737987019039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12298888901034317316025385 9224166675775737987019039)
  ·
    refine ⟨13836250013663606980528559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9224166675775737987019039 13836250013663606980528559)
    ·
      refine ⟨20754375020495410470792839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13836250013663606980528559 20754375020495410470792839)
      ·
        refine ⟨31131562530743115706189259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20754375020495410470792839 31131562530743115706189259)
        ·
          refine ⟨46697343796114673559283889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31131562530743115706189259 46697343796114673559283889)
          ·
            refine ⟨35023007847086005169462917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46697343796114673559283889 35023007847086005169462917)
            ·
              refine ⟨6566813971328625969274297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35023007847086005169462917 6566813971328625969274297)
              ·
                refine ⟨4925110478496469476955723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566813971328625969274297 4925110478496469476955723)
                ·
                  refine ⟨7387665717744704215433585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925110478496469476955723 7387665717744704215433585)
                  ·
                    refine ⟨5540749288308528161575189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387665717744704215433585 5540749288308528161575189)
                    ·
                      refine ⟨259722622889462257573837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5540749288308528161575189 259722622889462257573837)
                      ·
                        rfl

theorem cell23_505808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_505808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505808 prefixEnd_505808 := by exact prefixLift 505808
  have htrace : WordTrace (prefixWord ++ tailWord_505808) baseStart_505808 baseEnd_505808 := by
    simpa [prefixWord, tailWord_505808, baseEnd_505808] using wordTrace_append hprefix tailTrace_505808
  have hstable : (prefixWord ++ tailWord_505808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505808).length < 2 ^ (prefixWord ++ tailWord_505808).sum := by decide
  have hdescent : baseEnd_505808 < baseStart_505808 := by decide
  rcases family_descends (prefixWord ++ tailWord_505808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505835 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 1, 5]
def baseStart_505835 : Nat := 118140960795 + 505835 * 2 ^ 59
def prefixEnd_505835 : Nat := 4983230072969 + 3 ^ 40 * 505835 * 2
def baseEnd_505835 : Nat := 86578828955711217312071

theorem tailTrace_505835 : CollatzResearch.WordTrace tailWord_505835 prefixEnd_505835 86578828955711217312071 := by
  unfold tailWord_505835
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449318122453659585270959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12299545414969106390180639 18449318122453659585270959)
  ·
    refine ⟨27673977183680489377906439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18449318122453659585270959 27673977183680489377906439)
    ·
      refine ⟨41510965775520734066859659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27673977183680489377906439 41510965775520734066859659)
      ·
        refine ⟨62266448663281101100289489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41510965775520734066859659 62266448663281101100289489)
        ·
          refine ⟨46699836497460825825217117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62266448663281101100289489 46699836497460825825217117)
          ·
            refine ⟨17512438686547809684456419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46699836497460825825217117 17512438686547809684456419)
            ·
              refine ⟨26268658029821714526684629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17512438686547809684456419 26268658029821714526684629)
              ·
                refine ⟨615671672573946434219171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26268658029821714526684629 615671672573946434219171)
                ·
                  refine ⟨923507508860919651328757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615671672573946434219171 923507508860919651328757)
                  ·
                    refine ⟨86578828955711217312071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 923507508860919651328757 86578828955711217312071)
                    ·
                      rfl

theorem cell23_505835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 5].length) (baseStart_505835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505835 prefixEnd_505835 := by exact prefixLift 505835
  have htrace : WordTrace (prefixWord ++ tailWord_505835) baseStart_505835 baseEnd_505835 := by
    simpa [prefixWord, tailWord_505835, baseEnd_505835] using wordTrace_append hprefix tailTrace_505835
  have hstable : (prefixWord ++ tailWord_505835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505835).length < 2 ^ (prefixWord ++ tailWord_505835).sum := by decide
  have hdescent : baseEnd_505835 < baseStart_505835 := by decide
  rcases family_descends (prefixWord ++ tailWord_505835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505865 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_505865 : Nat := 118140960795 + 505865 * 2 ^ 59
def prefixEnd_505865 : Nat := 4983230072969 + 3 ^ 40 * 505865 * 2
def baseEnd_505865 : Nat := 86583963762256178187025

theorem tailTrace_505865 : CollatzResearch.WordTrace tailWord_505865 prefixEnd_505865 86583963762256178187025 := by
  unfold tailWord_505865
  simp only [CollatzResearch.WordTrace]
  refine ⟨18450412312344974708863049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12300274874896649805908699 18450412312344974708863049)
  ·
    refine ⟨13837809234258731031647287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18450412312344974708863049 13837809234258731031647287)
    ·
      refine ⟨20756713851388096547470931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13837809234258731031647287 20756713851388096547470931)
      ·
        refine ⟨31135070777082144821206397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20756713851388096547470931 31135070777082144821206397)
        ·
          refine ⟨11675651541405804307952399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31135070777082144821206397 11675651541405804307952399)
          ·
            refine ⟨17513477312108706461928599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11675651541405804307952399 17513477312108706461928599)
            ·
              refine ⟨26270215968163059692892899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17513477312108706461928599 26270215968163059692892899)
              ·
                refine ⟨39405323952244589539339349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26270215968163059692892899 39405323952244589539339349)
                ·
                  refine ⟨461781140065366283664133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39405323952244589539339349 461781140065366283664133)
                  ·
                    refine ⟨86583963762256178187025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461781140065366283664133 86583963762256178187025)
                    ·
                      rfl

theorem cell23_505865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_505865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505865 prefixEnd_505865 := by exact prefixLift 505865
  have htrace : WordTrace (prefixWord ++ tailWord_505865) baseStart_505865 baseEnd_505865 := by
    simpa [prefixWord, tailWord_505865, baseEnd_505865] using wordTrace_append hprefix tailTrace_505865
  have hstable : (prefixWord ++ tailWord_505865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505865).length < 2 ^ (prefixWord ++ tailWord_505865).sum := by decide
  have hdescent : baseEnd_505865 < baseStart_505865 := by decide
  rcases family_descends (prefixWord ++ tailWord_505865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505889 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_505889 : Nat := 118140960795 + 505889 * 2 ^ 59
def prefixEnd_505889 : Nat := 4983230072969 + 3 ^ 40 * 505889 * 2
def baseEnd_505889 : Nat := 259764214822476440660965

theorem tailTrace_505889 : CollatzResearch.WordTrace tailWord_505889 prefixEnd_505889 259764214822476440660965 := by
  unfold tailWord_505889
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451287664258026807736721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12300858442838684538491147 18451287664258026807736721)
  ·
    refine ⟨13838465748193520105802541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18451287664258026807736721 13838465748193520105802541)
    ·
      refine ⟨5189424655572570039675953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13838465748193520105802541 5189424655572570039675953)
      ·
        refine ⟨3892068491679427529756965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189424655572570039675953 3892068491679427529756965)
        ·
          refine ⟨729762842189892661829431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3892068491679427529756965 729762842189892661829431)
          ·
            refine ⟨1094644263284838992744147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729762842189892661829431 1094644263284838992744147)
            ·
              refine ⟨1641966394927258489116221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094644263284838992744147 1641966394927258489116221)
              ·
                refine ⟨615737398097721933418583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1641966394927258489116221 615737398097721933418583)
                ·
                  refine ⟨923606097146582900127875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615737398097721933418583 923606097146582900127875)
                  ·
                    refine ⟨1385409145719874350191813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 923606097146582900127875 1385409145719874350191813)
                    ·
                      refine ⟨259764214822476440660965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1385409145719874350191813 259764214822476440660965)
                      ·
                        rfl

theorem cell23_505889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_505889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505889 prefixEnd_505889 := by exact prefixLift 505889
  have htrace : WordTrace (prefixWord ++ tailWord_505889) baseStart_505889 baseEnd_505889 := by
    simpa [prefixWord, tailWord_505889, baseEnd_505889] using wordTrace_append hprefix tailTrace_505889
  have hstable : (prefixWord ++ tailWord_505889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505889).length < 2 ^ (prefixWord ++ tailWord_505889).sum := by decide
  have hdescent : baseEnd_505889 < baseStart_505889 := by decide
  rcases family_descends (prefixWord ++ tailWord_505889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505906 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_505906 : Nat := 118140960795 + 505906 * 2 ^ 59
def prefixEnd_505906 : Nat := 4983230072969 + 3 ^ 40 * 505906 * 2
def baseEnd_505906 : Nat := 259772943993602874148387

theorem tailTrace_505906 : CollatzResearch.WordTrace tailWord_505906 prefixEnd_505906 259772943993602874148387 := by
  unfold tailWord_505906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4612976926299109677776393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12301271803464292474070381 4612976926299109677776393)
  ·
    refine ⟨3459732694724332258332295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4612976926299109677776393 3459732694724332258332295)
    ·
      refine ⟨5189599042086498387498443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459732694724332258332295 5189599042086498387498443)
      ·
        refine ⟨7784398563129747581247665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189599042086498387498443 7784398563129747581247665)
        ·
          refine ⟨5838298922347310685935749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7784398563129747581247665 5838298922347310685935749)
          ·
            refine ⟨1094681047940120753612953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5838298922347310685935749 1094681047940120753612953)
            ·
              refine ⟨821010785955090565209715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094681047940120753612953 821010785955090565209715)
              ·
                refine ⟨1231516178932635847814573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821010785955090565209715 1231516178932635847814573)
                ·
                  refine ⟨461818567099738442930465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231516178932635847814573 461818567099738442930465)
                  ·
                    refine ⟨346363925324803832197849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461818567099738442930465 346363925324803832197849)
                    ·
                      refine ⟨259772943993602874148387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346363925324803832197849 259772943993602874148387)
                      ·
                        rfl

theorem cell23_505906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_505906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505906 prefixEnd_505906 := by exact prefixLift 505906
  have htrace : WordTrace (prefixWord ++ tailWord_505906) baseStart_505906 baseEnd_505906 := by
    simpa [prefixWord, tailWord_505906, baseEnd_505906] using wordTrace_append hprefix tailTrace_505906
  have hstable : (prefixWord ++ tailWord_505906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505906).length < 2 ^ (prefixWord ++ tailWord_505906).sum := by decide
  have hdescent : baseEnd_505906 < baseStart_505906 := by decide
  rcases family_descends (prefixWord ++ tailWord_505906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505955 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 4, 6]
def baseStart_505955 : Nat := 118140960795 + 505955 * 2 ^ 59
def prefixEnd_505955 : Nat := 4983230072969 + 3 ^ 40 * 505955 * 2
def baseEnd_505955 : Nat := 86599368181891060811887

theorem tailTrace_505955 : CollatzResearch.WordTrace tailWord_505955 prefixEnd_505955 86599368181891060811887 := by
  unfold tailWord_505955
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453694882018920079639319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302463254679280053092879 18453694882018920079639319)
  ·
    refine ⟨27680542323028380119458979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18453694882018920079639319 27680542323028380119458979)
    ·
      refine ⟨41520813484542570179188469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27680542323028380119458979 41520813484542570179188469)
      ·
        refine ⟨3892576264175865954298919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41520813484542570179188469 3892576264175865954298919)
        ·
          refine ⟨5838864396263798931448379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892576264175865954298919 5838864396263798931448379)
          ·
            refine ⟨8758296594395698397172569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838864396263798931448379 8758296594395698397172569)
            ·
              refine ⟨6568722445796773797879427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758296594395698397172569 6568722445796773797879427)
              ·
                refine ⟨9853083668695160696819141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568722445796773797879427 9853083668695160696819141)
                ·
                  refine ⟨1847453187880342630653589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9853083668695160696819141 1847453187880342630653589)
                  ·
                    refine ⟨86599368181891060811887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1847453187880342630653589 86599368181891060811887)
                    ·
                      rfl

theorem cell23_505955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_505955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505955 prefixEnd_505955 := by exact prefixLift 505955
  have htrace : WordTrace (prefixWord ++ tailWord_505955) baseStart_505955 baseEnd_505955 := by
    simpa [prefixWord, tailWord_505955, baseEnd_505955] using wordTrace_append hprefix tailTrace_505955
  have hstable : (prefixWord ++ tailWord_505955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505955).length < 2 ^ (prefixWord ++ tailWord_505955).sum := by decide
  have hdescent : baseEnd_505955 < baseStart_505955 := by decide
  rcases family_descends (prefixWord ++ tailWord_505955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506013 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_506013 : Nat := 118140960795 + 506013 * 2 ^ 59
def prefixEnd_506013 : Nat := 4983230072969 + 3 ^ 40 * 506013 * 2
def baseEnd_506013 : Nat := 259827886423633955510395

theorem tailTrace_506013 : CollatzResearch.WordTrace tailWord_506013 prefixEnd_506013 259827886423633955510395 := by
  unfold tailWord_506013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455810315808795985250693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12303873543872530656833795 18455810315808795985250693)
  ·
    refine ⟨3460464434214149247234505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18455810315808795985250693 3460464434214149247234505)
    ·
      refine ⟨2595348325660611935425879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3460464434214149247234505 2595348325660611935425879)
      ·
        refine ⟨3893022488490917903138819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595348325660611935425879 3893022488490917903138819)
        ·
          refine ⟨5839533732736376854708229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893022488490917903138819 5839533732736376854708229)
          ·
            refine ⟨1094912574888070660257793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5839533732736376854708229 1094912574888070660257793)
            ·
              refine ⟨821184431166052995193345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094912574888070660257793 821184431166052995193345)
              ·
                refine ⟨615888323374539746395009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821184431166052995193345 615888323374539746395009)
                ·
                  refine ⟨461916242530904809796257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615888323374539746395009 461916242530904809796257)
                  ·
                    refine ⟨346437181898178607347193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461916242530904809796257 346437181898178607347193)
                    ·
                      refine ⟨259827886423633955510395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346437181898178607347193 259827886423633955510395)
                      ·
                        rfl

theorem cell23_506013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_506013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506013 prefixEnd_506013 := by exact prefixLift 506013
  have htrace : WordTrace (prefixWord ++ tailWord_506013) baseStart_506013 baseEnd_506013 := by
    simpa [prefixWord, tailWord_506013, baseEnd_506013] using wordTrace_append hprefix tailTrace_506013
  have hstable : (prefixWord ++ tailWord_506013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506013).length < 2 ^ (prefixWord ++ tailWord_506013).sum := by decide
  have hdescent : baseEnd_506013 < baseStart_506013 := by decide
  rcases family_descends (prefixWord ++ tailWord_506013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506026 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_506026 : Nat := 118140960795 + 506026 * 2 ^ 59
def prefixEnd_506026 : Nat := 4983230072969 + 3 ^ 40 * 506026 * 2
def baseEnd_506026 : Nat := 259834561672142404647835

theorem tailTrace_506026 : CollatzResearch.WordTrace tailWord_506026 prefixEnd_506026 259834561672142404647835 := by
  unfold tailWord_506026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614071116190424801368483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12304189643174466136982621 4614071116190424801368483)
  ·
    refine ⟨6921106674285637202052725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4614071116190424801368483 6921106674285637202052725)
    ·
      refine ⟨648853750714278487692443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6921106674285637202052725 648853750714278487692443)
      ·
        refine ⟨973280626071417731538665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648853750714278487692443 973280626071417731538665)
        ·
          refine ⟨729960469553563298653999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973280626071417731538665 729960469553563298653999)
          ·
            refine ⟨1094940704330344947980999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729960469553563298653999 1094940704330344947980999)
            ·
              refine ⟨1642411056495517421971499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094940704330344947980999 1642411056495517421971499)
              ·
                refine ⟨2463616584743276132957249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642411056495517421971499 2463616584743276132957249)
                ·
                  refine ⟨1847712438557457099717937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463616584743276132957249 1847712438557457099717937)
                  ·
                    refine ⟨1385784328918092824788453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847712438557457099717937 1385784328918092824788453)
                    ·
                      refine ⟨259834561672142404647835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1385784328918092824788453 259834561672142404647835)
                      ·
                        rfl

theorem cell23_506026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_506026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506026 prefixEnd_506026 := by exact prefixLift 506026
  have htrace : WordTrace (prefixWord ++ tailWord_506026) baseStart_506026 baseEnd_506026 := by
    simpa [prefixWord, tailWord_506026, baseEnd_506026] using wordTrace_append hprefix tailTrace_506026
  have hstable : (prefixWord ++ tailWord_506026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506026).length < 2 ^ (prefixWord ++ tailWord_506026).sum := by decide
  have hdescent : baseEnd_506026 < baseStart_506026 := by decide
  rcases family_descends (prefixWord ++ tailWord_506026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506029 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_506029 : Nat := 118140960795 + 506029 * 2 ^ 59
def prefixEnd_506029 : Nat := 4983230072969 + 3 ^ 40 * 506029 * 2
def baseEnd_506029 : Nat := 259836102114105892910321

theorem tailTrace_506029 : CollatzResearch.WordTrace tailWord_506029 prefixEnd_506029 259836102114105892910321 := by
  unfold tailWord_506029
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456393883750830717833141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12304262589167220478555427 18456393883750830717833141)
  ·
    refine ⟨1730286926601640379796857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18456393883750830717833141 1730286926601640379796857)
    ·
      refine ⟨1297715194951230284847643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1730286926601640379796857 1297715194951230284847643)
      ·
        refine ⟨1946572792426845427271465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297715194951230284847643 1946572792426845427271465)
        ·
          refine ⟨1459929594320134070453599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946572792426845427271465 1459929594320134070453599)
          ·
            refine ⟨2189894391480201105680399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459929594320134070453599 2189894391480201105680399)
            ·
              refine ⟨3284841587220301658520599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189894391480201105680399 3284841587220301658520599)
              ·
                refine ⟨4927262380830452487780899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284841587220301658520599 4927262380830452487780899)
                ·
                  refine ⟨7390893571245678731671349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927262380830452487780899 7390893571245678731671349)
                  ·
                    refine ⟨692896272304282381094189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7390893571245678731671349 692896272304282381094189)
                    ·
                      refine ⟨259836102114105892910321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 692896272304282381094189 259836102114105892910321)
                      ·
                        rfl

theorem cell23_506029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_506029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506029 prefixEnd_506029 := by exact prefixLift 506029
  have htrace : WordTrace (prefixWord ++ tailWord_506029) baseStart_506029 baseEnd_506029 := by
    simpa [prefixWord, tailWord_506029, baseEnd_506029] using wordTrace_append hprefix tailTrace_506029
  have hstable : (prefixWord ++ tailWord_506029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506029).length < 2 ^ (prefixWord ++ tailWord_506029).sum := by decide
  have hdescent : baseEnd_506029 < baseStart_506029 := by decide
  rcases family_descends (prefixWord ++ tailWord_506029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506030 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_506030 : Nat := 118140960795 + 506030 * 2 ^ 59
def prefixEnd_506030 : Nat := 4983230072969 + 3 ^ 40 * 506030 * 2
def baseEnd_506030 : Nat := 259836615594760388997817

theorem tailTrace_506030 : CollatzResearch.WordTrace tailWord_506030 prefixEnd_506030 259836615594760388997817 := by
  unfold tailWord_506030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307053794593400986077443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12304286904498138592413029 2307053794593400986077443)
  ·
    refine ⟨3460580691890101479116165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2307053794593400986077443 3460580691890101479116165)
    ·
      refine ⟨648858879729394027334281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3460580691890101479116165 648858879729394027334281)
      ·
        refine ⟨486644159797045520500711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 648858879729394027334281 486644159797045520500711)
        ·
          refine ⟨729966239695568280751067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486644159797045520500711 729966239695568280751067)
          ·
            refine ⟨1094949359543352421126601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729966239695568280751067 1094949359543352421126601)
            ·
              refine ⟨821212019657514315844951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094949359543352421126601 821212019657514315844951)
              ·
                refine ⟨1231818029486271473767427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821212019657514315844951 1231818029486271473767427)
                ·
                  refine ⟨1847727044229407210651141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231818029486271473767427 1847727044229407210651141)
                  ·
                    refine ⟨346448820793013851997089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847727044229407210651141 346448820793013851997089)
                    ·
                      refine ⟨259836615594760388997817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346448820793013851997089 259836615594760388997817)
                      ·
                        rfl

theorem cell23_506030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_506030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506030 prefixEnd_506030 := by exact prefixLift 506030
  have htrace : WordTrace (prefixWord ++ tailWord_506030) baseStart_506030 baseEnd_506030 := by
    simpa [prefixWord, tailWord_506030, baseEnd_506030] using wordTrace_append hprefix tailTrace_506030
  have hstable : (prefixWord ++ tailWord_506030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506030).length < 2 ^ (prefixWord ++ tailWord_506030).sum := by decide
  have hdescent : baseEnd_506030 < baseStart_506030 := by decide
  rcases family_descends (prefixWord ++ tailWord_506030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506159 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 6, 2]
def baseStart_506159 : Nat := 118140960795 + 506159 * 2 ^ 59
def prefixEnd_506159 : Nat := 4983230072969 + 3 ^ 40 * 506159 * 2
def baseEnd_506159 : Nat := 259902854599190384284723

theorem tailTrace_506159 : CollatzResearch.WordTrace tailWord_506159 prefixEnd_506159 259902854599190384284723 := by
  unfold tailWord_506159
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461135373279862920065531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12307423582186575280043687 18461135373279862920065531)
  ·
    refine ⟨27691703059919794380098297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18461135373279862920065531 27691703059919794380098297)
    ·
      refine ⟨20768777294939845785073723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27691703059919794380098297 20768777294939845785073723)
      ·
        refine ⟨31153165942409768677610585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20768777294939845785073723 31153165942409768677610585)
        ·
          refine ⟨23364874456807326508207939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31153165942409768677610585 23364874456807326508207939)
          ·
            refine ⟨35047311685210989762311909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364874456807326508207939 35047311685210989762311909)
            ·
              refine ⟨6571370940977060580433483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35047311685210989762311909 6571370940977060580433483)
              ·
                refine ⟨9857056411465590870650225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571370940977060580433483 9857056411465590870650225)
                ·
                  refine ⟨7392792308599193152987669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857056411465590870650225 7392792308599193152987669)
                  ·
                    refine ⟨346537139465587179046297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7392792308599193152987669 346537139465587179046297)
                    ·
                      refine ⟨259902854599190384284723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346537139465587179046297 259902854599190384284723)
                      ·
                        rfl

theorem cell23_506159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6, 2].length) (baseStart_506159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506159 prefixEnd_506159 := by exact prefixLift 506159
  have htrace : WordTrace (prefixWord ++ tailWord_506159) baseStart_506159 baseEnd_506159 := by
    simpa [prefixWord, tailWord_506159, baseEnd_506159] using wordTrace_append hprefix tailTrace_506159
  have hstable : (prefixWord ++ tailWord_506159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506159).length < 2 ^ (prefixWord ++ tailWord_506159).sum := by decide
  have hdescent : baseEnd_506159 < baseStart_506159 := by decide
  rcases family_descends (prefixWord ++ tailWord_506159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506169 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_506169 : Nat := 118140960795 + 506169 * 2 ^ 59
def prefixEnd_506169 : Nat := 4983230072969 + 3 ^ 40 * 506169 * 2
def baseEnd_506169 : Nat := 86635996468578448386559

theorem tailTrace_506169 : CollatzResearch.WordTrace tailWord_506169 prefixEnd_506169 86635996468578448386559 := by
  unfold tailWord_506169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461500103243634627929561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12307666735495756418619707 18461500103243634627929561)
  ·
    refine ⟨13846125077432725970947171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18461500103243634627929561 13846125077432725970947171)
    ·
      refine ⟨20769187616149088956420757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13846125077432725970947171 20769187616149088956420757)
      ·
        refine ⟨973555669506988544832223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20769187616149088956420757 973555669506988544832223)
        ·
          refine ⟨1460333504260482817248335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973555669506988544832223 1460333504260482817248335)
          ·
            refine ⟨2190500256390724225872503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460333504260482817248335 2190500256390724225872503)
            ·
              refine ⟨3285750384586086338808755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190500256390724225872503 3285750384586086338808755)
              ·
                refine ⟨4928625576879129508213133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285750384586086338808755 4928625576879129508213133)
                ·
                  refine ⟨1848234591329673565579925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4928625576879129508213133 1848234591329673565579925)
                  ·
                    refine ⟨86635996468578448386559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1848234591329673565579925 86635996468578448386559)
                    ·
                      rfl

theorem cell23_506169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_506169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506169 prefixEnd_506169 := by exact prefixLift 506169
  have htrace : WordTrace (prefixWord ++ tailWord_506169) baseStart_506169 baseEnd_506169 := by
    simpa [prefixWord, tailWord_506169, baseEnd_506169] using wordTrace_append hprefix tailTrace_506169
  have hstable : (prefixWord ++ tailWord_506169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506169).length < 2 ^ (prefixWord ++ tailWord_506169).sum := by decide
  have hdescent : baseEnd_506169 < baseStart_506169 := by decide
  rcases family_descends (prefixWord ++ tailWord_506169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506176 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2]
def baseStart_506176 : Nat := 118140960795 + 506176 * 2 ^ 59
def prefixEnd_506176 : Nat := 4983230072969 + 3 ^ 40 * 506176 * 2
def baseEnd_506176 : Nat := 259911583770316817772145

theorem tailTrace_506176 : CollatzResearch.WordTrace tailWord_506176 prefixEnd_506176 259911583770316817772145 := by
  unfold tailWord_506176
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230877707109137411717191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12307836942812183215622921 9230877707109137411717191)
  ·
    refine ⟨13846316560663706117575787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9230877707109137411717191 13846316560663706117575787)
    ·
      refine ⟨20769474840995559176363681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13846316560663706117575787 20769474840995559176363681)
      ·
        refine ⟨15577106130746669382272761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20769474840995559176363681 15577106130746669382272761)
        ·
          refine ⟨11682829598060002036704571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15577106130746669382272761 11682829598060002036704571)
          ·
            refine ⟨17524244397090003055056857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682829598060002036704571 17524244397090003055056857)
            ·
              refine ⟨13143183297817502291292643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17524244397090003055056857 13143183297817502291292643)
              ·
                refine ⟨19714774946726253436938965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13143183297817502291292643 19714774946726253436938965)
                ·
                  refine ⟨462065037813896564928257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19714774946726253436938965 462065037813896564928257)
                  ·
                    refine ⟨346548778360422423696193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462065037813896564928257 346548778360422423696193)
                    ·
                      refine ⟨259911583770316817772145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346548778360422423696193 259911583770316817772145)
                      ·
                        rfl

theorem cell23_506176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_506176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506176 prefixEnd_506176 := by exact prefixLift 506176
  have htrace : WordTrace (prefixWord ++ tailWord_506176) baseStart_506176 baseEnd_506176 := by
    simpa [prefixWord, tailWord_506176, baseEnd_506176] using wordTrace_append hprefix tailTrace_506176
  have hstable : (prefixWord ++ tailWord_506176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506176).length < 2 ^ (prefixWord ++ tailWord_506176).sum := by decide
  have hdescent : baseEnd_506176 < baseStart_506176 := by decide
  rcases family_descends (prefixWord ++ tailWord_506176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506179 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5]
def baseStart_506179 : Nat := 118140960795 + 506179 * 2 ^ 59
def prefixEnd_506179 : Nat := 4983230072969 + 3 ^ 40 * 506179 * 2
def baseEnd_506179 : Nat := 259913124212280306034631

theorem tailTrace_506179 : CollatzResearch.WordTrace tailWord_506179 prefixEnd_506179 259913124212280306034631 := by
  unfold tailWord_506179
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461864833207406335793591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12307909888804937557195727 18461864833207406335793591)
  ·
    refine ⟨27692797249811109503690387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18461864833207406335793591 27692797249811109503690387)
    ·
      refine ⟨41539195874716664255535581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27692797249811109503690387 41539195874716664255535581)
      ·
        refine ⟨15577198453018749095825843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41539195874716664255535581 15577198453018749095825843)
        ·
          refine ⟨23365797679528123643738765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577198453018749095825843 23365797679528123643738765)
          ·
            refine ⟨8762174129823046366402037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23365797679528123643738765 8762174129823046366402037)
            ·
              refine ⟨821453824670910596850191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8762174129823046366402037 821453824670910596850191)
              ·
                refine ⟨1232180737006365895275287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821453824670910596850191 1232180737006365895275287)
                ·
                  refine ⟨1848271105509548842912931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232180737006365895275287 1848271105509548842912931)
                  ·
                    refine ⟨2772406658264323264369397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848271105509548842912931 2772406658264323264369397)
                    ·
                      refine ⟨259913124212280306034631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2772406658264323264369397 259913124212280306034631)
                      ·
                        rfl

theorem cell23_506179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_506179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506179 prefixEnd_506179 := by exact prefixLift 506179
  have htrace : WordTrace (prefixWord ++ tailWord_506179) baseStart_506179 baseEnd_506179 := by
    simpa [prefixWord, tailWord_506179, baseEnd_506179] using wordTrace_append hprefix tailTrace_506179
  have hstable : (prefixWord ++ tailWord_506179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506179).length < 2 ^ (prefixWord ++ tailWord_506179).sum := by decide
  have hdescent : baseEnd_506179 < baseStart_506179 := by decide
  rcases family_descends (prefixWord ++ tailWord_506179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506196 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_506196 : Nat := 118140960795 + 506196 * 2 ^ 59
def prefixEnd_506196 : Nat := 4983230072969 + 3 ^ 40 * 506196 * 2
def baseEnd_506196 : Nat := 259921853383406739522053

theorem tailTrace_506196 : CollatzResearch.WordTrace tailWord_506196 prefixEnd_506196 259921853383406739522053 := by
  unfold tailWord_506196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9231242437072909119581221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12308323249430545492774961 9231242437072909119581221)
  ·
    refine ⟨1730857956951170459921479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9231242437072909119581221 1730857956951170459921479)
    ·
      refine ⟨2596286935426755689882219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1730857956951170459921479 2596286935426755689882219)
      ·
        refine ⟨3894430403140133534823329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596286935426755689882219 3894430403140133534823329)
        ·
          refine ⟨2920822802355100151117497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3894430403140133534823329 2920822802355100151117497)
          ·
            refine ⟨2190617101766325113338123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920822802355100151117497 2190617101766325113338123)
            ·
              refine ⟨3285925652649487670007185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190617101766325113338123 3285925652649487670007185)
              ·
                refine ⟨2464444239487115752505389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285925652649487670007185 2464444239487115752505389)
                ·
                  refine ⟨924166589807668407189521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2464444239487115752505389 924166589807668407189521)
                  ·
                    refine ⟨693124942355751305392141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 924166589807668407189521 693124942355751305392141)
                    ·
                      refine ⟨259921853383406739522053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693124942355751305392141 259921853383406739522053)
                      ·
                        rfl

theorem cell23_506196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_506196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506196 prefixEnd_506196 := by exact prefixLift 506196
  have htrace : WordTrace (prefixWord ++ tailWord_506196) baseStart_506196 baseEnd_506196 := by
    simpa [prefixWord, tailWord_506196, baseEnd_506196] using wordTrace_append hprefix tailTrace_506196
  have hstable : (prefixWord ++ tailWord_506196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506196).length < 2 ^ (prefixWord ++ tailWord_506196).sum := by decide
  have hdescent : baseEnd_506196 < baseStart_506196 := by decide
  rcases family_descends (prefixWord ++ tailWord_506196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506210 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_506210 : Nat := 118140960795 + 506210 * 2 ^ 59
def prefixEnd_506210 : Nat := 4983230072969 + 3 ^ 40 * 506210 * 2
def baseEnd_506210 : Nat := 259929042112569684746989

theorem tailTrace_506210 : CollatzResearch.WordTrace tailWord_506210 prefixEnd_506210 259929042112569684746989 := by
  unfold tailWord_506210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615748874023774657543021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12308663664063399086781389 4615748874023774657543021)
  ·
    refine ⟨1730905827758915496578633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4615748874023774657543021 1730905827758915496578633)
    ·
      refine ⟨1298179370819186622433975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1730905827758915496578633 1298179370819186622433975)
      ·
        refine ⟨1947269056228779933650963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298179370819186622433975 1947269056228779933650963)
        ·
          refine ⟨2920903584343169900476445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947269056228779933650963 2920903584343169900476445)
          ·
            refine ⟨1095338844128688712678667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2920903584343169900476445 1095338844128688712678667)
            ·
              refine ⟨1643008266193033069018001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095338844128688712678667 1643008266193033069018001)
              ·
                refine ⟨1232256199644774801763501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643008266193033069018001 1232256199644774801763501)
                ·
                  refine ⟨462096074866790550661313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1232256199644774801763501 462096074866790550661313)
                  ·
                    refine ⟨346572056150092912995985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462096074866790550661313 346572056150092912995985)
                    ·
                      refine ⟨259929042112569684746989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346572056150092912995985 259929042112569684746989)
                      ·
                        rfl

theorem cell23_506210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_506210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506210 prefixEnd_506210 := by exact prefixLift 506210
  have htrace : WordTrace (prefixWord ++ tailWord_506210) baseStart_506210 baseEnd_506210 := by
    simpa [prefixWord, tailWord_506210, baseEnd_506210] using wordTrace_append hprefix tailTrace_506210
  have hstable : (prefixWord ++ tailWord_506210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506210).length < 2 ^ (prefixWord ++ tailWord_506210).sum := by decide
  have hdescent : baseEnd_506210 < baseStart_506210 := by decide
  rcases family_descends (prefixWord ++ tailWord_506210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506216 : List Nat := [2, 1, 4, 2, 2, 2, 3, 7]
def baseStart_506216 : Nat := 118140960795 + 506216 * 2 ^ 59
def prefixEnd_506216 : Nat := 4983230072969 + 3 ^ 40 * 506216 * 2
def baseEnd_506216 : Nat := 9627115666536913380443

theorem tailTrace_506216 : CollatzResearch.WordTrace tailWord_506216 prefixEnd_506216 9627115666536913380443 := by
  unfold tailWord_506216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9231607167036680827445251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12308809556048907769927001 9231607167036680827445251)
  ·
    refine ⟨13847410750555021241167877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9231607167036680827445251 13847410750555021241167877)
    ·
      refine ⟨2596389515729066482718977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13847410750555021241167877 2596389515729066482718977)
      ·
        refine ⟨1947292136796799862039233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2596389515729066482718977 1947292136796799862039233)
        ·
          refine ⟨1460469102597599896529425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1947292136796799862039233 1460469102597599896529425)
          ·
            refine ⟨1095351826948199922397069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1460469102597599896529425 1095351826948199922397069)
            ·
              refine ⟨410756935105574970898901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095351826948199922397069 410756935105574970898901)
              ·
                refine ⟨9627115666536913380443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 410756935105574970898901 9627115666536913380443)
                ·
                  rfl

theorem cell23_506216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 7].length) (baseStart_506216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506216 prefixEnd_506216 := by exact prefixLift 506216
  have htrace : WordTrace (prefixWord ++ tailWord_506216) baseStart_506216 baseEnd_506216 := by
    simpa [prefixWord, tailWord_506216, baseEnd_506216] using wordTrace_append hprefix tailTrace_506216
  have hstable : (prefixWord ++ tailWord_506216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506216).length < 2 ^ (prefixWord ++ tailWord_506216).sum := by decide
  have hdescent : baseEnd_506216 < baseStart_506216 := by decide
  rcases family_descends (prefixWord ++ tailWord_506216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506226 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_506226 : Nat := 118140960795 + 506226 * 2 ^ 59
def prefixEnd_506226 : Nat := 4983230072969 + 3 ^ 40 * 506226 * 2
def baseEnd_506226 : Nat := 259937257803041622146915

theorem tailTrace_506226 : CollatzResearch.WordTrace tailWord_506226 prefixEnd_506226 259937257803041622146915 := by
  unfold tailWord_506226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615894766009283340688633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12309052709358088908503021 4615894766009283340688633)
  ·
    refine ⟨3461921074506962505516475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4615894766009283340688633 3461921074506962505516475)
    ·
      refine ⟨5192881611760443758274713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3461921074506962505516475 5192881611760443758274713)
      ·
        refine ⟨3894661208820332818706035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192881611760443758274713 3894661208820332818706035)
        ·
          refine ⟨5841991813230499228059053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894661208820332818706035 5841991813230499228059053)
          ·
            refine ⟨2190746929961437210522145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5841991813230499228059053 2190746929961437210522145)
            ·
              refine ⟨1643060197471077907891609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190746929961437210522145 1643060197471077907891609)
              ·
                refine ⟨1232295148103308430918707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1643060197471077907891609 1232295148103308430918707)
                ·
                  refine ⟨1848442722154962646378061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232295148103308430918707 1848442722154962646378061)
                  ·
                    refine ⟨693166020808110992391773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848442722154962646378061 693166020808110992391773)
                    ·
                      refine ⟨259937257803041622146915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693166020808110992391773 259937257803041622146915)
                      ·
                        rfl

theorem cell23_506226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_506226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506226 prefixEnd_506226 := by exact prefixLift 506226
  have htrace : WordTrace (prefixWord ++ tailWord_506226) baseStart_506226 baseEnd_506226 := by
    simpa [prefixWord, tailWord_506226, baseEnd_506226] using wordTrace_append hprefix tailTrace_506226
  have hstable : (prefixWord ++ tailWord_506226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506226).length < 2 ^ (prefixWord ++ tailWord_506226).sum := by decide
  have hdescent : baseEnd_506226 < baseStart_506226 := by decide
  rcases family_descends (prefixWord ++ tailWord_506226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506236 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_506236 : Nat := 118140960795 + 506236 * 2 ^ 59
def prefixEnd_506236 : Nat := 4983230072969 + 3 ^ 40 * 506236 * 2
def baseEnd_506236 : Nat := 259942392609586583021869

theorem tailTrace_506236 : CollatzResearch.WordTrace tailWord_506236 prefixEnd_506236 259942392609586583021869 := by
  unfold tailWord_506236
  simp only [CollatzResearch.WordTrace]
  refine ⟨9231971897000452535309281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12309295862667270047079041 9231971897000452535309281)
  ·
    refine ⟨6923978922750339401481961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9231971897000452535309281 6923978922750339401481961)
    ·
      refine ⟨5192984192062754551111471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923978922750339401481961 5192984192062754551111471)
      ·
        refine ⟨7789476288094131826667207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5192984192062754551111471 7789476288094131826667207)
        ·
          refine ⟨11684214432141197740000811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789476288094131826667207 11684214432141197740000811)
          ·
            refine ⟨17526321648211796610001217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684214432141197740000811 17526321648211796610001217)
            ·
              refine ⟨13144741236158847457500913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17526321648211796610001217 13144741236158847457500913)
              ·
                refine ⟨9858555927119135593125685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144741236158847457500913 9858555927119135593125685)
                ·
                  refine ⟨924239618167418961855533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9858555927119135593125685 924239618167418961855533)
                  ·
                    refine ⟨346589856812782110695825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924239618167418961855533 346589856812782110695825)
                    ·
                      refine ⟨259942392609586583021869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346589856812782110695825 259942392609586583021869)
                      ·
                        rfl

theorem cell23_506236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_506236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506236 prefixEnd_506236 := by exact prefixLift 506236
  have htrace : WordTrace (prefixWord ++ tailWord_506236) baseStart_506236 baseEnd_506236 := by
    simpa [prefixWord, tailWord_506236, baseEnd_506236] using wordTrace_append hprefix tailTrace_506236
  have hstable : (prefixWord ++ tailWord_506236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506236).length < 2 ^ (prefixWord ++ tailWord_506236).sum := by decide
  have hdescent : baseEnd_506236 < baseStart_506236 := by decide
  rcases family_descends (prefixWord ++ tailWord_506236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506243 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 3]
def baseStart_506243 : Nat := 118140960795 + 506243 * 2 ^ 59
def prefixEnd_506243 : Nat := 4983230072969 + 3 ^ 40 * 506243 * 2
def baseEnd_506243 : Nat := 259945986974168055634337

theorem tailTrace_506243 : CollatzResearch.WordTrace tailWord_506243 prefixEnd_506243 259945986974168055634337 := by
  unfold tailWord_506243
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464199104975545266123383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12309466069983696844082255 18464199104975545266123383)
  ·
    refine ⟨27696298657463317899185075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18464199104975545266123383 27696298657463317899185075)
    ·
      refine ⟨41544447986194976848777613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27696298657463317899185075 41544447986194976848777613)
      ·
        refine ⟨15579167994823116318291605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41544447986194976848777613 15579167994823116318291605)
        ·
          refine ⟨730273499757333577419919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15579167994823116318291605 730273499757333577419919)
          ·
            refine ⟨1095410249636000366129879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730273499757333577419919 1095410249636000366129879)
            ·
              refine ⟨1643115374454000549194819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095410249636000366129879 1643115374454000549194819)
              ·
                refine ⟨2464673061681000823792229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643115374454000549194819 2464673061681000823792229)
                ·
                  refine ⟨462126199065187654461043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464673061681000823792229 462126199065187654461043)
                  ·
                    refine ⟨693189298597781481691565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462126199065187654461043 693189298597781481691565)
                    ·
                      refine ⟨259945986974168055634337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693189298597781481691565 259945986974168055634337)
                      ·
                        rfl

theorem cell23_506243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_506243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506243 prefixEnd_506243 := by exact prefixLift 506243
  have htrace : WordTrace (prefixWord ++ tailWord_506243) baseStart_506243 baseEnd_506243 := by
    simpa [prefixWord, tailWord_506243, baseEnd_506243] using wordTrace_append hprefix tailTrace_506243
  have hstable : (prefixWord ++ tailWord_506243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506243).length < 2 ^ (prefixWord ++ tailWord_506243).sum := by decide
  have hdescent : baseEnd_506243 < baseStart_506243 := by decide
  rcases family_descends (prefixWord ++ tailWord_506243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506260 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_506260 : Nat := 118140960795 + 506260 * 2 ^ 59
def prefixEnd_506260 : Nat := 4983230072969 + 3 ^ 40 * 506260 * 2
def baseEnd_506260 : Nat := 259954716145294489121759

theorem tailTrace_506260 : CollatzResearch.WordTrace tailWord_506260 prefixEnd_506260 259954716145294489121759 := by
  unfold tailWord_506260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232409572956978584746117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12309879430609304779661489 9232409572956978584746117)
  ·
    refine ⟨1731076794929433484639897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9232409572956978584746117 1731076794929433484639897)
    ·
      refine ⟨1298307596197075113479923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1731076794929433484639897 1298307596197075113479923)
      ·
        refine ⟨1947461394295612670219885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298307596197075113479923 1947461394295612670219885)
        ·
          refine ⟨730298022860854751332457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1947461394295612670219885 730298022860854751332457)
          ·
            refine ⟨547723517145641063499343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730298022860854751332457 547723517145641063499343)
            ·
              refine ⟨821585275718461595249015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547723517145641063499343 821585275718461595249015)
              ·
                refine ⟨1232377913577692392873523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821585275718461595249015 1232377913577692392873523)
                ·
                  refine ⟨1848566870366538589310285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232377913577692392873523 1848566870366538589310285)
                  ·
                    refine ⟨693212576387451970991357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1848566870366538589310285 693212576387451970991357)
                    ·
                      refine ⟨259954716145294489121759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693212576387451970991357 259954716145294489121759)
                      ·
                        rfl

theorem cell23_506260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_506260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506260 prefixEnd_506260 := by exact prefixLift 506260
  have htrace : WordTrace (prefixWord ++ tailWord_506260) baseStart_506260 baseEnd_506260 := by
    simpa [prefixWord, tailWord_506260, baseEnd_506260] using wordTrace_append hprefix tailTrace_506260
  have hstable : (prefixWord ++ tailWord_506260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506260).length < 2 ^ (prefixWord ++ tailWord_506260).sum := by decide
  have hdescent : baseEnd_506260 < baseStart_506260 := by decide
  rcases family_descends (prefixWord ++ tailWord_506260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506299 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3]
def baseStart_506299 : Nat := 118140960795 + 506299 * 2 ^ 59
def prefixEnd_506299 : Nat := 4983230072969 + 3 ^ 40 * 506299 * 2
def baseEnd_506299 : Nat := 259974741890819836534079

theorem tailTrace_506299 : CollatzResearch.WordTrace tailWord_506299 prefixEnd_506299 259974741890819836534079 := by
  unfold tailWord_506299
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466241592772666830161951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310827728515111220107967 18466241592772666830161951)
  ·
    refine ⟨27699362389159000245242927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18466241592772666830161951 27699362389159000245242927)
    ·
      refine ⟨41549043583738500367864391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27699362389159000245242927 41549043583738500367864391)
      ·
        refine ⟨62323565375607750551796587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41549043583738500367864391 62323565375607750551796587)
        ·
          refine ⟨93485348063411625827694881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62323565375607750551796587 93485348063411625827694881)
          ·
            refine ⟨70114011047558719370771161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93485348063411625827694881 70114011047558719370771161)
            ·
              refine ⟨52585508285669039528078371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70114011047558719370771161 52585508285669039528078371)
              ·
                refine ⟨78878262428503559292117557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52585508285669039528078371 78878262428503559292117557)
                ·
                  refine ⟨7394837102672208683636021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78878262428503559292117557 7394837102672208683636021)
                  ·
                    refine ⟨693265978375519564090877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7394837102672208683636021 693265978375519564090877)
                    ·
                      refine ⟨259974741890819836534079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693265978375519564090877 259974741890819836534079)
                      ·
                        rfl

theorem cell23_506299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 3].length) (baseStart_506299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506299 prefixEnd_506299 := by exact prefixLift 506299
  have htrace : WordTrace (prefixWord ++ tailWord_506299) baseStart_506299 baseEnd_506299 := by
    simpa [prefixWord, tailWord_506299, baseEnd_506299] using wordTrace_append hprefix tailTrace_506299
  have hstable : (prefixWord ++ tailWord_506299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506299).length < 2 ^ (prefixWord ++ tailWord_506299).sum := by decide
  have hdescent : baseEnd_506299 < baseStart_506299 := by decide
  rcases family_descends (prefixWord ++ tailWord_506299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506300 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_506300 : Nat := 118140960795 + 506300 * 2 ^ 59
def prefixEnd_506300 : Nat := 4983230072969 + 3 ^ 40 * 506300 * 2
def baseEnd_506300 : Nat := 259975255371474332621575

theorem tailTrace_506300 : CollatzResearch.WordTrace tailWord_506300 prefixEnd_506300 259975255371474332621575 := by
  unfold tailWord_506300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9233139032884522000474177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12310852043846029333965569 9233139032884522000474177)
  ·
    refine ⟨6924854274663391500355633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9233139032884522000474177 6924854274663391500355633)
    ·
      refine ⟨5193640705997543625266725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6924854274663391500355633 5193640705997543625266725)
      ·
        refine ⟨973807632374539429737511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5193640705997543625266725 973807632374539429737511)
        ·
          refine ⟨1460711448561809144606267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973807632374539429737511 1460711448561809144606267)
          ·
            refine ⟨2191067172842713716909401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460711448561809144606267 2191067172842713716909401)
            ·
              refine ⟨1643300379632035287682051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191067172842713716909401 1643300379632035287682051)
              ·
                refine ⟨2464950569448052931523077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643300379632035287682051 2464950569448052931523077)
                ·
                  refine ⟨462178231771509924660577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464950569448052931523077 462178231771509924660577)
                  ·
                    refine ⟨346633673828632443495433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462178231771509924660577 346633673828632443495433)
                    ·
                      refine ⟨259975255371474332621575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346633673828632443495433 259975255371474332621575)
                      ·
                        rfl

theorem cell23_506300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_506300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506300 prefixEnd_506300 := by exact prefixLift 506300
  have htrace : WordTrace (prefixWord ++ tailWord_506300) baseStart_506300 baseEnd_506300 := by
    simpa [prefixWord, tailWord_506300, baseEnd_506300] using wordTrace_append hprefix tailTrace_506300
  have hstable : (prefixWord ++ tailWord_506300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506300).length < 2 ^ (prefixWord ++ tailWord_506300).sum := by decide
  have hdescent : baseEnd_506300 < baseStart_506300 := by decide
  rcases family_descends (prefixWord ++ tailWord_506300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506319 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 6, 5]
def baseStart_506319 : Nat := 118140960795 + 506319 * 2 ^ 59
def prefixEnd_506319 : Nat := 4983230072969 + 3 ^ 40 * 506319 * 2
def baseEnd_506319 : Nat := 86661670501303252761329

theorem tailTrace_506319 : CollatzResearch.WordTrace tailWord_506319 prefixEnd_506319 86661670501303252761329 := by
  unfold tailWord_506319
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466971052700210245890011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12311314035133473497260007 18466971052700210245890011)
  ·
    refine ⟨27700456579050315368835017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18466971052700210245890011 27700456579050315368835017)
    ·
      refine ⟨20775342434287736526626263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27700456579050315368835017 20775342434287736526626263)
      ·
        refine ⟨31163013651431604789939395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20775342434287736526626263 31163013651431604789939395)
        ·
          refine ⟨46744520477147407184909093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31163013651431604789939395 46744520477147407184909093)
          ·
            refine ⟨8764597589465138847170455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46744520477147407184909093 8764597589465138847170455)
            ·
              refine ⟨13146896384197708270755683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764597589465138847170455 13146896384197708270755683)
              ·
                refine ⟨19720344576296562406133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13146896384197708270755683 19720344576296562406133525)
                ·
                  refine ⟨924391152013901362787509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19720344576296562406133525 924391152013901362787509)
                  ·
                    refine ⟨86661670501303252761329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 924391152013901362787509 86661670501303252761329)
                    ·
                      rfl

theorem cell23_506319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 5].length) (baseStart_506319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506319 prefixEnd_506319 := by exact prefixLift 506319
  have htrace : WordTrace (prefixWord ++ tailWord_506319) baseStart_506319 baseEnd_506319 := by
    simpa [prefixWord, tailWord_506319, baseEnd_506319] using wordTrace_append hprefix tailTrace_506319
  have hstable : (prefixWord ++ tailWord_506319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506319).length < 2 ^ (prefixWord ++ tailWord_506319).sum := by decide
  have hdescent : baseEnd_506319 < baseStart_506319 := by decide
  rcases family_descends (prefixWord ++ tailWord_506319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506329 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_506329 : Nat := 118140960795 + 506329 * 2 ^ 59
def prefixEnd_506329 : Nat := 4983230072969 + 3 ^ 40 * 506329 * 2
def baseEnd_506329 : Nat := 259990146310454719158941

theorem tailTrace_506329 : CollatzResearch.WordTrace tailWord_506329 prefixEnd_506329 259990146310454719158941 := by
  unfold tailWord_506329
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467335782663981953754041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12311557188442654635836027 18467335782663981953754041)
  ·
    refine ⟨13850501836997986465315531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18467335782663981953754041 13850501836997986465315531)
    ·
      refine ⟨20775752755496979697973297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13850501836997986465315531 20775752755496979697973297)
      ·
        refine ⟨15581814566622734773479973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20775752755496979697973297 15581814566622734773479973)
        ·
          refine ⟨2921590231241762770027495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15581814566622734773479973 2921590231241762770027495)
          ·
            refine ⟨4382385346862644155041243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921590231241762770027495 4382385346862644155041243)
            ·
              refine ⟨6573578020293966232561865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382385346862644155041243 6573578020293966232561865)
              ·
                refine ⟨4930183515220474674421399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573578020293966232561865 4930183515220474674421399)
                ·
                  refine ⟨7395275272830712011632099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930183515220474674421399 7395275272830712011632099)
                  ·
                    refine ⟨11092912909246068017448149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395275272830712011632099 11092912909246068017448149)
                    ·
                      refine ⟨259990146310454719158941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11092912909246068017448149 259990146310454719158941)
                      ·
                        rfl

theorem cell23_506329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_506329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506329 prefixEnd_506329 := by exact prefixLift 506329
  have htrace : WordTrace (prefixWord ++ tailWord_506329) baseStart_506329 baseEnd_506329 := by
    simpa [prefixWord, tailWord_506329, baseEnd_506329] using wordTrace_append hprefix tailTrace_506329
  have hstable : (prefixWord ++ tailWord_506329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506329).length < 2 ^ (prefixWord ++ tailWord_506329).sum := by decide
  have hdescent : baseEnd_506329 < baseStart_506329 := by decide
  rcases family_descends (prefixWord ++ tailWord_506329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506336 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_506336 : Nat := 118140960795 + 506336 * 2 ^ 59
def prefixEnd_506336 : Nat := 4983230072969 + 3 ^ 40 * 506336 * 2
def baseEnd_506336 : Nat := 86664580225012063923803

theorem tailTrace_506336 : CollatzResearch.WordTrace tailWord_506336 prefixEnd_506336 86664580225012063923803 := by
  unfold tailWord_506336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9233795546819311074629431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12311727395759081432839241 9233795546819311074629431)
  ·
    refine ⟨13850693320228966611944147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9233795546819311074629431 13850693320228966611944147)
    ·
      refine ⟨20776039980343449917916221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13850693320228966611944147 20776039980343449917916221)
      ·
        refine ⟨7791014992628793719218583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20776039980343449917916221 7791014992628793719218583)
        ·
          refine ⟨11686522488943190578827875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791014992628793719218583 11686522488943190578827875)
          ·
            refine ⟨17529783733414785868241813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11686522488943190578827875 17529783733414785868241813)
            ·
              refine ⟨821708612503818087573835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17529783733414785868241813 821708612503818087573835)
              ·
                refine ⟨1232562918755727131360753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821708612503818087573835 1232562918755727131360753)
                ·
                  refine ⟨924422189066795348520565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232562918755727131360753 924422189066795348520565)
                  ·
                    refine ⟨86664580225012063923803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 924422189066795348520565 86664580225012063923803)
                    ·
                      rfl

theorem cell23_506336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_506336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506336 prefixEnd_506336 := by exact prefixLift 506336
  have htrace : WordTrace (prefixWord ++ tailWord_506336) baseStart_506336 baseEnd_506336 := by
    simpa [prefixWord, tailWord_506336, baseEnd_506336] using wordTrace_append hprefix tailTrace_506336
  have hstable : (prefixWord ++ tailWord_506336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506336).length < 2 ^ (prefixWord ++ tailWord_506336).sum := by decide
  have hdescent : baseEnd_506336 < baseStart_506336 := by decide
  rcases family_descends (prefixWord ++ tailWord_506336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506346 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_506346 : Nat := 118140960795 + 506346 * 2 ^ 59
def prefixEnd_506346 : Nat := 4983230072969 + 3 ^ 40 * 506346 * 2
def baseEnd_506346 : Nat := 259998875481581152646363

theorem tailTrace_506346 : CollatzResearch.WordTrace tailWord_506346 prefixEnd_506346 259998875481581152646363 := by
  unfold tailWord_506346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616988955900598464280723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12311970549068262571415261 4616988955900598464280723)
  ·
    refine ⟨6925483433850897696421085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4616988955900598464280723 6925483433850897696421085)
    ·
      refine ⟨2597056287694086636157907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6925483433850897696421085 2597056287694086636157907)
      ·
        refine ⟨3895584431541129954236861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597056287694086636157907 3895584431541129954236861)
        ·
          refine ⟨1460844161827923732838823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3895584431541129954236861 1460844161827923732838823)
          ·
            refine ⟨2191266242741885599258235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460844161827923732838823 2191266242741885599258235)
            ·
              refine ⟨3286899364112828398887353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191266242741885599258235 3286899364112828398887353)
              ·
                refine ⟨2465174523084621299165515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286899364112828398887353 2465174523084621299165515)
                ·
                  refine ⟨3697761784626931948748273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465174523084621299165515 3697761784626931948748273)
                  ·
                    refine ⟨2773321338470198961561205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697761784626931948748273 2773321338470198961561205)
                    ·
                      refine ⟨259998875481581152646363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2773321338470198961561205 259998875481581152646363)
                      ·
                        rfl

theorem cell23_506346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_506346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506346 prefixEnd_506346 := by exact prefixLift 506346
  have htrace : WordTrace (prefixWord ++ tailWord_506346) baseStart_506346 baseEnd_506346 := by
    simpa [prefixWord, tailWord_506346, baseEnd_506346] using wordTrace_append hprefix tailTrace_506346
  have hstable : (prefixWord ++ tailWord_506346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506346).length < 2 ^ (prefixWord ++ tailWord_506346).sum := by decide
  have hdescent : baseEnd_506346 < baseStart_506346 := by decide
  rcases family_descends (prefixWord ++ tailWord_506346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506376 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_506376 : Nat := 118140960795 + 506376 * 2 ^ 59
def prefixEnd_506376 : Nat := 4983230072969 + 3 ^ 40 * 506376 * 2
def baseEnd_506376 : Nat := 260014279901216035271225

theorem tailTrace_506376 : CollatzResearch.WordTrace tailWord_506376 prefixEnd_506376 260014279901216035271225 := by
  unfold tailWord_506376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234525006746854490357491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12312700008995805987143321 9234525006746854490357491)
  ·
    refine ⟨13851787510120281735536237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234525006746854490357491 13851787510120281735536237)
    ·
      refine ⟨5194420316295105650826089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13851787510120281735536237 5194420316295105650826089)
      ·
        refine ⟨3895815237221329238119567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5194420316295105650826089 3895815237221329238119567)
        ·
          refine ⟨5843722855831993857179351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895815237221329238119567 5843722855831993857179351)
          ·
            refine ⟨8765584283747990785769027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843722855831993857179351 8765584283747990785769027)
            ·
              refine ⟨13148376425621986178653541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765584283747990785769027 13148376425621986178653541)
              ·
                refine ⟨2465320579804122408497539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13148376425621986178653541 2465320579804122408497539)
                ·
                  refine ⟨3697980869706183612746309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465320579804122408497539 3697980869706183612746309)
                  ·
                    refine ⟨693371413069909427389933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3697980869706183612746309 693371413069909427389933)
                    ·
                      refine ⟨260014279901216035271225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693371413069909427389933 260014279901216035271225)
                      ·
                        rfl

theorem cell23_506376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_506376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506376 prefixEnd_506376 := by exact prefixLift 506376
  have htrace : WordTrace (prefixWord ++ tailWord_506376) baseStart_506376 baseEnd_506376 := by
    simpa [prefixWord, tailWord_506376, baseEnd_506376] using wordTrace_append hprefix tailTrace_506376
  have hstable : (prefixWord ++ tailWord_506376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506376).length < 2 ^ (prefixWord ++ tailWord_506376).sum := by decide
  have hdescent : baseEnd_506376 < baseStart_506376 := by decide
  rcases family_descends (prefixWord ++ tailWord_506376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506450 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_506450 : Nat := 118140960795 + 506450 * 2 ^ 59
def prefixEnd_506450 : Nat := 4983230072969 + 3 ^ 40 * 506450 * 2
def baseEnd_506450 : Nat := 260052277469648745745885

theorem tailTrace_506450 : CollatzResearch.WordTrace tailWord_506450 prefixEnd_506450 260052277469648745745885 := by
  unfold tailWord_506450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617937253806404904727201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12314499343483746412605869 4617937253806404904727201)
  ·
    refine ⟨3463452940354803678545401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4617937253806404904727201 3463452940354803678545401)
    ·
      refine ⟨2597589705266102758909051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3463452940354803678545401 2597589705266102758909051)
      ·
        refine ⟨3896384557899154138363577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597589705266102758909051 3896384557899154138363577)
        ·
          refine ⟨2922288418424365603772683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896384557899154138363577 2922288418424365603772683)
          ·
            refine ⟨4383432627636548405659025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922288418424365603772683 4383432627636548405659025)
            ·
              refine ⟨3287574470727411304244269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4383432627636548405659025 3287574470727411304244269)
              ·
                refine ⟨1232840426522779239091601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3287574470727411304244269 1232840426522779239091601)
                ·
                  refine ⟨924630319892084429318701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232840426522779239091601 924630319892084429318701)
                  ·
                    refine ⟨346736369959531660994513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924630319892084429318701 346736369959531660994513)
                    ·
                      refine ⟨260052277469648745745885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346736369959531660994513 260052277469648745745885)
                      ·
                        rfl

theorem cell23_506450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_506450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506450 prefixEnd_506450 := by exact prefixLift 506450
  have htrace : WordTrace (prefixWord ++ tailWord_506450) baseStart_506450 baseEnd_506450 := by
    simpa [prefixWord, tailWord_506450, baseEnd_506450] using wordTrace_append hprefix tailTrace_506450
  have hstable : (prefixWord ++ tailWord_506450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506450).length < 2 ^ (prefixWord ++ tailWord_506450).sum := by decide
  have hdescent : baseEnd_506450 < baseStart_506450 := by decide
  rcases family_descends (prefixWord ++ tailWord_506450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506456 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_506456 : Nat := 118140960795 + 506456 * 2 ^ 59
def prefixEnd_506456 : Nat := 4983230072969 + 3 ^ 40 * 506456 * 2
def baseEnd_506456 : Nat := 86685119451191907423619

theorem tailTrace_506456 : CollatzResearch.WordTrace tailWord_506456 prefixEnd_506456 86685119451191907423619 := by
  unfold tailWord_506456
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235983926601941321813611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12314645235469255095751481 9235983926601941321813611)
  ·
    refine ⟨13853975889902911982720417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235983926601941321813611 13853975889902911982720417)
    ·
      refine ⟨10390481917427183987040313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13853975889902911982720417 10390481917427183987040313)
      ·
        refine ⟨7792861438070387990280235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10390481917427183987040313 7792861438070387990280235)
        ·
          refine ⟨11689292157105581985420353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792861438070387990280235 11689292157105581985420353)
          ·
            refine ⟨8766969117829186489065265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689292157105581985420353 8766969117829186489065265)
            ·
              refine ⟨6575226838371889866798949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8766969117829186489065265 6575226838371889866798949)
              ·
                refine ⟨1232855032194729350024803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6575226838371889866798949 1232855032194729350024803)
                ·
                  refine ⟨1849282548292094025037205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232855032194729350024803 1849282548292094025037205)
                  ·
                    refine ⟨86685119451191907423619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1849282548292094025037205 86685119451191907423619)
                    ·
                      rfl

theorem cell23_506456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_506456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506456 prefixEnd_506456 := by exact prefixLift 506456
  have htrace : WordTrace (prefixWord ++ tailWord_506456) baseStart_506456 baseEnd_506456 := by
    simpa [prefixWord, tailWord_506456, baseEnd_506456] using wordTrace_append hprefix tailTrace_506456
  have hstable : (prefixWord ++ tailWord_506456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506456).length < 2 ^ (prefixWord ++ tailWord_506456).sum := by decide
  have hdescent : baseEnd_506456 < baseStart_506456 := by decide
  rcases family_descends (prefixWord ++ tailWord_506456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506473 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_506473 : Nat := 118140960795 + 506473 * 2 ^ 59
def prefixEnd_506473 : Nat := 4983230072969 + 3 ^ 40 * 506473 * 2
def baseEnd_506473 : Nat := 86688029174900718586093

theorem tailTrace_506473 : CollatzResearch.WordTrace tailWord_506473 prefixEnd_506473 86688029174900718586093 := by
  unfold tailWord_506473
  simp only [CollatzResearch.WordTrace]
  refine ⟨18472587894142294546996073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12315058596094863031330715 18472587894142294546996073)
  ·
    refine ⟨13854440920606720910247055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18472587894142294546996073 13854440920606720910247055)
    ·
      refine ⟨20781661380910081365370583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13854440920606720910247055 20781661380910081365370583)
      ·
        refine ⟨31172492071365122048055875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20781661380910081365370583 31172492071365122048055875)
        ·
          refine ⟨46758738107047683072083813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31172492071365122048055875 46758738107047683072083813)
          ·
            refine ⟨8767263395071440576015715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46758738107047683072083813 8767263395071440576015715)
            ·
              refine ⟨13150895092607160864023573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8767263395071440576015715 13150895092607160864023573)
              ·
                refine ⟨616448207465960665501105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13150895092607160864023573 616448207465960665501105)
                ·
                  refine ⟨462336155599470499125829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616448207465960665501105 462336155599470499125829)
                  ·
                    refine ⟨86688029174900718586093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462336155599470499125829 86688029174900718586093)
                    ·
                      rfl

theorem cell23_506473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_506473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506473 prefixEnd_506473 := by exact prefixLift 506473
  have htrace : WordTrace (prefixWord ++ tailWord_506473) baseStart_506473 baseEnd_506473 := by
    simpa [prefixWord, tailWord_506473, baseEnd_506473] using wordTrace_append hprefix tailTrace_506473
  have hstable : (prefixWord ++ tailWord_506473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506473).length < 2 ^ (prefixWord ++ tailWord_506473).sum := by decide
  have hdescent : baseEnd_506473 < baseStart_506473 := by decide
  rcases family_descends (prefixWord ++ tailWord_506473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506474 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_506474 : Nat := 118140960795 + 506474 * 2 ^ 59
def prefixEnd_506474 : Nat := 4983230072969 + 3 ^ 40 * 506474 * 2
def baseEnd_506474 : Nat := 260064601005356651845775

theorem tailTrace_506474 : CollatzResearch.WordTrace tailWord_506474 prefixEnd_506474 260064601005356651845775 := by
  unfold tailWord_506474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618156091784667929445619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12315082911425781145188317 4618156091784667929445619)
  ·
    refine ⟨6927234137677001894168429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618156091784667929445619 6927234137677001894168429)
    ·
      refine ⟨2597712801628875710313161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6927234137677001894168429 2597712801628875710313161)
      ·
        refine ⟨1948284601221656782734871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2597712801628875710313161 1948284601221656782734871)
        ·
          refine ⟨2922426901832485174102307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948284601221656782734871 2922426901832485174102307)
          ·
            refine ⟨4383640352748727761153461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922426901832485174102307 4383640352748727761153461)
            ·
              refine ⟨410966283070193227608137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4383640352748727761153461 410966283070193227608137)
              ·
                refine ⟨308224712302644920706103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410966283070193227608137 308224712302644920706103)
                ·
                  refine ⟨462337068453967381059155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308224712302644920706103 462337068453967381059155)
                  ·
                    refine ⟨693505602680951071588733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462337068453967381059155 693505602680951071588733)
                    ·
                      refine ⟨260064601005356651845775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693505602680951071588733 260064601005356651845775)
                      ·
                        rfl

theorem cell23_506474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_506474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506474 prefixEnd_506474 := by exact prefixLift 506474
  have htrace : WordTrace (prefixWord ++ tailWord_506474) baseStart_506474 baseEnd_506474 := by
    simpa [prefixWord, tailWord_506474, baseEnd_506474] using wordTrace_append hprefix tailTrace_506474
  have hstable : (prefixWord ++ tailWord_506474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506474).length < 2 ^ (prefixWord ++ tailWord_506474).sum := by decide
  have hdescent : baseEnd_506474 < baseStart_506474 := by decide
  rcases family_descends (prefixWord ++ tailWord_506474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506476 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_506476 : Nat := 118140960795 + 506476 * 2 ^ 59
def prefixEnd_506476 : Nat := 4983230072969 + 3 ^ 40 * 506476 * 2
def baseEnd_506476 : Nat := 260065627966665644020765

theorem tailTrace_506476 : CollatzResearch.WordTrace tailWord_506476 prefixEnd_506476 260065627966665644020765 := by
  unfold tailWord_506476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236348656565713029677641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12315131542087617372903521 9236348656565713029677641)
  ·
    refine ⟨6927261492424284772258231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9236348656565713029677641 6927261492424284772258231)
    ·
      refine ⟨10390892238636427158387347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927261492424284772258231 10390892238636427158387347)
      ·
        refine ⟨15586338357954640737581021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10390892238636427158387347 15586338357954640737581021)
        ·
          refine ⟨5844876884232990276592883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15586338357954640737581021 5844876884232990276592883)
          ·
            refine ⟨8767315326349485414889325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844876884232990276592883 8767315326349485414889325)
            ·
              refine ⟨3287743247381057030583497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8767315326349485414889325 3287743247381057030583497)
              ·
                refine ⟨2465807435535792772937623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3287743247381057030583497 2465807435535792772937623)
                ·
                  refine ⟨3698711153303689159406435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465807435535792772937623 3698711153303689159406435)
                  ·
                    refine ⟨5548066729955533739109653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698711153303689159406435 5548066729955533739109653)
                    ·
                      refine ⟨260065627966665644020765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5548066729955533739109653 260065627966665644020765)
                      ·
                        rfl

theorem cell23_506476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_506476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506476 prefixEnd_506476 := by exact prefixLift 506476
  have htrace : WordTrace (prefixWord ++ tailWord_506476) baseStart_506476 baseEnd_506476 := by
    simpa [prefixWord, tailWord_506476, baseEnd_506476] using wordTrace_append hprefix tailTrace_506476
  have hstable : (prefixWord ++ tailWord_506476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506476).length < 2 ^ (prefixWord ++ tailWord_506476).sum := by decide
  have hdescent : baseEnd_506476 < baseStart_506476 := by decide
  rcases family_descends (prefixWord ++ tailWord_506476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506500 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_506500 : Nat := 118140960795 + 506500 * 2 ^ 59
def prefixEnd_506500 : Nat := 4983230072969 + 3 ^ 40 * 506500 * 2
def baseEnd_506500 : Nat := 260077951502373550120655

theorem tailTrace_506500 : CollatzResearch.WordTrace tailWord_506500 prefixEnd_506500 260077951502373550120655 := by
  unfold tailWord_506500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236786332522239079114477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12315715110029652105485969 9236786332522239079114477)
  ·
    refine ⟨3463794874695839654667929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9236786332522239079114477 3463794874695839654667929)
    ·
      refine ⟨2597846156021879741000947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3463794874695839654667929 2597846156021879741000947)
      ·
        refine ⟨3896769234032819611501421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597846156021879741000947 3896769234032819611501421)
        ·
          refine ⟨1461288462762307354313033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3896769234032819611501421 1461288462762307354313033)
          ·
            refine ⟨1095966347071730515734775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461288462762307354313033 1095966347071730515734775)
            ·
              refine ⟨1643949520607595773602163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095966347071730515734775 1643949520607595773602163)
              ·
                refine ⟨2465924280911393660403245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643949520607595773602163 2465924280911393660403245)
                ·
                  refine ⟨924721605341772622651217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2465924280911393660403245 924721605341772622651217)
                  ·
                    refine ⟨693541204006329466988413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 924721605341772622651217 693541204006329466988413)
                    ·
                      refine ⟨260077951502373550120655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693541204006329466988413 260077951502373550120655)
                      ·
                        rfl

theorem cell23_506500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_506500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506500 prefixEnd_506500 := by exact prefixLift 506500
  have htrace : WordTrace (prefixWord ++ tailWord_506500) baseStart_506500 baseEnd_506500 := by
    simpa [prefixWord, tailWord_506500, baseEnd_506500] using wordTrace_append hprefix tailTrace_506500
  have hstable : (prefixWord ++ tailWord_506500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506500).length < 2 ^ (prefixWord ++ tailWord_506500).sum := by decide
  have hdescent : baseEnd_506500 < baseStart_506500 := by decide
  rcases family_descends (prefixWord ++ tailWord_506500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506574 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_506574 : Nat := 118140960795 + 506574 * 2 ^ 59
def prefixEnd_506574 : Nat := 4983230072969 + 3 ^ 40 * 506574 * 2
def baseEnd_506574 : Nat := 260115949070806260595315

theorem tailTrace_506574 : CollatzResearch.WordTrace tailWord_506574 prefixEnd_506574 260115949070806260595315 := by
  unfold tailWord_506574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309533958347048599552847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12317514444517592530948517 2309533958347048599552847)
  ·
    refine ⟨3464300937520572899329271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2309533958347048599552847 3464300937520572899329271)
    ·
      refine ⟨5196451406280859348993907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464300937520572899329271 5196451406280859348993907)
      ·
        refine ⟨7794677109421289023490861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196451406280859348993907 7794677109421289023490861)
        ·
          refine ⟨2923003916032983383809073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7794677109421289023490861 2923003916032983383809073)
          ·
            refine ⟨2192252937024737537856805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923003916032983383809073 2192252937024737537856805)
            ·
              refine ⟨411047425692138288348151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2192252937024737537856805 411047425692138288348151)
              ·
                refine ⟨616571138538207432522227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411047425692138288348151 616571138538207432522227)
                ·
                  refine ⟨924856707807311148783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616571138538207432522227 924856707807311148783341)
                  ·
                    refine ⟨346821265427741680793753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924856707807311148783341 346821265427741680793753)
                    ·
                      refine ⟨260115949070806260595315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346821265427741680793753 260115949070806260595315)
                      ·
                        rfl

theorem cell23_506574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_506574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506574 prefixEnd_506574 := by exact prefixLift 506574
  have htrace : WordTrace (prefixWord ++ tailWord_506574) baseStart_506574 baseEnd_506574 := by
    simpa [prefixWord, tailWord_506574, baseEnd_506574] using wordTrace_append hprefix tailTrace_506574
  have hstable : (prefixWord ++ tailWord_506574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506574).length < 2 ^ (prefixWord ++ tailWord_506574).sum := by decide
  have hdescent : baseEnd_506574 < baseStart_506574 := by decide
  rcases family_descends (prefixWord ++ tailWord_506574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506581 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_506581 : Nat := 118140960795 + 506581 * 2 ^ 59
def prefixEnd_506581 : Nat := 4983230072969 + 3 ^ 40 * 506581 * 2
def baseEnd_506581 : Nat := 260119543435387733207783

theorem tailTrace_506581 : CollatzResearch.WordTrace tailWord_506581 prefixEnd_506581 260119543435387733207783 := by
  unfold tailWord_506581
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476526977751028991927597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12317684651834019327951731 18476526977751028991927597)
  ·
    refine ⟨6928697616656635871972849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18476526977751028991927597 6928697616656635871972849)
    ·
      refine ⟨5196523212492476903979637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6928697616656635871972849 5196523212492476903979637)
      ·
        refine ⟨487174051171169709748091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5196523212492476903979637 487174051171169709748091)
        ·
          refine ⟨730761076756754564622137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487174051171169709748091 730761076756754564622137)
          ·
            refine ⟨548070807567565923466603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730761076756754564622137 548070807567565923466603)
            ·
              refine ⟨822106211351348885199905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548070807567565923466603 822106211351348885199905)
              ·
                refine ⟨616579658513511663899929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822106211351348885199905 616579658513511663899929)
                ·
                  refine ⟨462434743885133747924947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616579658513511663899929 462434743885133747924947)
                  ·
                    refine ⟨693652115827700621887421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462434743885133747924947 693652115827700621887421)
                    ·
                      refine ⟨260119543435387733207783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693652115827700621887421 260119543435387733207783)
                      ·
                        rfl

theorem cell23_506581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_506581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506581 prefixEnd_506581 := by exact prefixLift 506581
  have htrace : WordTrace (prefixWord ++ tailWord_506581) baseStart_506581 baseEnd_506581 := by
    simpa [prefixWord, tailWord_506581, baseEnd_506581] using wordTrace_append hprefix tailTrace_506581
  have hstable : (prefixWord ++ tailWord_506581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506581).length < 2 ^ (prefixWord ++ tailWord_506581).sum := by decide
  have hdescent : baseEnd_506581 < baseStart_506581 := by decide
  rcases family_descends (prefixWord ++ tailWord_506581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506583 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_506583 : Nat := 118140960795 + 506583 * 2 ^ 59
def prefixEnd_506583 : Nat := 4983230072969 + 3 ^ 40 * 506583 * 2
def baseEnd_506583 : Nat := 260120570396696725382773

theorem tailTrace_506583 : CollatzResearch.WordTrace tailWord_506583 prefixEnd_506583 260120570396696725382773 := by
  unfold tailWord_506583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476599923743783333500403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12317733282495855555666935 18476599923743783333500403)
  ·
    refine ⟨27714899885615675000250605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18476599923743783333500403 27714899885615675000250605)
    ·
      refine ⟨10393087457105878125093977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27714899885615675000250605 10393087457105878125093977)
      ·
        refine ⟨7794815592829408593820483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10393087457105878125093977 7794815592829408593820483)
        ·
          refine ⟨11692223389244112890730725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794815592829408593820483 11692223389244112890730725)
          ·
            refine ⟨2192291885483271167012011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11692223389244112890730725 2192291885483271167012011)
            ·
              refine ⟨3288437828224906750518017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192291885483271167012011 3288437828224906750518017)
              ·
                refine ⟨2466328371168680062888513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288437828224906750518017 2466328371168680062888513)
                ·
                  refine ⟨1849746278376510047166385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466328371168680062888513 1849746278376510047166385)
                  ·
                    refine ⟨1387309708782382535374789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1849746278376510047166385 1387309708782382535374789)
                    ·
                      refine ⟨260120570396696725382773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1387309708782382535374789 260120570396696725382773)
                      ·
                        rfl

theorem cell23_506583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_506583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506583 prefixEnd_506583 := by exact prefixLift 506583
  have htrace : WordTrace (prefixWord ++ tailWord_506583) baseStart_506583 baseEnd_506583 := by
    simpa [prefixWord, tailWord_506583, baseEnd_506583] using wordTrace_append hprefix tailTrace_506583
  have hstable : (prefixWord ++ tailWord_506583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506583).length < 2 ^ (prefixWord ++ tailWord_506583).sum := by decide
  have hdescent : baseEnd_506583 < baseStart_506583 := by decide
  rcases family_descends (prefixWord ++ tailWord_506583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506593 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 7]
def baseStart_506593 : Nat := 118140960795 + 506593 * 2 ^ 59
def prefixEnd_506593 : Nat := 4983230072969 + 3 ^ 40 * 506593 * 2
def baseEnd_506593 : Nat := 28902856133693520695303

theorem tailTrace_506593 : CollatzResearch.WordTrace tailWord_506593 prefixEnd_506593 28902856133693520695303 := by
  unfold tailWord_506593
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476964653707555041364433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12317976435805036694242955 18476964653707555041364433)
  ·
    refine ⟨13857723490280666281023325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18476964653707555041364433 13857723490280666281023325)
    ·
      refine ⟨5196646308855249855383747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13857723490280666281023325 5196646308855249855383747)
      ·
        refine ⟨7794969463282874783075621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196646308855249855383747 7794969463282874783075621)
        ·
          refine ⟨1461556774365539021826679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7794969463282874783075621 1461556774365539021826679)
          ·
            refine ⟨2192335161548308532740019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461556774365539021826679 2192335161548308532740019)
            ·
              refine ⟨3288502742322462799110029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192335161548308532740019 3288502742322462799110029)
              ·
                refine ⟨1233188528370923549666261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3288502742322462799110029 1233188528370923549666261)
                ·
                  refine ⟨28902856133693520695303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1233188528370923549666261 28902856133693520695303)
                  ·
                    rfl

theorem cell23_506593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_506593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506593 prefixEnd_506593 := by exact prefixLift 506593
  have htrace : WordTrace (prefixWord ++ tailWord_506593) baseStart_506593 baseEnd_506593 := by
    simpa [prefixWord, tailWord_506593, baseEnd_506593] using wordTrace_append hprefix tailTrace_506593
  have hstable : (prefixWord ++ tailWord_506593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506593).length < 2 ^ (prefixWord ++ tailWord_506593).sum := by decide
  have hdescent : baseEnd_506593 < baseStart_506593 := by decide
  rcases family_descends (prefixWord ++ tailWord_506593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506623 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 2, 5]
def baseStart_506623 : Nat := 118140960795 + 506623 * 2 ^ 59
def prefixEnd_506623 : Nat := 4983230072969 + 3 ^ 40 * 506623 * 2
def baseEnd_506623 : Nat := 86713703207625522960863

theorem tailTrace_506623 : CollatzResearch.WordTrace tailWord_506623 prefixEnd_506623 86713703207625522960863 := by
  unfold tailWord_506623
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478058843598870164956523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12318705895732580109971015 18478058843598870164956523)
  ·
    refine ⟨27717088265398305247434785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18478058843598870164956523 27717088265398305247434785)
    ·
      refine ⟨20787816199048728935576089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27717088265398305247434785 20787816199048728935576089)
      ·
        refine ⟨15590862149286546701682067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20787816199048728935576089 15590862149286546701682067)
        ·
          refine ⟨23386293223929820052523101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15590862149286546701682067 23386293223929820052523101)
          ·
            refine ⟨8769859958973682519696163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23386293223929820052523101 8769859958973682519696163)
            ·
              refine ⟨13154789938460523779544245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769859958973682519696163 13154789938460523779544245)
              ·
                refine ⟨1233261556730674104332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13154789938460523779544245 1233261556730674104332273)
                ·
                  refine ⟨924946167548005578249205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233261556730674104332273 924946167548005578249205)
                  ·
                    refine ⟨86713703207625522960863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 924946167548005578249205 86713703207625522960863)
                    ·
                      rfl

theorem cell23_506623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_506623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506623 prefixEnd_506623 := by exact prefixLift 506623
  have htrace : WordTrace (prefixWord ++ tailWord_506623) baseStart_506623 baseEnd_506623 := by
    simpa [prefixWord, tailWord_506623, baseEnd_506623] using wordTrace_append hprefix tailTrace_506623
  have hstable : (prefixWord ++ tailWord_506623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506623).length < 2 ^ (prefixWord ++ tailWord_506623).sum := by decide
  have hdescent : baseEnd_506623 < baseStart_506623 := by decide
  rcases family_descends (prefixWord ++ tailWord_506623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506677 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_506677 : Nat := 118140960795 + 506677 * 2 ^ 59
def prefixEnd_506677 : Nat := 4983230072969 + 3 ^ 40 * 506677 * 2
def baseEnd_506677 : Nat := 260168837578219357607341

theorem tailTrace_506677 : CollatzResearch.WordTrace tailWord_506677 prefixEnd_506677 260168837578219357607341 := by
  unfold tailWord_506677
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480028385403237387422285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12320018923602158258281523 18480028385403237387422285)
  ·
    refine ⟨6930010644526214020283357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18480028385403237387422285 6930010644526214020283357)
    ·
      refine ⟨2598753991697330257606259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6930010644526214020283357 2598753991697330257606259)
      ·
        refine ⟨3898130987545995386409389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2598753991697330257606259 3898130987545995386409389)
        ·
          refine ⟨1461799120329748269903521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3898130987545995386409389 1461799120329748269903521)
          ·
            refine ⟨1096349340247311202427641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461799120329748269903521 1096349340247311202427641)
            ·
              refine ⟨822262005185483401820731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096349340247311202427641 822262005185483401820731)
              ·
                refine ⟨1233393007778225102731097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822262005185483401820731 1233393007778225102731097)
                ·
                  refine ⟨925044755833668827048323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233393007778225102731097 925044755833668827048323)
                  ·
                    refine ⟨1387567133750503240572485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 925044755833668827048323 1387567133750503240572485)
                    ·
                      refine ⟨260168837578219357607341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1387567133750503240572485 260168837578219357607341)
                      ·
                        rfl

theorem cell23_506677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_506677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506677 prefixEnd_506677 := by exact prefixLift 506677
  have htrace : WordTrace (prefixWord ++ tailWord_506677) baseStart_506677 baseEnd_506677 := by
    simpa [prefixWord, tailWord_506677, baseEnd_506677] using wordTrace_append hprefix tailTrace_506677
  have hstable : (prefixWord ++ tailWord_506677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506677).length < 2 ^ (prefixWord ++ tailWord_506677).sum := by decide
  have hdescent : baseEnd_506677 < baseStart_506677 := by decide
  rcases family_descends (prefixWord ++ tailWord_506677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506700 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 6]
def baseStart_506700 : Nat := 118140960795 + 506700 * 2 ^ 59
def prefixEnd_506700 : Nat := 4983230072969 + 3 ^ 40 * 506700 * 2
def baseEnd_506700 : Nat := 28908960848141418624415

theorem tailTrace_506700 : CollatzResearch.WordTrace tailWord_506700 prefixEnd_506700 28908960848141418624415 := by
  unfold tailWord_506700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240433632159956157754777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12320578176213274877006369 9240433632159956157754777)
  ·
    refine ⟨6930325224119967118316083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9240433632159956157754777 6930325224119967118316083)
    ·
      refine ⟨10395487836179950677474125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930325224119967118316083 10395487836179950677474125)
      ·
        refine ⟨3898307938567481504052797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10395487836179950677474125 3898307938567481504052797)
        ·
          refine ⟨1461865476962805564019799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3898307938567481504052797 1461865476962805564019799)
          ·
            refine ⟨2192798215444208346029699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461865476962805564019799 2192798215444208346029699)
            ·
              refine ⟨3289197323166312519044549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192798215444208346029699 3289197323166312519044549)
              ·
                refine ⟨616724498093683597320853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3289197323166312519044549 616724498093683597320853)
                ·
                  refine ⟨28908960848141418624415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 616724498093683597320853 28908960848141418624415)
                  ·
                    rfl

theorem cell23_506700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_506700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506700 prefixEnd_506700 := by exact prefixLift 506700
  have htrace : WordTrace (prefixWord ++ tailWord_506700) baseStart_506700 baseEnd_506700 := by
    simpa [prefixWord, tailWord_506700, baseEnd_506700] using wordTrace_append hprefix tailTrace_506700
  have hstable : (prefixWord ++ tailWord_506700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506700).length < 2 ^ (prefixWord ++ tailWord_506700).sum := by decide
  have hdescent : baseEnd_506700 < baseStart_506700 := by decide
  rcases family_descends (prefixWord ++ tailWord_506700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506704 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 1, 4]
def baseStart_506704 : Nat := 118140960795 + 506704 * 2 ^ 59
def prefixEnd_506704 : Nat := 4983230072969 + 3 ^ 40 * 506704 * 2
def baseEnd_506704 : Nat := 86727567185296917323239

theorem tailTrace_506704 : CollatzResearch.WordTrace tailWord_506704 prefixEnd_506704 86727567185296917323239 := by
  unfold tailWord_506704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240506578152710499327583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12320675437536947332436777 9240506578152710499327583)
  ·
    refine ⟨13860759867229065748991375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9240506578152710499327583 13860759867229065748991375)
    ·
      refine ⟨20791139800843598623487063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860759867229065748991375 20791139800843598623487063)
      ·
        refine ⟨31186709701265397935230595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20791139800843598623487063 31186709701265397935230595)
        ·
          refine ⟨46780064551898096902845893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31186709701265397935230595 46780064551898096902845893)
          ·
            refine ⟨8771262103480893169283605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46780064551898096902845893 8771262103480893169283605)
            ·
              refine ⟨411152911100666867310169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8771262103480893169283605 411152911100666867310169)
              ·
                refine ⟨308364683325500150482627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411152911100666867310169 308364683325500150482627)
                ·
                  refine ⟨462547024988250225723941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308364683325500150482627 462547024988250225723941)
                  ·
                    refine ⟨86727567185296917323239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462547024988250225723941 86727567185296917323239)
                    ·
                      rfl

theorem cell23_506704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 1, 4].length) (baseStart_506704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506704 prefixEnd_506704 := by exact prefixLift 506704
  have htrace : WordTrace (prefixWord ++ tailWord_506704) baseStart_506704 baseEnd_506704 := by
    simpa [prefixWord, tailWord_506704, baseEnd_506704] using wordTrace_append hprefix tailTrace_506704
  have hstable : (prefixWord ++ tailWord_506704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506704).length < 2 ^ (prefixWord ++ tailWord_506704).sum := by decide
  have hdescent : baseEnd_506704 < baseStart_506704 := by decide
  rcases family_descends (prefixWord ++ tailWord_506704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506727 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_506727 : Nat := 118140960795 + 506727 * 2 ^ 59
def prefixEnd_506727 : Nat := 4983230072969 + 3 ^ 40 * 506727 * 2
def baseEnd_506727 : Nat := 260194511610944161982111

theorem tailTrace_506727 : CollatzResearch.WordTrace tailWord_506727 prefixEnd_506727 260194511610944161982111 := by
  unfold tailWord_506727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18481852035222095926742435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12321234690148063951161623 18481852035222095926742435)
  ·
    refine ⟨27722778052833143890113653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18481852035222095926742435 27722778052833143890113653)
    ·
      refine ⟨2599010442453107239698155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27722778052833143890113653 2599010442453107239698155)
      ·
        refine ⟨3898515663679660859547233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599010442453107239698155 3898515663679660859547233)
        ·
          refine ⟨2923886747759745644660425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898515663679660859547233 2923886747759745644660425)
          ·
            refine ⟨2192915060819809233495319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923886747759745644660425 2192915060819809233495319)
            ·
              refine ⟨3289372591229713850242979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192915060819809233495319 3289372591229713850242979)
              ·
                refine ⟨4934058886844570775364469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289372591229713850242979 4934058886844570775364469)
                ·
                  refine ⟨462568020641678510190419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4934058886844570775364469 462568020641678510190419)
                  ·
                    refine ⟨693852030962517765285629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 462568020641678510190419 693852030962517765285629)
                    ·
                      refine ⟨260194511610944161982111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693852030962517765285629 260194511610944161982111)
                      ·
                        rfl

theorem cell23_506727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_506727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506727 prefixEnd_506727 := by exact prefixLift 506727
  have htrace : WordTrace (prefixWord ++ tailWord_506727) baseStart_506727 baseEnd_506727 := by
    simpa [prefixWord, tailWord_506727, baseEnd_506727] using wordTrace_append hprefix tailTrace_506727
  have hstable : (prefixWord ++ tailWord_506727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506727).length < 2 ^ (prefixWord ++ tailWord_506727).sum := by decide
  have hdescent : baseEnd_506727 < baseStart_506727 := by decide
  rcases family_descends (prefixWord ++ tailWord_506727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506737 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_506737 : Nat := 118140960795 + 506737 * 2 ^ 59
def prefixEnd_506737 : Nat := 4983230072969 + 3 ^ 40 * 506737 * 2
def baseEnd_506737 : Nat := 260199646417489122857065

theorem tailTrace_506737 : CollatzResearch.WordTrace tailWord_506737 prefixEnd_506737 260199646417489122857065 := by
  unfold tailWord_506737
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482216765185867634606465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12321477843457245089737643 18482216765185867634606465)
  ·
    refine ⟨13861662573889400725954849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18482216765185867634606465 13861662573889400725954849)
    ·
      refine ⟨10396246930417050544466137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13861662573889400725954849 10396246930417050544466137)
      ·
        refine ⟨7797185197812787908349603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10396246930417050544466137 7797185197812787908349603)
        ·
          refine ⟨11695777796719181862524405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797185197812787908349603 11695777796719181862524405)
          ·
            refine ⟨1096479168442423299611663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11695777796719181862524405 1096479168442423299611663)
            ·
              refine ⟨1644718752663634949417495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096479168442423299611663 1644718752663634949417495)
              ·
                refine ⟨2467078128995452424126243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644718752663634949417495 2467078128995452424126243)
                ·
                  refine ⟨3700617193493178636189365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467078128995452424126243 3700617193493178636189365)
                  ·
                    refine ⟨346932861889985497142753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3700617193493178636189365 346932861889985497142753)
                    ·
                      refine ⟨260199646417489122857065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346932861889985497142753 260199646417489122857065)
                      ·
                        rfl

theorem cell23_506737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_506737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506737 prefixEnd_506737 := by exact prefixLift 506737
  have htrace : WordTrace (prefixWord ++ tailWord_506737) baseStart_506737 baseEnd_506737 := by
    simpa [prefixWord, tailWord_506737, baseEnd_506737] using wordTrace_append hprefix tailTrace_506737
  have hstable : (prefixWord ++ tailWord_506737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506737).length < 2 ^ (prefixWord ++ tailWord_506737).sum := by decide
  have hdescent : baseEnd_506737 < baseStart_506737 := by decide
  rcases family_descends (prefixWord ++ tailWord_506737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506747 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 1, 5]
def baseStart_506747 : Nat := 118140960795 + 506747 * 2 ^ 59
def prefixEnd_506747 : Nat := 4983230072969 + 3 ^ 40 * 506747 * 2
def baseEnd_506747 : Nat := 86734927074678027910673

theorem tailTrace_506747 : CollatzResearch.WordTrace tailWord_506747 prefixEnd_506747 86734927074678027910673 := by
  unfold tailWord_506747
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482581495149639342470495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12321720996766426228313663 18482581495149639342470495)
  ·
    refine ⟨27723872242724459013705743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18482581495149639342470495 27723872242724459013705743)
    ·
      refine ⟨41585808364086688520558615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27723872242724459013705743 41585808364086688520558615)
      ·
        refine ⟨62378712546130032780837923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41585808364086688520558615 62378712546130032780837923)
        ·
          refine ⟨93568068819195049171256885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62378712546130032780837923 93568068819195049171256885)
          ·
            refine ⟨8772006451799535859805333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93568068819195049171256885 8772006451799535859805333)
            ·
              refine ⟨411187802428103243428375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8772006451799535859805333 411187802428103243428375)
              ·
                refine ⟨616781703642154865142563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411187802428103243428375 616781703642154865142563)
                ·
                  refine ⟨925172555463232297713845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616781703642154865142563 925172555463232297713845)
                  ·
                    refine ⟨86734927074678027910673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 925172555463232297713845 86734927074678027910673)
                    ·
                      rfl

theorem cell23_506747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 1, 5].length) (baseStart_506747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506747 prefixEnd_506747 := by exact prefixLift 506747
  have htrace : WordTrace (prefixWord ++ tailWord_506747) baseStart_506747 baseEnd_506747 := by
    simpa [prefixWord, tailWord_506747, baseEnd_506747] using wordTrace_append hprefix tailTrace_506747
  have hstable : (prefixWord ++ tailWord_506747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506747).length < 2 ^ (prefixWord ++ tailWord_506747).sum := by decide
  have hdescent : baseEnd_506747 < baseStart_506747 := by decide
  rcases family_descends (prefixWord ++ tailWord_506747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506784 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2]
def baseStart_506784 : Nat := 118140960795 + 506784 * 2 ^ 59
def prefixEnd_506784 : Nat := 4983230072969 + 3 ^ 40 * 506784 * 2
def baseEnd_506784 : Nat := 260223780008250438969349

theorem tailTrace_506784 : CollatzResearch.WordTrace tailWord_506784 prefixEnd_506784 260223780008250438969349 := by
  unfold tailWord_506784
  simp only [CollatzResearch.WordTrace]
  refine ⟨9241965498007797330783703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12322620664010396441044937 9241965498007797330783703)
  ·
    refine ⟨13862948247011695996175555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9241965498007797330783703 13862948247011695996175555)
    ·
      refine ⟨20794422370517543994263333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862948247011695996175555 20794422370517543994263333)
      ·
        refine ⟨3898954194472039498924375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20794422370517543994263333 3898954194472039498924375)
        ·
          refine ⟨5848431291708059248386563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898954194472039498924375 5848431291708059248386563)
          ·
            refine ⟨8772646937562088872579845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848431291708059248386563 8772646937562088872579845)
            ·
              refine ⟨1644871300792891663608721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8772646937562088872579845 1644871300792891663608721)
              ·
                refine ⟨1233653475594668747706541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644871300792891663608721 1233653475594668747706541)
                ·
                  refine ⟨462620053348000780389953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1233653475594668747706541 462620053348000780389953)
                  ·
                    refine ⟨346965040011000585292465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462620053348000780389953 346965040011000585292465)
                    ·
                      refine ⟨260223780008250438969349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346965040011000585292465 260223780008250438969349)
                      ·
                        rfl

theorem cell23_506784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_506784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506784 prefixEnd_506784 := by exact prefixLift 506784
  have htrace : WordTrace (prefixWord ++ tailWord_506784) baseStart_506784 baseEnd_506784 := by
    simpa [prefixWord, tailWord_506784, baseEnd_506784] using wordTrace_append hprefix tailTrace_506784
  have hstable : (prefixWord ++ tailWord_506784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506784).length < 2 ^ (prefixWord ++ tailWord_506784).sum := by decide
  have hdescent : baseEnd_506784 < baseStart_506784 := by decide
  rcases family_descends (prefixWord ++ tailWord_506784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506787 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 3]
def baseStart_506787 : Nat := 118140960795 + 506787 * 2 ^ 59
def prefixEnd_506787 : Nat := 4983230072969 + 3 ^ 40 * 506787 * 2
def baseEnd_506787 : Nat := 260225320450213927231835

theorem tailTrace_506787 : CollatzResearch.WordTrace tailWord_506787 prefixEnd_506787 260225320450213927231835 := by
  unfold tailWord_506787
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484040415004726173926615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12322693610003150782617743 18484040415004726173926615)
  ·
    refine ⟨27726060622507089260889923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18484040415004726173926615 27726060622507089260889923)
    ·
      refine ⟨41589090933760633891334885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27726060622507089260889923 41589090933760633891334885)
      ·
        refine ⟨7797954550080118854625291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41589090933760633891334885 7797954550080118854625291)
        ·
          refine ⟨11696931825120178281937937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797954550080118854625291 11696931825120178281937937)
          ·
            refine ⟨8772698868840133711453453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11696931825120178281937937 8772698868840133711453453)
            ·
              refine ⟨3289762075815050141795045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8772698868840133711453453 3289762075815050141795045)
              ·
                refine ⟨616830389215321901586571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3289762075815050141795045 616830389215321901586571)
                ·
                  refine ⟨925245583822982852379857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616830389215321901586571 925245583822982852379857)
                  ·
                    refine ⟨693934187867237139284893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 925245583822982852379857 693934187867237139284893)
                    ·
                      refine ⟨260225320450213927231835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 693934187867237139284893 260225320450213927231835)
                      ·
                        rfl

theorem cell23_506787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_506787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506787 prefixEnd_506787 := by exact prefixLift 506787
  have htrace : WordTrace (prefixWord ++ tailWord_506787) baseStart_506787 baseEnd_506787 := by
    simpa [prefixWord, tailWord_506787, baseEnd_506787] using wordTrace_append hprefix tailTrace_506787
  have hstable : (prefixWord ++ tailWord_506787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506787).length < 2 ^ (prefixWord ++ tailWord_506787).sum := by decide
  have hdescent : baseEnd_506787 < baseStart_506787 := by decide
  rcases family_descends (prefixWord ++ tailWord_506787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506804 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_506804 : Nat := 118140960795 + 506804 * 2 ^ 59
def prefixEnd_506804 : Nat := 4983230072969 + 3 ^ 40 * 506804 * 2
def baseEnd_506804 : Nat := 260234049621340360719257

theorem tailTrace_506804 : CollatzResearch.WordTrace tailWord_506804 prefixEnd_506804 260234049621340360719257 := by
  unfold tailWord_506804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242330227971569038647733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12323106970628758718196977 9242330227971569038647733)
  ·
    refine ⟨866468458872334597373225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9242330227971569038647733 866468458872334597373225)
    ·
      refine ⟨649851344154250948029919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 866468458872334597373225 649851344154250948029919)
      ·
        refine ⟨974777016231376422044879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649851344154250948029919 974777016231376422044879)
        ·
          refine ⟨1462165524347064633067319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974777016231376422044879 1462165524347064633067319)
          ·
            refine ⟨2193248286520596949600979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462165524347064633067319 2193248286520596949600979)
            ·
              refine ⟨3289872429780895424401469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193248286520596949600979 3289872429780895424401469)
              ·
                refine ⟨1233702161167835784150551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3289872429780895424401469 1233702161167835784150551)
                ·
                  refine ⟨1850553241751753676225827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233702161167835784150551 1850553241751753676225827)
                  ·
                    refine ⟨2775829862627630514338741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850553241751753676225827 2775829862627630514338741)
                    ·
                      refine ⟨260234049621340360719257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2775829862627630514338741 260234049621340360719257)
                      ·
                        rfl

theorem cell23_506804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_506804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506804 prefixEnd_506804 := by exact prefixLift 506804
  have htrace : WordTrace (prefixWord ++ tailWord_506804) baseStart_506804 baseEnd_506804 := by
    simpa [prefixWord, tailWord_506804, baseEnd_506804] using wordTrace_append hprefix tailTrace_506804
  have hstable : (prefixWord ++ tailWord_506804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506804).length < 2 ^ (prefixWord ++ tailWord_506804).sum := by decide
  have hdescent : baseEnd_506804 < baseStart_506804 := by decide
  rcases family_descends (prefixWord ++ tailWord_506804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506838 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_506838 : Nat := 118140960795 + 506838 * 2 ^ 59
def prefixEnd_506838 : Nat := 4983230072969 + 3 ^ 40 * 506838 * 2
def baseEnd_506838 : Nat := 260251507963593227694101

theorem tailTrace_506838 : CollatzResearch.WordTrace tailWord_506838 prefixEnd_506838 260251507963593227694101 := by
  unfold tailWord_506838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155368783613747617752073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12323933691879974589355445 1155368783613747617752073)
  ·
    refine ⟨866526587710310713314055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1155368783613747617752073 866526587710310713314055)
    ·
      refine ⟨1299789881565466069971083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866526587710310713314055 1299789881565466069971083)
      ·
        refine ⟨1949684822348199104956625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299789881565466069971083 1949684822348199104956625)
        ·
          refine ⟨1462263616761149328717469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949684822348199104956625 1462263616761149328717469)
          ·
            refine ⟨548348856285430998269051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1462263616761149328717469 548348856285430998269051)
            ·
              refine ⟨822523284428146497403577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548348856285430998269051 822523284428146497403577)
              ·
                refine ⟨616892463321109873052683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822523284428146497403577 616892463321109873052683)
                ·
                  refine ⟨925338694981664809579025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616892463321109873052683 925338694981664809579025)
                  ·
                    refine ⟨694004021236248607184269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 925338694981664809579025 694004021236248607184269)
                    ·
                      refine ⟨260251507963593227694101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 694004021236248607184269 260251507963593227694101)
                      ·
                        rfl

theorem cell23_506838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_506838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506838 prefixEnd_506838 := by exact prefixLift 506838
  have htrace : WordTrace (prefixWord ++ tailWord_506838) baseStart_506838 baseEnd_506838 := by
    simpa [prefixWord, tailWord_506838, baseEnd_506838] using wordTrace_append hprefix tailTrace_506838
  have hstable : (prefixWord ++ tailWord_506838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506838).length < 2 ^ (prefixWord ++ tailWord_506838).sum := by decide
  have hdescent : baseEnd_506838 < baseStart_506838 := by decide
  rcases family_descends (prefixWord ++ tailWord_506838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506869 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_506869 : Nat := 118140960795 + 506869 * 2 ^ 59
def prefixEnd_506869 : Nat := 4983230072969 + 3 ^ 40 * 506869 * 2
def baseEnd_506869 : Nat := 260267425863882606406459

theorem tailTrace_506869 : CollatzResearch.WordTrace tailWord_506869 prefixEnd_506869 260267425863882606406459 := by
  unfold tailWord_506869
  simp only [CollatzResearch.WordTrace]
  refine ⟨18487031200707654178411661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12324687467138436118941107 18487031200707654178411661)
  ·
    refine ⟨6932636700265370316904373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18487031200707654178411661 6932636700265370316904373)
    ·
      refine ⟨649934690649878467209785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6932636700265370316904373 649934690649878467209785)
      ·
        refine ⟨487451017987408850407339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649934690649878467209785 487451017987408850407339)
        ·
          refine ⟨731176526981113275611009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487451017987408850407339 731176526981113275611009)
          ·
            refine ⟨548382395235834956708257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731176526981113275611009 548382395235834956708257)
            ·
              refine ⟨411286796426876217531193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548382395235834956708257 411286796426876217531193)
              ·
                refine ⟨308465097320157163148395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411286796426876217531193 308465097320157163148395)
                ·
                  refine ⟨462697645980235744722593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308465097320157163148395 462697645980235744722593)
                  ·
                    refine ⟨347023234485176808541945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462697645980235744722593 347023234485176808541945)
                    ·
                      refine ⟨260267425863882606406459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347023234485176808541945 260267425863882606406459)
                      ·
                        rfl

theorem cell23_506869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_506869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506869 prefixEnd_506869 := by exact prefixLift 506869
  have htrace : WordTrace (prefixWord ++ tailWord_506869) baseStart_506869 baseEnd_506869 := by
    simpa [prefixWord, tailWord_506869, baseEnd_506869] using wordTrace_append hprefix tailTrace_506869
  have hstable : (prefixWord ++ tailWord_506869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506869).length < 2 ^ (prefixWord ++ tailWord_506869).sum := by decide
  have hdescent : baseEnd_506869 < baseStart_506869 := by decide
  rcases family_descends (prefixWord ++ tailWord_506869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506874 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_506874 : Nat := 118140960795 + 506874 * 2 ^ 59
def prefixEnd_506874 : Nat := 4983230072969 + 3 ^ 40 * 506874 * 2
def baseEnd_506874 : Nat := 260269993267155086843935

theorem tailTrace_506874 : CollatzResearch.WordTrace tailWord_506874 prefixEnd_506874 260269993267155086843935 := by
  unfold tailWord_506874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621803391422385008085919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12324809043793026688229117 4621803391422385008085919)
  ·
    refine ⟨6932705087133577512128879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621803391422385008085919 6932705087133577512128879)
    ·
      refine ⟨10399057630700366268193319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6932705087133577512128879 10399057630700366268193319)
      ·
        refine ⟨15598586446050549402289979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399057630700366268193319 15598586446050549402289979)
        ·
          refine ⟨23397879669075824103434969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15598586446050549402289979 23397879669075824103434969)
          ·
            refine ⟨17548409751806868077576227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23397879669075824103434969 17548409751806868077576227)
            ·
              refine ⟨26322614627710302116364341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17548409751806868077576227 26322614627710302116364341)
              ·
                refine ⟨2467745121347840823409157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26322614627710302116364341 2467745121347840823409157)
                ·
                  refine ⟨462702210252720154389217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467745121347840823409157 462702210252720154389217)
                  ·
                    refine ⟨347026657689540115791913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462702210252720154389217 347026657689540115791913)
                    ·
                      refine ⟨260269993267155086843935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347026657689540115791913 260269993267155086843935)
                      ·
                        rfl

theorem cell23_506874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_506874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506874 prefixEnd_506874 := by exact prefixLift 506874
  have htrace : WordTrace (prefixWord ++ tailWord_506874) baseStart_506874 baseEnd_506874 := by
    simpa [prefixWord, tailWord_506874, baseEnd_506874] using wordTrace_append hprefix tailTrace_506874
  have hstable : (prefixWord ++ tailWord_506874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506874).length < 2 ^ (prefixWord ++ tailWord_506874).sum := by decide
  have hdescent : baseEnd_506874 < baseStart_506874 := by decide
  rcases family_descends (prefixWord ++ tailWord_506874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506887 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_506887 : Nat := 118140960795 + 506887 * 2 ^ 59
def prefixEnd_506887 : Nat := 4983230072969 + 3 ^ 40 * 506887 * 2
def baseEnd_506887 : Nat := 260276668515663535981375

theorem tailTrace_506887 : CollatzResearch.WordTrace tailWord_506887 prefixEnd_506887 260276668515663535981375 := by
  unfold tailWord_506887
  simp only [CollatzResearch.WordTrace]
  refine ⟨18487687714642443252566915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12325125143094962168377943 18487687714642443252566915)
  ·
    refine ⟨27731531571963664878850373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18487687714642443252566915 27731531571963664878850373)
    ·
      refine ⟨5199662169743187164784445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27731531571963664878850373 5199662169743187164784445)
      ·
        refine ⟨1949873313653695186794167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5199662169743187164784445 1949873313653695186794167)
        ·
          refine ⟨2924809970480542780191251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949873313653695186794167 2924809970480542780191251)
          ·
            refine ⟨4387214955720814170286877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924809970480542780191251 4387214955720814170286877)
            ·
              refine ⟨1645205608395305313857579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4387214955720814170286877 1645205608395305313857579)
              ·
                refine ⟨2467808412592957970786369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645205608395305313857579 2467808412592957970786369)
                ·
                  refine ⟨1850856309444718478089777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2467808412592957970786369 1850856309444718478089777)
                  ·
                    refine ⟨1388142232083538858567333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1850856309444718478089777 1388142232083538858567333)
                    ·
                      refine ⟨260276668515663535981375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1388142232083538858567333 260276668515663535981375)
                      ·
                        rfl

theorem cell23_506887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_506887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506887 prefixEnd_506887 := by exact prefixLift 506887
  have htrace : WordTrace (prefixWord ++ tailWord_506887) baseStart_506887 baseEnd_506887 := by
    simpa [prefixWord, tailWord_506887, baseEnd_506887] using wordTrace_append hprefix tailTrace_506887
  have hstable : (prefixWord ++ tailWord_506887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506887).length < 2 ^ (prefixWord ++ tailWord_506887).sum := by decide
  have hdescent : baseEnd_506887 < baseStart_506887 := by decide
  rcases family_descends (prefixWord ++ tailWord_506887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506891 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 2, 2, 2]
def baseStart_506891 : Nat := 118140960795 + 506891 * 2 ^ 59
def prefixEnd_506891 : Nat := 4983230072969 + 3 ^ 40 * 506891 * 2
def baseEnd_506891 : Nat := 260278722438281520331357

theorem tailTrace_506891 : CollatzResearch.WordTrace tailWord_506891 prefixEnd_506891 260278722438281520331357 := by
  unfold tailWord_506891
  simp only [CollatzResearch.WordTrace]
  refine ⟨18487833606627951935712527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12325222404418634623808351 18487833606627951935712527)
  ·
    refine ⟨27731750409941927903568791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18487833606627951935712527 27731750409941927903568791)
    ·
      refine ⟨41597625614912891855353187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27731750409941927903568791 41597625614912891855353187)
      ·
        refine ⟨62396438422369337783029781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41597625614912891855353187 62396438422369337783029781)
        ·
          refine ⟨2924833051048562708579521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62396438422369337783029781 2924833051048562708579521)
          ·
            refine ⟨2193624788286422031434641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924833051048562708579521 2193624788286422031434641)
            ·
              refine ⟨1645218591214816523575981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193624788286422031434641 1645218591214816523575981)
              ·
                refine ⟨616956971705556196340993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645218591214816523575981 616956971705556196340993)
                ·
                  refine ⟨462717728779167147255745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616956971705556196340993 462717728779167147255745)
                  ·
                    refine ⟨347038296584375360441809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462717728779167147255745 347038296584375360441809)
                    ·
                      refine ⟨260278722438281520331357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347038296584375360441809 260278722438281520331357)
                      ·
                        rfl

theorem cell23_506891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2, 2].length) (baseStart_506891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506891 prefixEnd_506891 := by exact prefixLift 506891
  have htrace : WordTrace (prefixWord ++ tailWord_506891) baseStart_506891 baseEnd_506891 := by
    simpa [prefixWord, tailWord_506891, baseEnd_506891] using wordTrace_append hprefix tailTrace_506891
  have hstable : (prefixWord ++ tailWord_506891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506891).length < 2 ^ (prefixWord ++ tailWord_506891).sum := by decide
  have hdescent : baseEnd_506891 < baseStart_506891 := by decide
  rcases family_descends (prefixWord ++ tailWord_506891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506912 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2]
def baseStart_506912 : Nat := 118140960795 + 506912 * 2 ^ 59
def prefixEnd_506912 : Nat := 4983230072969 + 3 ^ 40 * 506912 * 2
def baseEnd_506912 : Nat := 260289505532025938168761

theorem tailTrace_506912 : CollatzResearch.WordTrace tailWord_506912 prefixEnd_506912 260289505532025938168761 := by
  unfold tailWord_506912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244299769775936261113495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12325733026367915014817993 9244299769775936261113495)
  ·
    refine ⟨13866449654663904391670243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9244299769775936261113495 13866449654663904391670243)
    ·
      refine ⟨20799674481995856587505365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13866449654663904391670243 20799674481995856587505365)
      ·
        refine ⟨487492370671777888769657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20799674481995856587505365 487492370671777888769657)
        ·
          refine ⟨365619278003833416577243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487492370671777888769657 365619278003833416577243)
          ·
            refine ⟨548428917005750124865865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365619278003833416577243 548428917005750124865865)
            ·
              refine ⟨411321687754312593649399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548428917005750124865865 411321687754312593649399)
              ·
                refine ⟨616982531631468890474099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411321687754312593649399 616982531631468890474099)
                ·
                  refine ⟨925473797447203335711149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616982531631468890474099 925473797447203335711149)
                  ·
                    refine ⟨347052674042701250891681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925473797447203335711149 347052674042701250891681)
                    ·
                      refine ⟨260289505532025938168761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347052674042701250891681 260289505532025938168761)
                      ·
                        rfl

theorem cell23_506912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_506912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506912 prefixEnd_506912 := by exact prefixLift 506912
  have htrace : WordTrace (prefixWord ++ tailWord_506912) baseStart_506912 baseEnd_506912 := by
    simpa [prefixWord, tailWord_506912, baseEnd_506912] using wordTrace_append hprefix tailTrace_506912
  have hstable : (prefixWord ++ tailWord_506912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506912).length < 2 ^ (prefixWord ++ tailWord_506912).sum := by decide
  have hdescent : baseEnd_506912 < baseStart_506912 := by decide
  rcases family_descends (prefixWord ++ tailWord_506912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506914 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_506914 : Nat := 118140960795 + 506914 * 2 ^ 59
def prefixEnd_506914 : Nat := 4983230072969 + 3 ^ 40 * 506914 * 2
def baseEnd_506914 : Nat := 28921170277037214482639

theorem tailTrace_506914 : CollatzResearch.WordTrace tailWord_506914 prefixEnd_506914 28921170277037214482639 := by
  unfold tailWord_506914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622168121386156715949949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12325781657029751242533197 4622168121386156715949949)
  ·
    refine ⟨1733313045519808768481231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4622168121386156715949949 1733313045519808768481231)
    ·
      refine ⟨2599969568279713152721847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733313045519808768481231 2599969568279713152721847)
      ·
        refine ⟨3899954352419569729082771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599969568279713152721847 3899954352419569729082771)
        ·
          refine ⟨5849931528629354593624157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899954352419569729082771 5849931528629354593624157)
          ·
            refine ⟨2193724323236007972609059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5849931528629354593624157 2193724323236007972609059)
            ·
              refine ⟨3290586484854011958913589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193724323236007972609059 3290586484854011958913589)
              ·
                refine ⟨308492482955063621148149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3290586484854011958913589 308492482955063621148149)
                ·
                  refine ⟨28921170277037214482639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308492482955063621148149 28921170277037214482639)
                  ·
                    rfl

theorem cell23_506914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_506914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506914 prefixEnd_506914 := by exact prefixLift 506914
  have htrace : WordTrace (prefixWord ++ tailWord_506914) baseStart_506914 baseEnd_506914 := by
    simpa [prefixWord, tailWord_506914, baseEnd_506914] using wordTrace_append hprefix tailTrace_506914
  have hstable : (prefixWord ++ tailWord_506914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506914).length < 2 ^ (prefixWord ++ tailWord_506914).sum := by decide
  have hdescent : baseEnd_506914 < baseStart_506914 := by decide
  rcases family_descends (prefixWord ++ tailWord_506914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506964 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_506964 : Nat := 118140960795 + 506964 * 2 ^ 59
def prefixEnd_506964 : Nat := 4983230072969 + 3 ^ 40 * 506964 * 2
def baseEnd_506964 : Nat := 260316206526059734718521

theorem tailTrace_506964 : CollatzResearch.WordTrace tailWord_506964 prefixEnd_506964 260316206526059734718521 := by
  unfold tailWord_506964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245248067681742701559973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12326997423575656935413297 9245248067681742701559973)
  ·
    refine ⟨1733484012690326756542495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9245248067681742701559973 1733484012690326756542495)
    ·
      refine ⟨2600226019035490134813743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733484012690326756542495 2600226019035490134813743)
      ·
        refine ⟨3900339028553235202220615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600226019035490134813743 3900339028553235202220615)
        ·
          refine ⟨5850508542829852803330923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900339028553235202220615 5850508542829852803330923)
          ·
            refine ⟨8775762814244779204996385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850508542829852803330923 8775762814244779204996385)
            ·
              refine ⟨6581822110683584403747289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775762814244779204996385 6581822110683584403747289)
              ·
                refine ⟨4936366583012688302810467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581822110683584403747289 4936366583012688302810467)
                ·
                  refine ⟨7404549874519032454215701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936366583012688302810467 7404549874519032454215701)
                  ·
                    refine ⟨347088275368079646291361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7404549874519032454215701 347088275368079646291361)
                    ·
                      refine ⟨260316206526059734718521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347088275368079646291361 260316206526059734718521)
                      ·
                        rfl

theorem cell23_506964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_506964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_506964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_506964 prefixEnd_506964 := by exact prefixLift 506964
  have htrace : WordTrace (prefixWord ++ tailWord_506964) baseStart_506964 baseEnd_506964 := by
    simpa [prefixWord, tailWord_506964, baseEnd_506964] using wordTrace_append hprefix tailTrace_506964
  have hstable : (prefixWord ++ tailWord_506964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506964).length < 2 ^ (prefixWord ++ tailWord_506964).sum := by decide
  have hdescent : baseEnd_506964 < baseStart_506964 := by decide
  rcases family_descends (prefixWord ++ tailWord_506964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507041 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_507041 : Nat := 118140960795 + 507041 * 2 ^ 59
def prefixEnd_507041 : Nat := 4983230072969 + 3 ^ 40 * 507041 * 2
def baseEnd_507041 : Nat := 260355744536455933455667

theorem tailTrace_507041 : CollatzResearch.WordTrace tailWord_507041 prefixEnd_507041 260355744536455933455667 := by
  unfold tailWord_507041
  simp only [CollatzResearch.WordTrace]
  refine ⟨18493304556084527553672977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12328869704056351702448651 18493304556084527553672977)
  ·
    refine ⟨13869978417063395665254733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18493304556084527553672977 13869978417063395665254733)
    ·
      refine ⟨5201241906398773374470525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13869978417063395665254733 5201241906398773374470525)
      ·
        refine ⟨1950465714899540015426447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5201241906398773374470525 1950465714899540015426447)
        ·
          refine ⟨2925698572349310023139671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950465714899540015426447 2925698572349310023139671)
          ·
            refine ⟨4388547858523965034709507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925698572349310023139671 4388547858523965034709507)
            ·
              refine ⟨6582821787785947552064261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388547858523965034709507 6582821787785947552064261)
              ·
                refine ⟨1234279085209865166012049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6582821787785947552064261 1234279085209865166012049)
                ·
                  refine ⟨925709313907398874509037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234279085209865166012049 925709313907398874509037)
                  ·
                    refine ⟨347140992715274577940889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925709313907398874509037 347140992715274577940889)
                    ·
                      refine ⟨260355744536455933455667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347140992715274577940889 260355744536455933455667)
                      ·
                        rfl

theorem cell23_507041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_507041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507041 prefixEnd_507041 := by exact prefixLift 507041
  have htrace : WordTrace (prefixWord ++ tailWord_507041) baseStart_507041 baseEnd_507041 := by
    simpa [prefixWord, tailWord_507041, baseEnd_507041] using wordTrace_append hprefix tailTrace_507041
  have hstable : (prefixWord ++ tailWord_507041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507041).length < 2 ^ (prefixWord ++ tailWord_507041).sum := by decide
  have hdescent : baseEnd_507041 < baseStart_507041 := by decide
  rcases family_descends (prefixWord ++ tailWord_507041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507042 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_507042 : Nat := 118140960795 + 507042 * 2 ^ 59
def prefixEnd_507042 : Nat := 4983230072969 + 3 ^ 40 * 507042 * 2
def baseEnd_507042 : Nat := 86785419339036809847721

theorem tailTrace_507042 : CollatzResearch.WordTrace tailWord_507042 prefixEnd_507042 86785419339036809847721 := by
  unfold tailWord_507042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623335257270226181114845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12328894019387269816306253 4623335257270226181114845)
  ·
    refine ⟨1733750721476334817918067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4623335257270226181114845 1733750721476334817918067)
    ·
      refine ⟨2600626082214502226877101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733750721476334817918067 2600626082214502226877101)
      ·
        refine ⟨975234780830438335078913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2600626082214502226877101 975234780830438335078913)
        ·
          refine ⟨731426085622828751309185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975234780830438335078913 731426085622828751309185)
          ·
            refine ⟨548569564217121563481889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731426085622828751309185 548569564217121563481889)
            ·
              refine ⟨411427173162841172611417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548569564217121563481889 411427173162841172611417)
              ·
                refine ⟨308570379872130879458563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411427173162841172611417 308570379872130879458563)
                ·
                  refine ⟨462855569808196319187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308570379872130879458563 462855569808196319187845)
                  ·
                    refine ⟨86785419339036809847721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462855569808196319187845 86785419339036809847721)
                    ·
                      rfl

theorem cell23_507042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_507042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507042 prefixEnd_507042 := by exact prefixLift 507042
  have htrace : WordTrace (prefixWord ++ tailWord_507042) baseStart_507042 baseEnd_507042 := by
    simpa [prefixWord, tailWord_507042, baseEnd_507042] using wordTrace_append hprefix tailTrace_507042
  have hstable : (prefixWord ++ tailWord_507042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507042).length < 2 ^ (prefixWord ++ tailWord_507042).sum := by decide
  have hdescent : baseEnd_507042 < baseStart_507042 := by decide
  rcases family_descends (prefixWord ++ tailWord_507042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507071 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 5, 2, 2]
def baseStart_507071 : Nat := 118140960795 + 507071 * 2 ^ 59
def prefixEnd_507071 : Nat := 4983230072969 + 3 ^ 40 * 507071 * 2
def baseEnd_507071 : Nat := 260371148956090816080529

theorem tailTrace_507071 : CollatzResearch.WordTrace tailWord_507071 prefixEnd_507071 260371148956090816080529 := by
  unfold tailWord_507071
  simp only [CollatzResearch.WordTrace]
  refine ⟨18494398745975842677265067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12329599163983895118176711 18494398745975842677265067)
  ·
    refine ⟨27741598118963764015897601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18494398745975842677265067 27741598118963764015897601)
    ·
      refine ⟨20806198589222823011923201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27741598118963764015897601 20806198589222823011923201)
      ·
        refine ⟨15604648941917117258942401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20806198589222823011923201 15604648941917117258942401)
        ·
          refine ⟨11703486706437837944206801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15604648941917117258942401 11703486706437837944206801)
          ·
            refine ⟨8777615029828378458155101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11703486706437837944206801 8777615029828378458155101)
            ·
              refine ⟨3291605636185641921808163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8777615029828378458155101 3291605636185641921808163)
              ·
                refine ⟨4937408454278462882712245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291605636185641921808163 4937408454278462882712245)
                ·
                  refine ⟨462882042588605895254273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4937408454278462882712245 462882042588605895254273)
                  ·
                    refine ⟨347161531941454421440705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462882042588605895254273 347161531941454421440705)
                    ·
                      refine ⟨260371148956090816080529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347161531941454421440705 260371148956090816080529)
                      ·
                        rfl

theorem cell23_507071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_507071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507071 prefixEnd_507071 := by exact prefixLift 507071
  have htrace : WordTrace (prefixWord ++ tailWord_507071) baseStart_507071 baseEnd_507071 := by
    simpa [prefixWord, tailWord_507071, baseEnd_507071] using wordTrace_append hprefix tailTrace_507071
  have hstable : (prefixWord ++ tailWord_507071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507071).length < 2 ^ (prefixWord ++ tailWord_507071).sum := by decide
  have hdescent : baseEnd_507071 < baseStart_507071 := by decide
  rcases family_descends (prefixWord ++ tailWord_507071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507085 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_507085 : Nat := 118140960795 + 507085 * 2 ^ 59
def prefixEnd_507085 : Nat := 4983230072969 + 3 ^ 40 * 507085 * 2
def baseEnd_507085 : Nat := 86792779228417920435155

theorem tailTrace_507085 : CollatzResearch.WordTrace tailWord_507085 prefixEnd_507085 86792779228417920435155 := by
  unfold tailWord_507085
  simp only [CollatzResearch.WordTrace]
  refine ⟨18494909367925123068274709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12329939578616748712183139 18494909367925123068274709)
  ·
    refine ⟨866948876621490143825377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18494909367925123068274709 866948876621490143825377)
    ·
      refine ⟨650211657466117607869033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 866948876621490143825377 650211657466117607869033)
      ·
        refine ⟨487658743099588205901775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650211657466117607869033 487658743099588205901775)
        ·
          refine ⟨731488114649382308852663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487658743099588205901775 731488114649382308852663)
          ·
            refine ⟨1097232171974073463278995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731488114649382308852663 1097232171974073463278995)
            ·
              refine ⟨1645848257961110194918493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097232171974073463278995 1645848257961110194918493)
              ·
                refine ⟨617193096735416323094435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1645848257961110194918493 617193096735416323094435)
                ·
                  refine ⟨925789645103124484641653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617193096735416323094435 925789645103124484641653)
                  ·
                    refine ⟨86792779228417920435155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 925789645103124484641653 86792779228417920435155)
                    ·
                      rfl

theorem cell23_507085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_507085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507085 prefixEnd_507085 := by exact prefixLift 507085
  have htrace : WordTrace (prefixWord ++ tailWord_507085) baseStart_507085 baseEnd_507085 := by
    simpa [prefixWord, tailWord_507085, baseEnd_507085] using wordTrace_append hprefix tailTrace_507085
  have hstable : (prefixWord ++ tailWord_507085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507085).length < 2 ^ (prefixWord ++ tailWord_507085).sum := by decide
  have hdescent : baseEnd_507085 < baseStart_507085 := by decide
  rcases family_descends (prefixWord ++ tailWord_507085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507097 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_507097 : Nat := 118140960795 + 507097 * 2 ^ 59
def prefixEnd_507097 : Nat := 4983230072969 + 3 ^ 40 * 507097 * 2
def baseEnd_507097 : Nat := 260384499453107714355409

theorem tailTrace_507097 : CollatzResearch.WordTrace tailWord_507097 prefixEnd_507097 260384499453107714355409 := by
  unfold tailWord_507097
  simp only [CollatzResearch.WordTrace]
  refine ⟨18495347043881649117711545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12330231362587766078474363 18495347043881649117711545)
  ·
    refine ⟨13871510282911236838283659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18495347043881649117711545 13871510282911236838283659)
    ·
      refine ⟨20807265424366855257425489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13871510282911236838283659 20807265424366855257425489)
      ·
        refine ⟨15605449068275141443069117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20807265424366855257425489 15605449068275141443069117)
        ·
          refine ⟨5852043400603178041150919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15605449068275141443069117 5852043400603178041150919)
          ·
            refine ⟨8778065100904767061726379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852043400603178041150919 8778065100904767061726379)
            ·
              refine ⟨13167097651357150592589569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778065100904767061726379 13167097651357150592589569)
              ·
                refine ⟨9875323238517862944442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13167097651357150592589569 9875323238517862944442177)
                ·
                  refine ⟨7406492428888397208331633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875323238517862944442177 7406492428888397208331633)
                  ·
                    refine ⟨5554869321666297906248725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7406492428888397208331633 5554869321666297906248725)
                    ·
                      refine ⟨260384499453107714355409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5554869321666297906248725 260384499453107714355409)
                      ·
                        rfl

theorem cell23_507097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_507097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507097 prefixEnd_507097 := by exact prefixLift 507097
  have htrace : WordTrace (prefixWord ++ tailWord_507097) baseStart_507097 baseEnd_507097 := by
    simpa [prefixWord, tailWord_507097, baseEnd_507097] using wordTrace_append hprefix tailTrace_507097
  have hstable : (prefixWord ++ tailWord_507097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507097).length < 2 ^ (prefixWord ++ tailWord_507097).sum := by decide
  have hdescent : baseEnd_507097 < baseStart_507097 := by decide
  rcases family_descends (prefixWord ++ tailWord_507097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507105 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 1, 2, 2]
def baseStart_507105 : Nat := 118140960795 + 507105 * 2 ^ 59
def prefixEnd_507105 : Nat := 4983230072969 + 3 ^ 40 * 507105 * 2
def baseEnd_507105 : Nat := 260388607298343683055373

theorem tailTrace_507105 : CollatzResearch.WordTrace tailWord_507105 prefixEnd_507105 260388607298343683055373 := by
  unfold tailWord_507105
  simp only [CollatzResearch.WordTrace]
  refine ⟨18495638827852666484002769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12330425885235110989335179 18495638827852666484002769)
  ·
    refine ⟨13871729120889499863002077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18495638827852666484002769 13871729120889499863002077)
    ·
      refine ⟨5201898420333562448625779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13871729120889499863002077 5201898420333562448625779)
      ·
        refine ⟨7802847630500343672938669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5201898420333562448625779 7802847630500343672938669)
        ·
          refine ⟨2926067861437628877352001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7802847630500343672938669 2926067861437628877352001)
          ·
            refine ⟨2194550896078221658014001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2926067861437628877352001 2194550896078221658014001)
            ·
              refine ⟨1645913172058666243510501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2194550896078221658014001 1645913172058666243510501)
              ·
                refine ⟨308608719760999920658219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1645913172058666243510501 308608719760999920658219)
                ·
                  refine ⟨462913079641499880987329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308608719760999920658219 462913079641499880987329)
                  ·
                    refine ⟨347184809731124910740497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 462913079641499880987329 347184809731124910740497)
                    ·
                      refine ⟨260388607298343683055373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347184809731124910740497 260388607298343683055373)
                      ·
                        rfl

theorem cell23_507105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_507105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507105 prefixEnd_507105 := by exact prefixLift 507105
  have htrace : WordTrace (prefixWord ++ tailWord_507105) baseStart_507105 baseEnd_507105 := by
    simpa [prefixWord, tailWord_507105, baseEnd_507105] using wordTrace_append hprefix tailTrace_507105
  have hstable : (prefixWord ++ tailWord_507105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507105).length < 2 ^ (prefixWord ++ tailWord_507105).sum := by decide
  have hdescent : baseEnd_507105 < baseStart_507105 := by decide
  rcases family_descends (prefixWord ++ tailWord_507105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507148 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_507148 : Nat := 118140960795 + 507148 * 2 ^ 59
def prefixEnd_507148 : Nat := 4983230072969 + 3 ^ 40 * 507148 * 2
def baseEnd_507148 : Nat := 260410686966487014817675

theorem tailTrace_507148 : CollatzResearch.WordTrace tailWord_507148 prefixEnd_507148 260410686966487014817675 := by
  unfold tailWord_507148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248603583348442413909049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12331471444464589885212065 9248603583348442413909049)
  ·
    refine ⟨6936452687511331810431787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9248603583348442413909049 6936452687511331810431787)
    ·
      refine ⟨10404679031266997715647681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936452687511331810431787 10404679031266997715647681)
      ·
        refine ⟨7803509273450248286735761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10404679031266997715647681 7803509273450248286735761)
        ·
          refine ⟨5852631955087686215051821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7803509273450248286735761 5852631955087686215051821)
          ·
            refine ⟨2194736983157882330644433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5852631955087686215051821 2194736983157882330644433)
            ·
              refine ⟨1646052737368411747983325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2194736983157882330644433 1646052737368411747983325)
              ·
                refine ⟨617269776513154405493747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646052737368411747983325 617269776513154405493747)
                ·
                  refine ⟨925904664769731608240621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617269776513154405493747 925904664769731608240621)
                  ·
                    refine ⟨347214249288649353090233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925904664769731608240621 347214249288649353090233)
                    ·
                      refine ⟨260410686966487014817675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347214249288649353090233 260410686966487014817675)
                      ·
                        rfl

theorem cell23_507148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_507148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507148 prefixEnd_507148 := by exact prefixLift 507148
  have htrace : WordTrace (prefixWord ++ tailWord_507148) baseStart_507148 baseEnd_507148 := by
    simpa [prefixWord, tailWord_507148, baseEnd_507148] using wordTrace_append hprefix tailTrace_507148
  have hstable : (prefixWord ++ tailWord_507148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507148).length < 2 ^ (prefixWord ++ tailWord_507148).sum := by decide
  have hdescent : baseEnd_507148 < baseStart_507148 := by decide
  rcases family_descends (prefixWord ++ tailWord_507148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507222 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_507222 : Nat := 118140960795 + 507222 * 2 ^ 59
def prefixEnd_507222 : Nat := 4983230072969 + 3 ^ 40 * 507222 * 2
def baseEnd_507222 : Nat := 86816228178306575097445

theorem tailTrace_507222 : CollatzResearch.WordTrace tailWord_507222 prefixEnd_507222 86816228178306575097445 := by
  unfold tailWord_507222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156244135526799716625745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12333270778952530310674613 1156244135526799716625745)
  ·
    refine ⟨867183101645099787469309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156244135526799716625745 867183101645099787469309)
    ·
      refine ⟨325193663116912420300991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 867183101645099787469309 325193663116912420300991)
      ·
        refine ⟨487790494675368630451487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325193663116912420300991 487790494675368630451487)
        ·
          refine ⟨731685742013052945677231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487790494675368630451487 731685742013052945677231)
          ·
            refine ⟨1097528613019579418515847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731685742013052945677231 1097528613019579418515847)
            ·
              refine ⟨1646292919529369127773771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097528613019579418515847 1646292919529369127773771)
              ·
                refine ⟨2469439379294053691660657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646292919529369127773771 2469439379294053691660657)
                ·
                  refine ⟨1852079534470540268745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469439379294053691660657 1852079534470540268745493)
                  ·
                    refine ⟨86816228178306575097445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1852079534470540268745493 86816228178306575097445)
                    ·
                      rfl

theorem cell23_507222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_507222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507222 prefixEnd_507222 := by exact prefixLift 507222
  have htrace : WordTrace (prefixWord ++ tailWord_507222) baseStart_507222 baseEnd_507222 := by
    simpa [prefixWord, tailWord_507222, baseEnd_507222] using wordTrace_append hprefix tailTrace_507222
  have hstable : (prefixWord ++ tailWord_507222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507222).length < 2 ^ (prefixWord ++ tailWord_507222).sum := by decide
  have hdescent : baseEnd_507222 < baseStart_507222 := by decide
  rcases family_descends (prefixWord ++ tailWord_507222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507224 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_507224 : Nat := 118140960795 + 507224 * 2 ^ 59
def prefixEnd_507224 : Nat := 4983230072969 + 3 ^ 40 * 507224 * 2
def baseEnd_507224 : Nat := 260449711496228717467325

theorem tailTrace_507224 : CollatzResearch.WordTrace tailWord_507224 prefixEnd_507224 260449711496228717467325 := by
  unfold tailWord_507224
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249989557210774903792363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12333319409614366538389817 9249989557210774903792363)
  ·
    refine ⟨13874984335816162355688545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249989557210774903792363 13874984335816162355688545)
    ·
      refine ⟨10406238251862121766766409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13874984335816162355688545 10406238251862121766766409)
      ·
        refine ⟨7804678688896591325074807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10406238251862121766766409 7804678688896591325074807)
        ·
          refine ⟨11707018033344886987612211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7804678688896591325074807 11707018033344886987612211)
          ·
            refine ⟨17560527050017330481418317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707018033344886987612211 17560527050017330481418317)
            ·
              refine ⟨6585197643756498930531869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17560527050017330481418317 6585197643756498930531869)
              ·
                refine ⟨2469449116408687098949451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6585197643756498930531869 2469449116408687098949451)
                ·
                  refine ⟨3704173674613030648424177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469449116408687098949451 3704173674613030648424177)
                  ·
                    refine ⟨2778130255959772986318133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704173674613030648424177 2778130255959772986318133)
                    ·
                      refine ⟨260449711496228717467325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2778130255959772986318133 260449711496228717467325)
                      ·
                        rfl

theorem cell23_507224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_507224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507224 prefixEnd_507224 := by exact prefixLift 507224
  have htrace : WordTrace (prefixWord ++ tailWord_507224) baseStart_507224 baseEnd_507224 := by
    simpa [prefixWord, tailWord_507224, baseEnd_507224] using wordTrace_append hprefix tailTrace_507224
  have hstable : (prefixWord ++ tailWord_507224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507224).length < 2 ^ (prefixWord ++ tailWord_507224).sum := by decide
  have hdescent : baseEnd_507224 < baseStart_507224 := by decide
  rcases family_descends (prefixWord ++ tailWord_507224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507229 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_507229 : Nat := 118140960795 + 507229 * 2 ^ 59
def prefixEnd_507229 : Nat := 4983230072969 + 3 ^ 40 * 507229 * 2
def baseEnd_507229 : Nat := 260452278899501197904803

theorem tailTrace_507229 : CollatzResearch.WordTrace tailWord_507229 prefixEnd_507229 260452278899501197904803 := by
  unfold tailWord_507229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500161479403435661516741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12333440986268957107677827 18500161479403435661516741)
  ·
    refine ⟨3468780277388144186534389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18500161479403435661516741 3468780277388144186534389)
    ·
      refine ⟨325198151005138517487599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3468780277388144186534389 325198151005138517487599)
      ·
        refine ⟨487797226507707776231399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325198151005138517487599 487797226507707776231399)
        ·
          refine ⟨731695839761561664347099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487797226507707776231399 731695839761561664347099)
          ·
            refine ⟨1097543759642342496520649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731695839761561664347099 1097543759642342496520649)
            ·
              refine ⟨823157819731756872390487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097543759642342496520649 823157819731756872390487)
              ·
                refine ⟨1234736729597635308585731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823157819731756872390487 1234736729597635308585731)
                ·
                  refine ⟨1852105094396452962878597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234736729597635308585731 1852105094396452962878597)
                  ·
                    refine ⟨347269705199334930539737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852105094396452962878597 347269705199334930539737)
                    ·
                      refine ⟨260452278899501197904803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347269705199334930539737 260452278899501197904803)
                      ·
                        rfl

theorem cell23_507229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_507229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507229 prefixEnd_507229 := by exact prefixLift 507229
  have htrace : WordTrace (prefixWord ++ tailWord_507229) baseStart_507229 baseEnd_507229 := by
    simpa [prefixWord, tailWord_507229, baseEnd_507229] using wordTrace_append hprefix tailTrace_507229
  have hstable : (prefixWord ++ tailWord_507229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507229).length < 2 ^ (prefixWord ++ tailWord_507229).sum := by decide
  have hdescent : baseEnd_507229 < baseStart_507229 := by decide
  rcases family_descends (prefixWord ++ tailWord_507229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507251 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 6, 4, 2]
def baseStart_507251 : Nat := 118140960795 + 507251 * 2 ^ 59
def prefixEnd_507251 : Nat := 4983230072969 + 3 ^ 40 * 507251 * 2
def baseEnd_507251 : Nat := 260463575473900111829701

theorem tailTrace_507251 : CollatzResearch.WordTrace tailWord_507251 prefixEnd_507251 260463575473900111829701 := by
  unfold tailWord_507251
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500963885323733418817607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12333975923549155612545071 18500963885323733418817607)
  ·
    refine ⟨27751445827985600128226411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18500963885323733418817607 27751445827985600128226411)
    ·
      refine ⟨41627168741978400192339617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27751445827985600128226411 41627168741978400192339617)
      ·
        refine ⟨31220376556483800144254713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41627168741978400192339617 31220376556483800144254713)
        ·
          refine ⟨23415282417362850108191035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31220376556483800144254713 23415282417362850108191035)
          ·
            refine ⟨35122923626044275162286553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23415282417362850108191035 35122923626044275162286553)
            ·
              refine ⟨26342192719533206371714915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35122923626044275162286553 26342192719533206371714915)
              ·
                refine ⟨39513289079299809557572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26342192719533206371714915 39513289079299809557572373)
                ·
                  refine ⟨1852185425592178573011205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39513289079299809557572373 1852185425592178573011205)
                  ·
                    refine ⟨347284767298533482439601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852185425592178573011205 347284767298533482439601)
                    ·
                      refine ⟨260463575473900111829701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347284767298533482439601 260463575473900111829701)
                      ·
                        rfl

theorem cell23_507251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4, 2].length) (baseStart_507251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507251 prefixEnd_507251 := by exact prefixLift 507251
  have htrace : WordTrace (prefixWord ++ tailWord_507251) baseStart_507251 baseEnd_507251 := by
    simpa [prefixWord, tailWord_507251, baseEnd_507251] using wordTrace_append hprefix tailTrace_507251
  have hstable : (prefixWord ++ tailWord_507251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507251).length < 2 ^ (prefixWord ++ tailWord_507251).sum := by decide
  have hdescent : baseEnd_507251 < baseStart_507251 := by decide
  rcases family_descends (prefixWord ++ tailWord_507251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507261 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_507261 : Nat := 118140960795 + 507261 * 2 ^ 59
def prefixEnd_507261 : Nat := 4983230072969 + 3 ^ 40 * 507261 * 2
def baseEnd_507261 : Nat := 86822903426815024234885

theorem tailTrace_507261 : CollatzResearch.WordTrace tailWord_507261 prefixEnd_507261 86822903426815024234885 := by
  unfold tailWord_507261
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501328615287505126681637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334219076858336751121091 18501328615287505126681637)
  ·
    refine ⟨3468999115366407211252807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18501328615287505126681637 3468999115366407211252807)
    ·
      refine ⟨5203498673049610816879211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3468999115366407211252807 5203498673049610816879211)
      ·
        refine ⟨7805248009574416225318817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5203498673049610816879211 7805248009574416225318817)
        ·
          refine ⟨5853936007180812168989113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7805248009574416225318817 5853936007180812168989113)
          ·
            refine ⟨4390452005385609126741835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853936007180812168989113 4390452005385609126741835)
            ·
              refine ⟨6585678008078413690112753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390452005385609126741835 6585678008078413690112753)
              ·
                refine ⟨4939258506058810267584565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6585678008078413690112753 4939258506058810267584565)
                ·
                  refine ⟨463055484943013462586053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939258506058810267584565 463055484943013462586053)
                  ·
                    refine ⟨86822903426815024234885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 463055484943013462586053 86822903426815024234885)
                    ·
                      rfl

theorem cell23_507261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_507261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507261 prefixEnd_507261 := by exact prefixLift 507261
  have htrace : WordTrace (prefixWord ++ tailWord_507261) baseStart_507261 baseEnd_507261 := by
    simpa [prefixWord, tailWord_507261, baseEnd_507261] using wordTrace_append hprefix tailTrace_507261
  have hstable : (prefixWord ++ tailWord_507261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507261).length < 2 ^ (prefixWord ++ tailWord_507261).sum := by decide
  have hdescent : baseEnd_507261 < baseStart_507261 := by decide
  rcases family_descends (prefixWord ++ tailWord_507261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507264 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_507264 : Nat := 118140960795 + 507264 * 2 ^ 59
def prefixEnd_507264 : Nat := 4983230072969 + 3 ^ 40 * 507264 * 2
def baseEnd_507264 : Nat := 260470250722408560967141

theorem tailTrace_507264 : CollatzResearch.WordTrace tailWord_507264 prefixEnd_507264 260470250722408560967141 := by
  unfold tailWord_507264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9250719017138318319520423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12334292022851091092693897 9250719017138318319520423)
  ·
    refine ⟨13876078525707477479280635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9250719017138318319520423 13876078525707477479280635)
    ·
      refine ⟨20814117788561216218920953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876078525707477479280635 20814117788561216218920953)
      ·
        refine ⟨15610588341420912164190715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20814117788561216218920953 15610588341420912164190715)
        ·
          refine ⟨23415882512131368246286073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610588341420912164190715 23415882512131368246286073)
          ·
            refine ⟨17561911884098526184714555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23415882512131368246286073 17561911884098526184714555)
            ·
              refine ⟨26342867826147789277071833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561911884098526184714555 26342867826147789277071833)
              ·
                refine ⟨19757150869610841957803875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26342867826147789277071833 19757150869610841957803875)
                ·
                  refine ⟨29635726304416262936705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19757150869610841957803875 29635726304416262936705813)
                  ·
                    refine ⟨1389174670519512325158085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29635726304416262936705813 1389174670519512325158085)
                    ·
                      refine ⟨260470250722408560967141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1389174670519512325158085 260470250722408560967141)
                      ·
                        rfl

theorem cell23_507264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_507264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507264 prefixEnd_507264 := by exact prefixLift 507264
  have htrace : WordTrace (prefixWord ++ tailWord_507264) baseStart_507264 baseEnd_507264 := by
    simpa [prefixWord, tailWord_507264, baseEnd_507264] using wordTrace_append hprefix tailTrace_507264
  have hstable : (prefixWord ++ tailWord_507264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507264).length < 2 ^ (prefixWord ++ tailWord_507264).sum := by decide
  have hdescent : baseEnd_507264 < baseStart_507264 := by decide
  rcases family_descends (prefixWord ++ tailWord_507264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507268 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_507268 : Nat := 118140960795 + 507268 * 2 ^ 59
def prefixEnd_507268 : Nat := 4983230072969 + 3 ^ 40 * 507268 * 2
def baseEnd_507268 : Nat := 260472304645026545317123

theorem tailTrace_507268 : CollatzResearch.WordTrace tailWord_507268 prefixEnd_507268 260472304645026545317123 := by
  unfold tailWord_507268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9250791963131072661093229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12334389284174763548124305 9250791963131072661093229)
  ·
    refine ⟨3469046986174152247909961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9250791963131072661093229 3469046986174152247909961)
    ·
      refine ⟨2601785239630614185932471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3469046986174152247909961 2601785239630614185932471)
      ·
        refine ⟨3902677859445921278898707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601785239630614185932471 3902677859445921278898707)
        ·
          refine ⟨5854016789168881918348061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902677859445921278898707 5854016789168881918348061)
          ·
            refine ⟨2195256295938330719380523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5854016789168881918348061 2195256295938330719380523)
            ·
              refine ⟨3292884443907496079070785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2195256295938330719380523 3292884443907496079070785)
              ·
                refine ⟨2469663332930622059303089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292884443907496079070785 2469663332930622059303089)
                ·
                  refine ⟨1852247499697966544477317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2469663332930622059303089 1852247499697966544477317)
                  ·
                    refine ⟨347296406193368727089497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852247499697966544477317 347296406193368727089497)
                    ·
                      refine ⟨260472304645026545317123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347296406193368727089497 260472304645026545317123)
                      ·
                        rfl

theorem cell23_507268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_507268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507268 prefixEnd_507268 := by exact prefixLift 507268
  have htrace : WordTrace (prefixWord ++ tailWord_507268) baseStart_507268 baseEnd_507268 := by
    simpa [prefixWord, tailWord_507268, baseEnd_507268] using wordTrace_append hprefix tailTrace_507268
  have hstable : (prefixWord ++ tailWord_507268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507268).length < 2 ^ (prefixWord ++ tailWord_507268).sum := by decide
  have hdescent : baseEnd_507268 < baseStart_507268 := by decide
  rcases family_descends (prefixWord ++ tailWord_507268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507328 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2]
def baseStart_507328 : Nat := 118140960795 + 507328 * 2 ^ 59
def prefixEnd_507328 : Nat := 4983230072969 + 3 ^ 40 * 507328 * 2
def baseEnd_507328 : Nat := 260503113484296310566847

theorem tailTrace_507328 : CollatzResearch.WordTrace tailWord_507328 prefixEnd_507328 260503113484296310566847 := by
  unfold tailWord_507328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9251886153022387784685319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12335848204029850379580425 9251886153022387784685319)
  ·
    refine ⟨13877829229533581677027979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9251886153022387784685319 13877829229533581677027979)
    ·
      refine ⟨20816743844300372515541969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13877829229533581677027979 20816743844300372515541969)
      ·
        refine ⟨15612557883225279386656477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20816743844300372515541969 15612557883225279386656477)
        ·
          refine ⟨5854709206209479769996179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15612557883225279386656477 5854709206209479769996179)
          ·
            refine ⟨8782063809314219654994269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854709206209479769996179 8782063809314219654994269)
            ·
              refine ⟨3293273928492832370622851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8782063809314219654994269 3293273928492832370622851)
              ·
                refine ⟨4939910892739248555934277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293273928492832370622851 4939910892739248555934277)
                ·
                  refine ⟨926233292388609104237677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4939910892739248555934277 926233292388609104237677)
                  ·
                    refine ⟨347337484645728414089129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926233292388609104237677 347337484645728414089129)
                    ·
                      refine ⟨260503113484296310566847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347337484645728414089129 260503113484296310566847)
                      ·
                        rfl

theorem cell23_507328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_507328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507328 prefixEnd_507328 := by exact prefixLift 507328
  have htrace : WordTrace (prefixWord ++ tailWord_507328) baseStart_507328 baseEnd_507328 := by
    simpa [prefixWord, tailWord_507328, baseEnd_507328] using wordTrace_append hprefix tailTrace_507328
  have hstable : (prefixWord ++ tailWord_507328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507328).length < 2 ^ (prefixWord ++ tailWord_507328).sum := by decide
  have hdescent : baseEnd_507328 < baseStart_507328 := by decide
  rcases family_descends (prefixWord ++ tailWord_507328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507555 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 2, 4, 2]
def baseStart_507555 : Nat := 118140960795 + 507555 * 2 ^ 59
def prefixEnd_507555 : Nat := 4983230072969 + 3 ^ 40 * 507555 * 2
def baseEnd_507555 : Nat := 260619673592866922428303

theorem tailTrace_507555 : CollatzResearch.WordTrace tailWord_507555 prefixEnd_507555 260619673592866922428303 := by
  unfold tailWord_507555
  simp only [CollatzResearch.WordTrace]
  refine ⟨18512051676222393337884119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12341367784148262225256079 18512051676222393337884119)
  ·
    refine ⟨27768077514333590006826179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18512051676222393337884119 27768077514333590006826179)
    ·
      refine ⟨41652116271500385010239269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27768077514333590006826179 41652116271500385010239269)
      ·
        refine ⟨7809771800906322189419863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41652116271500385010239269 7809771800906322189419863)
        ·
          refine ⟨11714657701359483284129795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809771800906322189419863 11714657701359483284129795)
          ·
            refine ⟨17571986552039224926194693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11714657701359483284129795 17571986552039224926194693)
            ·
              refine ⟨3294747478507354673661505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17571986552039224926194693 3294747478507354673661505)
              ·
                refine ⟨2471060608880516005246129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294747478507354673661505 2471060608880516005246129)
                ·
                  refine ⟨1853295456660387003934597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2471060608880516005246129 1853295456660387003934597)
                  ·
                    refine ⟨347492898123822563237737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1853295456660387003934597 347492898123822563237737)
                    ·
                      refine ⟨260619673592866922428303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347492898123822563237737 260619673592866922428303)
                      ·
                        rfl

theorem cell23_507555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_507555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507555 prefixEnd_507555 := by exact prefixLift 507555
  have htrace : WordTrace (prefixWord ++ tailWord_507555) baseStart_507555 baseEnd_507555 := by
    simpa [prefixWord, tailWord_507555, baseEnd_507555] using wordTrace_append hprefix tailTrace_507555
  have hstable : (prefixWord ++ tailWord_507555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507555).length < 2 ^ (prefixWord ++ tailWord_507555).sum := by decide
  have hdescent : baseEnd_507555 < baseStart_507555 := by decide
  rcases family_descends (prefixWord ++ tailWord_507555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507582 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_507582 : Nat := 118140960795 + 507582 * 2 ^ 59
def prefixEnd_507582 : Nat := 4983230072969 + 3 ^ 40 * 507582 * 2
def baseEnd_507582 : Nat := 86877845856846105596893

theorem tailTrace_507582 : CollatzResearch.WordTrace tailWord_507582 prefixEnd_507582 86877845856846105596893 := by
  unfold tailWord_507582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314129555890572118639625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12342024298083051299411333 2314129555890572118639625)
  ·
    refine ⟨1735597166917929088979719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2314129555890572118639625 1735597166917929088979719)
    ·
      refine ⟨2603395750376893633469579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735597166917929088979719 2603395750376893633469579)
      ·
        refine ⟨3905093625565340450204369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603395750376893633469579 3905093625565340450204369)
        ·
          refine ⟨2928820219174005337653277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905093625565340450204369 2928820219174005337653277)
          ·
            refine ⟨1098307582190252001619979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2928820219174005337653277 1098307582190252001619979)
            ·
              refine ⟨1647461373285378002429969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098307582190252001619979 1647461373285378002429969)
              ·
                refine ⟨1235596029964033501822477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647461373285378002429969 1235596029964033501822477)
                ·
                  refine ⟨463348511236512563183429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1235596029964033501822477 463348511236512563183429)
                  ·
                    refine ⟨86877845856846105596893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 463348511236512563183429 86877845856846105596893)
                    ·
                      rfl

theorem cell23_507582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_507582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507582 prefixEnd_507582 := by exact prefixLift 507582
  have htrace : WordTrace (prefixWord ++ tailWord_507582) baseStart_507582 baseEnd_507582 := by
    simpa [prefixWord, tailWord_507582, baseEnd_507582] using wordTrace_append hprefix tailTrace_507582
  have hstable : (prefixWord ++ tailWord_507582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507582).length < 2 ^ (prefixWord ++ tailWord_507582).sum := by decide
  have hdescent : baseEnd_507582 < baseStart_507582 := by decide
  rcases family_descends (prefixWord ++ tailWord_507582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507612 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 8]
def baseStart_507612 : Nat := 118140960795 + 507612 * 2 ^ 59
def prefixEnd_507612 : Nat := 4983230072969 + 3 ^ 40 * 507612 * 2
def baseEnd_507612 : Nat := 28960993554463688823949

theorem tailTrace_507612 : CollatzResearch.WordTrace tailWord_507612 prefixEnd_507612 28960993554463688823949 := by
  unfold tailWord_507612
  simp only [CollatzResearch.WordTrace]
  refine ⟨9257065318507946036354545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12342753758010594715139393 9257065318507946036354545)
  ·
    refine ⟨6942798988880959527265909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9257065318507946036354545 6942798988880959527265909)
    ·
      refine ⟨650887405207589955681179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6942798988880959527265909 650887405207589955681179)
      ·
        refine ⟨976331107811384933521769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650887405207589955681179 976331107811384933521769)
        ·
          refine ⟨732248330858538700141327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976331107811384933521769 732248330858538700141327)
          ·
            refine ⟨1098372496287808050211991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732248330858538700141327 1098372496287808050211991)
            ·
              refine ⟨1647558744431712075317987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098372496287808050211991 1647558744431712075317987)
              ·
                refine ⟨2471338116647568112976981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647558744431712075317987 2471338116647568112976981)
                ·
                  refine ⟨28960993554463688823949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2471338116647568112976981 28960993554463688823949)
                  ·
                    rfl

theorem cell23_507612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_507612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507612 prefixEnd_507612 := by exact prefixLift 507612
  have htrace : WordTrace (prefixWord ++ tailWord_507612) baseStart_507612 baseEnd_507612 := by
    simpa [prefixWord, tailWord_507612, baseEnd_507612] using wordTrace_append hprefix tailTrace_507612
  have hstable : (prefixWord ++ tailWord_507612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507612).length < 2 ^ (prefixWord ++ tailWord_507612).sum := by decide
  have hdescent : baseEnd_507612 < baseStart_507612 := by decide
  rcases family_descends (prefixWord ++ tailWord_507612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507662 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_507662 : Nat := 118140960795 + 507662 * 2 ^ 59
def prefixEnd_507662 : Nat := 4983230072969 + 3 ^ 40 * 507662 * 2
def baseEnd_507662 : Nat := 260674616022898003790311

theorem tailTrace_507662 : CollatzResearch.WordTrace tailWord_507662 prefixEnd_507662 260674616022898003790311 := by
  unfold tailWord_507662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314494285854343826503655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12343969524556500408019493 2314494285854343826503655)
  ·
    refine ⟨3471741428781515739755483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314494285854343826503655 3471741428781515739755483)
    ·
      refine ⟨5207612143172273609633225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3471741428781515739755483 5207612143172273609633225)
      ·
        refine ⟨3905709107379205207224919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5207612143172273609633225 3905709107379205207224919)
        ·
          refine ⟨5858563661068807810837379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905709107379205207224919 5858563661068807810837379)
          ·
            refine ⟨8787845491603211716256069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858563661068807810837379 8787845491603211716256069)
            ·
              refine ⟨1647721029675602196798013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8787845491603211716256069 1647721029675602196798013)
              ·
                refine ⟨617895386128350823799255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647721029675602196798013 617895386128350823799255)
                ·
                  refine ⟨926843079192526235698883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617895386128350823799255 926843079192526235698883)
                  ·
                    refine ⟨1390264618788789353548325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 926843079192526235698883 1390264618788789353548325)
                    ·
                      refine ⟨260674616022898003790311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1390264618788789353548325 260674616022898003790311)
                      ·
                        rfl

theorem cell23_507662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_507662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507662 prefixEnd_507662 := by exact prefixLift 507662
  have htrace : WordTrace (prefixWord ++ tailWord_507662) baseStart_507662 baseEnd_507662 := by
    simpa [prefixWord, tailWord_507662, baseEnd_507662] using wordTrace_append hprefix tailTrace_507662
  have hstable : (prefixWord ++ tailWord_507662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507662).length < 2 ^ (prefixWord ++ tailWord_507662).sum := by decide
  have hdescent : baseEnd_507662 < baseStart_507662 := by decide
  rcases family_descends (prefixWord ++ tailWord_507662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507665 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_507665 : Nat := 118140960795 + 507665 * 2 ^ 59
def prefixEnd_507665 : Nat := 4983230072969 + 3 ^ 40 * 507665 * 2
def baseEnd_507665 : Nat := 260676156464861492052797

theorem tailTrace_507665 : CollatzResearch.WordTrace tailWord_507665 prefixEnd_507665 260676156464861492052797 := by
  unfold tailWord_507665
  simp only [CollatzResearch.WordTrace]
  refine ⟨18516063705823882124388449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12344042470549254749592299 18516063705823882124388449)
  ·
    refine ⟨13887047779367911593291337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18516063705823882124388449 13887047779367911593291337)
    ·
      refine ⟨10415285834525933694968503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13887047779367911593291337 10415285834525933694968503)
      ·
        refine ⟨15622928751788900542452755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415285834525933694968503 15622928751788900542452755)
        ·
          refine ⟨23434393127683350813679133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15622928751788900542452755 23434393127683350813679133)
          ·
            refine ⟨8787897422881256555129675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23434393127683350813679133 8787897422881256555129675)
            ·
              refine ⟨13181846134321884832694513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787897422881256555129675 13181846134321884832694513)
              ·
                refine ⟨9886384600741413624520885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181846134321884832694513 9886384600741413624520885)
                ·
                  refine ⟨926848556319507527298833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9886384600741413624520885 926848556319507527298833)
                  ·
                    refine ⟨695136417239630645474125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 926848556319507527298833 695136417239630645474125)
                    ·
                      refine ⟨260676156464861492052797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695136417239630645474125 260676156464861492052797)
                      ·
                        rfl

theorem cell23_507665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_507665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507665 prefixEnd_507665 := by exact prefixLift 507665
  have htrace : WordTrace (prefixWord ++ tailWord_507665) baseStart_507665 baseEnd_507665 := by
    simpa [prefixWord, tailWord_507665, baseEnd_507665] using wordTrace_append hprefix tailTrace_507665
  have hstable : (prefixWord ++ tailWord_507665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507665).length < 2 ^ (prefixWord ++ tailWord_507665).sum := by decide
  have hdescent : baseEnd_507665 < baseStart_507665 := by decide
  rcases family_descends (prefixWord ++ tailWord_507665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507666 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_507666 : Nat := 118140960795 + 507666 * 2 ^ 59
def prefixEnd_507666 : Nat := 4983230072969 + 3 ^ 40 * 507666 * 2
def baseEnd_507666 : Nat := 260676669945515988140293

theorem tailTrace_507666 : CollatzResearch.WordTrace tailWord_507666 prefixEnd_507666 260676669945515988140293 := by
  unfold tailWord_507666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629025044705064823793713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12344066785880172863449901 4629025044705064823793713)
  ·
    refine ⟨3471768783528798617845285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4629025044705064823793713 3471768783528798617845285)
    ·
      refine ⟨650956646911649740845991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3471768783528798617845285 650956646911649740845991)
      ·
        refine ⟨976434970367474611268987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650956646911649740845991 976434970367474611268987)
        ·
          refine ⟨1464652455551211916903481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976434970367474611268987 1464652455551211916903481)
          ·
            refine ⟨1098489341663408937677611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464652455551211916903481 1098489341663408937677611)
            ·
              refine ⟨1647734012495113406516417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098489341663408937677611 1647734012495113406516417)
              ·
                refine ⟨1235800509371335054887313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647734012495113406516417 1235800509371335054887313)
                ·
                  refine ⟨926850382028501291165485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1235800509371335054887313 926850382028501291165485)
                  ·
                    refine ⟨347568893260687984187057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926850382028501291165485 347568893260687984187057)
                    ·
                      refine ⟨260676669945515988140293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347568893260687984187057 260676669945515988140293)
                      ·
                        rfl

theorem cell23_507666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_507666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507666 prefixEnd_507666 := by exact prefixLift 507666
  have htrace : WordTrace (prefixWord ++ tailWord_507666) baseStart_507666 baseEnd_507666 := by
    simpa [prefixWord, tailWord_507666, baseEnd_507666] using wordTrace_append hprefix tailTrace_507666
  have hstable : (prefixWord ++ tailWord_507666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507666).length < 2 ^ (prefixWord ++ tailWord_507666).sum := by decide
  have hdescent : baseEnd_507666 < baseStart_507666 := by decide
  rcases family_descends (prefixWord ++ tailWord_507666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507682 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_507682 : Nat := 118140960795 + 507682 * 2 ^ 59
def prefixEnd_507682 : Nat := 4983230072969 + 3 ^ 40 * 507682 * 2
def baseEnd_507682 : Nat := 260684885635987925540219

theorem tailTrace_507682 : CollatzResearch.WordTrace tailWord_507682 prefixEnd_507682 260684885635987925540219 := by
  unfold tailWord_507682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629170936690573506939325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12344455831174862685171533 4629170936690573506939325)
  ·
    refine ⟨1735939101258965065102247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4629170936690573506939325 1735939101258965065102247)
    ·
      refine ⟨2603908651888447597653371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735939101258965065102247 2603908651888447597653371)
      ·
        refine ⟨3905862977832671396480057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603908651888447597653371 3905862977832671396480057)
        ·
          refine ⟨2929397233374503547360043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905862977832671396480057 2929397233374503547360043)
          ·
            refine ⟨4394095850061755321040065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929397233374503547360043 4394095850061755321040065)
            ·
              refine ⟨3295571887546316490780049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394095850061755321040065 3295571887546316490780049)
              ·
                refine ⟨2471678915659737368085037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3295571887546316490780049 2471678915659737368085037)
                ·
                  refine ⟨926879593372401513031889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2471678915659737368085037 926879593372401513031889)
                  ·
                    refine ⟨695159695029301134773917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 926879593372401513031889 695159695029301134773917)
                    ·
                      refine ⟨260684885635987925540219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695159695029301134773917 260684885635987925540219)
                      ·
                        rfl

theorem cell23_507682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_507682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507682 prefixEnd_507682 := by exact prefixLift 507682
  have htrace : WordTrace (prefixWord ++ tailWord_507682) baseStart_507682 baseEnd_507682 := by
    simpa [prefixWord, tailWord_507682, baseEnd_507682] using wordTrace_append hprefix tailTrace_507682
  have hstable : (prefixWord ++ tailWord_507682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507682).length < 2 ^ (prefixWord ++ tailWord_507682).sum := by decide
  have hdescent : baseEnd_507682 < baseStart_507682 := by decide
  rcases family_descends (prefixWord ++ tailWord_507682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507685 : List Nat := [1, 3, 1, 2, 3, 3, 2, 8]
def baseStart_507685 : Nat := 118140960795 + 507685 * 2 ^ 59
def prefixEnd_507685 : Nat := 4983230072969 + 3 ^ 40 * 507685 * 2
def baseEnd_507685 : Nat := 9655052817701904214915

theorem tailTrace_507685 : CollatzResearch.WordTrace tailWord_507685 prefixEnd_507685 9655052817701904214915 := by
  unfold tailWord_507685
  simp only [CollatzResearch.WordTrace]
  refine ⟨18516793165751425540116509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12344528777167617026744339 18516793165751425540116509)
  ·
    refine ⟨6943797437156784577543691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18516793165751425540116509 6943797437156784577543691)
    ·
      refine ⟨10415696155735176866315537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6943797437156784577543691 10415696155735176866315537)
      ·
        refine ⟨7811772116801382649736653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10415696155735176866315537 7811772116801382649736653)
        ·
          refine ⟨2929414543800518493651245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7811772116801382649736653 2929414543800518493651245)
          ·
            refine ⟨1098530453925194435119217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2929414543800518493651245 1098530453925194435119217)
            ·
              refine ⟨823897840443895826339413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098530453925194435119217 823897840443895826339413)
              ·
                refine ⟨9655052817701904214915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 823897840443895826339413 9655052817701904214915)
                ·
                  rfl

theorem cell23_507685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 8].length) (baseStart_507685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507685 prefixEnd_507685 := by exact prefixLift 507685
  have htrace : WordTrace (prefixWord ++ tailWord_507685) baseStart_507685 baseEnd_507685 := by
    simpa [prefixWord, tailWord_507685, baseEnd_507685] using wordTrace_append hprefix tailTrace_507685
  have hstable : (prefixWord ++ tailWord_507685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507685).length < 2 ^ (prefixWord ++ tailWord_507685).sum := by decide
  have hdescent : baseEnd_507685 < baseStart_507685 := by decide
  rcases family_descends (prefixWord ++ tailWord_507685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507702 : List Nat := [5, 1, 2, 2, 1, 1, 2, 9]
def baseStart_507702 : Nat := 118140960795 + 507702 * 2 ^ 59
def prefixEnd_507702 : Nat := 4983230072969 + 3 ^ 40 * 507702 * 2
def baseEnd_507702 : Nat := 9655376120336216566301

theorem tailTrace_507702 : CollatzResearch.WordTrace tailWord_507702 prefixEnd_507702 9655376120336216566301 := by
  unfold tailWord_507702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157338325418114840217835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12344942137793224962323573 1157338325418114840217835)
  ·
    refine ⟨1736007488127172260326753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1157338325418114840217835 1736007488127172260326753)
    ·
      refine ⟨1302005616095379195245065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1736007488127172260326753 1302005616095379195245065)
      ·
        refine ⟨976504212071534396433799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302005616095379195245065 976504212071534396433799)
        ·
          refine ⟨1464756318107301594650699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976504212071534396433799 1464756318107301594650699)
          ·
            refine ⟨2197134477160952391976049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464756318107301594650699 2197134477160952391976049)
            ·
              refine ⟨1647850857870714293982037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197134477160952391976049 1647850857870714293982037)
              ·
                refine ⟨9655376120336216566301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1647850857870714293982037 9655376120336216566301)
                ·
                  rfl

theorem cell23_507702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_507702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507702 prefixEnd_507702 := by exact prefixLift 507702
  have htrace : WordTrace (prefixWord ++ tailWord_507702) baseStart_507702 baseEnd_507702 := by
    simpa [prefixWord, tailWord_507702, baseEnd_507702] using wordTrace_append hprefix tailTrace_507702
  have hstable : (prefixWord ++ tailWord_507702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507702).length < 2 ^ (prefixWord ++ tailWord_507702).sum := by decide
  have hdescent : baseEnd_507702 < baseStart_507702 := by decide
  rcases family_descends (prefixWord ++ tailWord_507702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507729 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_507729 : Nat := 118140960795 + 507729 * 2 ^ 59
def prefixEnd_507729 : Nat := 4983230072969 + 3 ^ 40 * 507729 * 2
def baseEnd_507729 : Nat := 260709019226749241652503

theorem tailTrace_507729 : CollatzResearch.WordTrace tailWord_507729 prefixEnd_507729 260709019226749241652503 := by
  unfold tailWord_507729
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518397977592021054718241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12345598651728014036478827 18518397977592021054718241)
  ·
    refine ⟨13888798483194015791038681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18518397977592021054718241 13888798483194015791038681)
    ·
      refine ⟨10416598862395511843279011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13888798483194015791038681 10416598862395511843279011)
      ·
        refine ⟨15624898293593267764918517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10416598862395511843279011 15624898293593267764918517)
        ·
          refine ⟨1464834215024368852961111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15624898293593267764918517 1464834215024368852961111)
          ·
            refine ⟨2197251322536553279441667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464834215024368852961111 2197251322536553279441667)
            ·
              refine ⟨3295876983804829919162501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197251322536553279441667 3295876983804829919162501)
              ·
                refine ⟨617976934463405609842969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3295876983804829919162501 617976934463405609842969)
                ·
                  refine ⟨463482700847554207382227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617976934463405609842969 463482700847554207382227)
                  ·
                    refine ⟨695224051271331311073341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 463482700847554207382227 695224051271331311073341)
                    ·
                      refine ⟨260709019226749241652503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695224051271331311073341 260709019226749241652503)
                      ·
                        rfl

theorem cell23_507729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_507729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507729 prefixEnd_507729 := by exact prefixLift 507729
  have htrace : WordTrace (prefixWord ++ tailWord_507729) baseStart_507729 baseEnd_507729 := by
    simpa [prefixWord, tailWord_507729, baseEnd_507729] using wordTrace_append hprefix tailTrace_507729
  have hstable : (prefixWord ++ tailWord_507729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507729).length < 2 ^ (prefixWord ++ tailWord_507729).sum := by decide
  have hdescent : baseEnd_507729 < baseStart_507729 := by decide
  rcases family_descends (prefixWord ++ tailWord_507729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507730 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2]
def baseStart_507730 : Nat := 118140960795 + 507730 * 2 ^ 59
def prefixEnd_507730 : Nat := 4983230072969 + 3 ^ 40 * 507730 * 2
def baseEnd_507730 : Nat := 260709532707403737739999

theorem tailTrace_507730 : CollatzResearch.WordTrace tailWord_507730 prefixEnd_507730 260709532707403737739999 := by
  unfold tailWord_507730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629608612647099556376161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12345622967058932150336429 4629608612647099556376161)
  ·
    refine ⟨3472206459485324667282121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4629608612647099556376161 3472206459485324667282121)
    ·
      refine ⟨2604154844613993500461591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3472206459485324667282121 2604154844613993500461591)
      ·
        refine ⟨3906232266920990250692387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2604154844613993500461591 3906232266920990250692387)
        ·
          refine ⟨5859348400381485376038581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906232266920990250692387 5859348400381485376038581)
          ·
            refine ⟨549313912535764254003617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5859348400381485376038581 549313912535764254003617)
            ·
              refine ⟨411985434401823190502713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549313912535764254003617 411985434401823190502713)
              ·
                refine ⟨308989075801367392877035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411985434401823190502713 308989075801367392877035)
                ·
                  refine ⟨463483613702051089315553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308989075801367392877035 463483613702051089315553)
                  ·
                    refine ⟨347612710276538316986665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 463483613702051089315553 347612710276538316986665)
                    ·
                      refine ⟨260709532707403737739999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347612710276538316986665 260709532707403737739999)
                      ·
                        rfl

theorem cell23_507730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_507730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507730 prefixEnd_507730 := by exact prefixLift 507730
  have htrace : WordTrace (prefixWord ++ tailWord_507730) baseStart_507730 baseEnd_507730 := by
    simpa [prefixWord, tailWord_507730, baseEnd_507730] using wordTrace_append hprefix tailTrace_507730
  have hstable : (prefixWord ++ tailWord_507730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507730).length < 2 ^ (prefixWord ++ tailWord_507730).sum := by decide
  have hdescent : baseEnd_507730 < baseStart_507730 := by decide
  rcases family_descends (prefixWord ++ tailWord_507730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507745 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_507745 : Nat := 118140960795 + 507745 * 2 ^ 59
def prefixEnd_507745 : Nat := 4983230072969 + 3 ^ 40 * 507745 * 2
def baseEnd_507745 : Nat := 86905744972407059684143

theorem tailTrace_507745 : CollatzResearch.WordTrace tailWord_507745 prefixEnd_507745 86905744972407059684143 := by
  unfold tailWord_507745
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518981545534055787300689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12345987697022703858200459 18518981545534055787300689)
  ·
    refine ⟨13889236159150541840475517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18518981545534055787300689 13889236159150541840475517)
    ·
      refine ⟨5208463559681453190178319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13889236159150541840475517 5208463559681453190178319)
      ·
        refine ⟨7812695339522179785267479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208463559681453190178319 7812695339522179785267479)
        ·
          refine ⟨11719043009283269677901219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812695339522179785267479 11719043009283269677901219)
          ·
            refine ⟨17578564513924904516851829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719043009283269677901219 17578564513924904516851829)
            ·
              refine ⟨1647990423180459798454859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17578564513924904516851829 1647990423180459798454859)
              ·
                refine ⟨2471985634770689697682289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647990423180459798454859 2471985634770689697682289)
                ·
                  refine ⟨1853989226078017273261717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2471985634770689697682289 1853989226078017273261717)
                  ·
                    refine ⟨86905744972407059684143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1853989226078017273261717 86905744972407059684143)
                    ·
                      rfl

theorem cell23_507745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_507745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507745 prefixEnd_507745 := by exact prefixLift 507745
  have htrace : WordTrace (prefixWord ++ tailWord_507745) baseStart_507745 baseEnd_507745 := by
    simpa [prefixWord, tailWord_507745, baseEnd_507745] using wordTrace_append hprefix tailTrace_507745
  have hstable : (prefixWord ++ tailWord_507745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507745).length < 2 ^ (prefixWord ++ tailWord_507745).sum := by decide
  have hdescent : baseEnd_507745 < baseStart_507745 := by decide
  rcases family_descends (prefixWord ++ tailWord_507745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507746 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_507746 : Nat := 118140960795 + 507746 * 2 ^ 59
def prefixEnd_507746 : Nat := 4983230072969 + 3 ^ 40 * 507746 * 2
def baseEnd_507746 : Nat := 260717748397875675139925

theorem tailTrace_507746 : CollatzResearch.WordTrace tailWord_507746 prefixEnd_507746 260717748397875675139925 := by
  unfold tailWord_507746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4629754504632608239521773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12346012012353621972058061 4629754504632608239521773)
  ·
    refine ⟨1736157939237228089820665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4629754504632608239521773 1736157939237228089820665)
    ·
      refine ⟨1302118454427921067365499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1736157939237228089820665 1302118454427921067365499)
      ·
        refine ⟨1953177681641881601048249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302118454427921067365499 1953177681641881601048249)
        ·
          refine ⟨1464883261231411200786187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953177681641881601048249 1464883261231411200786187)
          ·
            refine ⟨2197324891847116801179281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464883261231411200786187 2197324891847116801179281)
            ·
              refine ⟨1647993668885337600884461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197324891847116801179281 1647993668885337600884461)
              ·
                refine ⟨617997625832001600331673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647993668885337600884461 617997625832001600331673)
                ·
                  refine ⟨463498219374001200248755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617997625832001600331673 463498219374001200248755)
                  ·
                    refine ⟨695247329061001800373133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 463498219374001200248755 695247329061001800373133)
                    ·
                      refine ⟨260717748397875675139925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695247329061001800373133 260717748397875675139925)
                      ·
                        rfl

theorem cell23_507746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_507746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507746 prefixEnd_507746 := by exact prefixLift 507746
  have htrace : WordTrace (prefixWord ++ tailWord_507746) baseStart_507746 baseEnd_507746 := by
    simpa [prefixWord, tailWord_507746, baseEnd_507746] using wordTrace_append hprefix tailTrace_507746
  have hstable : (prefixWord ++ tailWord_507746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507746).length < 2 ^ (prefixWord ++ tailWord_507746).sum := by decide
  have hdescent : baseEnd_507746 < baseStart_507746 := by decide
  rcases family_descends (prefixWord ++ tailWord_507746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507755 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3]
def baseStart_507755 : Nat := 118140960795 + 507755 * 2 ^ 59
def prefixEnd_507755 : Nat := 4983230072969 + 3 ^ 40 * 507755 * 2
def baseEnd_507755 : Nat := 260722369723766139927383

theorem tailTrace_507755 : CollatzResearch.WordTrace tailWord_507755 prefixEnd_507755 260722369723766139927383 := by
  unfold tailWord_507755
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519346275497827495164719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12346230850331884996776479 18519346275497827495164719)
  ·
    refine ⟨27779019413246741242747079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18519346275497827495164719 27779019413246741242747079)
    ·
      refine ⟨41668529119870111864120619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27779019413246741242747079 41668529119870111864120619)
      ·
        refine ⟨62502793679805167796180929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41668529119870111864120619 62502793679805167796180929)
        ·
          refine ⟨46877095259853875847135697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62502793679805167796180929 46877095259853875847135697)
          ·
            refine ⟨35157821444890406885351773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46877095259853875847135697 35157821444890406885351773)
            ·
              refine ⟨13184183041833902582006915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35157821444890406885351773 13184183041833902582006915)
              ·
                refine ⟨19776274562750853873010373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13184183041833902582006915 19776274562750853873010373)
                ·
                  refine ⟨3708051480515785101189445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19776274562750853873010373 3708051480515785101189445)
                  ·
                    refine ⟨695259652596709706473021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708051480515785101189445 695259652596709706473021)
                    ·
                      refine ⟨260722369723766139927383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695259652596709706473021 260722369723766139927383)
                      ·
                        rfl

theorem cell23_507755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 3].length) (baseStart_507755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507755 prefixEnd_507755 := by exact prefixLift 507755
  have htrace : WordTrace (prefixWord ++ tailWord_507755) baseStart_507755 baseEnd_507755 := by
    simpa [prefixWord, tailWord_507755, baseEnd_507755] using wordTrace_append hprefix tailTrace_507755
  have hstable : (prefixWord ++ tailWord_507755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507755).length < 2 ^ (prefixWord ++ tailWord_507755).sum := by decide
  have hdescent : baseEnd_507755 < baseStart_507755 := by decide
  rcases family_descends (prefixWord ++ tailWord_507755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507769 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 4, 2, 2]
def baseStart_507769 : Nat := 118140960795 + 507769 * 2 ^ 59
def prefixEnd_507769 : Nat := 4983230072969 + 3 ^ 40 * 507769 * 2
def baseEnd_507769 : Nat := 260729558452929085152319

theorem tailTrace_507769 : CollatzResearch.WordTrace tailWord_507769 prefixEnd_507769 260729558452929085152319 := by
  unfold tailWord_507769
  simp only [CollatzResearch.WordTrace]
  refine ⟨18519856897447107886174361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12346571264964738590782907 18519856897447107886174361)
  ·
    refine ⟨13889892673085330914630771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18519856897447107886174361 13889892673085330914630771)
    ·
      refine ⟨20834839009627996371946157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13889892673085330914630771 20834839009627996371946157)
      ·
        refine ⟨7813064628610498639479809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20834839009627996371946157 7813064628610498639479809)
        ·
          refine ⟨5859798471457873979609857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7813064628610498639479809 5859798471457873979609857)
          ·
            refine ⟨4394848853593405484707393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5859798471457873979609857 4394848853593405484707393)
            ·
              refine ⟨3296136640195054113530545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4394848853593405484707393 3296136640195054113530545)
              ·
                refine ⟨2472102480146290585147909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3296136640195054113530545 2472102480146290585147909)
                ·
                  refine ⟨463519215027429484715233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472102480146290585147909 463519215027429484715233)
                  ·
                    refine ⟨347639411270572113536425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 463519215027429484715233 347639411270572113536425)
                    ·
                      refine ⟨260729558452929085152319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347639411270572113536425 260729558452929085152319)
                      ·
                        rfl

theorem cell23_507769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_507769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507769 prefixEnd_507769 := by exact prefixLift 507769
  have htrace : WordTrace (prefixWord ++ tailWord_507769) baseStart_507769 baseEnd_507769 := by
    simpa [prefixWord, tailWord_507769, baseEnd_507769] using wordTrace_append hprefix tailTrace_507769
  have hstable : (prefixWord ++ tailWord_507769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507769).length < 2 ^ (prefixWord ++ tailWord_507769).sum := by decide
  have hdescent : baseEnd_507769 < baseStart_507769 := by decide
  rcases family_descends (prefixWord ++ tailWord_507769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507845 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_507845 : Nat := 118140960795 + 507845 * 2 ^ 59
def prefixEnd_507845 : Nat := 4983230072969 + 3 ^ 40 * 507845 * 2
def baseEnd_507845 : Nat := 260768582982670787801969

theorem tailTrace_507845 : CollatzResearch.WordTrace tailWord_507845 prefixEnd_507845 260768582982670787801969 := by
  unfold tailWord_507845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18522628845171772865940989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12348419230114515243960659 18522628845171772865940989)
  ·
    refine ⟨6945985816939414824727871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18522628845171772865940989 6945985816939414824727871)
    ·
      refine ⟨10418978725409122237091807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6945985816939414824727871 10418978725409122237091807)
      ·
        refine ⟨15628468088113683355637711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418978725409122237091807 15628468088113683355637711)
        ·
          refine ⟨23442702132170525033456567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15628468088113683355637711 23442702132170525033456567)
          ·
            refine ⟨35164053198255787550184851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23442702132170525033456567 35164053198255787550184851)
            ·
              refine ⟨52746079797383681325277277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35164053198255787550184851 52746079797383681325277277)
              ·
                refine ⟨19779779924018880496978979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52746079797383681325277277 19779779924018880496978979)
                ·
                  refine ⟨29669669886028320745468469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19779779924018880496978979 29669669886028320745468469)
                  ·
                    refine ⟨2781531551815155069887669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29669669886028320745468469 2781531551815155069887669)
                    ·
                      refine ⟨260768582982670787801969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2781531551815155069887669 260768582982670787801969)
                      ·
                        rfl

theorem cell23_507845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_507845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507845 prefixEnd_507845 := by exact prefixLift 507845
  have htrace : WordTrace (prefixWord ++ tailWord_507845) baseStart_507845 baseEnd_507845 := by
    simpa [prefixWord, tailWord_507845, baseEnd_507845] using wordTrace_append hprefix tailTrace_507845
  have hstable : (prefixWord ++ tailWord_507845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507845).length < 2 ^ (prefixWord ++ tailWord_507845).sum := by decide
  have hdescent : baseEnd_507845 < baseStart_507845 := by decide
  rcases family_descends (prefixWord ++ tailWord_507845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507912 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_507912 : Nat := 118140960795 + 507912 * 2 ^ 59
def prefixEnd_507912 : Nat := 4983230072969 + 3 ^ 40 * 507912 * 2
def baseEnd_507912 : Nat := 86934328728840675221387

theorem tailTrace_507912 : CollatzResearch.WordTrace tailWord_507912 prefixEnd_507912 86934328728840675221387 := by
  unfold tailWord_507912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262536267964521654314995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12350048357286028872419993 9262536267964521654314995)
  ·
    refine ⟨13893804401946782481472493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9262536267964521654314995 13893804401946782481472493)
    ·
      refine ⟨5210176650730043430552185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13893804401946782481472493 5210176650730043430552185)
      ·
        refine ⟨3907632488047532572914139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210176650730043430552185 3907632488047532572914139)
        ·
          refine ⟨5861448732071298859371209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907632488047532572914139 5861448732071298859371209)
          ·
            refine ⟨4396086549053474144528407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5861448732071298859371209 4396086549053474144528407)
            ·
              refine ⟨6594129823580211216792611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396086549053474144528407 6594129823580211216792611)
              ·
                refine ⟨9891194735370316825188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594129823580211216792611 9891194735370316825188917)
                ·
                  refine ⟨927299506440967202361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9891194735370316825188917 927299506440967202361461)
                  ·
                    refine ⟨86934328728840675221387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 927299506440967202361461 86934328728840675221387)
                    ·
                      rfl

theorem cell23_507912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_507912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507912 prefixEnd_507912 := by exact prefixLift 507912
  have htrace : WordTrace (prefixWord ++ tailWord_507912) baseStart_507912 baseEnd_507912 := by
    simpa [prefixWord, tailWord_507912, baseEnd_507912] using wordTrace_append hprefix tailTrace_507912
  have hstable : (prefixWord ++ tailWord_507912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507912).length < 2 ^ (prefixWord ++ tailWord_507912).sum := by decide
  have hdescent : baseEnd_507912 < baseStart_507912 := by decide
  rcases family_descends (prefixWord ++ tailWord_507912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507946 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_507946 : Nat := 118140960795 + 507946 * 2 ^ 59
def prefixEnd_507946 : Nat := 4983230072969 + 3 ^ 40 * 507946 * 2
def baseEnd_507946 : Nat := 86940148176258297546335

theorem tailTrace_507946 : CollatzResearch.WordTrace tailWord_507946 prefixEnd_507946 86940148176258297546335 := by
  unfold tailWord_507946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631578154451466778841923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12350875078537244743578461 4631578154451466778841923)
  ·
    refine ⟨6947367231677200168262885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4631578154451466778841923 6947367231677200168262885)
    ·
      refine ⟨1302631355939475031549291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6947367231677200168262885 1302631355939475031549291)
      ·
        refine ⟨1953947033909212547323937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302631355939475031549291 1953947033909212547323937)
        ·
          refine ⟨1465460275431909410492953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953947033909212547323937 1465460275431909410492953)
          ·
            refine ⟨1099095206573932057869715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465460275431909410492953 1099095206573932057869715)
            ·
              refine ⟨1648642809860898086804573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099095206573932057869715 1648642809860898086804573)
              ·
                refine ⟨618241053697836782551715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648642809860898086804573 618241053697836782551715)
                ·
                  refine ⟨927361580546755173827573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618241053697836782551715 927361580546755173827573)
                  ·
                    refine ⟨86940148176258297546335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 927361580546755173827573 86940148176258297546335)
                    ·
                      rfl

theorem cell23_507946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_507946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507946 prefixEnd_507946 := by exact prefixLift 507946
  have htrace : WordTrace (prefixWord ++ tailWord_507946) baseStart_507946 baseEnd_507946 := by
    simpa [prefixWord, tailWord_507946, baseEnd_507946] using wordTrace_append hprefix tailTrace_507946
  have hstable : (prefixWord ++ tailWord_507946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507946).length < 2 ^ (prefixWord ++ tailWord_507946).sum := by decide
  have hdescent : baseEnd_507946 < baseStart_507946 := by decide
  rcases family_descends (prefixWord ++ tailWord_507946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507962 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_507962 : Nat := 118140960795 + 507962 * 2 ^ 59
def prefixEnd_507962 : Nat := 4983230072969 + 3 ^ 40 * 507962 * 2
def baseEnd_507962 : Nat := 260828660219246830038931

theorem tailTrace_507962 : CollatzResearch.WordTrace tailWord_507962 prefixEnd_507962 260828660219246830038931 := by
  unfold tailWord_507962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4631724046436975461987535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12351264123831934565300093 4631724046436975461987535)
  ·
    refine ⟨6947586069655463192981303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4631724046436975461987535 6947586069655463192981303)
    ·
      refine ⟨10421379104483194789471955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6947586069655463192981303 10421379104483194789471955)
      ·
        refine ⟨15632068656724792184207933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421379104483194789471955 15632068656724792184207933)
        ·
          refine ⟨5862025746271797069077975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15632068656724792184207933 5862025746271797069077975)
          ·
            refine ⟨8793038619407695603616963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862025746271797069077975 8793038619407695603616963)
            ·
              refine ⟨13189557929111543405425445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793038619407695603616963 13189557929111543405425445)
              ·
                refine ⟨2473042111708414388517271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13189557929111543405425445 2473042111708414388517271)
                ·
                  refine ⟨3709563167562621582775907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473042111708414388517271 3709563167562621582775907)
                  ·
                    refine ⟨5564344751343932374163861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709563167562621582775907 5564344751343932374163861)
                    ·
                      refine ⟨260828660219246830038931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5564344751343932374163861 260828660219246830038931)
                      ·
                        rfl

theorem cell23_507962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_507962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507962 prefixEnd_507962 := by exact prefixLift 507962
  have htrace : WordTrace (prefixWord ++ tailWord_507962) baseStart_507962 baseEnd_507962 := by
    simpa [prefixWord, tailWord_507962, baseEnd_507962] using wordTrace_append hprefix tailTrace_507962
  have hstable : (prefixWord ++ tailWord_507962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507962).length < 2 ^ (prefixWord ++ tailWord_507962).sum := by decide
  have hdescent : baseEnd_507962 < baseStart_507962 := by decide
  rcases family_descends (prefixWord ++ tailWord_507962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507969 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_507969 : Nat := 118140960795 + 507969 * 2 ^ 59
def prefixEnd_507969 : Nat := 4983230072969 + 3 ^ 40 * 507969 * 2
def baseEnd_507969 : Nat := 260832254583828302651399

theorem tailTrace_507969 : CollatzResearch.WordTrace tailWord_507969 prefixEnd_507969 260832254583828302651399 := by
  unfold tailWord_507969
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527151496722542043454961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12351434331148361362303307 18527151496722542043454961)
  ·
    refine ⟨13895363622541906532591221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18527151496722542043454961 13895363622541906532591221)
    ·
      refine ⟨1302690339613303737430427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13895363622541906532591221 1302690339613303737430427)
      ·
        refine ⟨1954035509419955606145641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302690339613303737430427 1954035509419955606145641)
        ·
          refine ⟨1465526632064966704609231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954035509419955606145641 1465526632064966704609231)
          ·
            refine ⟨2198289948097450056913847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465526632064966704609231 2198289948097450056913847)
            ·
              refine ⟨3297434922146175085370771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198289948097450056913847 3297434922146175085370771)
              ·
                refine ⟨4946152383219262628056157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297434922146175085370771 4946152383219262628056157)
                ·
                  refine ⟨1854807143707223485521059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4946152383219262628056157 1854807143707223485521059)
                  ·
                    refine ⟨2782210715560835228281589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1854807143707223485521059 2782210715560835228281589)
                    ·
                      refine ⟨260832254583828302651399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2782210715560835228281589 260832254583828302651399)
                      ·
                        rfl

theorem cell23_507969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_507969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507969 prefixEnd_507969 := by exact prefixLift 507969
  have htrace : WordTrace (prefixWord ++ tailWord_507969) baseStart_507969 baseEnd_507969 := by
    simpa [prefixWord, tailWord_507969, baseEnd_507969] using wordTrace_append hprefix tailTrace_507969
  have hstable : (prefixWord ++ tailWord_507969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507969).length < 2 ^ (prefixWord ++ tailWord_507969).sum := by decide
  have hdescent : baseEnd_507969 < baseStart_507969 := by decide
  rcases family_descends (prefixWord ++ tailWord_507969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507989 : List Nat := [1, 3, 2, 2, 1, 3, 4, 7]
def baseStart_507989 : Nat := 118140960795 + 507989 * 2 ^ 59
def prefixEnd_507989 : Nat := 4983230072969 + 3 ^ 40 * 507989 * 2
def baseEnd_507989 : Nat := 9660834229515489792641

theorem tailTrace_507989 : CollatzResearch.WordTrace tailWord_507989 prefixEnd_507989 9660834229515489792641 := by
  unfold tailWord_507989
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527880956650085459183021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12351920637766723639455347 18527880956650085459183021)
  ·
    refine ⟨6947955358743782047193633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18527880956650085459183021 6947955358743782047193633)
    ·
      refine ⟨5210966519057836535395225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6947955358743782047193633 5210966519057836535395225)
      ·
        refine ⟨3908224889293377401546419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210966519057836535395225 3908224889293377401546419)
        ·
          refine ⟨5862337333940066102319629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908224889293377401546419 5862337333940066102319629)
          ·
            refine ⟨2198376500227524788369861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5862337333940066102319629 2198376500227524788369861)
            ·
              refine ⟨412195593792660897819349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2198376500227524788369861 412195593792660897819349)
              ·
                refine ⟨9660834229515489792641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 412195593792660897819349 9660834229515489792641)
                ·
                  rfl

theorem cell23_507989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 7].length) (baseStart_507989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_507989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_507989 prefixEnd_507989 := by exact prefixLift 507989
  have htrace : WordTrace (prefixWord ++ tailWord_507989) baseStart_507989 baseEnd_507989 := by
    simpa [prefixWord, tailWord_507989, baseEnd_507989] using wordTrace_append hprefix tailTrace_507989
  have hstable : (prefixWord ++ tailWord_507989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507989).length < 2 ^ (prefixWord ++ tailWord_507989).sum := by decide
  have hdescent : baseEnd_507989 < baseStart_507989 := by decide
  rcases family_descends (prefixWord ++ tailWord_507989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508000 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 1, 2, 2]
def baseStart_508000 : Nat := 118140960795 + 508000 * 2 ^ 59
def prefixEnd_508000 : Nat := 4983230072969 + 3 ^ 40 * 508000 * 2
def baseEnd_508000 : Nat := 260848172484117681363757

theorem tailTrace_508000 : CollatzResearch.WordTrace tailWord_508000 prefixEnd_508000 260848172484117681363757 := by
  unfold tailWord_508000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264141079805117168916727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12352188106406822891888969 9264141079805117168916727)
  ·
    refine ⟨13896211619707675753375091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9264141079805117168916727 13896211619707675753375091)
    ·
      refine ⟨20844317429561513630062637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13896211619707675753375091 20844317429561513630062637)
      ·
        refine ⟨7816619036085567611273489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20844317429561513630062637 7816619036085567611273489)
        ·
          refine ⟨5862464277064175708455117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7816619036085567611273489 5862464277064175708455117)
          ·
            refine ⟨2198424103899065890670669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5862464277064175708455117 2198424103899065890670669)
            ·
              refine ⟨824409038962149709001501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2198424103899065890670669 824409038962149709001501)
              ·
                refine ⟨309153389610806140875563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824409038962149709001501 309153389610806140875563)
                ·
                  refine ⟨463730084416209211313345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309153389610806140875563 463730084416209211313345)
                  ·
                    refine ⟨347797563312156908485009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 463730084416209211313345 347797563312156908485009)
                    ·
                      refine ⟨260848172484117681363757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347797563312156908485009 260848172484117681363757)
                      ·
                        rfl

theorem cell23_508000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_508000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508000 prefixEnd_508000 := by exact prefixLift 508000
  have htrace : WordTrace (prefixWord ++ tailWord_508000) baseStart_508000 baseEnd_508000 := by
    simpa [prefixWord, tailWord_508000, baseEnd_508000] using wordTrace_append hprefix tailTrace_508000
  have hstable : (prefixWord ++ tailWord_508000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508000).length < 2 ^ (prefixWord ++ tailWord_508000).sum := by decide
  have hdescent : baseEnd_508000 < baseStart_508000 := by decide
  rcases family_descends (prefixWord ++ tailWord_508000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508016 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3]
def baseStart_508016 : Nat := 118140960795 + 508016 * 2 ^ 59
def prefixEnd_508016 : Nat := 4983230072969 + 3 ^ 40 * 508016 * 2
def baseEnd_508016 : Nat := 260856388174589618763683

theorem tailTrace_508016 : CollatzResearch.WordTrace tailWord_508016 prefixEnd_508016 260856388174589618763683 := by
  unfold tailWord_508016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264432863776134535207951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12352577151701512713610601 9264432863776134535207951)
  ·
    refine ⟨13896649295664201802811927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9264432863776134535207951 13896649295664201802811927)
    ·
      refine ⟨20844973943496302704217891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13896649295664201802811927 20844973943496302704217891)
      ·
        refine ⟨31267460915244454056326837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20844973943496302704217891 31267460915244454056326837)
        ·
          refine ⟨2931324460804167567780641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31267460915244454056326837 2931324460804167567780641)
          ·
            refine ⟨2198493345603125675835481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2931324460804167567780641 2198493345603125675835481)
            ·
              refine ⟨1648870009202344256876611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198493345603125675835481 1648870009202344256876611)
              ·
                refine ⟨2473305013803516385314917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648870009202344256876611 2473305013803516385314917)
                ·
                  refine ⟨463744690088159322246547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473305013803516385314917 463744690088159322246547)
                  ·
                    refine ⟨695617035132238983369821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 463744690088159322246547 695617035132238983369821)
                    ·
                      refine ⟨260856388174589618763683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695617035132238983369821 260856388174589618763683)
                      ·
                        rfl

theorem cell23_508016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_508016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508016 prefixEnd_508016 := by exact prefixLift 508016
  have htrace : WordTrace (prefixWord ++ tailWord_508016) baseStart_508016 baseEnd_508016 := by
    simpa [prefixWord, tailWord_508016, baseEnd_508016] using wordTrace_append hprefix tailTrace_508016
  have hstable : (prefixWord ++ tailWord_508016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508016).length < 2 ^ (prefixWord ++ tailWord_508016).sum := by decide
  have hdescent : baseEnd_508016 < baseStart_508016 := by decide
  rcases family_descends (prefixWord ++ tailWord_508016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508032 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_508032 : Nat := 118140960795 + 508032 * 2 ^ 59
def prefixEnd_508032 : Nat := 4983230072969 + 3 ^ 40 * 508032 * 2
def baseEnd_508032 : Nat := 86954867955020518721203

theorem tailTrace_508032 : CollatzResearch.WordTrace tailWord_508032 prefixEnd_508032 86954867955020518721203 := by
  unfold tailWord_508032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264724647747151901499175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12352966196996202535332233 9264724647747151901499175)
  ·
    refine ⟨13897086971620727852248763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9264724647747151901499175 13897086971620727852248763)
    ·
      refine ⟨20845630457431091778373145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13897086971620727852248763 20845630457431091778373145)
      ·
        refine ⟨15634222843073318833779859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20845630457431091778373145 15634222843073318833779859)
        ·
          refine ⟨23451334264609978250669789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15634222843073318833779859 23451334264609978250669789)
          ·
            refine ⟨8794250349228741844001171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23451334264609978250669789 8794250349228741844001171)
            ·
              refine ⟨13191375523843112766001757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794250349228741844001171 13191375523843112766001757)
              ·
                refine ⟨4946765821441167287250659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13191375523843112766001757 4946765821441167287250659)
                ·
                  refine ⟨7420148732161750930875989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946765821441167287250659 7420148732161750930875989)
                  ·
                    refine ⟨86954867955020518721203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7420148732161750930875989 86954867955020518721203)
                    ·
                      rfl

theorem cell23_508032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_508032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508032 prefixEnd_508032 := by exact prefixLift 508032
  have htrace : WordTrace (prefixWord ++ tailWord_508032) baseStart_508032 baseEnd_508032 := by
    simpa [prefixWord, tailWord_508032, baseEnd_508032] using wordTrace_append hprefix tailTrace_508032
  have hstable : (prefixWord ++ tailWord_508032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508032).length < 2 ^ (prefixWord ++ tailWord_508032).sum := by decide
  have hdescent : baseEnd_508032 < baseStart_508032 := by decide
  rcases family_descends (prefixWord ++ tailWord_508032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508054 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_508054 : Nat := 118140960795 + 508054 * 2 ^ 59
def prefixEnd_508054 : Nat := 4983230072969 + 3 ^ 40 * 508054 * 2
def baseEnd_508054 : Nat := 260875900439460470088509

theorem tailTrace_508054 : CollatzResearch.WordTrace tailWord_508054 prefixEnd_508054 260875900439460470088509 := by
  unfold tailWord_508054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158140731338412597518701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12353501134276401040199477 1158140731338412597518701)
  ·
    refine ⟨434302774251904724069513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1158140731338412597518701 434302774251904724069513)
    ·
      refine ⟨325727080688928543052135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434302774251904724069513 325727080688928543052135)
      ·
        refine ⟨488590621033392814578203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325727080688928543052135 488590621033392814578203)
        ·
          refine ⟨732885931550089221867305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488590621033392814578203 732885931550089221867305)
          ·
            refine ⟨549664448662566916400479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732885931550089221867305 549664448662566916400479)
            ·
              refine ⟨824496672993850374600719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549664448662566916400479 824496672993850374600719)
              ·
                refine ⟨1236745009490775561901079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824496672993850374600719 1236745009490775561901079)
                ·
                  refine ⟨1855117514236163342851619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236745009490775561901079 1855117514236163342851619)
                  ·
                    refine ⟨2782676271354245014277429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1855117514236163342851619 2782676271354245014277429)
                    ·
                      refine ⟨260875900439460470088509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2782676271354245014277429 260875900439460470088509)
                      ·
                        rfl

theorem cell23_508054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_508054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508054 prefixEnd_508054 := by exact prefixLift 508054
  have htrace : WordTrace (prefixWord ++ tailWord_508054) baseStart_508054 baseEnd_508054 := by
    simpa [prefixWord, tailWord_508054, baseEnd_508054] using wordTrace_append hprefix tailTrace_508054
  have hstable : (prefixWord ++ tailWord_508054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508054).length < 2 ^ (prefixWord ++ tailWord_508054).sum := by decide
  have hdescent : baseEnd_508054 < baseStart_508054 := by decide
  rcases family_descends (prefixWord ++ tailWord_508054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508060 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_508060 : Nat := 118140960795 + 508060 * 2 ^ 59
def prefixEnd_508060 : Nat := 4983230072969 + 3 ^ 40 * 508060 * 2
def baseEnd_508060 : Nat := 260878981323387446613481

theorem tailTrace_508060 : CollatzResearch.WordTrace tailWord_508060 prefixEnd_508060 260878981323387446613481 := by
  unfold tailWord_508060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265235269696432292508817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12353647026261909723345089 9265235269696432292508817)
  ·
    refine ⟨6948926452272324219381613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9265235269696432292508817 6948926452272324219381613)
    ·
      refine ⟨2605847419602121582268105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6948926452272324219381613 2605847419602121582268105)
      ·
        refine ⟨1954385564701591186701079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2605847419602121582268105 1954385564701591186701079)
        ·
          refine ⟨2931578347052386780051619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954385564701591186701079 2931578347052386780051619)
          ·
            refine ⟨4397367520578580170077429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931578347052386780051619 4397367520578580170077429)
            ·
              refine ⟨412253205054241890944759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4397367520578580170077429 412253205054241890944759)
              ·
                refine ⟨618379807581362836417139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412253205054241890944759 618379807581362836417139)
                ·
                  refine ⟨927569711372044254625709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618379807581362836417139 927569711372044254625709)
                  ·
                    refine ⟨347838641764516595484641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927569711372044254625709 347838641764516595484641)
                    ·
                      refine ⟨260878981323387446613481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 347838641764516595484641 260878981323387446613481)
                      ·
                        rfl

theorem cell23_508060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_508060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508060 prefixEnd_508060 := by exact prefixLift 508060
  have htrace : WordTrace (prefixWord ++ tailWord_508060) baseStart_508060 baseEnd_508060 := by
    simpa [prefixWord, tailWord_508060, baseEnd_508060] using wordTrace_append hprefix tailTrace_508060
  have hstable : (prefixWord ++ tailWord_508060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508060).length < 2 ^ (prefixWord ++ tailWord_508060).sum := by decide
  have hdescent : baseEnd_508060 < baseStart_508060 := by decide
  rcases family_descends (prefixWord ++ tailWord_508060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508069 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_508069 : Nat := 118140960795 + 508069 * 2 ^ 59
def prefixEnd_508069 : Nat := 4983230072969 + 3 ^ 40 * 508069 * 2
def baseEnd_508069 : Nat := 260883602649277911400939

theorem tailTrace_508069 : CollatzResearch.WordTrace tailWord_508069 prefixEnd_508069 260883602649277911400939 := by
  unfold tailWord_508069
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530798796360259122095261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12353865864240172748063507 18530798796360259122095261)
  ·
    refine ⟨6949049548635097170785723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18530798796360259122095261 6949049548635097170785723)
    ·
      refine ⟨10423574322952645756178585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6949049548635097170785723 10423574322952645756178585)
      ·
        refine ⟨7817680742214484317133939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10423574322952645756178585 7817680742214484317133939)
        ·
          refine ⟨11726521113321726475700909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817680742214484317133939 11726521113321726475700909)
          ·
            refine ⟨4397445417495647428387841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11726521113321726475700909 4397445417495647428387841)
            ·
              refine ⟨3298084063121735571290881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397445417495647428387841 3298084063121735571290881)
              ·
                refine ⟨2473563047341301678468161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298084063121735571290881 2473563047341301678468161)
                ·
                  refine ⟨1855172285505976258851121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473563047341301678468161 1855172285505976258851121)
                  ·
                    refine ⟨1391379214129482194138341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1855172285505976258851121 1391379214129482194138341)
                    ·
                      refine ⟨260883602649277911400939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1391379214129482194138341 260883602649277911400939)
                      ·
                        rfl

theorem cell23_508069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_508069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508069 prefixEnd_508069 := by exact prefixLift 508069
  have htrace : WordTrace (prefixWord ++ tailWord_508069) baseStart_508069 baseEnd_508069 := by
    simpa [prefixWord, tailWord_508069, baseEnd_508069] using wordTrace_append hprefix tailTrace_508069
  have hstable : (prefixWord ++ tailWord_508069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508069).length < 2 ^ (prefixWord ++ tailWord_508069).sum := by decide
  have hdescent : baseEnd_508069 < baseStart_508069 := by decide
  rcases family_descends (prefixWord ++ tailWord_508069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508146 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_508146 : Nat := 118140960795 + 508146 * 2 ^ 59
def prefixEnd_508146 : Nat := 4983230072969 + 3 ^ 40 * 508146 * 2
def baseEnd_508146 : Nat := 260923140659674110138085

theorem tailTrace_508146 : CollatzResearch.WordTrace tailWord_508146 prefixEnd_508146 260923140659674110138085 := by
  unfold tailWord_508146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633401804270325318162073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12355738144720867515098861 4633401804270325318162073)
  ·
    refine ⟨3475051353202743988621555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4633401804270325318162073 3475051353202743988621555)
    ·
      refine ⟨5212577029804115982932333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475051353202743988621555 5212577029804115982932333)
      ·
        refine ⟨1954716386176543493599625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5212577029804115982932333 1954716386176543493599625)
        ·
          refine ⟨1466037289632407620199719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954716386176543493599625 1466037289632407620199719)
          ·
            refine ⟨2199055934448611430299579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466037289632407620199719 2199055934448611430299579)
            ·
              refine ⟨3298583901672917145449369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199055934448611430299579 3298583901672917145449369)
              ·
                refine ⟨2473937926254687859087027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298583901672917145449369 2473937926254687859087027)
                ·
                  refine ⟨3710906889382031788630541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473937926254687859087027 3710906889382031788630541)
                  ·
                    refine ⟨1391590083518261920736453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710906889382031788630541 1391590083518261920736453)
                    ·
                      refine ⟨260923140659674110138085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1391590083518261920736453 260923140659674110138085)
                      ·
                        rfl

theorem cell23_508146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_508146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508146 prefixEnd_508146 := by exact prefixLift 508146
  have htrace : WordTrace (prefixWord ++ tailWord_508146) baseStart_508146 baseEnd_508146 := by
    simpa [prefixWord, tailWord_508146, baseEnd_508146] using wordTrace_append hprefix tailTrace_508146
  have hstable : (prefixWord ++ tailWord_508146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508146).length < 2 ^ (prefixWord ++ tailWord_508146).sum := by decide
  have hdescent : baseEnd_508146 < baseStart_508146 := by decide
  rcases family_descends (prefixWord ++ tailWord_508146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508159 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_508159 : Nat := 118140960795 + 508159 * 2 ^ 59
def prefixEnd_508159 : Nat := 4983230072969 + 3 ^ 40 * 508159 * 2
def baseEnd_508159 : Nat := 260929815908182559275525

theorem tailTrace_508159 : CollatzResearch.WordTrace tailWord_508159 prefixEnd_508159 260929815908182559275525 := by
  unfold tailWord_508159
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534081366034204492871531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356054244022802995247687 18534081366034204492871531)
  ·
    refine ⟨27801122049051306739307297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534081366034204492871531 27801122049051306739307297)
    ·
      refine ⟨20850841536788480054480473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27801122049051306739307297 20850841536788480054480473)
      ·
        refine ⟨15638131152591360040860355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20850841536788480054480473 15638131152591360040860355)
        ·
          refine ⟨23457196728887040061290533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638131152591360040860355 23457196728887040061290533)
          ·
            refine ⟨4398224386666320011491975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23457196728887040061290533 4398224386666320011491975)
            ·
              refine ⟨6597336579999480017237963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398224386666320011491975 6597336579999480017237963)
              ·
                refine ⟨9896004869999220025856945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597336579999480017237963 9896004869999220025856945)
                ·
                  refine ⟨7422003652499415019392709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896004869999220025856945 7422003652499415019392709)
                  ·
                    refine ⟨1391625684843640316136133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422003652499415019392709 1391625684843640316136133)
                    ·
                      refine ⟨260929815908182559275525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1391625684843640316136133 260929815908182559275525)
                      ·
                        rfl

theorem cell23_508159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_508159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508159 prefixEnd_508159 := by exact prefixLift 508159
  have htrace : WordTrace (prefixWord ++ tailWord_508159) baseStart_508159 baseEnd_508159 := by
    simpa [prefixWord, tailWord_508159, baseEnd_508159] using wordTrace_append hprefix tailTrace_508159
  have hstable : (prefixWord ++ tailWord_508159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508159).length < 2 ^ (prefixWord ++ tailWord_508159).sum := by decide
  have hdescent : baseEnd_508159 < baseStart_508159 := by decide
  rcases family_descends (prefixWord ++ tailWord_508159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508169 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 8]
def baseStart_508169 : Nat := 118140960795 + 508169 * 2 ^ 59
def prefixEnd_508169 : Nat := 4983230072969 + 3 ^ 40 * 508169 * 2
def baseEnd_508169 : Nat := 28992772301636391127831

theorem tailTrace_508169 : CollatzResearch.WordTrace tailWord_508169 prefixEnd_508169 28992772301636391127831 := by
  unfold tailWord_508169
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534446095997976200735561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356297397331984133823707 18534446095997976200735561)
  ·
    refine ⟨13900834571998482150551671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18534446095997976200735561 13900834571998482150551671)
    ·
      refine ⟨20851251857997723225827507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13900834571998482150551671 20851251857997723225827507)
      ·
        refine ⟨31276877786996584838741261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20851251857997723225827507 31276877786996584838741261)
        ·
          refine ⟨11728829170123719314527973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31276877786996584838741261 11728829170123719314527973)
          ·
            refine ⟨2199155469398197371473995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11728829170123719314527973 2199155469398197371473995)
            ·
              refine ⟨3298733204097296057210993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199155469398197371473995 3298733204097296057210993)
              ·
                refine ⟨2474049903072972042908245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298733204097296057210993 2474049903072972042908245)
                ·
                  refine ⟨28992772301636391127831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2474049903072972042908245 28992772301636391127831)
                  ·
                    rfl

theorem cell23_508169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 8].length) (baseStart_508169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508169 prefixEnd_508169 := by exact prefixLift 508169
  have htrace : WordTrace (prefixWord ++ tailWord_508169) baseStart_508169 baseEnd_508169 := by
    simpa [prefixWord, tailWord_508169, baseEnd_508169] using wordTrace_append hprefix tailTrace_508169
  have hstable : (prefixWord ++ tailWord_508169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508169).length < 2 ^ (prefixWord ++ tailWord_508169).sum := by decide
  have hdescent : baseEnd_508169 < baseStart_508169 := by decide
  rcases family_descends (prefixWord ++ tailWord_508169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508183 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_508183 : Nat := 118140960795 + 508183 * 2 ^ 59
def prefixEnd_508183 : Nat := 4983230072969 + 3 ^ 40 * 508183 * 2
def baseEnd_508183 : Nat := 260942139443890465375415

theorem tailTrace_508183 : CollatzResearch.WordTrace tailWord_508183 prefixEnd_508183 260942139443890465375415 := by
  unfold tailWord_508183
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534956717947256591745203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356637811964837727830135 18534956717947256591745203)
  ·
    refine ⟨27802435076920884887617805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534956717947256591745203 27802435076920884887617805)
    ·
      refine ⟨10425913153845331832856677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27802435076920884887617805 10425913153845331832856677)
      ·
        refine ⟨1954858716345999718660627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10425913153845331832856677 1954858716345999718660627)
        ·
          refine ⟨2932288074518999577990941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954858716345999718660627 2932288074518999577990941)
          ·
            refine ⟨1099608027944624841746603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2932288074518999577990941 1099608027944624841746603)
            ·
              refine ⟨1649412041916937262619905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099608027944624841746603 1649412041916937262619905)
              ·
                refine ⟨1237059031437702946964929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649412041916937262619905 1237059031437702946964929)
                ·
                  refine ⟨927794273578277210223697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237059031437702946964929 927794273578277210223697)
                  ·
                    refine ⟨695845705183707907667773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927794273578277210223697 695845705183707907667773)
                    ·
                      refine ⟨260942139443890465375415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695845705183707907667773 260942139443890465375415)
                      ·
                        rfl

theorem cell23_508183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_508183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508183 prefixEnd_508183 := by exact prefixLift 508183
  have htrace : WordTrace (prefixWord ++ tailWord_508183) baseStart_508183 baseEnd_508183 := by
    simpa [prefixWord, tailWord_508183, baseEnd_508183] using wordTrace_append hprefix tailTrace_508183
  have hstable : (prefixWord ++ tailWord_508183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508183).length < 2 ^ (prefixWord ++ tailWord_508183).sum := by decide
  have hdescent : baseEnd_508183 < baseStart_508183 := by decide
  rcases family_descends (prefixWord ++ tailWord_508183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508213 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_508213 : Nat := 118140960795 + 508213 * 2 ^ 59
def prefixEnd_508213 : Nat := 4983230072969 + 3 ^ 40 * 508213 * 2
def baseEnd_508213 : Nat := 260957543863525348000277

theorem tailTrace_508213 : CollatzResearch.WordTrace tailWord_508213 prefixEnd_508213 260957543863525348000277 := by
  unfold tailWord_508213
  simp only [CollatzResearch.WordTrace]
  refine ⟨18536050907838571715337293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12357367271892381143558195 18536050907838571715337293)
  ·
    refine ⟨6951019090439464393251485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18536050907838571715337293 6951019090439464393251485)
    ·
      refine ⟨2606632158914799147469307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6951019090439464393251485 2606632158914799147469307)
      ·
        refine ⟨3909948238372198721203961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606632158914799147469307 3909948238372198721203961)
        ·
          refine ⟨2932461178779149040902971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3909948238372198721203961 2932461178779149040902971)
          ·
            refine ⟨4398691768168723561354457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932461178779149040902971 4398691768168723561354457)
            ·
              refine ⟨3299018826126542671015843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398691768168723561354457 3299018826126542671015843)
              ·
                refine ⟨4948528239189814006523765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299018826126542671015843 4948528239189814006523765)
                ·
                  refine ⟨463924522424045063111603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4948528239189814006523765 463924522424045063111603)
                  ·
                    refine ⟨695886783636067594667405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 463924522424045063111603 695886783636067594667405)
                    ·
                      refine ⟨260957543863525348000277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695886783636067594667405 260957543863525348000277)
                      ·
                        rfl

theorem cell23_508213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_508213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508213 prefixEnd_508213 := by exact prefixLift 508213
  have htrace : WordTrace (prefixWord ++ tailWord_508213) baseStart_508213 baseEnd_508213 := by
    simpa [prefixWord, tailWord_508213, baseEnd_508213] using wordTrace_append hprefix tailTrace_508213
  have hstable : (prefixWord ++ tailWord_508213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508213).length < 2 ^ (prefixWord ++ tailWord_508213).sum := by decide
  have hdescent : baseEnd_508213 < baseStart_508213 := by decide
  rcases family_descends (prefixWord ++ tailWord_508213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508263 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 1, 6]
def baseStart_508263 : Nat := 118140960795 + 508263 * 2 ^ 59
def prefixEnd_508263 : Nat := 4983230072969 + 3 ^ 40 * 508263 * 2
def baseEnd_508263 : Nat := 86994405965416717458349

theorem tailTrace_508263 : CollatzResearch.WordTrace tailWord_508263 prefixEnd_508263 86994405965416717458349 := by
  unfold tailWord_508263
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537874557657430254657443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12358583038438286836438295 18537874557657430254657443)
  ·
    refine ⟨27806811836486145381986165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18537874557657430254657443 27806811836486145381986165)
    ·
      refine ⟨2606888609670576129561203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27806811836486145381986165 2606888609670576129561203)
      ·
        refine ⟨3910332914505864194341805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606888609670576129561203 3910332914505864194341805)
        ·
          refine ⟨1466374842939699072878177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3910332914505864194341805 1466374842939699072878177)
          ·
            refine ⟨1099781132204774304658633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466374842939699072878177 1099781132204774304658633)
            ·
              refine ⟨824835849153580728493975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099781132204774304658633 824835849153580728493975)
              ·
                refine ⟨1237253773730371092740963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824835849153580728493975 1237253773730371092740963)
                ·
                  refine ⟨1855880660595556639111445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237253773730371092740963 1855880660595556639111445)
                  ·
                    refine ⟨86994405965416717458349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1855880660595556639111445 86994405965416717458349)
                    ·
                      rfl

theorem cell23_508263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_508263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508263 prefixEnd_508263 := by exact prefixLift 508263
  have htrace : WordTrace (prefixWord ++ tailWord_508263) baseStart_508263 baseEnd_508263 := by
    simpa [prefixWord, tailWord_508263, baseEnd_508263] using wordTrace_append hprefix tailTrace_508263
  have hstable : (prefixWord ++ tailWord_508263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508263).length < 2 ^ (prefixWord ++ tailWord_508263).sum := by decide
  have hdescent : baseEnd_508263 < baseStart_508263 := by decide
  rcases family_descends (prefixWord ++ tailWord_508263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508273 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_508273 : Nat := 118140960795 + 508273 * 2 ^ 59
def prefixEnd_508273 : Nat := 4983230072969 + 3 ^ 40 * 508273 * 2
def baseEnd_508273 : Nat := 260988352702795113250001

theorem tailTrace_508273 : CollatzResearch.WordTrace tailWord_508273 prefixEnd_508273 260988352702795113250001 := by
  unfold tailWord_508273
  simp only [CollatzResearch.WordTrace]
  refine ⟨18538239287621201962521473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12358826191747467975014315 18538239287621201962521473)
  ·
    refine ⟨13903679465715901471891105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18538239287621201962521473 13903679465715901471891105)
    ·
      refine ⟨10427759599286926103918329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13903679465715901471891105 10427759599286926103918329)
      ·
        refine ⟨7820819699465194577938747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10427759599286926103918329 7820819699465194577938747)
        ·
          refine ⟨11731229549197791866908121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820819699465194577938747 11731229549197791866908121)
          ·
            refine ⟨8798422161898343900181091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731229549197791866908121 8798422161898343900181091)
            ·
              refine ⟨13197633242847515850271637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798422161898343900181091 13197633242847515850271637)
              ·
                refine ⟨618639058258477305481483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13197633242847515850271637 618639058258477305481483)
                ·
                  refine ⟨927958587387715958222225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618639058258477305481483 927958587387715958222225)
                  ·
                    refine ⟨695968940540786968666669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 927958587387715958222225 695968940540786968666669)
                    ·
                      refine ⟨260988352702795113250001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 695968940540786968666669 260988352702795113250001)
                      ·
                        rfl

theorem cell23_508273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_508273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508273 prefixEnd_508273 := by exact prefixLift 508273
  have htrace : WordTrace (prefixWord ++ tailWord_508273) baseStart_508273 baseEnd_508273 := by
    simpa [prefixWord, tailWord_508273, baseEnd_508273] using wordTrace_append hprefix tailTrace_508273
  have hstable : (prefixWord ++ tailWord_508273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508273).length < 2 ^ (prefixWord ++ tailWord_508273).sum := by decide
  have hdescent : baseEnd_508273 < baseStart_508273 := by decide
  rcases family_descends (prefixWord ++ tailWord_508273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508317 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_508317 : Nat := 118140960795 + 508317 * 2 ^ 59
def prefixEnd_508317 : Nat := 4983230072969 + 3 ^ 40 * 508317 * 2
def baseEnd_508317 : Nat := 261010945851592941099799

theorem tailTrace_508317 : CollatzResearch.WordTrace tailWord_508317 prefixEnd_508317 261010945851592941099799 := by
  unfold tailWord_508317
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539844099461797477123205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12359896066307864984748803 18539844099461797477123205)
  ·
    refine ⟨3476220768649087026960601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18539844099461797477123205 3476220768649087026960601)
    ·
      refine ⟨2607165576486815270220451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3476220768649087026960601 2607165576486815270220451)
      ·
        refine ⟨3910748364730222905330677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607165576486815270220451 3910748364730222905330677)
        ·
          refine ⟨366632659193458397374751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3910748364730222905330677 366632659193458397374751)
          ·
            refine ⟨549948988790187596062127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366632659193458397374751 549948988790187596062127)
            ·
              refine ⟨824923483185281394093191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549948988790187596062127 824923483185281394093191)
              ·
                refine ⟨1237385224777922091139787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824923483185281394093191 1237385224777922091139787)
                ·
                  refine ⟨1856077837166883136709681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237385224777922091139787 1856077837166883136709681)
                  ·
                    refine ⟨1392058377875162352532261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1856077837166883136709681 1392058377875162352532261)
                    ·
                      refine ⟨261010945851592941099799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1392058377875162352532261 261010945851592941099799)
                      ·
                        rfl

theorem cell23_508317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_508317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508317 prefixEnd_508317 := by exact prefixLift 508317
  have htrace : WordTrace (prefixWord ++ tailWord_508317) baseStart_508317 baseEnd_508317 := by
    simpa [prefixWord, tailWord_508317, baseEnd_508317] using wordTrace_append hprefix tailTrace_508317
  have hstable : (prefixWord ++ tailWord_508317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508317).length < 2 ^ (prefixWord ++ tailWord_508317).sum := by decide
  have hdescent : baseEnd_508317 < baseStart_508317 := by decide
  rcases family_descends (prefixWord ++ tailWord_508317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508320 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_508320 : Nat := 118140960795 + 508320 * 2 ^ 59
def prefixEnd_508320 : Nat := 4983230072969 + 3 ^ 40 * 508320 * 2
def baseEnd_508320 : Nat := 261012486293556429362285

theorem tailTrace_508320 : CollatzResearch.WordTrace tailWord_508320 prefixEnd_508320 261012486293556429362285 := by
  unfold tailWord_508320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269976759225464494741207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12359969012300619326321609 9269976759225464494741207)
  ·
    refine ⟨13904965138838196742111811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9269976759225464494741207 13904965138838196742111811)
    ·
      refine ⟨20857447708257295113167717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13904965138838196742111811 20857447708257295113167717)
      ·
        refine ⟨3910771445298242833718947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20857447708257295113167717 3910771445298242833718947)
        ·
          refine ⟨5866157167947364250578421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910771445298242833718947 5866157167947364250578421)
          ·
            refine ⟨549952234495065398491727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5866157167947364250578421 549952234495065398491727)
            ·
              refine ⟨824928351742598097737591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549952234495065398491727 824928351742598097737591)
              ·
                refine ⟨1237392527613897146606387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824928351742598097737591 1237392527613897146606387)
                ·
                  refine ⟨1856088791420845719909581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237392527613897146606387 1856088791420845719909581)
                  ·
                    refine ⟨696033296782817144966093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1856088791420845719909581 696033296782817144966093)
                    ·
                      refine ⟨261012486293556429362285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696033296782817144966093 261012486293556429362285)
                      ·
                        rfl

theorem cell23_508320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_508320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508320 prefixEnd_508320 := by exact prefixLift 508320
  have htrace : WordTrace (prefixWord ++ tailWord_508320) baseStart_508320 baseEnd_508320 := by
    simpa [prefixWord, tailWord_508320, baseEnd_508320] using wordTrace_append hprefix tailTrace_508320
  have hstable : (prefixWord ++ tailWord_508320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508320).length < 2 ^ (prefixWord ++ tailWord_508320).sum := by decide
  have hdescent : baseEnd_508320 < baseStart_508320 := by decide
  rcases family_descends (prefixWord ++ tailWord_508320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508377 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 2, 2, 2]
def baseStart_508377 : Nat := 118140960795 + 508377 * 2 ^ 59
def prefixEnd_508377 : Nat := 4983230072969 + 3 ^ 40 * 508377 * 2
def baseEnd_508377 : Nat := 261041754690862706349523

theorem tailTrace_508377 : CollatzResearch.WordTrace tailWord_508377 prefixEnd_508377 261041754690862706349523 := by
  unfold tailWord_508377
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542032479244427724307385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12361354986162951816204923 18542032479244427724307385)
  ·
    refine ⟨13906524359433320793230539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18542032479244427724307385 13906524359433320793230539)
    ·
      refine ⟨20859786539149981189845809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13906524359433320793230539 20859786539149981189845809)
      ·
        refine ⟨15644839904362485892384357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20859786539149981189845809 15644839904362485892384357)
        ·
          refine ⟨2933407482067966104822067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15644839904362485892384357 2933407482067966104822067)
          ·
            refine ⟨4400111223101949157233101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933407482067966104822067 4400111223101949157233101)
            ·
              refine ⟨1650041708663230933962413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4400111223101949157233101 1650041708663230933962413)
              ·
                refine ⟨618765640748711600235905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650041708663230933962413 618765640748711600235905)
                ·
                  refine ⟨464074230561533700176929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618765640748711600235905 464074230561533700176929)
                  ·
                    refine ⟨348055672921150275132697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464074230561533700176929 348055672921150275132697)
                    ·
                      refine ⟨261041754690862706349523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348055672921150275132697 261041754690862706349523)
                      ·
                        rfl

theorem cell23_508377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_508377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508377 prefixEnd_508377 := by exact prefixLift 508377
  have htrace : WordTrace (prefixWord ++ tailWord_508377) baseStart_508377 baseEnd_508377 := by
    simpa [prefixWord, tailWord_508377, baseEnd_508377] using wordTrace_append hprefix tailTrace_508377
  have hstable : (prefixWord ++ tailWord_508377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508377).length < 2 ^ (prefixWord ++ tailWord_508377).sum := by decide
  have hdescent : baseEnd_508377 < baseStart_508377 := by decide
  rcases family_descends (prefixWord ++ tailWord_508377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508413 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_508413 : Nat := 118140960795 + 508413 * 2 ^ 59
def prefixEnd_508413 : Nat := 4983230072969 + 3 ^ 40 * 508413 * 2
def baseEnd_508413 : Nat := 87020079998141521833119

theorem tailTrace_508413 : CollatzResearch.WordTrace tailWord_508413 prefixEnd_508413 87020079998141521833119 := by
  unfold tailWord_508413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543345507114005872617893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12362230338076003915078595 18543345507114005872617893)
  ·
    refine ⟨3476877282583876101115855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18543345507114005872617893 3476877282583876101115855)
    ·
      refine ⟨5215315923875814151673783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476877282583876101115855 5215315923875814151673783)
      ·
        refine ⟨7822973885813721227510675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215315923875814151673783 7822973885813721227510675)
        ·
          refine ⟨11734460828720581841266013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822973885813721227510675 11734460828720581841266013)
          ·
            refine ⟨4400422810770218190474755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11734460828720581841266013 4400422810770218190474755)
            ·
              refine ⟨6600634216155327285712133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400422810770218190474755 6600634216155327285712133)
              ·
                refine ⟨1237618915529123866071025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6600634216155327285712133 1237618915529123866071025)
                ·
                  refine ⟨928214186646842899553269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237618915529123866071025 928214186646842899553269)
                  ·
                    refine ⟨87020079998141521833119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 928214186646842899553269 87020079998141521833119)
                    ·
                      rfl

theorem cell23_508413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_508413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508413 prefixEnd_508413 := by exact prefixLift 508413
  have htrace : WordTrace (prefixWord ++ tailWord_508413) baseStart_508413 baseEnd_508413 := by
    simpa [prefixWord, tailWord_508413, baseEnd_508413] using wordTrace_append hprefix tailTrace_508413
  have hstable : (prefixWord ++ tailWord_508413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508413).length < 2 ^ (prefixWord ++ tailWord_508413).sum := by decide
  have hdescent : baseEnd_508413 < baseStart_508413 := by decide
  rcases family_descends (prefixWord ++ tailWord_508413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508417 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 5]
def baseStart_508417 : Nat := 118140960795 + 508417 * 2 ^ 59
def prefixEnd_508417 : Nat := 4983230072969 + 3 ^ 40 * 508417 * 2
def baseEnd_508417 : Nat := 29006921546338061094371

theorem tailTrace_508417 : CollatzResearch.WordTrace tailWord_508417 prefixEnd_508417 29006921546338061094371 := by
  unfold tailWord_508417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543491399099514555763505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12362327599399676370509003 18543491399099514555763505)
  ·
    refine ⟨13907618549324635916822629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18543491399099514555763505 13907618549324635916822629)
    ·
      refine ⟨2607678477998369234404243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13907618549324635916822629 2607678477998369234404243)
      ·
        refine ⟨3911517716997553851606365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607678477998369234404243 3911517716997553851606365)
        ·
          refine ⟨1466819143874082694352387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3911517716997553851606365 1466819143874082694352387)
          ·
            refine ⟨2200228715811124041528581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466819143874082694352387 2200228715811124041528581)
            ·
              refine ⟨412542884214585757786609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2200228715811124041528581 412542884214585757786609)
              ·
                refine ⟨309407163160939318339957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412542884214585757786609 309407163160939318339957)
                ·
                  refine ⟨29006921546338061094371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309407163160939318339957 29006921546338061094371)
                  ·
                    rfl

theorem cell23_508417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 5].length) (baseStart_508417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508417 prefixEnd_508417 := by exact prefixLift 508417
  have htrace : WordTrace (prefixWord ++ tailWord_508417) baseStart_508417 baseEnd_508417 := by
    simpa [prefixWord, tailWord_508417, baseEnd_508417] using wordTrace_append hprefix tailTrace_508417
  have hstable : (prefixWord ++ tailWord_508417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508417).length < 2 ^ (prefixWord ++ tailWord_508417).sum := by decide
  have hdescent : baseEnd_508417 < baseStart_508417 := by decide
  rcases family_descends (prefixWord ++ tailWord_508417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508450 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_508450 : Nat := 118140960795 + 508450 * 2 ^ 59
def prefixEnd_508450 : Nat := 4983230072969 + 3 ^ 40 * 508450 * 2
def baseEnd_508450 : Nat := 261079238778640920736687

theorem tailTrace_508450 : CollatzResearch.WordTrace tailWord_508450 prefixEnd_508450 261079238778640920736687 := by
  unfold tailWord_508450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636173751994990297928701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12363130005319974127809869 4636173751994990297928701)
  ·
    refine ⟨1738565156998121361723263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4636173751994990297928701 1738565156998121361723263)
    ·
      refine ⟨2607847735497182042584895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1738565156998121361723263 2607847735497182042584895)
      ·
        refine ⟨3911771603245773063877343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2607847735497182042584895 3911771603245773063877343)
        ·
          refine ⟨5867657404868659595816015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911771603245773063877343 5867657404868659595816015)
          ·
            refine ⟨8801486107302989393724023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867657404868659595816015 8801486107302989393724023)
            ·
              refine ⟨13202229160954484090586035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8801486107302989393724023 13202229160954484090586035)
              ·
                refine ⟨19803343741431726135879053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13202229160954484090586035 19803343741431726135879053)
                ·
                  refine ⟨7426253903036897300954645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19803343741431726135879053 7426253903036897300954645)
                  ·
                    refine ⟨348105651704854560982249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7426253903036897300954645 348105651704854560982249)
                    ·
                      refine ⟨261079238778640920736687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348105651704854560982249 261079238778640920736687)
                      ·
                        rfl

theorem cell23_508450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_508450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508450 prefixEnd_508450 := by exact prefixLift 508450
  have htrace : WordTrace (prefixWord ++ tailWord_508450) baseStart_508450 baseEnd_508450 := by
    simpa [prefixWord, tailWord_508450, baseEnd_508450] using wordTrace_append hprefix tailTrace_508450
  have hstable : (prefixWord ++ tailWord_508450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508450).length < 2 ^ (prefixWord ++ tailWord_508450).sum := by decide
  have hdescent : baseEnd_508450 < baseStart_508450 := by decide
  rcases family_descends (prefixWord ++ tailWord_508450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508473 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 8]
def baseStart_508473 : Nat := 118140960795 + 508473 * 2 ^ 59
def prefixEnd_508473 : Nat := 4983230072969 + 3 ^ 40 * 508473 * 2
def baseEnd_508473 : Nat := 29010116537077147861009

theorem tailTrace_508473 : CollatzResearch.WordTrace tailWord_508473 prefixEnd_508473 29010116537077147861009 := by
  unfold tailWord_508473
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545533886896636119802073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12363689257931090746534715 18545533886896636119802073)
  ·
    refine ⟨13909150415172477089851555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18545533886896636119802073 13909150415172477089851555)
    ·
      refine ⟨20863725622758715634777333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13909150415172477089851555 20863725622758715634777333)
      ·
        refine ⟨1955974277133629590760375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20863725622758715634777333 1955974277133629590760375)
        ·
          refine ⟨2933961415700444386140563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955974277133629590760375 2933961415700444386140563)
          ·
            refine ⟨4400942123550666579210845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933961415700444386140563 4400942123550666579210845)
            ·
              refine ⟨1650353296331499967204067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4400942123550666579210845 1650353296331499967204067)
              ·
                refine ⟨2475529944497249950806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650353296331499967204067 2475529944497249950806101)
                ·
                  refine ⟨29010116537077147861009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2475529944497249950806101 29010116537077147861009)
                  ·
                    rfl

theorem cell23_508473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 8].length) (baseStart_508473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508473 prefixEnd_508473 := by exact prefixLift 508473
  have htrace : WordTrace (prefixWord ++ tailWord_508473) baseStart_508473 baseEnd_508473 := by
    simpa [prefixWord, tailWord_508473, baseEnd_508473] using wordTrace_append hprefix tailTrace_508473
  have hstable : (prefixWord ++ tailWord_508473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508473).length < 2 ^ (prefixWord ++ tailWord_508473).sum := by decide
  have hdescent : baseEnd_508473 < baseStart_508473 := by decide
  rcases family_descends (prefixWord ++ tailWord_508473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508477 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_508477 : Nat := 118140960795 + 508477 * 2 ^ 59
def prefixEnd_508477 : Nat := 4983230072969 + 3 ^ 40 * 508477 * 2
def baseEnd_508477 : Nat := 87031034252104105033021

theorem tailTrace_508477 : CollatzResearch.WordTrace tailWord_508477 prefixEnd_508477 87031034252104105033021 := by
  unfold tailWord_508477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18545679778882144802947685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12363786519254763201965123 18545679778882144802947685)
  ·
    refine ⟨3477314958540402150552691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18545679778882144802947685 3477314958540402150552691)
    ·
      refine ⟨5215972437810603225829037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477314958540402150552691 5215972437810603225829037)
      ·
        refine ⟨1955989664178976209685889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5215972437810603225829037 1955989664178976209685889)
        ·
          refine ⟨1466992248134232157264417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955989664178976209685889 1466992248134232157264417)
          ·
            refine ⟨1100244186100674117948313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466992248134232157264417 1100244186100674117948313)
            ·
              refine ⟨825183139575505588461235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100244186100674117948313 825183139575505588461235)
              ·
                refine ⟨1237774709363258382691853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825183139575505588461235 1237774709363258382691853)
                ·
                  refine ⟨464165516011221893509445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237774709363258382691853 464165516011221893509445)
                  ·
                    refine ⟨87031034252104105033021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 464165516011221893509445 87031034252104105033021)
                    ·
                      rfl

theorem cell23_508477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_508477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508477 prefixEnd_508477 := by exact prefixLift 508477
  have htrace : WordTrace (prefixWord ++ tailWord_508477) baseStart_508477 baseEnd_508477 := by
    simpa [prefixWord, tailWord_508477, baseEnd_508477] using wordTrace_append hprefix tailTrace_508477
  have hstable : (prefixWord ++ tailWord_508477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508477).length < 2 ^ (prefixWord ++ tailWord_508477).sum := by decide
  have hdescent : baseEnd_508477 < baseStart_508477 := by decide
  rcases family_descends (prefixWord ++ tailWord_508477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508543 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_508543 : Nat := 118140960795 + 508543 * 2 ^ 59
def prefixEnd_508543 : Nat := 4983230072969 + 3 ^ 40 * 508543 * 2
def baseEnd_508543 : Nat := 261126992479509056873759

theorem tailTrace_508543 : CollatzResearch.WordTrace tailWord_508543 prefixEnd_508543 261126992479509056873759 := by
  unfold tailWord_508543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548086996643038074850283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12365391331095358716566855 18548086996643038074850283)
  ·
    refine ⟨27822130494964557112275425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18548086996643038074850283 27822130494964557112275425)
    ·
      refine ⟨20866597871223417834206569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27822130494964557112275425 20866597871223417834206569)
      ·
        refine ⟨15649948403417563375654927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20866597871223417834206569 15649948403417563375654927)
        ·
          refine ⟨23474922605126345063482391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15649948403417563375654927 23474922605126345063482391)
          ·
            refine ⟨35212383907689517595223587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23474922605126345063482391 35212383907689517595223587)
            ·
              refine ⟨52818575861534276392835381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35212383907689517595223587 52818575861534276392835381)
              ·
                refine ⟨4951741487018838411828317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52818575861534276392835381 4951741487018838411828317)
                ·
                  refine ⟨1856903057632064404435619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4951741487018838411828317 1856903057632064404435619)
                  ·
                    refine ⟨2785354586448096606653429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1856903057632064404435619 2785354586448096606653429)
                    ·
                      refine ⟨261126992479509056873759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2785354586448096606653429 261126992479509056873759)
                      ·
                        rfl

theorem cell23_508543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_508543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508543 prefixEnd_508543 := by exact prefixLift 508543
  have htrace : WordTrace (prefixWord ++ tailWord_508543) baseStart_508543 baseEnd_508543 := by
    simpa [prefixWord, tailWord_508543, baseEnd_508543] using wordTrace_append hprefix tailTrace_508543
  have hstable : (prefixWord ++ tailWord_508543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508543).length < 2 ^ (prefixWord ++ tailWord_508543).sum := by decide
  have hdescent : baseEnd_508543 < baseStart_508543 := by decide
  rcases family_descends (prefixWord ++ tailWord_508543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508554 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_508554 : Nat := 118140960795 + 508554 * 2 ^ 59
def prefixEnd_508554 : Nat := 4983230072969 + 3 ^ 40 * 508554 * 2
def baseEnd_508554 : Nat := 87044213588902837945403

theorem tailTrace_508554 : CollatzResearch.WordTrace tailWord_508554 prefixEnd_508554 87044213588902837945403 := by
  unfold tailWord_508554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637122049900796738375179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12365658799735457969000477 4637122049900796738375179)
  ·
    refine ⟨6955683074851195107562769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637122049900796738375179 6955683074851195107562769)
    ·
      refine ⟨5216762306138396330672077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6955683074851195107562769 5216762306138396330672077)
      ·
        refine ⟨1956285864801898624002029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5216762306138396330672077 1956285864801898624002029)
        ·
          refine ⟨733607199300711984000761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1956285864801898624002029 733607199300711984000761)
          ·
            refine ⟨550205399475533988000571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733607199300711984000761 550205399475533988000571)
            ·
              refine ⟨825308099213300982000857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550205399475533988000571 825308099213300982000857)
              ·
                refine ⟨618981074409975736500643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825308099213300982000857 618981074409975736500643)
                ·
                  refine ⟨928471611614963604750965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618981074409975736500643 928471611614963604750965)
                  ·
                    refine ⟨87044213588902837945403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 928471611614963604750965 87044213588902837945403)
                    ·
                      rfl

theorem cell23_508554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_508554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508554 prefixEnd_508554 := by exact prefixLift 508554
  have htrace : WordTrace (prefixWord ++ tailWord_508554) baseStart_508554 baseEnd_508554 := by
    simpa [prefixWord, tailWord_508554, baseEnd_508554] using wordTrace_append hprefix tailTrace_508554
  have hstable : (prefixWord ++ tailWord_508554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508554).length < 2 ^ (prefixWord ++ tailWord_508554).sum := by decide
  have hdescent : baseEnd_508554 < baseStart_508554 := by decide
  rcases family_descends (prefixWord ++ tailWord_508554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508591 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 1, 2, 2]
def baseStart_508591 : Nat := 118140960795 + 508591 * 2 ^ 59
def prefixEnd_508591 : Nat := 4983230072969 + 3 ^ 40 * 508591 * 2
def baseEnd_508591 : Nat := 261151639550924869073539

theorem tailTrace_508591 : CollatzResearch.WordTrace tailWord_508591 prefixEnd_508591 261151639550924869073539 := by
  unfold tailWord_508591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549837700469142272597627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12366558466979428181731751 18549837700469142272597627)
  ·
    refine ⟨27824756550703713408896441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18549837700469142272597627 27824756550703713408896441)
    ·
      refine ⟨20868567413027785056672331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27824756550703713408896441 20868567413027785056672331)
      ·
        refine ⟨31302851119541677585008497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20868567413027785056672331 31302851119541677585008497)
        ·
          refine ⟨23477138339656258188756373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31302851119541677585008497 23477138339656258188756373)
          ·
            refine ⟨1100490859671387102597955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23477138339656258188756373 1100490859671387102597955)
            ·
              refine ⟨1650736289507080653896933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100490859671387102597955 1650736289507080653896933)
              ·
                refine ⟨309513054282577622605675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1650736289507080653896933 309513054282577622605675)
                ·
                  refine ⟨464269581423866433908513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309513054282577622605675 464269581423866433908513)
                  ·
                    refine ⟨348202186067899825431385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464269581423866433908513 348202186067899825431385)
                    ·
                      refine ⟨261151639550924869073539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348202186067899825431385 261151639550924869073539)
                      ·
                        rfl

theorem cell23_508591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 2, 2].length) (baseStart_508591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508591 prefixEnd_508591 := by exact prefixLift 508591
  have htrace : WordTrace (prefixWord ++ tailWord_508591) baseStart_508591 baseEnd_508591 := by
    simpa [prefixWord, tailWord_508591, baseEnd_508591] using wordTrace_append hprefix tailTrace_508591
  have hstable : (prefixWord ++ tailWord_508591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508591).length < 2 ^ (prefixWord ++ tailWord_508591).sum := by decide
  have hdescent : baseEnd_508591 < baseStart_508591 := by decide
  rcases family_descends (prefixWord ++ tailWord_508591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508597 : List Nat := [1, 3, 3, 3, 1, 3, 1, 8]
def baseStart_508597 : Nat := 118140960795 + 508597 * 2 ^ 59
def prefixEnd_508597 : Nat := 4983230072969 + 3 ^ 40 * 508597 * 2
def baseEnd_508597 : Nat := 9672397053142660948093

theorem tailTrace_508597 : CollatzResearch.WordTrace tailWord_508597 prefixEnd_508597 9672397053142660948093 := by
  unfold tailWord_508597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550056538447405297316045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12366704358964936864877363 18550056538447405297316045)
  ·
    refine ⟨6956271201917776986493517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18550056538447405297316045 6956271201917776986493517)
    ·
      refine ⟨2608601700719166369935069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6956271201917776986493517 2608601700719166369935069)
      ·
        refine ⟨978225637769687388725651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2608601700719166369935069 978225637769687388725651)
        ·
          refine ⟨1467338456654531083088477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978225637769687388725651 1467338456654531083088477)
          ·
            refine ⟨550251921245449156158179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1467338456654531083088477 550251921245449156158179)
            ·
              refine ⟨825377881868173734237269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550251921245449156158179 825377881868173734237269)
              ·
                refine ⟨9672397053142660948093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 825377881868173734237269 9672397053142660948093)
                ·
                  rfl

theorem cell23_508597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 8].length) (baseStart_508597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508597 prefixEnd_508597 := by exact prefixLift 508597
  have htrace : WordTrace (prefixWord ++ tailWord_508597) baseStart_508597 baseEnd_508597 := by
    simpa [prefixWord, tailWord_508597, baseEnd_508597] using wordTrace_append hprefix tailTrace_508597
  have hstable : (prefixWord ++ tailWord_508597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508597).length < 2 ^ (prefixWord ++ tailWord_508597).sum := by decide
  have hdescent : baseEnd_508597 < baseStart_508597 := by decide
  rcases family_descends (prefixWord ++ tailWord_508597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508603 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_508603 : Nat := 118140960795 + 508603 * 2 ^ 59
def prefixEnd_508603 : Nat := 4983230072969 + 3 ^ 40 * 508603 * 2
def baseEnd_508603 : Nat := 261157801318778822123483

theorem tailTrace_508603 : CollatzResearch.WordTrace tailWord_508603 prefixEnd_508603 261157801318778822123483 := by
  unfold tailWord_508603
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550275376425668322034463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12366850250950445548022975 18550275376425668322034463)
  ·
    refine ⟨27825413064638502483051695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18550275376425668322034463 27825413064638502483051695)
    ·
      refine ⟨41738119596957753724577543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27825413064638502483051695 41738119596957753724577543)
      ·
        refine ⟨62607179395436630586866315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41738119596957753724577543 62607179395436630586866315)
        ·
          refine ⟨93910769093154945880299473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62607179395436630586866315 93910769093154945880299473)
          ·
            refine ⟨70433076819866209410224605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93910769093154945880299473 70433076819866209410224605)
            ·
              refine ⟨26412403807449828528834227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70433076819866209410224605 26412403807449828528834227)
              ·
                refine ⟨39618605711174742793251341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26412403807449828528834227 39618605711174742793251341)
                ·
                  refine ⟨14856977141690528547469253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39618605711174742793251341 14856977141690528547469253)
                  ·
                    refine ⟨2785683214066974102650485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14856977141690528547469253 2785683214066974102650485)
                    ·
                      refine ⟨261157801318778822123483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2785683214066974102650485 261157801318778822123483)
                      ·
                        rfl

theorem cell23_508603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_508603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508603 prefixEnd_508603 := by exact prefixLift 508603
  have htrace : WordTrace (prefixWord ++ tailWord_508603) baseStart_508603 baseEnd_508603 := by
    simpa [prefixWord, tailWord_508603, baseEnd_508603] using wordTrace_append hprefix tailTrace_508603
  have hstable : (prefixWord ++ tailWord_508603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508603).length < 2 ^ (prefixWord ++ tailWord_508603).sum := by decide
  have hdescent : baseEnd_508603 < baseStart_508603 := by decide
  rcases family_descends (prefixWord ++ tailWord_508603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508607 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3]
def baseStart_508607 : Nat := 118140960795 + 508607 * 2 ^ 59
def prefixEnd_508607 : Nat := 4983230072969 + 3 ^ 40 * 508607 * 2
def baseEnd_508607 : Nat := 261159855241396806473465

theorem tailTrace_508607 : CollatzResearch.WordTrace tailWord_508607 prefixEnd_508607 261159855241396806473465 := by
  unfold tailWord_508607
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550421268411177005180075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12366947512274118003453383 18550421268411177005180075)
  ·
    refine ⟨27825631902616765507770113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18550421268411177005180075 27825631902616765507770113)
    ·
      refine ⟨20869223926962574130827585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27825631902616765507770113 20869223926962574130827585)
      ·
        refine ⟨15651917945221930598120689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20869223926962574130827585 15651917945221930598120689)
        ·
          refine ⟨11738938458916447948590517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15651917945221930598120689 11738938458916447948590517)
          ·
            refine ⟨1100525480523416995180361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11738938458916447948590517 1100525480523416995180361)
            ·
              refine ⟨825394110392562746385271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100525480523416995180361 825394110392562746385271)
              ·
                refine ⟨1238091165588844119577907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825394110392562746385271 1238091165588844119577907)
                ·
                  refine ⟨1857136748383266179366861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238091165588844119577907 1857136748383266179366861)
                  ·
                    refine ⟨696426280643724817262573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1857136748383266179366861 696426280643724817262573)
                    ·
                      refine ⟨261159855241396806473465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696426280643724817262573 261159855241396806473465)
                      ·
                        rfl

theorem cell23_508607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_508607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508607 prefixEnd_508607 := by exact prefixLift 508607
  have htrace : WordTrace (prefixWord ++ tailWord_508607) baseStart_508607 baseEnd_508607 := by
    simpa [prefixWord, tailWord_508607, baseEnd_508607] using wordTrace_append hprefix tailTrace_508607
  have hstable : (prefixWord ++ tailWord_508607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508607).length < 2 ^ (prefixWord ++ tailWord_508607).sum := by decide
  have hdescent : baseEnd_508607 < baseStart_508607 := by decide
  rcases family_descends (prefixWord ++ tailWord_508607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508613 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_508613 : Nat := 118140960795 + 508613 * 2 ^ 59
def prefixEnd_508613 : Nat := 4983230072969 + 3 ^ 40 * 508613 * 2
def baseEnd_508613 : Nat := 261162936125323782998437

theorem tailTrace_508613 : CollatzResearch.WordTrace tailWord_508613 prefixEnd_508613 261162936125323782998437 := by
  unfold tailWord_508613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18550640106389440029898493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12367093404259626686598995 18550640106389440029898493)
  ·
    refine ⟨6956490039896040011211935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18550640106389440029898493 6956490039896040011211935)
    ·
      refine ⟨10434735059844060016817903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6956490039896040011211935 10434735059844060016817903)
      ·
        refine ⟨15652102589766090025226855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10434735059844060016817903 15652102589766090025226855)
        ·
          refine ⟨23478153884649135037840283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15652102589766090025226855 23478153884649135037840283)
          ·
            refine ⟨35217230826973702556760425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23478153884649135037840283 35217230826973702556760425)
            ·
              refine ⟨26412923120230276917570319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35217230826973702556760425 26412923120230276917570319)
              ·
                refine ⟨39619384680345415376355479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26412923120230276917570319 39619384680345415376355479)
                ·
                  refine ⟨59429077020518123064533219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39619384680345415376355479 59429077020518123064533219)
                  ·
                    refine ⟨89143615530777184596799829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59429077020518123064533219 89143615530777184596799829)
                    ·
                      refine ⟨261162936125323782998437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 89143615530777184596799829 261162936125323782998437)
                      ·
                        rfl

theorem cell23_508613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_508613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508613 prefixEnd_508613 := by exact prefixLift 508613
  have htrace : WordTrace (prefixWord ++ tailWord_508613) baseStart_508613 baseEnd_508613 := by
    simpa [prefixWord, tailWord_508613, baseEnd_508613] using wordTrace_append hprefix tailTrace_508613
  have hstable : (prefixWord ++ tailWord_508613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508613).length < 2 ^ (prefixWord ++ tailWord_508613).sum := by decide
  have hdescent : baseEnd_508613 < baseStart_508613 := by decide
  rcases family_descends (prefixWord ++ tailWord_508613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508628 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_508628 : Nat := 118140960795 + 508628 * 2 ^ 59
def prefixEnd_508628 : Nat := 4983230072969 + 3 ^ 40 * 508628 * 2
def baseEnd_508628 : Nat := 261170638335141224310869

theorem tailTrace_508628 : CollatzResearch.WordTrace tailWord_508628 prefixEnd_508628 261170638335141224310869 := by
  unfold tailWord_508628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275593600667548795847269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12367458134223398394463025 9275593600667548795847269)
  ·
    refine ⟨1739173800125165399221363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9275593600667548795847269 1739173800125165399221363)
    ·
      refine ⟨2608760700187748098832045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739173800125165399221363 2608760700187748098832045)
      ·
        refine ⟨978285262570405537062017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2608760700187748098832045 978285262570405537062017)
        ·
          refine ⟨733713946927804152796513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978285262570405537062017 733713946927804152796513)
          ·
            refine ⟨550285460195853114597385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733713946927804152796513 550285460195853114597385)
            ·
              refine ⟨412714095146889835948039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550285460195853114597385 412714095146889835948039)
              ·
                refine ⟨619071142720334753922059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412714095146889835948039 619071142720334753922059)
                ·
                  refine ⟨928606714080502130883089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619071142720334753922059 928606714080502130883089)
                  ·
                    refine ⟨696455035560376598162317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 928606714080502130883089 696455035560376598162317)
                    ·
                      refine ⟨261170638335141224310869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696455035560376598162317 261170638335141224310869)
                      ·
                        rfl

theorem cell23_508628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_508628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508628 prefixEnd_508628 := by exact prefixLift 508628
  have htrace : WordTrace (prefixWord ++ tailWord_508628) baseStart_508628 baseEnd_508628 := by
    simpa [prefixWord, tailWord_508628, baseEnd_508628] using wordTrace_append hprefix tailTrace_508628
  have hstable : (prefixWord ++ tailWord_508628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508628).length < 2 ^ (prefixWord ++ tailWord_508628).sum := by decide
  have hdescent : baseEnd_508628 < baseStart_508628 := by decide
  rcases family_descends (prefixWord ++ tailWord_508628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508634 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_508634 : Nat := 118140960795 + 508634 * 2 ^ 59
def prefixEnd_508634 : Nat := 4983230072969 + 3 ^ 40 * 508634 * 2
def baseEnd_508634 : Nat := 261173719219068200835841

theorem tailTrace_508634 : CollatzResearch.WordTrace tailWord_508634 prefixEnd_508634 261173719219068200835841 := by
  unfold tailWord_508634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637851509828340154103239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12367604026208907077608637 4637851509828340154103239)
  ·
    refine ⟨6956777264742510231154859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637851509828340154103239 6956777264742510231154859)
    ·
      refine ⟨10435165897113765346732289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6956777264742510231154859 10435165897113765346732289)
      ·
        refine ⟨7826374422835324010049217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10435165897113765346732289 7826374422835324010049217)
        ·
          refine ⟨5869780817126493007536913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7826374422835324010049217 5869780817126493007536913)
          ·
            refine ⟨4402335612844869755652685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5869780817126493007536913 4402335612844869755652685)
            ·
              refine ⟨1650875854816826158369757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4402335612844869755652685 1650875854816826158369757)
              ·
                refine ⟨619078445556309809388659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650875854816826158369757 619078445556309809388659)
                ·
                  refine ⟨928617668334464714082989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619078445556309809388659 928617668334464714082989)
                  ·
                    refine ⟨348231625625424267781121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928617668334464714082989 348231625625424267781121)
                    ·
                      refine ⟨261173719219068200835841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348231625625424267781121 261173719219068200835841)
                      ·
                        rfl

theorem cell23_508634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_508634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508634 prefixEnd_508634 := by exact prefixLift 508634
  have htrace : WordTrace (prefixWord ++ tailWord_508634) baseStart_508634 baseEnd_508634 := by
    simpa [prefixWord, tailWord_508634, baseEnd_508634] using wordTrace_append hprefix tailTrace_508634
  have hstable : (prefixWord ++ tailWord_508634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508634).length < 2 ^ (prefixWord ++ tailWord_508634).sum := by decide
  have hdescent : baseEnd_508634 < baseStart_508634 := by decide
  rcases family_descends (prefixWord ++ tailWord_508634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508641 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_508641 : Nat := 118140960795 + 508641 * 2 ^ 59
def prefixEnd_508641 : Nat := 4983230072969 + 3 ^ 40 * 508641 * 2
def baseEnd_508641 : Nat := 261177313583649673448309

theorem tailTrace_508641 : CollatzResearch.WordTrace tailWord_508641 prefixEnd_508641 261177313583649673448309 := by
  unfold tailWord_508641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18551661350288000811917777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12367774233525333874611851 18551661350288000811917777)
  ·
    refine ⟨13913746012716000608938333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18551661350288000811917777 13913746012716000608938333)
    ·
      refine ⟨5217654754768500228351875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13913746012716000608938333 5217654754768500228351875)
      ·
        refine ⟨7826482132152750342527813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217654754768500228351875 7826482132152750342527813)
        ·
          refine ⟨1467465399778640689223965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7826482132152750342527813 1467465399778640689223965)
          ·
            refine ⟨550299524916990258458987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1467465399778640689223965 550299524916990258458987)
            ·
              refine ⟨825449287375485387688481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550299524916990258458987 825449287375485387688481)
              ·
                refine ⟨619086965531614040766361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825449287375485387688481 619086965531614040766361)
                ·
                  refine ⟨464315224148710530574771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619086965531614040766361 464315224148710530574771)
                  ·
                    refine ⟨696472836223065795862157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464315224148710530574771 696472836223065795862157)
                    ·
                      refine ⟨261177313583649673448309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696472836223065795862157 261177313583649673448309)
                      ·
                        rfl

theorem cell23_508641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_508641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508641 prefixEnd_508641 := by exact prefixLift 508641
  have htrace : WordTrace (prefixWord ++ tailWord_508641) baseStart_508641 baseEnd_508641 := by
    simpa [prefixWord, tailWord_508641, baseEnd_508641] using wordTrace_append hprefix tailTrace_508641
  have hstable : (prefixWord ++ tailWord_508641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508641).length < 2 ^ (prefixWord ++ tailWord_508641).sum := by decide
  have hdescent : baseEnd_508641 < baseStart_508641 := by decide
  rcases family_descends (prefixWord ++ tailWord_508641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508650 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_508650 : Nat := 118140960795 + 508650 * 2 ^ 59
def prefixEnd_508650 : Nat := 4983230072969 + 3 ^ 40 * 508650 * 2
def baseEnd_508650 : Nat := 261181934909540138235767

theorem tailTrace_508650 : CollatzResearch.WordTrace tailWord_508650 prefixEnd_508650 261181934909540138235767 := by
  unfold tailWord_508650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637997401813848837248851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12367993071503596899330269 4637997401813848837248851)
  ·
    refine ⟨6956996102720773255873277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4637997401813848837248851 6956996102720773255873277)
    ·
      refine ⟨2608873538520289970952479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6956996102720773255873277 2608873538520289970952479)
      ·
        refine ⟨3913310307780434956428719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2608873538520289970952479 3913310307780434956428719)
        ·
          refine ⟨5869965461670652434643079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3913310307780434956428719 5869965461670652434643079)
          ·
            refine ⟨8804948192505978651964619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5869965461670652434643079 8804948192505978651964619)
            ·
              refine ⟨13207422288758967977946929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8804948192505978651964619 13207422288758967977946929)
              ·
                refine ⟨9905566716569225983460197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13207422288758967977946929 9905566716569225983460197)
                ·
                  refine ⟨1857293759356729871898787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9905566716569225983460197 1857293759356729871898787)
                  ·
                    refine ⟨2785940639035094807848181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1857293759356729871898787 2785940639035094807848181)
                    ·
                      refine ⟨261181934909540138235767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2785940639035094807848181 261181934909540138235767)
                      ·
                        rfl

theorem cell23_508650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_508650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508650 prefixEnd_508650 := by exact prefixLift 508650
  have htrace : WordTrace (prefixWord ++ tailWord_508650) baseStart_508650 baseEnd_508650 := by
    simpa [prefixWord, tailWord_508650, baseEnd_508650] using wordTrace_append hprefix tailTrace_508650
  have hstable : (prefixWord ++ tailWord_508650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508650).length < 2 ^ (prefixWord ++ tailWord_508650).sum := by decide
  have hdescent : baseEnd_508650 < baseStart_508650 := by decide
  rcases family_descends (prefixWord ++ tailWord_508650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508707 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 5, 2]
def baseStart_508707 : Nat := 118140960795 + 508707 * 2 ^ 59
def prefixEnd_508707 : Nat := 4983230072969 + 3 ^ 40 * 508707 * 2
def baseEnd_508707 : Nat := 261211203306846415223005

theorem tailTrace_508707 : CollatzResearch.WordTrace tailWord_508707 prefixEnd_508707 261211203306846415223005 := by
  unfold tailWord_508707
  simp only [CollatzResearch.WordTrace]
  refine ⟨18554068568048894083820375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12369379045365929389213583 18554068568048894083820375)
  ·
    refine ⟨27831102852073341125730563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18554068568048894083820375 27831102852073341125730563)
    ·
      refine ⟨41746654278110011688595845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27831102852073341125730563 41746654278110011688595845)
      ·
        refine ⟨7827497677145627191611721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41746654278110011688595845 7827497677145627191611721)
        ·
          refine ⟨5870623257859220393708791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7827497677145627191611721 5870623257859220393708791)
          ·
            refine ⟨8805934886788830590563187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870623257859220393708791 8805934886788830590563187)
            ·
              refine ⟨13208902330183245885844781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8805934886788830590563187 13208902330183245885844781)
              ·
                refine ⟨4953338373818717207191793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13208902330183245885844781 4953338373818717207191793)
                ·
                  refine ⟨3715003780364037905393845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4953338373818717207191793 3715003780364037905393845)
                  ·
                    refine ⟨348281604409128553630673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3715003780364037905393845 348281604409128553630673)
                    ·
                      refine ⟨261211203306846415223005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348281604409128553630673 261211203306846415223005)
                      ·
                        rfl

theorem cell23_508707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_508707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508707 prefixEnd_508707 := by exact prefixLift 508707
  have htrace : WordTrace (prefixWord ++ tailWord_508707) baseStart_508707 baseEnd_508707 := by
    simpa [prefixWord, tailWord_508707, baseEnd_508707] using wordTrace_append hprefix tailTrace_508707
  have hstable : (prefixWord ++ tailWord_508707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508707).length < 2 ^ (prefixWord ++ tailWord_508707).sum := by decide
  have hdescent : baseEnd_508707 < baseStart_508707 := by decide
  rcases family_descends (prefixWord ++ tailWord_508707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508720 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_508720 : Nat := 118140960795 + 508720 * 2 ^ 59
def prefixEnd_508720 : Nat := 4983230072969 + 3 ^ 40 * 508720 * 2
def baseEnd_508720 : Nat := 261217878555354864360445

theorem tailTrace_508720 : CollatzResearch.WordTrace tailWord_508720 prefixEnd_508720 261217878555354864360445 := by
  unfold tailWord_508720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277271358500898652021807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12369695144667864869362409 9277271358500898652021807)
  ·
    refine ⟨13915907037751347978032711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9277271358500898652021807 13915907037751347978032711)
    ·
      refine ⟨20873860556627021967049067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13915907037751347978032711 20873860556627021967049067)
      ·
        refine ⟨31310790834940532950573601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20873860556627021967049067 31310790834940532950573601)
        ·
          refine ⟨23483093126205399712930201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31310790834940532950573601 23483093126205399712930201)
          ·
            refine ⟨17612319844654049784697651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23483093126205399712930201 17612319844654049784697651)
            ·
              refine ⟨26418479766981074677046477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612319844654049784697651 26418479766981074677046477)
              ·
                refine ⟨9906929912617903003892429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26418479766981074677046477 9906929912617903003892429)
                ·
                  refine ⟨3715098717231713626459661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9906929912617903003892429 3715098717231713626459661)
                  ·
                    refine ⟨1393162018961892609922373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715098717231713626459661 1393162018961892609922373)
                    ·
                      refine ⟨261217878555354864360445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1393162018961892609922373 261217878555354864360445)
                      ·
                        rfl

theorem cell23_508720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_508720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508720 prefixEnd_508720 := by exact prefixLift 508720
  have htrace : WordTrace (prefixWord ++ tailWord_508720) baseStart_508720 baseEnd_508720 := by
    simpa [prefixWord, tailWord_508720, baseEnd_508720] using wordTrace_append hprefix tailTrace_508720
  have hstable : (prefixWord ++ tailWord_508720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508720).length < 2 ^ (prefixWord ++ tailWord_508720).sum := by decide
  have hdescent : baseEnd_508720 < baseStart_508720 := by decide
  rcases family_descends (prefixWord ++ tailWord_508720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508754 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_508754 : Nat := 118140960795 + 508754 * 2 ^ 59
def prefixEnd_508754 : Nat := 4983230072969 + 3 ^ 40 * 508754 * 2
def baseEnd_508754 : Nat := 261235336897607731335289

theorem tailTrace_508754 : CollatzResearch.WordTrace tailWord_508754 prefixEnd_508754 261235336897607731335289 := by
  unfold tailWord_508754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638945699719655277695329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12370521865919080740520877 4638945699719655277695329)
  ·
    refine ⟨3479209274789741458271497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4638945699719655277695329 3479209274789741458271497)
    ·
      refine ⟨2609406956092306093703623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479209274789741458271497 2609406956092306093703623)
      ·
        refine ⟨3914110434138459140555435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609406956092306093703623 3914110434138459140555435)
        ·
          refine ⟨5871165651207688710833153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914110434138459140555435 5871165651207688710833153)
          ·
            refine ⟨4403374238405766533124865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5871165651207688710833153 4403374238405766533124865)
            ·
              refine ⟨3302530678804324899843649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403374238405766533124865 3302530678804324899843649)
              ·
                refine ⟨2476898009103243674882737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302530678804324899843649 2476898009103243674882737)
                ·
                  refine ⟨1857673506827432756162053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2476898009103243674882737 1857673506827432756162053)
                  ·
                    refine ⟨348313782530143641780385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857673506827432756162053 348313782530143641780385)
                    ·
                      refine ⟨261235336897607731335289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348313782530143641780385 261235336897607731335289)
                      ·
                        rfl

theorem cell23_508754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_508754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508754 prefixEnd_508754 := by exact prefixLift 508754
  have htrace : WordTrace (prefixWord ++ tailWord_508754) baseStart_508754 baseEnd_508754 := by
    simpa [prefixWord, tailWord_508754, baseEnd_508754] using wordTrace_append hprefix tailTrace_508754
  have hstable : (prefixWord ++ tailWord_508754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508754).length < 2 ^ (prefixWord ++ tailWord_508754).sum := by decide
  have hdescent : baseEnd_508754 < baseStart_508754 := by decide
  rcases family_descends (prefixWord ++ tailWord_508754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508760 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 8]
def baseStart_508760 : Nat := 118140960795 + 508760 * 2 ^ 59
def prefixEnd_508760 : Nat := 4983230072969 + 3 ^ 40 * 508760 * 2
def baseEnd_508760 : Nat := 29026490864614967540029

theorem tailTrace_508760 : CollatzResearch.WordTrace tailWord_508760 prefixEnd_508760 29026490864614967540029 := by
  unfold tailWord_508760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9278000818428442067749867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12370667757904589423666489 9278000818428442067749867)
  ·
    refine ⟨13917001227642663101624801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9278000818428442067749867 13917001227642663101624801)
    ·
      refine ⟨10437750920731997326218601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13917001227642663101624801 10437750920731997326218601)
      ·
        refine ⟨7828313190548997994663951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10437750920731997326218601 7828313190548997994663951)
        ·
          refine ⟨11742469785823496991995927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828313190548997994663951 11742469785823496991995927)
          ·
            refine ⟨17613704678735245487993891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11742469785823496991995927 17613704678735245487993891)
            ·
              refine ⟨26420557018102868231990837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17613704678735245487993891 26420557018102868231990837)
              ·
                refine ⟨2476927220447143896749141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26420557018102868231990837 2476927220447143896749141)
                ·
                  refine ⟨29026490864614967540029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2476927220447143896749141 29026490864614967540029)
                  ·
                    rfl

theorem cell23_508760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_508760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508760 prefixEnd_508760 := by exact prefixLift 508760
  have htrace : WordTrace (prefixWord ++ tailWord_508760) baseStart_508760 baseEnd_508760 := by
    simpa [prefixWord, tailWord_508760, baseEnd_508760] using wordTrace_append hprefix tailTrace_508760
  have hstable : (prefixWord ++ tailWord_508760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508760).length < 2 ^ (prefixWord ++ tailWord_508760).sum := by decide
  have hdescent : baseEnd_508760 < baseStart_508760 := by decide
  rcases family_descends (prefixWord ++ tailWord_508760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508804 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_508804 : Nat := 118140960795 + 508804 * 2 ^ 59
def prefixEnd_508804 : Nat := 4983230072969 + 3 ^ 40 * 508804 * 2
def baseEnd_508804 : Nat := 261261010930332535710059

theorem tailTrace_508804 : CollatzResearch.WordTrace tailWord_508804 prefixEnd_508804 261261010930332535710059 := by
  unfold tailWord_508804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9278803224348739825050733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12371737632464986433400977 9278803224348739825050733)
  ·
    refine ⟨3479551209130777434394025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9278803224348739825050733 3479551209130777434394025)
    ·
      refine ⟨2609663406848083075795519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479551209130777434394025 2609663406848083075795519)
      ·
        refine ⟨3914495110272124613693279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609663406848083075795519 3914495110272124613693279)
        ·
          refine ⟨5871742665408186920539919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914495110272124613693279 5871742665408186920539919)
          ·
            refine ⟨8807613998112280380809879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871742665408186920539919 8807613998112280380809879)
            ·
              refine ⟨13211420997168420571214819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807613998112280380809879 13211420997168420571214819)
              ·
                refine ⟨19817131495752630856822229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13211420997168420571214819 19817131495752630856822229)
                ·
                  refine ⟨464464019431702285706771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19817131495752630856822229 464464019431702285706771)
                  ·
                    refine ⟨696696029147553428560157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464464019431702285706771 696696029147553428560157)
                    ·
                      refine ⟨261261010930332535710059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696696029147553428560157 261261010930332535710059)
                      ·
                        rfl

theorem cell23_508804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_508804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508804 prefixEnd_508804 := by exact prefixLift 508804
  have htrace : WordTrace (prefixWord ++ tailWord_508804) baseStart_508804 baseEnd_508804 := by
    simpa [prefixWord, tailWord_508804, baseEnd_508804] using wordTrace_append hprefix tailTrace_508804
  have hstable : (prefixWord ++ tailWord_508804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508804).length < 2 ^ (prefixWord ++ tailWord_508804).sum := by decide
  have hdescent : baseEnd_508804 < baseStart_508804 := by decide
  rcases family_descends (prefixWord ++ tailWord_508804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508821 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_508821 : Nat := 118140960795 + 508821 * 2 ^ 59
def prefixEnd_508821 : Nat := 4983230072969 + 3 ^ 40 * 508821 * 2
def baseEnd_508821 : Nat := 261269740101458969197481

theorem tailTrace_508821 : CollatzResearch.WordTrace tailWord_508821 prefixEnd_508821 261269740101458969197481 := by
  unfold tailWord_508821
  simp only [CollatzResearch.WordTrace]
  refine ⟨18558226489635891553470317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12372150993090594368980211 18558226489635891553470317)
  ·
    refine ⟨6959334933613459332551369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18558226489635891553470317 6959334933613459332551369)
    ·
      refine ⟨5219501200210094499413527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6959334933613459332551369 5219501200210094499413527)
      ·
        refine ⟨7829251800315141749120291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219501200210094499413527 7829251800315141749120291)
        ·
          refine ⟨11743877700472712623680437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829251800315141749120291 11743877700472712623680437)
          ·
            refine ⟨1100988534419316808470041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11743877700472712623680437 1100988534419316808470041)
            ·
              refine ⟨825741400814487606352531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100988534419316808470041 825741400814487606352531)
              ·
                refine ⟨1238612101221731409528797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825741400814487606352531 1238612101221731409528797)
                ·
                  refine ⟨464479537958149278573299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238612101221731409528797 464479537958149278573299)
                  ·
                    refine ⟨696719306937223917859949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464479537958149278573299 696719306937223917859949)
                    ·
                      refine ⟨261269740101458969197481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696719306937223917859949 261269740101458969197481)
                      ·
                        rfl

theorem cell23_508821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_508821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508821 prefixEnd_508821 := by exact prefixLift 508821
  have htrace : WordTrace (prefixWord ++ tailWord_508821) baseStart_508821 baseEnd_508821 := by
    simpa [prefixWord, tailWord_508821, baseEnd_508821] using wordTrace_append hprefix tailTrace_508821
  have hstable : (prefixWord ++ tailWord_508821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508821).length < 2 ^ (prefixWord ++ tailWord_508821).sum := by decide
  have hdescent : baseEnd_508821 < baseStart_508821 := by decide
  rcases family_descends (prefixWord ++ tailWord_508821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508864 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_508864 : Nat := 118140960795 + 508864 * 2 ^ 59
def prefixEnd_508864 : Nat := 4983230072969 + 3 ^ 40 * 508864 * 2
def baseEnd_508864 : Nat := 261291819769602300959783

theorem tailTrace_508864 : CollatzResearch.WordTrace tailWord_508864 prefixEnd_508864 261291819769602300959783 := by
  unfold tailWord_508864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279897414240054948642823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12373196552320073264857097 9279897414240054948642823)
  ·
    refine ⟨13919846121360082422964235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9279897414240054948642823 13919846121360082422964235)
    ·
      refine ⟨20879769182040123634446353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919846121360082422964235 20879769182040123634446353)
      ·
        refine ⟨15659826886530092725834765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20879769182040123634446353 15659826886530092725834765)
        ·
          refine ⟨5872435082448784772188037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15659826886530092725834765 5872435082448784772188037)
          ·
            refine ⟨1101081577959147144785257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5872435082448784772188037 1101081577959147144785257)
            ·
              refine ⟨825811183469360358588943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101081577959147144785257 825811183469360358588943)
              ·
                refine ⟨1238716775204040537883415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825811183469360358588943 1238716775204040537883415)
                ·
                  refine ⟨1858075162806060806825123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238716775204040537883415 1858075162806060806825123)
                  ·
                    refine ⟨2787112744209091210237685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858075162806060806825123 2787112744209091210237685)
                    ·
                      refine ⟨261291819769602300959783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2787112744209091210237685 261291819769602300959783)
                      ·
                        rfl

theorem cell23_508864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_508864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508864 prefixEnd_508864 := by exact prefixLift 508864
  have htrace : WordTrace (prefixWord ++ tailWord_508864) baseStart_508864 baseEnd_508864 := by
    simpa [prefixWord, tailWord_508864, baseEnd_508864] using wordTrace_append hprefix tailTrace_508864
  have hstable : (prefixWord ++ tailWord_508864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508864).length < 2 ^ (prefixWord ++ tailWord_508864).sum := by decide
  have hdescent : baseEnd_508864 < baseStart_508864 := by decide
  rcases family_descends (prefixWord ++ tailWord_508864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508878 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_508878 : Nat := 118140960795 + 508878 * 2 ^ 59
def prefixEnd_508878 : Nat := 4983230072969 + 3 ^ 40 * 508878 * 2
def baseEnd_508878 : Nat := 261299008498765246184719

theorem tailTrace_508878 : CollatzResearch.WordTrace tailWord_508878 prefixEnd_508878 261299008498765246184719 := by
  unfold tailWord_508878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320038181303673786036911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12373536966952926858863525 2320038181303673786036911)
  ·
    refine ⟨3480057271955510679055367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2320038181303673786036911 3480057271955510679055367)
    ·
      refine ⟨5220085907933266018583051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480057271955510679055367 5220085907933266018583051)
      ·
        refine ⟨7830128861899899027874577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220085907933266018583051 7830128861899899027874577)
        ·
          refine ⟨5872596646424924270905933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830128861899899027874577 5872596646424924270905933)
          ·
            refine ⟨2202223742409346601589725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5872596646424924270905933 2202223742409346601589725)
            ·
              refine ⟨825833903403504975596147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202223742409346601589725 825833903403504975596147)
              ·
                refine ⟨1238750855105257463394221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825833903403504975596147 1238750855105257463394221)
                ·
                  refine ⟨464531570664471548772833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1238750855105257463394221 464531570664471548772833)
                  ·
                    refine ⟨348398677998353661579625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464531570664471548772833 348398677998353661579625)
                    ·
                      refine ⟨261299008498765246184719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348398677998353661579625 261299008498765246184719)
                      ·
                        rfl

theorem cell23_508878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_508878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508878 prefixEnd_508878 := by exact prefixLift 508878
  have htrace : WordTrace (prefixWord ++ tailWord_508878) baseStart_508878 baseEnd_508878 := by
    simpa [prefixWord, tailWord_508878, baseEnd_508878] using wordTrace_append hprefix tailTrace_508878
  have hstable : (prefixWord ++ tailWord_508878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508878).length < 2 ^ (prefixWord ++ tailWord_508878).sum := by decide
  have hdescent : baseEnd_508878 < baseStart_508878 := by decide
  rcases family_descends (prefixWord ++ tailWord_508878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508884 : List Nat := [2, 4, 1, 2, 1, 3, 2, 8]
def baseStart_508884 : Nat := 118140960795 + 508884 * 2 ^ 59
def prefixEnd_508884 : Nat := 4983230072969 + 3 ^ 40 * 508884 * 2
def baseEnd_508884 : Nat := 9677855162321934174433

theorem tailTrace_508884 : CollatzResearch.WordTrace tailWord_508884 prefixEnd_508884 9677855162321934174433 := by
  unfold tailWord_508884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280262144203826656506853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12373682858938435542009137 9280262144203826656506853)
  ·
    refine ⟨1740049152038217498095035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9280262144203826656506853 1740049152038217498095035)
    ·
      refine ⟨2610073728057326247142553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740049152038217498095035 2610073728057326247142553)
      ·
        refine ⟨1957555296042994685356915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610073728057326247142553 1957555296042994685356915)
        ·
          refine ⟨2936332944064492028035373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957555296042994685356915 2936332944064492028035373)
          ·
            refine ⟨1101124854024184510513265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2936332944064492028035373 1101124854024184510513265)
            ·
              refine ⟨825843640518138382884949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101124854024184510513265 825843640518138382884949)
              ·
                refine ⟨9677855162321934174433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 825843640518138382884949 9677855162321934174433)
                ·
                  rfl

theorem cell23_508884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 8].length) (baseStart_508884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508884 prefixEnd_508884 := by exact prefixLift 508884
  have htrace : WordTrace (prefixWord ++ tailWord_508884) baseStart_508884 baseEnd_508884 := by
    simpa [prefixWord, tailWord_508884, baseEnd_508884] using wordTrace_append hprefix tailTrace_508884
  have hstable : (prefixWord ++ tailWord_508884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508884).length < 2 ^ (prefixWord ++ tailWord_508884).sum := by decide
  have hdescent : baseEnd_508884 < baseStart_508884 := by decide
  rcases family_descends (prefixWord ++ tailWord_508884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508888 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 2, 4]
def baseStart_508888 : Nat := 118140960795 + 508888 * 2 ^ 59
def prefixEnd_508888 : Nat := 4983230072969 + 3 ^ 40 * 508888 * 2
def baseEnd_508888 : Nat := 87101381101770069019891

theorem tailTrace_508888 : CollatzResearch.WordTrace tailWord_508888 prefixEnd_508888 87101381101770069019891 := by
  unfold tailWord_508888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280335090196580998079659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12373780120262107997439545 9280335090196580998079659)
  ·
    refine ⟨13920502635294871497119489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9280335090196580998079659 13920502635294871497119489)
    ·
      refine ⟨10440376976471153622839617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13920502635294871497119489 10440376976471153622839617)
      ·
        refine ⟨7830282732353365217129713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10440376976471153622839617 7830282732353365217129713)
        ·
          refine ⟨5872712049265023912847285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7830282732353365217129713 5872712049265023912847285)
          ·
            refine ⟨550566754618595991829433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5872712049265023912847285 550566754618595991829433)
            ·
              refine ⟨412925065963946993872075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550566754618595991829433 412925065963946993872075)
              ·
                refine ⟨619387598945920490808113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412925065963946993872075 619387598945920490808113)
                ·
                  refine ⟨464540699209440368106085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619387598945920490808113 464540699209440368106085)
                  ·
                    refine ⟨87101381101770069019891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 464540699209440368106085 87101381101770069019891)
                    ·
                      rfl

theorem cell23_508888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_508888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508888 prefixEnd_508888 := by exact prefixLift 508888
  have htrace : WordTrace (prefixWord ++ tailWord_508888) baseStart_508888 baseEnd_508888 := by
    simpa [prefixWord, tailWord_508888, baseEnd_508888] using wordTrace_append hprefix tailTrace_508888
  have hstable : (prefixWord ++ tailWord_508888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508888).length < 2 ^ (prefixWord ++ tailWord_508888).sum := by decide
  have hdescent : baseEnd_508888 < baseStart_508888 := by decide
  rcases family_descends (prefixWord ++ tailWord_508888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508898 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_508898 : Nat := 118140960795 + 508898 * 2 ^ 59
def prefixEnd_508898 : Nat := 4983230072969 + 3 ^ 40 * 508898 * 2
def baseEnd_508898 : Nat := 261309278111855167934627

theorem tailTrace_508898 : CollatzResearch.WordTrace tailWord_508898 prefixEnd_508898 261309278111855167934627 := by
  unfold tailWord_508898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640258727589233426005837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12374023273571289136015565 4640258727589233426005837)
  ·
    refine ⟨1740097022845962534752189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4640258727589233426005837 1740097022845962534752189)
    ·
      refine ⟨652536383567235950532071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1740097022845962534752189 652536383567235950532071)
      ·
        refine ⟨978804575350853925798107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652536383567235950532071 978804575350853925798107)
        ·
          refine ⟨1468206863026280888697161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978804575350853925798107 1468206863026280888697161)
          ·
            refine ⟨1101155147269710666522871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468206863026280888697161 1101155147269710666522871)
            ·
              refine ⟨1651732720904565999784307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101155147269710666522871 1651732720904565999784307)
              ·
                refine ⟨2477599081356848999676461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651732720904565999784307 2477599081356848999676461)
                ·
                  refine ⟨929099655508818374878673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2477599081356848999676461 929099655508818374878673)
                  ·
                    refine ⟨696824741631613781159005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929099655508818374878673 696824741631613781159005)
                    ·
                      refine ⟨261309278111855167934627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696824741631613781159005 261309278111855167934627)
                      ·
                        rfl

theorem cell23_508898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_508898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508898 prefixEnd_508898 := by exact prefixLift 508898
  have htrace : WordTrace (prefixWord ++ tailWord_508898) baseStart_508898 baseEnd_508898 := by
    simpa [prefixWord, tailWord_508898, baseEnd_508898] using wordTrace_append hprefix tailTrace_508898
  have hstable : (prefixWord ++ tailWord_508898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508898).length < 2 ^ (prefixWord ++ tailWord_508898).sum := by decide
  have hdescent : baseEnd_508898 < baseStart_508898 := by decide
  rcases family_descends (prefixWord ++ tailWord_508898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508937 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_508937 : Nat := 118140960795 + 508937 * 2 ^ 59
def prefixEnd_508937 : Nat := 4983230072969 + 3 ^ 40 * 508937 * 2
def baseEnd_508937 : Nat := 261329303857380515346947

theorem tailTrace_508937 : CollatzResearch.WordTrace tailWord_508937 prefixEnd_508937 261329303857380515346947 := by
  unfold tailWord_508937
  simp only [CollatzResearch.WordTrace]
  refine ⟨18562457357215643364693065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12374971571477095576462043 18562457357215643364693065)
  ·
    refine ⟨13921843017911732523519799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18562457357215643364693065 13921843017911732523519799)
    ·
      refine ⟨20882764526867598785279699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921843017911732523519799 20882764526867598785279699)
      ·
        refine ⟨31324146790301398177919549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20882764526867598785279699 31324146790301398177919549)
        ·
          refine ⟨11746555046363024316719831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31324146790301398177919549 11746555046363024316719831)
          ·
            refine ⟨17619832569544536475079747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746555046363024316719831 17619832569544536475079747)
            ·
              refine ⟨26429748854316804712619621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17619832569544536475079747 26429748854316804712619621)
              ·
                refine ⟨4955577910184400883616179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26429748854316804712619621 4955577910184400883616179)
                ·
                  refine ⟨7433366865276601325424269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955577910184400883616179 7433366865276601325424269)
                  ·
                    refine ⟨2787512574478725497034101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7433366865276601325424269 2787512574478725497034101)
                    ·
                      refine ⟨261329303857380515346947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2787512574478725497034101 261329303857380515346947)
                      ·
                        rfl

theorem cell23_508937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_508937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508937 prefixEnd_508937 := by exact prefixLift 508937
  have htrace : WordTrace (prefixWord ++ tailWord_508937) baseStart_508937 baseEnd_508937 := by
    simpa [prefixWord, tailWord_508937, baseEnd_508937] using wordTrace_append hprefix tailTrace_508937
  have hstable : (prefixWord ++ tailWord_508937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508937).length < 2 ^ (prefixWord ++ tailWord_508937).sum := by decide
  have hdescent : baseEnd_508937 < baseStart_508937 := by decide
  rcases family_descends (prefixWord ++ tailWord_508937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508954 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_508954 : Nat := 118140960795 + 508954 * 2 ^ 59
def prefixEnd_508954 : Nat := 4983230072969 + 3 ^ 40 * 508954 * 2
def baseEnd_508954 : Nat := 261338033028506948834369

theorem tailTrace_508954 : CollatzResearch.WordTrace tailWord_508954 prefixEnd_508954 261338033028506948834369 := by
  unfold tailWord_508954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640769349538513817015479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12375384932102703512041277 4640769349538513817015479)
  ·
    refine ⟨6961154024307770725523219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640769349538513817015479 6961154024307770725523219)
    ·
      refine ⟨10441731036461656088284829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961154024307770725523219 10441731036461656088284829)
      ·
        refine ⟨3915649138673121033106811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10441731036461656088284829 3915649138673121033106811)
        ·
          refine ⟨5873473708009681549660217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915649138673121033106811 5873473708009681549660217)
          ·
            refine ⟨4405105281007261162245163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5873473708009681549660217 4405105281007261162245163)
            ·
              refine ⟨6607657921510891743367745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405105281007261162245163 6607657921510891743367745)
              ·
                refine ⟨4955743441133168807525809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607657921510891743367745 4955743441133168807525809)
                ·
                  refine ⟨3716807580849876605644357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955743441133168807525809 3716807580849876605644357)
                  ·
                    refine ⟨696901421409351863558317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3716807580849876605644357 696901421409351863558317)
                    ·
                      refine ⟨261338033028506948834369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 696901421409351863558317 261338033028506948834369)
                      ·
                        rfl

theorem cell23_508954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_508954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508954 prefixEnd_508954 := by exact prefixLift 508954
  have htrace : WordTrace (prefixWord ++ tailWord_508954) baseStart_508954 baseEnd_508954 := by
    simpa [prefixWord, tailWord_508954, baseEnd_508954] using wordTrace_append hprefix tailTrace_508954
  have hstable : (prefixWord ++ tailWord_508954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508954).length < 2 ^ (prefixWord ++ tailWord_508954).sum := by decide
  have hdescent : baseEnd_508954 < baseStart_508954 := by decide
  rcases family_descends (prefixWord ++ tailWord_508954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508974 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_508974 : Nat := 118140960795 + 508974 * 2 ^ 59
def prefixEnd_508974 : Nat := 4983230072969 + 3 ^ 40 * 508974 * 2
def baseEnd_508974 : Nat := 29038700293510763398253

theorem tailTrace_508974 : CollatzResearch.WordTrace tailWord_508974 prefixEnd_508974 29038700293510763398253 := by
  unfold tailWord_508974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320475857260199835473747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12375871238721065789193317 2320475857260199835473747)
  ·
    refine ⟨3480713785890299753210621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2320475857260199835473747 3480713785890299753210621)
    ·
      refine ⟨1305267669708862407453983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3480713785890299753210621 1305267669708862407453983)
      ·
        refine ⟨1957901504563293611180975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305267669708862407453983 1957901504563293611180975)
        ·
          refine ⟨2936852256844940416771463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957901504563293611180975 2936852256844940416771463)
          ·
            refine ⟨4405278385267410625157195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936852256844940416771463 4405278385267410625157195)
            ·
              refine ⟨6607917577901115937735793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405278385267410625157195 6607917577901115937735793)
              ·
                refine ⟨4955938183425836953301845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607917577901115937735793 4955938183425836953301845)
                ·
                  refine ⟨29038700293510763398253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4955938183425836953301845 29038700293510763398253)
                  ·
                    rfl

theorem cell23_508974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_508974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508974 prefixEnd_508974 := by exact prefixLift 508974
  have htrace : WordTrace (prefixWord ++ tailWord_508974) baseStart_508974 baseEnd_508974 := by
    simpa [prefixWord, tailWord_508974, baseEnd_508974] using wordTrace_append hprefix tailTrace_508974
  have hstable : (prefixWord ++ tailWord_508974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508974).length < 2 ^ (prefixWord ++ tailWord_508974).sum := by decide
  have hdescent : baseEnd_508974 < baseStart_508974 := by decide
  rcases family_descends (prefixWord ++ tailWord_508974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508985 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 2, 2, 2]
def baseStart_508985 : Nat := 118140960795 + 508985 * 2 ^ 59
def prefixEnd_508985 : Nat := 4983230072969 + 3 ^ 40 * 508985 * 2
def baseEnd_508985 : Nat := 261353950928796327546727

theorem tailTrace_508985 : CollatzResearch.WordTrace tailWord_508985 prefixEnd_508985 261353950928796327546727 := by
  unfold tailWord_508985
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564208061041747562440409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12376138707361165041626939 18564208061041747562440409)
  ·
    refine ⟨13923156045781310671830307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18564208061041747562440409 13923156045781310671830307)
    ·
      refine ⟨20884734068671966007745461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923156045781310671830307 20884734068671966007745461)
      ·
        refine ⟨1957943818937996813226137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20884734068671966007745461 1957943818937996813226137)
        ·
          refine ⟨1468457864203497609919603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1957943818937996813226137 1468457864203497609919603)
          ·
            refine ⟨2202686796305246414879405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468457864203497609919603 2202686796305246414879405)
            ·
              refine ⟨826007548614467405579777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202686796305246414879405 826007548614467405579777)
              ·
                refine ⟨619505661460850554184833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826007548614467405579777 619505661460850554184833)
                ·
                  refine ⟨464629246095637915638625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619505661460850554184833 464629246095637915638625)
                  ·
                    refine ⟨348471934571728436728969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464629246095637915638625 348471934571728436728969)
                    ·
                      refine ⟨261353950928796327546727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348471934571728436728969 261353950928796327546727)
                      ·
                        rfl

theorem cell23_508985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_508985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508985 prefixEnd_508985 := by exact prefixLift 508985
  have htrace : WordTrace (prefixWord ++ tailWord_508985) baseStart_508985 baseEnd_508985 := by
    simpa [prefixWord, tailWord_508985, baseEnd_508985] using wordTrace_append hprefix tailTrace_508985
  have hstable : (prefixWord ++ tailWord_508985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508985).length < 2 ^ (prefixWord ++ tailWord_508985).sum := by decide
  have hdescent : baseEnd_508985 < baseStart_508985 := by decide
  rcases family_descends (prefixWord ++ tailWord_508985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508987 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 7]
def baseStart_508987 : Nat := 118140960795 + 508987 * 2 ^ 59
def prefixEnd_508987 : Nat := 4983230072969 + 3 ^ 40 * 508987 * 2
def baseEnd_508987 : Nat := 87118325963368439907239

theorem tailTrace_508987 : CollatzResearch.WordTrace tailWord_508987 prefixEnd_508987 87118325963368439907239 := by
  unfold tailWord_508987
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564281007034501904013215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12376187338023001269342143 18564281007034501904013215)
  ·
    refine ⟨27846421510551752856019823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18564281007034501904013215 27846421510551752856019823)
    ·
      refine ⟨41769632265827629284029735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27846421510551752856019823 41769632265827629284029735)
      ·
        refine ⟨62654448398741443926044603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41769632265827629284029735 62654448398741443926044603)
        ·
          refine ⟨93981672598112165889066905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62654448398741443926044603 93981672598112165889066905)
          ·
            refine ⟨70486254448584124416800179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93981672598112165889066905 70486254448584124416800179)
            ·
              refine ⟨105729381672876186625200269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70486254448584124416800179 105729381672876186625200269)
              ·
                refine ⟨39648518127328569984450101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105729381672876186625200269 39648518127328569984450101)
                ·
                  refine ⟨3717048574437053436042197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39648518127328569984450101 3717048574437053436042197)
                  ·
                    refine ⟨87118325963368439907239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3717048574437053436042197 87118325963368439907239)
                    ·
                      rfl

theorem cell23_508987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_508987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508987 prefixEnd_508987 := by exact prefixLift 508987
  have htrace : WordTrace (prefixWord ++ tailWord_508987) baseStart_508987 baseEnd_508987 := by
    simpa [prefixWord, tailWord_508987, baseEnd_508987] using wordTrace_append hprefix tailTrace_508987
  have hstable : (prefixWord ++ tailWord_508987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508987).length < 2 ^ (prefixWord ++ tailWord_508987).sum := by decide
  have hdescent : baseEnd_508987 < baseStart_508987 := by decide
  rcases family_descends (prefixWord ++ tailWord_508987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508998 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_508998 : Nat := 118140960795 + 508998 * 2 ^ 59
def prefixEnd_508998 : Nat := 4983230072969 + 3 ^ 40 * 508998 * 2
def baseEnd_508998 : Nat := 261360626177304776684167

theorem tailTrace_508998 : CollatzResearch.WordTrace tailWord_508998 prefixEnd_508998 261360626177304776684167 := by
  unfold tailWord_508998
  simp only [CollatzResearch.WordTrace]
  refine ⟨580146319062332836958239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12376454806663100521775765 580146319062332836958239)
  ·
    refine ⟨870219478593499255437359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580146319062332836958239 870219478593499255437359)
    ·
      refine ⟨1305329217890248883156039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870219478593499255437359 1305329217890248883156039)
      ·
        refine ⟨1957993826835373324734059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305329217890248883156039 1957993826835373324734059)
        ·
          refine ⟨2936990740253059987101089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957993826835373324734059 2936990740253059987101089)
          ·
            refine ⟨2202743055189794990325817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936990740253059987101089 2202743055189794990325817)
            ·
              refine ⟨1652057291392346242744363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202743055189794990325817 1652057291392346242744363)
              ·
                refine ⟨2478085937088519364116545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652057291392346242744363 2478085937088519364116545)
                ·
                  refine ⟨1858564452816389523087409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478085937088519364116545 1858564452816389523087409)
                  ·
                    refine ⟨1393923339612292142315557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1858564452816389523087409 1393923339612292142315557)
                    ·
                      refine ⟨261360626177304776684167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1393923339612292142315557 261360626177304776684167)
                      ·
                        rfl

theorem cell23_508998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_508998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_508998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_508998 prefixEnd_508998 := by exact prefixLift 508998
  have htrace : WordTrace (prefixWord ++ tailWord_508998) baseStart_508998 baseEnd_508998 := by
    simpa [prefixWord, tailWord_508998, baseEnd_508998] using wordTrace_append hprefix tailTrace_508998
  have hstable : (prefixWord ++ tailWord_508998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508998).length < 2 ^ (prefixWord ++ tailWord_508998).sum := by decide
  have hdescent : baseEnd_508998 < baseStart_508998 := by decide
  rcases family_descends (prefixWord ++ tailWord_508998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509024 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_509024 : Nat := 118140960795 + 509024 * 2 ^ 59
def prefixEnd_509024 : Nat := 4983230072969 + 3 ^ 40 * 509024 * 2
def baseEnd_509024 : Nat := 261373976674321674959047

theorem tailTrace_509024 : CollatzResearch.WordTrace tailWord_509024 prefixEnd_509024 261373976674321674959047 := by
  unfold tailWord_509024
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282815253950228611555063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12377087005266971482073417 9282815253950228611555063)
  ·
    refine ⟨13924222880925342917332595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282815253950228611555063 13924222880925342917332595)
    ·
      refine ⟨20886334321388014375998893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13924222880925342917332595 20886334321388014375998893)
      ·
        refine ⟨7832375370520505390999585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20886334321388014375998893 7832375370520505390999585)
        ·
          refine ⟨5874281527890379043249689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7832375370520505390999585 5874281527890379043249689)
          ·
            refine ⟨4405711145917784282437267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5874281527890379043249689 4405711145917784282437267)
            ·
              refine ⟨6608566718876676423655901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405711145917784282437267 6608566718876676423655901)
              ·
                refine ⟨2478212519578753658870963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608566718876676423655901 2478212519578753658870963)
                ·
                  refine ⟨3717318779368130488306445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478212519578753658870963 3717318779368130488306445)
                  ·
                    refine ⟨1393994542263048933114917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717318779368130488306445 1393994542263048933114917)
                    ·
                      refine ⟨261373976674321674959047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1393994542263048933114917 261373976674321674959047)
                      ·
                        rfl

theorem cell23_509024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_509024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509024 prefixEnd_509024 := by exact prefixLift 509024
  have htrace : WordTrace (prefixWord ++ tailWord_509024) baseStart_509024 baseEnd_509024 := by
    simpa [prefixWord, tailWord_509024, baseEnd_509024] using wordTrace_append hprefix tailTrace_509024
  have hstable : (prefixWord ++ tailWord_509024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509024).length < 2 ^ (prefixWord ++ tailWord_509024).sum := by decide
  have hdescent : baseEnd_509024 < baseStart_509024 := by decide
  rcases family_descends (prefixWord ++ tailWord_509024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509041 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_509041 : Nat := 118140960795 + 509041 * 2 ^ 59
def prefixEnd_509041 : Nat := 4983230072969 + 3 ^ 40 * 509041 * 2
def baseEnd_509041 : Nat := 261382705845448108446469

theorem tailTrace_509041 : CollatzResearch.WordTrace tailWord_509041 prefixEnd_509041 261382705845448108446469 := by
  unfold tailWord_509041
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566250548838869126478977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12377500365892579417652651 18566250548838869126478977)
  ·
    refine ⟨13924687911629151844859233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18566250548838869126478977 13924687911629151844859233)
    ·
      refine ⟨10443515933721863883644425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13924687911629151844859233 10443515933721863883644425)
      ·
        refine ⟨7832636950291397912733319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10443515933721863883644425 7832636950291397912733319)
        ·
          refine ⟨11748955425437096869099979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832636950291397912733319 11748955425437096869099979)
          ·
            refine ⟨17623433138155645303649969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11748955425437096869099979 17623433138155645303649969)
            ·
              refine ⟨13217574853616733977737477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17623433138155645303649969 13217574853616733977737477)
              ·
                refine ⟨2478295285053137620825777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13217574853616733977737477 2478295285053137620825777)
                ·
                  refine ⟨1858721463789853215619333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478295285053137620825777 1858721463789853215619333)
                  ·
                    refine ⟨348510274460597477928625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858721463789853215619333 348510274460597477928625)
                    ·
                      refine ⟨261382705845448108446469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348510274460597477928625 261382705845448108446469)
                      ·
                        rfl

theorem cell23_509041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_509041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509041 prefixEnd_509041 := by exact prefixLift 509041
  have htrace : WordTrace (prefixWord ++ tailWord_509041) baseStart_509041 baseEnd_509041 := by
    simpa [prefixWord, tailWord_509041, baseEnd_509041] using wordTrace_append hprefix tailTrace_509041
  have hstable : (prefixWord ++ tailWord_509041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509041).length < 2 ^ (prefixWord ++ tailWord_509041).sum := by decide
  have hdescent : baseEnd_509041 < baseStart_509041 := by decide
  rcases family_descends (prefixWord ++ tailWord_509041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509098 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_509098 : Nat := 118140960795 + 509098 * 2 ^ 59
def prefixEnd_509098 : Nat := 4983230072969 + 3 ^ 40 * 509098 * 2
def baseEnd_509098 : Nat := 29045774915861598381523

theorem tailTrace_509098 : CollatzResearch.WordTrace tailWord_509098 prefixEnd_509098 29045774915861598381523 := by
  unfold tailWord_509098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642082377408091965325987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12378886339754911907535965 4642082377408091965325987)
  ·
    refine ⟨6963123566112137947988981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4642082377408091965325987 6963123566112137947988981)
    ·
      refine ⟨652792834323012932623967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6963123566112137947988981 652792834323012932623967)
      ·
        refine ⟨979189251484519398935951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652792834323012932623967 979189251484519398935951)
        ·
          refine ⟨1468783877226779098403927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979189251484519398935951 1468783877226779098403927)
          ·
            refine ⟨2203175815840168647605891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468783877226779098403927 2203175815840168647605891)
            ·
              refine ⟨3304763723760252971408837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203175815840168647605891 3304763723760252971408837)
              ·
                refine ⟨619643198205047432139157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3304763723760252971408837 619643198205047432139157)
                ·
                  refine ⟨29045774915861598381523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 619643198205047432139157 29045774915861598381523)
                  ·
                    rfl

theorem cell23_509098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_509098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509098 prefixEnd_509098 := by exact prefixLift 509098
  have htrace : WordTrace (prefixWord ++ tailWord_509098) baseStart_509098 baseEnd_509098 := by
    simpa [prefixWord, tailWord_509098, baseEnd_509098] using wordTrace_append hprefix tailTrace_509098
  have hstable : (prefixWord ++ tailWord_509098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509098).length < 2 ^ (prefixWord ++ tailWord_509098).sum := by decide
  have hdescent : baseEnd_509098 < baseStart_509098 := by decide
  rcases family_descends (prefixWord ++ tailWord_509098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509126 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_509126 : Nat := 118140960795 + 509126 * 2 ^ 59
def prefixEnd_509126 : Nat := 4983230072969 + 3 ^ 40 * 509126 * 2
def baseEnd_509126 : Nat := 261426351701080275883579

theorem tailTrace_509126 : CollatzResearch.WordTrace tailWord_509126 prefixEnd_509126 261426351701080275883579 := by
  unfold tailWord_509126
  simp only [CollatzResearch.WordTrace]
  refine ⟨580292211047841520103851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12379567169020619095548821 580292211047841520103851)
  ·
    refine ⟨870438316571762280155777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580292211047841520103851 870438316571762280155777)
    ·
      refine ⟨652828737428821710116833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 870438316571762280155777 652828737428821710116833)
      ·
        refine ⟨489621553071616282587625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652828737428821710116833 489621553071616282587625)
        ·
          refine ⟨367216164803712211940719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489621553071616282587625 367216164803712211940719)
          ·
            refine ⟨550824247205568317911079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367216164803712211940719 550824247205568317911079)
            ·
              refine ⟨826236370808352476866619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550824247205568317911079 826236370808352476866619)
              ·
                refine ⟨1239354556212528715299929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826236370808352476866619 1239354556212528715299929)
                ·
                  refine ⟨929515917159396536474947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1239354556212528715299929 929515917159396536474947)
                  ·
                    refine ⟨1394273875739094804712421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 929515917159396536474947 1394273875739094804712421)
                    ·
                      refine ⟨261426351701080275883579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1394273875739094804712421 261426351701080275883579)
                      ·
                        rfl

theorem cell23_509126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_509126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509126 prefixEnd_509126 := by exact prefixLift 509126
  have htrace : WordTrace (prefixWord ++ tailWord_509126) baseStart_509126 baseEnd_509126 := by
    simpa [prefixWord, tailWord_509126, baseEnd_509126] using wordTrace_append hprefix tailTrace_509126
  have hstable : (prefixWord ++ tailWord_509126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509126).length < 2 ^ (prefixWord ++ tailWord_509126).sum := by decide
  have hdescent : baseEnd_509126 < baseStart_509126 := by decide
  rcases family_descends (prefixWord ++ tailWord_509126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509131 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 8, 2]
def baseStart_509131 : Nat := 118140960795 + 509131 * 2 ^ 59
def prefixEnd_509131 : Nat := 4983230072969 + 3 ^ 40 * 509131 * 2
def baseEnd_509131 : Nat := 261428919104352756321055

theorem tailTrace_509131 : CollatzResearch.WordTrace tailWord_509131 prefixEnd_509131 261428919104352756321055 := by
  unfold tailWord_509131
  simp only [CollatzResearch.WordTrace]
  refine ⟨18569533118512814497255247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12379688745675209664836831 18569533118512814497255247)
  ·
    refine ⟨27854299677769221745882871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18569533118512814497255247 27854299677769221745882871)
    ·
      refine ⟨41781449516653832618824307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27854299677769221745882871 41781449516653832618824307)
      ·
        refine ⟨62672174274980748928236461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41781449516653832618824307 62672174274980748928236461)
        ·
          refine ⟨23502065353117780848088673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62672174274980748928236461 23502065353117780848088673)
          ·
            refine ⟨17626549014838335636066505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23502065353117780848088673 17626549014838335636066505)
            ·
              refine ⟨13219911761128751727049879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17626549014838335636066505 13219911761128751727049879)
              ·
                refine ⟨19829867641693127590574819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13219911761128751727049879 19829867641693127590574819)
                ·
                  refine ⟨29744801462539691385862229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19829867641693127590574819 29744801462539691385862229)
                  ·
                    refine ⟨348571892139137008428073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29744801462539691385862229 348571892139137008428073)
                    ·
                      refine ⟨261428919104352756321055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348571892139137008428073 261428919104352756321055)
                      ·
                        rfl

theorem cell23_509131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8, 2].length) (baseStart_509131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509131 prefixEnd_509131 := by exact prefixLift 509131
  have htrace : WordTrace (prefixWord ++ tailWord_509131) baseStart_509131 baseEnd_509131 := by
    simpa [prefixWord, tailWord_509131, baseEnd_509131] using wordTrace_append hprefix tailTrace_509131
  have hstable : (prefixWord ++ tailWord_509131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509131).length < 2 ^ (prefixWord ++ tailWord_509131).sum := by decide
  have hdescent : baseEnd_509131 < baseStart_509131 := by decide
  rcases family_descends (prefixWord ++ tailWord_509131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509182 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_509182 : Nat := 118140960795 + 509182 * 2 ^ 59
def prefixEnd_509182 : Nat := 4983230072969 + 3 ^ 40 * 509182 * 2
def baseEnd_509182 : Nat := 261455106617732056783321

theorem tailTrace_509182 : CollatzResearch.WordTrace tailWord_509182 prefixEnd_509182 261455106617732056783321 := by
  unfold tailWord_509182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321424155166006275920225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12380928827552033471574533 2321424155166006275920225)
  ·
    refine ⟨1741068116374504706940169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2321424155166006275920225 1741068116374504706940169)
    ·
      refine ⟨1305801087280878530205127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1741068116374504706940169 1305801087280878530205127)
      ·
        refine ⟨1958701630921317795307691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305801087280878530205127 1958701630921317795307691)
        ·
          refine ⟨2938052446381976692961537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958701630921317795307691 2938052446381976692961537)
          ·
            refine ⟨2203539334786482519721153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938052446381976692961537 2203539334786482519721153)
            ·
              refine ⟨1652654501089861889790865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203539334786482519721153 1652654501089861889790865)
              ·
                refine ⟨1239490875817396417343149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652654501089861889790865 1239490875817396417343149)
                ·
                  refine ⟨464809078431523656503681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239490875817396417343149 464809078431523656503681)
                  ·
                    refine ⟨348606808823642742377761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464809078431523656503681 348606808823642742377761)
                    ·
                      refine ⟨261455106617732056783321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348606808823642742377761 261455106617732056783321)
                      ·
                        rfl

theorem cell23_509182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_509182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509182 prefixEnd_509182 := by exact prefixLift 509182
  have htrace : WordTrace (prefixWord ++ tailWord_509182) baseStart_509182 baseEnd_509182 := by
    simpa [prefixWord, tailWord_509182, baseEnd_509182] using wordTrace_append hprefix tailTrace_509182
  have hstable : (prefixWord ++ tailWord_509182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509182).length < 2 ^ (prefixWord ++ tailWord_509182).sum := by decide
  have hdescent : baseEnd_509182 < baseStart_509182 := by decide
  rcases family_descends (prefixWord ++ tailWord_509182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509185 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_509185 : Nat := 118140960795 + 509185 * 2 ^ 59
def prefixEnd_509185 : Nat := 4983230072969 + 3 ^ 40 * 509185 * 2
def baseEnd_509185 : Nat := 261456647059695545045807

theorem tailTrace_509185 : CollatzResearch.WordTrace tailWord_509185 prefixEnd_509185 261456647059695545045807 := by
  unfold tailWord_509185
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571502660317181719721009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12381001773544787813147339 18571502660317181719721009)
  ·
    refine ⟨13928626995237886289790757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18571502660317181719721009 13928626995237886289790757)
    ·
      refine ⟨2611617561607103679335767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13928626995237886289790757 2611617561607103679335767)
      ·
        refine ⟨3917426342410655519003651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611617561607103679335767 3917426342410655519003651)
        ·
          refine ⟨5876139513615983278505477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917426342410655519003651 5876139513615983278505477)
          ·
            refine ⟨1101776158802996864719777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5876139513615983278505477 1101776158802996864719777)
            ·
              refine ⟨826332119102247648539833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101776158802996864719777 826332119102247648539833)
              ·
                refine ⟨619749089326685736404875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826332119102247648539833 619749089326685736404875)
                ·
                  refine ⟨929623633990028604607313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619749089326685736404875 929623633990028604607313)
                  ·
                    refine ⟨697217725492521453455485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 929623633990028604607313 697217725492521453455485)
                    ·
                      refine ⟨261456647059695545045807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 697217725492521453455485 261456647059695545045807)
                      ·
                        rfl

theorem cell23_509185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_509185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509185 prefixEnd_509185 := by exact prefixLift 509185
  have htrace : WordTrace (prefixWord ++ tailWord_509185) baseStart_509185 baseEnd_509185 := by
    simpa [prefixWord, tailWord_509185, baseEnd_509185] using wordTrace_append hprefix tailTrace_509185
  have hstable : (prefixWord ++ tailWord_509185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509185).length < 2 ^ (prefixWord ++ tailWord_509185).sum := by decide
  have hdescent : baseEnd_509185 < baseStart_509185 := by decide
  rcases family_descends (prefixWord ++ tailWord_509185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509188 : List Nat := [2, 3, 2, 2, 2, 1, 4, 7]
def baseStart_509188 : Nat := 118140960795 + 509188 * 2 ^ 59
def prefixEnd_509188 : Nat := 4983230072969 + 3 ^ 40 * 509188 * 2
def baseEnd_509188 : Nat := 9683636574135519752159

theorem tailTrace_509188 : CollatzResearch.WordTrace tailWord_509188 prefixEnd_509188 9683636574135519752159 := by
  unfold tailWord_509188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285806039653156616040109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12381074719537542154720145 9285806039653156616040109)
  ·
    refine ⟨3482177264869933731015041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9285806039653156616040109 3482177264869933731015041)
    ·
      refine ⟨2611632948652450298261281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3482177264869933731015041 2611632948652450298261281)
      ·
        refine ⟨1958724711489337723695961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2611632948652450298261281 1958724711489337723695961)
        ·
          refine ⟨1469043533617003292771971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958724711489337723695961 1469043533617003292771971)
          ·
            refine ⟨2203565300425504939157957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469043533617003292771971 2203565300425504939157957)
            ·
              refine ⟨413168493829782176092117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2203565300425504939157957 413168493829782176092117)
              ·
                refine ⟨9683636574135519752159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 413168493829782176092117 9683636574135519752159)
                ·
                  rfl

theorem cell23_509188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 7].length) (baseStart_509188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509188 prefixEnd_509188 := by exact prefixLift 509188
  have htrace : WordTrace (prefixWord ++ tailWord_509188) baseStart_509188 baseEnd_509188 := by
    simpa [prefixWord, tailWord_509188, baseEnd_509188] using wordTrace_append hprefix tailTrace_509188
  have hstable : (prefixWord ++ tailWord_509188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509188).length < 2 ^ (prefixWord ++ tailWord_509188).sum := by decide
  have hdescent : baseEnd_509188 < baseStart_509188 := by decide
  rcases family_descends (prefixWord ++ tailWord_509188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509202 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_509202 : Nat := 118140960795 + 509202 * 2 ^ 59
def prefixEnd_509202 : Nat := 4983230072969 + 3 ^ 40 * 509202 * 2
def baseEnd_509202 : Nat := 261465376230821978533229

theorem tailTrace_509202 : CollatzResearch.WordTrace tailWord_509202 prefixEnd_509202 261465376230821978533229 := by
  unfold tailWord_509202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643030675313898405772465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12381415134170395748726573 4643030675313898405772465)
  ·
    refine ⟨3482273006485423804329349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4643030675313898405772465 3482273006485423804329349)
    ·
      refine ⟨652926188716016963311753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3482273006485423804329349 652926188716016963311753)
      ·
        refine ⟨489694641537012722483815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652926188716016963311753 489694641537012722483815)
        ·
          refine ⟨734541962305519083725723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489694641537012722483815 734541962305519083725723)
          ·
            refine ⟨1101812943458278625588585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734541962305519083725723 1101812943458278625588585)
            ·
              refine ⟨826359707593708969191439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101812943458278625588585 826359707593708969191439)
              ·
                refine ⟨1239539561390563453787159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826359707593708969191439 1239539561390563453787159)
                ·
                  refine ⟨1859309342085845180680739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239539561390563453787159 1859309342085845180680739)
                  ·
                    refine ⟨2788964013128767771021109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1859309342085845180680739 2788964013128767771021109)
                    ·
                      refine ⟨261465376230821978533229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2788964013128767771021109 261465376230821978533229)
                      ·
                        rfl

theorem cell23_509202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_509202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509202 prefixEnd_509202 := by exact prefixLift 509202
  have htrace : WordTrace (prefixWord ++ tailWord_509202) baseStart_509202 baseEnd_509202 := by
    simpa [prefixWord, tailWord_509202, baseEnd_509202] using wordTrace_append hprefix tailTrace_509202
  have hstable : (prefixWord ++ tailWord_509202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509202).length < 2 ^ (prefixWord ++ tailWord_509202).sum := by decide
  have hdescent : baseEnd_509202 < baseStart_509202 := by decide
  rcases family_descends (prefixWord ++ tailWord_509202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509216 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 1, 2, 2]
def baseStart_509216 : Nat := 118140960795 + 509216 * 2 ^ 59
def prefixEnd_509216 : Nat := 4983230072969 + 3 ^ 40 * 509216 * 2
def baseEnd_509216 : Nat := 261472564959984923758165

theorem tailTrace_509216 : CollatzResearch.WordTrace tailWord_509216 prefixEnd_509216 261472564959984923758165 := by
  unfold tailWord_509216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9286316661602437007049751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12381755548803249342733001 9286316661602437007049751)
  ·
    refine ⟨13929474992403655510574627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9286316661602437007049751 13929474992403655510574627)
    ·
      refine ⟨20894212488605483265861941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13929474992403655510574627 20894212488605483265861941)
      ·
        refine ⟨1958832420806764056174557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20894212488605483265861941 1958832420806764056174557)
        ·
          refine ⟨734562157802536521065459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1958832420806764056174557 734562157802536521065459)
          ·
            refine ⟨1101843236703804781598189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734562157802536521065459 1101843236703804781598189)
            ·
              refine ⟨413191213763926793099321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1101843236703804781598189 413191213763926793099321)
              ·
                refine ⟨309893410322945094824491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413191213763926793099321 309893410322945094824491)
                ·
                  refine ⟨464840115484417642236737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309893410322945094824491 464840115484417642236737)
                  ·
                    refine ⟨348630086613313231677553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464840115484417642236737 348630086613313231677553)
                    ·
                      refine ⟨261472564959984923758165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348630086613313231677553 261472564959984923758165)
                      ·
                        rfl

theorem cell23_509216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_509216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509216 prefixEnd_509216 := by exact prefixLift 509216
  have htrace : WordTrace (prefixWord ++ tailWord_509216) baseStart_509216 baseEnd_509216 := by
    simpa [prefixWord, tailWord_509216, baseEnd_509216] using wordTrace_append hprefix tailTrace_509216
  have hstable : (prefixWord ++ tailWord_509216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509216).length < 2 ^ (prefixWord ++ tailWord_509216).sum := by decide
  have hdescent : baseEnd_509216 < baseStart_509216 := by decide
  rcases family_descends (prefixWord ++ tailWord_509216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509251 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_509251 : Nat := 118140960795 + 509251 * 2 ^ 59
def prefixEnd_509251 : Nat := 4983230072969 + 3 ^ 40 * 509251 * 2
def baseEnd_509251 : Nat := 261490536782892286820503

theorem tailTrace_509251 : CollatzResearch.WordTrace tailWord_509251 prefixEnd_509251 261490536782892286820503 := by
  unfold tailWord_509251
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573909878078074991623607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12382606585385383327749071 18573909878078074991623607)
  ·
    refine ⟨27860864817117112487435411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18573909878078074991623607 27860864817117112487435411)
    ·
      refine ⟨41791297225675668731153117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27860864817117112487435411 41791297225675668731153117)
      ·
        refine ⟨15671736459628375774182419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41791297225675668731153117 15671736459628375774182419)
        ·
          refine ⟨23507604689442563661273629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15671736459628375774182419 23507604689442563661273629)
          ·
            refine ⟨8815351758540961372977611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23507604689442563661273629 8815351758540961372977611)
            ·
              refine ⟨13223027637811442059466417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815351758540961372977611 13223027637811442059466417)
              ·
                refine ⟨9917270728358581544599813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13223027637811442059466417 9917270728358581544599813)
                ·
                  refine ⟨1859488261567234039612465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9917270728358581544599813 1859488261567234039612465)
                  ·
                    refine ⟨1394616196175425529709349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859488261567234039612465 1394616196175425529709349)
                    ·
                      refine ⟨261490536782892286820503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1394616196175425529709349 261490536782892286820503)
                      ·
                        rfl

theorem cell23_509251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_509251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509251 prefixEnd_509251 := by exact prefixLift 509251
  have htrace : WordTrace (prefixWord ++ tailWord_509251) baseStart_509251 baseEnd_509251 := by
    simpa [prefixWord, tailWord_509251, baseEnd_509251] using wordTrace_append hprefix tailTrace_509251
  have hstable : (prefixWord ++ tailWord_509251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509251).length < 2 ^ (prefixWord ++ tailWord_509251).sum := by decide
  have hdescent : baseEnd_509251 < baseStart_509251 := by decide
  rcases family_descends (prefixWord ++ tailWord_509251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509255 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_509255 : Nat := 118140960795 + 509255 * 2 ^ 59
def prefixEnd_509255 : Nat := 4983230072969 + 3 ^ 40 * 509255 * 2
def baseEnd_509255 : Nat := 261492590705510271170485

theorem tailTrace_509255 : CollatzResearch.WordTrace tailWord_509255 prefixEnd_509255 261492590705510271170485 := by
  unfold tailWord_509255
  simp only [CollatzResearch.WordTrace]
  refine ⟨18574055770063583674769219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12382703846709055783179479 18574055770063583674769219)
  ·
    refine ⟨27861083655095375512153829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18574055770063583674769219 27861083655095375512153829)
    ·
      refine ⟨5223953185330382908528843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27861083655095375512153829 5223953185330382908528843)
      ·
        refine ⟨7835929777995574362793265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223953185330382908528843 7835929777995574362793265)
        ·
          refine ⟨5876947333496680772094949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7835929777995574362793265 5876947333496680772094949)
          ·
            refine ⟨1101927625030627644767803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5876947333496680772094949 1101927625030627644767803)
            ·
              refine ⟨1652891437545941467151705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101927625030627644767803 1652891437545941467151705)
              ·
                refine ⟨1239668578159456100363779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652891437545941467151705 1239668578159456100363779)
                ·
                  refine ⟨1859502867239184150545669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239668578159456100363779 1859502867239184150545669)
                  ·
                    refine ⟨348656787607347028227313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859502867239184150545669 348656787607347028227313)
                    ·
                      refine ⟨261492590705510271170485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348656787607347028227313 261492590705510271170485)
                      ·
                        rfl

theorem cell23_509255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_509255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509255 prefixEnd_509255 := by exact prefixLift 509255
  have htrace : WordTrace (prefixWord ++ tailWord_509255) baseStart_509255 baseEnd_509255 := by
    simpa [prefixWord, tailWord_509255, baseEnd_509255] using wordTrace_append hprefix tailTrace_509255
  have hstable : (prefixWord ++ tailWord_509255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509255).length < 2 ^ (prefixWord ++ tailWord_509255).sum := by decide
  have hdescent : baseEnd_509255 < baseStart_509255 := by decide
  rcases family_descends (prefixWord ++ tailWord_509255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509268 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_509268 : Nat := 118140960795 + 509268 * 2 ^ 59
def prefixEnd_509268 : Nat := 4983230072969 + 3 ^ 40 * 509268 * 2
def baseEnd_509268 : Nat := 261499265954018720307925

theorem tailTrace_509268 : CollatzResearch.WordTrace tailWord_509268 prefixEnd_509268 261499265954018720307925 := by
  unfold tailWord_509268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287264959508243447496229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12383019946010991263328305 9287264959508243447496229)
  ·
    refine ⟨1741362179907795646405543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9287264959508243447496229 1741362179907795646405543)
    ·
      refine ⟨2612043269861693469608315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1741362179907795646405543 2612043269861693469608315)
      ·
        refine ⟨3918064904792540204412473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612043269861693469608315 3918064904792540204412473)
        ·
          refine ⟨2938548678594405153309355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3918064904792540204412473 2938548678594405153309355)
          ·
            refine ⟨4407823017891607729964033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938548678594405153309355 4407823017891607729964033)
            ·
              refine ⟨3305867263418705797473025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4407823017891607729964033 3305867263418705797473025)
              ·
                refine ⟨2479400447564029348104769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3305867263418705797473025 2479400447564029348104769)
                ·
                  refine ⟨1859550335673022011078577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2479400447564029348104769 1859550335673022011078577)
                  ·
                    refine ⟨1394662751754766508308933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859550335673022011078577 1394662751754766508308933)
                    ·
                      refine ⟨261499265954018720307925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1394662751754766508308933 261499265954018720307925)
                      ·
                        rfl

theorem cell23_509268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_509268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509268 prefixEnd_509268 := by exact prefixLift 509268
  have htrace : WordTrace (prefixWord ++ tailWord_509268) baseStart_509268 baseEnd_509268 := by
    simpa [prefixWord, tailWord_509268, baseEnd_509268] using wordTrace_append hprefix tailTrace_509268
  have hstable : (prefixWord ++ tailWord_509268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509268).length < 2 ^ (prefixWord ++ tailWord_509268).sum := by decide
  have hdescent : baseEnd_509268 < baseStart_509268 := by decide
  rcases family_descends (prefixWord ++ tailWord_509268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509272 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_509272 : Nat := 118140960795 + 509272 * 2 ^ 59
def prefixEnd_509272 : Nat := 4983230072969 + 3 ^ 40 * 509272 * 2
def baseEnd_509272 : Nat := 261501319876636704657907

theorem tailTrace_509272 : CollatzResearch.WordTrace tailWord_509272 prefixEnd_509272 261501319876636704657907 := by
  unfold tailWord_509272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287337905500997789069035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12383117207334663718758713 9287337905500997789069035)
  ·
    refine ⟨13931006858251496683603553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9287337905500997789069035 13931006858251496683603553)
    ·
      refine ⟨10448255143688622512702665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13931006858251496683603553 10448255143688622512702665)
      ·
        refine ⟨7836191357766466884526999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10448255143688622512702665 7836191357766466884526999)
        ·
          refine ⟨11754287036649700326790499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836191357766466884526999 11754287036649700326790499)
          ·
            refine ⟨17631430554974550490185749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754287036649700326790499 17631430554974550490185749)
            ·
              refine ⟨826473307264432054227457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17631430554974550490185749 826473307264432054227457)
              ·
                refine ⟨619854980448324040670593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826473307264432054227457 619854980448324040670593)
                ·
                  refine ⟨464891235336243030502945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 619854980448324040670593 464891235336243030502945)
                  ·
                    refine ⟨348668426502182272877209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464891235336243030502945 348668426502182272877209)
                    ·
                      refine ⟨261501319876636704657907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348668426502182272877209 261501319876636704657907)
                      ·
                        rfl

theorem cell23_509272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_509272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509272 prefixEnd_509272 := by exact prefixLift 509272
  have htrace : WordTrace (prefixWord ++ tailWord_509272) baseStart_509272 baseEnd_509272 := by
    simpa [prefixWord, tailWord_509272, baseEnd_509272] using wordTrace_append hprefix tailTrace_509272
  have hstable : (prefixWord ++ tailWord_509272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509272).length < 2 ^ (prefixWord ++ tailWord_509272).sum := by decide
  have hdescent : baseEnd_509272 < baseStart_509272 := by decide
  rcases family_descends (prefixWord ++ tailWord_509272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509310 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_509310 : Nat := 118140960795 + 509310 * 2 ^ 59
def prefixEnd_509310 : Nat := 4983230072969 + 3 ^ 40 * 509310 * 2
def baseEnd_509310 : Nat := 261520832141507555982733

theorem tailTrace_509310 : CollatzResearch.WordTrace tailWord_509310 prefixEnd_509310 261520832141507555982733 := by
  unfold tailWord_509310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322007723108041008502673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12384041189909552045347589 2322007723108041008502673)
  ·
    refine ⟨1741505792331030756377005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2322007723108041008502673 1741505792331030756377005)
    ·
      refine ⟨653064672124136533641377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1741505792331030756377005 653064672124136533641377)
      ·
        refine ⟨489798504093102400231033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653064672124136533641377 489798504093102400231033)
        ·
          refine ⟨367348878069826800173275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489798504093102400231033 367348878069826800173275)
          ·
            refine ⟨551023317104740200259913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367348878069826800173275 551023317104740200259913)
            ·
              refine ⟨413267487828555150194935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551023317104740200259913 413267487828555150194935)
              ·
                refine ⟨619901231742832725292403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413267487828555150194935 619901231742832725292403)
                ·
                  refine ⟨929851847614249087938605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619901231742832725292403 929851847614249087938605)
                  ·
                    refine ⟨348694442855343407976977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929851847614249087938605 348694442855343407976977)
                    ·
                      refine ⟨261520832141507555982733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348694442855343407976977 261520832141507555982733)
                      ·
                        rfl

theorem cell23_509310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_509310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509310 prefixEnd_509310 := by exact prefixLift 509310
  have htrace : WordTrace (prefixWord ++ tailWord_509310) baseStart_509310 baseEnd_509310 := by
    simpa [prefixWord, tailWord_509310, baseEnd_509310] using wordTrace_append hprefix tailTrace_509310
  have hstable : (prefixWord ++ tailWord_509310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509310).length < 2 ^ (prefixWord ++ tailWord_509310).sum := by decide
  have hdescent : baseEnd_509310 < baseStart_509310 := by decide
  rcases family_descends (prefixWord ++ tailWord_509310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509365 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_509365 : Nat := 118140960795 + 509365 * 2 ^ 59
def prefixEnd_509365 : Nat := 4983230072969 + 3 ^ 40 * 509365 * 2
def baseEnd_509365 : Nat := 261549073577504840794979

theorem tailTrace_509365 : CollatzResearch.WordTrace tailWord_509365 prefixEnd_509365 261549073577504840794979 := by
  unfold tailWord_509365
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578067799665072461273549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12385378533110048307515699 18578067799665072461273549)
  ·
    refine ⟨6966775424874402172977581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18578067799665072461273549 6966775424874402172977581)
    ·
      refine ⟨2612540784327900814866593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6966775424874402172977581 2612540784327900814866593)
      ·
        refine ⟨1959405588245925611149945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2612540784327900814866593 1959405588245925611149945)
        ·
          refine ⟨1469554191184444208362459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959405588245925611149945 1469554191184444208362459)
          ·
            refine ⟨2204331286776666312543689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469554191184444208362459 2204331286776666312543689)
            ·
              refine ⟨1653248465082499734407767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204331286776666312543689 1653248465082499734407767)
              ·
                refine ⟨2479872697623749601611651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653248465082499734407767 2479872697623749601611651)
                ·
                  refine ⟨3719809046435624402417477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479872697623749601611651 3719809046435624402417477)
                  ·
                    refine ⟨697464196206679575453277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719809046435624402417477 697464196206679575453277)
                    ·
                      refine ⟨261549073577504840794979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 697464196206679575453277 261549073577504840794979)
                      ·
                        rfl

theorem cell23_509365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_509365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509365 prefixEnd_509365 := by exact prefixLift 509365
  have htrace : WordTrace (prefixWord ++ tailWord_509365) baseStart_509365 baseEnd_509365 := by
    simpa [prefixWord, tailWord_509365, baseEnd_509365] using wordTrace_append hprefix tailTrace_509365
  have hstable : (prefixWord ++ tailWord_509365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509365).length < 2 ^ (prefixWord ++ tailWord_509365).sum := by decide
  have hdescent : baseEnd_509365 < baseStart_509365 := by decide
  rcases family_descends (prefixWord ++ tailWord_509365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509402 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_509402 : Nat := 118140960795 + 509402 * 2 ^ 59
def prefixEnd_509402 : Nat := 4983230072969 + 3 ^ 40 * 509402 * 2
def baseEnd_509402 : Nat := 29063119151302355114701

theorem tailTrace_509402 : CollatzResearch.WordTrace tailWord_509402 prefixEnd_509402 29063119151302355114701 := by
  unfold tailWord_509402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4644854325132756945092615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12386278200354018520246973 4644854325132756945092615)
  ·
    refine ⟨6967281487699135417638923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4644854325132756945092615 6967281487699135417638923)
    ·
      refine ⟨10450922231548703126458385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967281487699135417638923 10450922231548703126458385)
      ·
        refine ⟨7838191673661527344843789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10450922231548703126458385 7838191673661527344843789)
        ·
          refine ⟨2939321877623072754316421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7838191673661527344843789 2939321877623072754316421)
          ·
            refine ⟨551122852054326141434329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2939321877623072754316421 551122852054326141434329)
            ·
              refine ⟨413342139040744606075747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551122852054326141434329 413342139040744606075747)
              ·
                refine ⟨620013208561116909113621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413342139040744606075747 620013208561116909113621)
                ·
                  refine ⟨29063119151302355114701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 620013208561116909113621 29063119151302355114701)
                  ·
                    rfl

theorem cell23_509402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_509402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509402 prefixEnd_509402 := by exact prefixLift 509402
  have htrace : WordTrace (prefixWord ++ tailWord_509402) baseStart_509402 baseEnd_509402 := by
    simpa [prefixWord, tailWord_509402, baseEnd_509402] using wordTrace_append hprefix tailTrace_509402
  have hstable : (prefixWord ++ tailWord_509402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509402).length < 2 ^ (prefixWord ++ tailWord_509402).sum := by decide
  have hdescent : baseEnd_509402 < baseStart_509402 := by decide
  rcases family_descends (prefixWord ++ tailWord_509402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509415 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 3, 5]
def baseStart_509415 : Nat := 118140960795 + 509415 * 2 ^ 59
def prefixEnd_509415 : Nat := 4983230072969 + 3 ^ 40 * 509415 * 2
def baseEnd_509415 : Nat := 87191582536743215056583

theorem tailTrace_509415 : CollatzResearch.WordTrace tailWord_509415 prefixEnd_509415 87191582536743215056583 := by
  unfold tailWord_509415
  simp only [CollatzResearch.WordTrace]
  refine ⟨18579891449483931000593699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12386594299655954000395799 18579891449483931000593699)
  ·
    refine ⟨27869837174225896500890549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18579891449483931000593699 27869837174225896500890549)
    ·
      refine ⟨2612797235083677796958489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27869837174225896500890549 2612797235083677796958489)
      ·
        refine ⟨1959597926312758347718867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2612797235083677796958489 1959597926312758347718867)
        ·
          refine ⟨2939396889469137521578301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959597926312758347718867 2939396889469137521578301)
          ·
            refine ⟨1102273833550926570591863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2939396889469137521578301 1102273833550926570591863)
            ·
              refine ⟨1653410750326389855887795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102273833550926570591863 1653410750326389855887795)
              ·
                refine ⟨2480116125489584783831693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653410750326389855887795 2480116125489584783831693)
                ·
                  refine ⟨930043547058594293936885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2480116125489584783831693 930043547058594293936885)
                  ·
                    refine ⟨87191582536743215056583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 930043547058594293936885 87191582536743215056583)
                    ·
                      rfl

theorem cell23_509415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_509415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509415 prefixEnd_509415 := by exact prefixLift 509415
  have htrace : WordTrace (prefixWord ++ tailWord_509415) baseStart_509415 baseEnd_509415 := by
    simpa [prefixWord, tailWord_509415, baseEnd_509415] using wordTrace_append hprefix tailTrace_509415
  have hstable : (prefixWord ++ tailWord_509415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509415).length < 2 ^ (prefixWord ++ tailWord_509415).sum := by decide
  have hdescent : baseEnd_509415 < baseStart_509415 := by decide
  rcases family_descends (prefixWord ++ tailWord_509415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509432 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 1, 5]
def baseStart_509432 : Nat := 118140960795 + 509432 * 2 ^ 59
def prefixEnd_509432 : Nat := 4983230072969 + 3 ^ 40 * 509432 * 2
def baseEnd_509432 : Nat := 87194492260452026219057

theorem tailTrace_509432 : CollatzResearch.WordTrace tailWord_509432 prefixEnd_509432 87194492260452026219057 := by
  unfold tailWord_509432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290255745211171451981275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12387007660281561935975033 9290255745211171451981275)
  ·
    refine ⟨13935383617816757177971913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290255745211171451981275 13935383617816757177971913)
    ·
      refine ⟨10451537713362567883478935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13935383617816757177971913 10451537713362567883478935)
      ·
        refine ⟨15677306570043851825218403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451537713362567883478935 15677306570043851825218403)
        ·
          refine ⟨23515959855065777737827605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677306570043851825218403 23515959855065777737827605)
          ·
            refine ⟨1102310618206208331460669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23515959855065777737827605 1102310618206208331460669)
            ·
              refine ⟨413366481827328124297751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102310618206208331460669 413366481827328124297751)
              ·
                refine ⟨620049722740992186446627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413366481827328124297751 620049722740992186446627)
                ·
                  refine ⟨930074584111488279669941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620049722740992186446627 930074584111488279669941)
                  ·
                    refine ⟨87194492260452026219057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 930074584111488279669941 87194492260452026219057)
                    ·
                      rfl

theorem cell23_509432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_509432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509432 prefixEnd_509432 := by exact prefixLift 509432
  have htrace : WordTrace (prefixWord ++ tailWord_509432) baseStart_509432 baseEnd_509432 := by
    simpa [prefixWord, tailWord_509432, baseEnd_509432] using wordTrace_append hprefix tailTrace_509432
  have hstable : (prefixWord ++ tailWord_509432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509432).length < 2 ^ (prefixWord ++ tailWord_509432).sum := by decide
  have hdescent : baseEnd_509432 < baseStart_509432 := by decide
  rcases family_descends (prefixWord ++ tailWord_509432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509448 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_509448 : Nat := 118140960795 + 509448 * 2 ^ 59
def prefixEnd_509448 : Nat := 4983230072969 + 3 ^ 40 * 509448 * 2
def baseEnd_509448 : Nat := 261591692471828016057097

theorem tailTrace_509448 : CollatzResearch.WordTrace tailWord_509448 prefixEnd_509448 261591692471828016057097 := by
  unfold tailWord_509448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290547529182188818272499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12387396705576251757696665 9290547529182188818272499)
  ·
    refine ⟨13935821293773283227408749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290547529182188818272499 13935821293773283227408749)
    ·
      refine ⟨5225932985164981210278281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13935821293773283227408749 5225932985164981210278281)
      ·
        refine ⟨3919449738873735907708711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5225932985164981210278281 3919449738873735907708711)
        ·
          refine ⟨5879174608310603861563067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919449738873735907708711 5879174608310603861563067)
          ·
            refine ⟨8818761912465905792344601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879174608310603861563067 8818761912465905792344601)
            ·
              refine ⟨6614071434349429344258451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8818761912465905792344601 6614071434349429344258451)
              ·
                refine ⟨9921107151524144016387677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6614071434349429344258451 9921107151524144016387677)
                ·
                  refine ⟨3720415181821554006145379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9921107151524144016387677 3720415181821554006145379)
                  ·
                    refine ⟨5580622772732331009218069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720415181821554006145379 5580622772732331009218069)
                    ·
                      refine ⟨261591692471828016057097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5580622772732331009218069 261591692471828016057097)
                      ·
                        rfl

theorem cell23_509448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_509448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509448 prefixEnd_509448 := by exact prefixLift 509448
  have htrace : WordTrace (prefixWord ++ tailWord_509448) baseStart_509448 baseEnd_509448 := by
    simpa [prefixWord, tailWord_509448, baseEnd_509448] using wordTrace_append hprefix tailTrace_509448
  have hstable : (prefixWord ++ tailWord_509448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509448).length < 2 ^ (prefixWord ++ tailWord_509448).sum := by decide
  have hdescent : baseEnd_509448 < baseStart_509448 := by decide
  rcases family_descends (prefixWord ++ tailWord_509448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509469 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_509469 : Nat := 118140960795 + 509469 * 2 ^ 59
def prefixEnd_509469 : Nat := 4983230072969 + 3 ^ 40 * 509469 * 2
def baseEnd_509469 : Nat := 261602475565572433894501

theorem tailTrace_509469 : CollatzResearch.WordTrace tailWord_509469 prefixEnd_509469 261602475565572433894501 := by
  unfold tailWord_509469
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581860991288298223059461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12387907327525532148706307 18581860991288298223059461)
  ·
    refine ⟨3484098935866555916823649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18581860991288298223059461 3484098935866555916823649)
    ·
      refine ⟨2613074201899916937617737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3484098935866555916823649 2613074201899916937617737)
      ·
        refine ⟨1959805651424937703213303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613074201899916937617737 1959805651424937703213303)
        ·
          refine ⟨2939708477137406554819955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959805651424937703213303 2939708477137406554819955)
          ·
            refine ⟨4409562715706109832229933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939708477137406554819955 4409562715706109832229933)
            ·
              refine ⟨1653586018389791187086225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409562715706109832229933 1653586018389791187086225)
              ·
                refine ⟨1240189513792343390314669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653586018389791187086225 1240189513792343390314669)
                ·
                  refine ⟨465071067672128771368001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240189513792343390314669 465071067672128771368001)
                  ·
                    refine ⟨348803300754096578526001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465071067672128771368001 348803300754096578526001)
                    ·
                      refine ⟨261602475565572433894501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348803300754096578526001 261602475565572433894501)
                      ·
                        rfl

theorem cell23_509469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_509469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509469 prefixEnd_509469 := by exact prefixLift 509469
  have htrace : WordTrace (prefixWord ++ tailWord_509469) baseStart_509469 baseEnd_509469 := by
    simpa [prefixWord, tailWord_509469, baseEnd_509469] using wordTrace_append hprefix tailTrace_509469
  have hstable : (prefixWord ++ tailWord_509469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509469).length < 2 ^ (prefixWord ++ tailWord_509469).sum := by decide
  have hdescent : baseEnd_509469 < baseStart_509469 := by decide
  rcases family_descends (prefixWord ++ tailWord_509469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509472 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_509472 : Nat := 118140960795 + 509472 * 2 ^ 59
def prefixEnd_509472 : Nat := 4983230072969 + 3 ^ 40 * 509472 * 2
def baseEnd_509472 : Nat := 261604016007535922156987

theorem tailTrace_509472 : CollatzResearch.WordTrace tailWord_509472 prefixEnd_509472 261604016007535922156987 := by
  unfold tailWord_509472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290985205138714867709335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12387980273518286490279113 9290985205138714867709335)
  ·
    refine ⟨13936477807708072301564003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290985205138714867709335 13936477807708072301564003)
    ·
      refine ⟨20904716711562108452346005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13936477807708072301564003 20904716711562108452346005)
      ·
        refine ⟨979908595854473833703719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20904716711562108452346005 979908595854473833703719)
        ·
          refine ⟨1469862893781710750555579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979908595854473833703719 1469862893781710750555579)
          ·
            refine ⟨2204794340672566125833369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469862893781710750555579 2204794340672566125833369)
            ·
              refine ⟨1653595755504424594375027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204794340672566125833369 1653595755504424594375027)
              ·
                refine ⟨2480393633256636891562541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653595755504424594375027 2480393633256636891562541)
                ·
                  refine ⟨930147612471238834335953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2480393633256636891562541 930147612471238834335953)
                  ·
                    refine ⟨697610709353429125751965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 930147612471238834335953 697610709353429125751965)
                    ·
                      refine ⟨261604016007535922156987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 697610709353429125751965 261604016007535922156987)
                      ·
                        rfl

theorem cell23_509472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_509472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509472 prefixEnd_509472 := by exact prefixLift 509472
  have htrace : WordTrace (prefixWord ++ tailWord_509472) baseStart_509472 baseEnd_509472 := by
    simpa [prefixWord, tailWord_509472, baseEnd_509472] using wordTrace_append hprefix tailTrace_509472
  have hstable : (prefixWord ++ tailWord_509472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509472).length < 2 ^ (prefixWord ++ tailWord_509472).sum := by decide
  have hdescent : baseEnd_509472 < baseStart_509472 := by decide
  rcases family_descends (prefixWord ++ tailWord_509472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509486 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_509486 : Nat := 118140960795 + 509486 * 2 ^ 59
def prefixEnd_509486 : Nat := 4983230072969 + 3 ^ 40 * 509486 * 2
def baseEnd_509486 : Nat := 261611204736698867381923

theorem tailTrace_509486 : CollatzResearch.WordTrace tailWord_509486 prefixEnd_509486 261611204736698867381923 := by
  unfold tailWord_509486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322810129028338765803539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12388320688151140084285541 2322810129028338765803539)
  ·
    refine ⟨3484215193542508148705309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322810129028338765803539 3484215193542508148705309)
    ·
      refine ⟨1306580697578440555764491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3484215193542508148705309 1306580697578440555764491)
      ·
        refine ⟨1959871046367660833646737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306580697578440555764491 1959871046367660833646737)
        ·
          refine ⟨1469903284775745625235053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959871046367660833646737 1469903284775745625235053)
          ·
            refine ⟨551213731790904609463145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1469903284775745625235053 551213731790904609463145)
            ·
              refine ⟨413410298843178457097359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551213731790904609463145 413410298843178457097359)
              ·
                refine ⟨620115448264767685646039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413410298843178457097359 620115448264767685646039)
                ·
                  refine ⟨930173172397151528469059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620115448264767685646039 930173172397151528469059)
                  ·
                    refine ⟨1395259758595727292703589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930173172397151528469059 1395259758595727292703589)
                    ·
                      refine ⟨261611204736698867381923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1395259758595727292703589 261611204736698867381923)
                      ·
                        rfl

theorem cell23_509486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_509486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509486 prefixEnd_509486 := by exact prefixLift 509486
  have htrace : WordTrace (prefixWord ++ tailWord_509486) baseStart_509486 baseEnd_509486 := by
    simpa [prefixWord, tailWord_509486, baseEnd_509486] using wordTrace_append hprefix tailTrace_509486
  have hstable : (prefixWord ++ tailWord_509486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509486).length < 2 ^ (prefixWord ++ tailWord_509486).sum := by decide
  have hdescent : baseEnd_509486 < baseStart_509486 := by decide
  rcases family_descends (prefixWord ++ tailWord_509486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509559 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_509559 : Nat := 118140960795 + 509559 * 2 ^ 59
def prefixEnd_509559 : Nat := 4983230072969 + 3 ^ 40 * 509559 * 2
def baseEnd_509559 : Nat := 261648688824477081769087

theorem tailTrace_509559 : CollatzResearch.WordTrace tailWord_509559 prefixEnd_509559 261648688824477081769087 := by
  unfold tailWord_509559
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585143560962243593835731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12390095707308162395890487 18585143560962243593835731)
  ·
    refine ⟨27877715341443365390753597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18585143560962243593835731 27877715341443365390753597)
    ·
      refine ⟨10454143253041262021532599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27877715341443365390753597 10454143253041262021532599)
      ·
        refine ⟨15681214879561893032298899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454143253041262021532599 15681214879561893032298899)
        ·
          refine ⟨23521822319342839548448349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681214879561893032298899 23521822319342839548448349)
          ·
            refine ⟨8820683369753564830668131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23521822319342839548448349 8820683369753564830668131)
            ·
              refine ⟨13231025054630347246002197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820683369753564830668131 13231025054630347246002197)
              ·
                refine ⟨620204299435797527156353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13231025054630347246002197 620204299435797527156353)
                ·
                  refine ⟨465153224576848145367265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620204299435797527156353 465153224576848145367265)
                  ·
                    refine ⟨348864918432636109025449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465153224576848145367265 348864918432636109025449)
                    ·
                      refine ⟨261648688824477081769087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348864918432636109025449 261648688824477081769087)
                      ·
                        rfl

theorem cell23_509559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_509559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509559 prefixEnd_509559 := by exact prefixLift 509559
  have htrace : WordTrace (prefixWord ++ tailWord_509559) baseStart_509559 baseEnd_509559 := by
    simpa [prefixWord, tailWord_509559, baseEnd_509559] using wordTrace_append hprefix tailTrace_509559
  have hstable : (prefixWord ++ tailWord_509559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509559).length < 2 ^ (prefixWord ++ tailWord_509559).sum := by decide
  have hdescent : baseEnd_509559 < baseStart_509559 := by decide
  rcases family_descends (prefixWord ++ tailWord_509559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509605 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_509605 : Nat := 118140960795 + 509605 * 2 ^ 59
def prefixEnd_509605 : Nat := 4983230072969 + 3 ^ 40 * 509605 * 2
def baseEnd_509605 : Nat := 261672308934583901793875

theorem tailTrace_509605 : CollatzResearch.WordTrace tailWord_509605 prefixEnd_509605 261672308934583901793875 := by
  unfold tailWord_509605
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586821318795593450010269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12391214212530395633340179 18586821318795593450010269)
  ·
    refine ⟨6970057994548347543753851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18586821318795593450010269 6970057994548347543753851)
    ·
      refine ⟨10455086991822521315630777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970057994548347543753851 10455086991822521315630777)
      ·
        refine ⟨7841315243866890986723083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10455086991822521315630777 7841315243866890986723083)
        ·
          refine ⟨11761972865800336480084625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841315243866890986723083 11761972865800336480084625)
          ·
            refine ⟨8821479649350252360063469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761972865800336480084625 8821479649350252360063469)
            ·
              refine ⟨3308054868506344635023801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8821479649350252360063469 3308054868506344635023801)
              ·
                refine ⟨2481041151379758476267851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308054868506344635023801 2481041151379758476267851)
                ·
                  refine ⟨3721561727069637714401777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481041151379758476267851 3721561727069637714401777)
                  ·
                    refine ⟨2791171295302228285801333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3721561727069637714401777 2791171295302228285801333)
                    ·
                      refine ⟨261672308934583901793875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2791171295302228285801333 261672308934583901793875)
                      ·
                        rfl

theorem cell23_509605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_509605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509605 prefixEnd_509605 := by exact prefixLift 509605
  have htrace : WordTrace (prefixWord ++ tailWord_509605) baseStart_509605 baseEnd_509605 := by
    simpa [prefixWord, tailWord_509605, baseEnd_509605] using wordTrace_append hprefix tailTrace_509605
  have hstable : (prefixWord ++ tailWord_509605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509605).length < 2 ^ (prefixWord ++ tailWord_509605).sum := by decide
  have hdescent : baseEnd_509605 < baseStart_509605 := by decide
  rcases family_descends (prefixWord ++ tailWord_509605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509649 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_509649 : Nat := 118140960795 + 509649 * 2 ^ 59
def prefixEnd_509649 : Nat := 4983230072969 + 3 ^ 40 * 509649 * 2
def baseEnd_509649 : Nat := 261694902083381729643673

theorem tailTrace_509649 : CollatzResearch.WordTrace tailWord_509649 prefixEnd_509649 261694902083381729643673 := by
  unfold tailWord_509649
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588426130636188964612001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12392284087090792643074667 18588426130636188964612001)
  ·
    refine ⟨13941319597977141723459001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18588426130636188964612001 13941319597977141723459001)
    ·
      refine ⟨10455989698482856292594251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13941319597977141723459001 10455989698482856292594251)
      ·
        refine ⟨15683984547724284438891377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455989698482856292594251 15683984547724284438891377)
        ·
          refine ⟨11762988410793213329168533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15683984547724284438891377 11762988410793213329168533)
          ·
            refine ⟨551390081755931874804775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11762988410793213329168533 551390081755931874804775)
            ·
              refine ⟨827085122633897812207163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551390081755931874804775 827085122633897812207163)
              ·
                refine ⟨1240627683950846718310745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827085122633897812207163 1240627683950846718310745)
                ·
                  refine ⟨930470762963135038733059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1240627683950846718310745 930470762963135038733059)
                  ·
                    refine ⟨1395706144444702558099589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 930470762963135038733059 1395706144444702558099589)
                    ·
                      refine ⟨261694902083381729643673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1395706144444702558099589 261694902083381729643673)
                      ·
                        rfl

theorem cell23_509649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_509649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509649 prefixEnd_509649 := by exact prefixLift 509649
  have htrace : WordTrace (prefixWord ++ tailWord_509649) baseStart_509649 baseEnd_509649 := by
    simpa [prefixWord, tailWord_509649, baseEnd_509649] using wordTrace_append hprefix tailTrace_509649
  have hstable : (prefixWord ++ tailWord_509649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509649).length < 2 ^ (prefixWord ++ tailWord_509649).sum := by decide
  have hdescent : baseEnd_509649 < baseStart_509649 := by decide
  rcases family_descends (prefixWord ++ tailWord_509649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509655 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 8]
def baseStart_509655 : Nat := 118140960795 + 509655 * 2 ^ 59
def prefixEnd_509655 : Nat := 4983230072969 + 3 ^ 40 * 509655 * 2
def baseEnd_509655 : Nat := 29077553663034300685405

theorem tailTrace_509655 : CollatzResearch.WordTrace tailWord_509655 prefixEnd_509655 29077553663034300685405 := by
  unfold tailWord_509655
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588644968614451989330419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12392429979076301326220279 18588644968614451989330419)
  ·
    refine ⟨27882967452921677983995629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18588644968614451989330419 27882967452921677983995629)
    ·
      refine ⟨10456112794845629243998361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27882967452921677983995629 10456112794845629243998361)
      ·
        refine ⟨7842084596134221932998771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10456112794845629243998361 7842084596134221932998771)
        ·
          refine ⟨11763126894201332899498157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842084596134221932998771 11763126894201332899498157)
          ·
            refine ⟨4411172585325499837311809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11763126894201332899498157 4411172585325499837311809)
            ·
              refine ⟨3308379438994124877983857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411172585325499837311809 3308379438994124877983857)
              ·
                refine ⟨2481284579245593658487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308379438994124877983857 2481284579245593658487893)
                ·
                  refine ⟨29077553663034300685405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2481284579245593658487893 29077553663034300685405)
                  ·
                    rfl

theorem cell23_509655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 8].length) (baseStart_509655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509655 prefixEnd_509655 := by exact prefixLift 509655
  have htrace : WordTrace (prefixWord ++ tailWord_509655) baseStart_509655 baseEnd_509655 := by
    simpa [prefixWord, tailWord_509655, baseEnd_509655] using wordTrace_append hprefix tailTrace_509655
  have hstable : (prefixWord ++ tailWord_509655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509655).length < 2 ^ (prefixWord ++ tailWord_509655).sum := by decide
  have hdescent : baseEnd_509655 < baseStart_509655 := by decide
  rcases family_descends (prefixWord ++ tailWord_509655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509672 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 8]
def baseStart_509672 : Nat := 118140960795 + 509672 * 2 ^ 59
def prefixEnd_509672 : Nat := 4983230072969 + 3 ^ 40 * 509672 * 2
def baseEnd_509672 : Nat := 29078523570937237739563

theorem tailTrace_509672 : CollatzResearch.WordTrace tailWord_509672 prefixEnd_509672 29078523570937237739563 := by
  unfold tailWord_509672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294632504776431946349635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12392843339701909261799513 9294632504776431946349635)
  ·
    refine ⟨13941948757164647919524453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9294632504776431946349635 13941948757164647919524453)
    ·
      refine ⟨2614115391968371484910835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13941948757164647919524453 2614115391968371484910835)
      ·
        refine ⟨3921173087952557227366253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614115391968371484910835 3921173087952557227366253)
        ·
          refine ⟨1470439907982208960262345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3921173087952557227366253 1470439907982208960262345)
          ·
            refine ⟨1102829930986656720196759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470439907982208960262345 1102829930986656720196759)
            ·
              refine ⟨1654244896479985080295139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102829930986656720196759 1654244896479985080295139)
              ·
                refine ⟨2481367344719977620442709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654244896479985080295139 2481367344719977620442709)
                ·
                  refine ⟨29078523570937237739563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2481367344719977620442709 29078523570937237739563)
                  ·
                    rfl

theorem cell23_509672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_509672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509672 prefixEnd_509672 := by exact prefixLift 509672
  have htrace : WordTrace (prefixWord ++ tailWord_509672) baseStart_509672 baseEnd_509672 := by
    simpa [prefixWord, tailWord_509672, baseEnd_509672] using wordTrace_append hprefix tailTrace_509672
  have hstable : (prefixWord ++ tailWord_509672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509672).length < 2 ^ (prefixWord ++ tailWord_509672).sum := by decide
  have hdescent : baseEnd_509672 < baseStart_509672 := by decide
  rcases family_descends (prefixWord ++ tailWord_509672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509675 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_509675 : Nat := 118140960795 + 509675 * 2 ^ 59
def prefixEnd_509675 : Nat := 4983230072969 + 3 ^ 40 * 509675 * 2
def baseEnd_509675 : Nat := 261708252580398627918553

theorem tailTrace_509675 : CollatzResearch.WordTrace tailWord_509675 prefixEnd_509675 261708252580398627918553 := by
  unfold tailWord_509675
  simp only [CollatzResearch.WordTrace]
  refine ⟨18589374428541995405058479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12392916285694663603372319 18589374428541995405058479)
  ·
    refine ⟨27884061642812993107587719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18589374428541995405058479 27884061642812993107587719)
    ·
      refine ⟨41826092464219489661381579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27884061642812993107587719 41826092464219489661381579)
      ·
        refine ⟨62739138696329234492072369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41826092464219489661381579 62739138696329234492072369)
        ·
          refine ⟨47054354022246925869054277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62739138696329234492072369 47054354022246925869054277)
          ·
            refine ⟨8822691379171298600447677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47054354022246925869054277 8822691379171298600447677)
            ·
              refine ⟨3308509267189236975167879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8822691379171298600447677 3308509267189236975167879)
              ·
                refine ⟨4962763900783855462751819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308509267189236975167879 4962763900783855462751819)
                ·
                  refine ⟨7444145851175783194127729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962763900783855462751819 7444145851175783194127729)
                  ·
                    refine ⟨5583109388381837395595797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444145851175783194127729 5583109388381837395595797)
                    ·
                      refine ⟨261708252580398627918553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5583109388381837395595797 261708252580398627918553)
                      ·
                        rfl

theorem cell23_509675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_509675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509675 prefixEnd_509675 := by exact prefixLift 509675
  have htrace : WordTrace (prefixWord ++ tailWord_509675) baseStart_509675 baseEnd_509675 := by
    simpa [prefixWord, tailWord_509675, baseEnd_509675] using wordTrace_append hprefix tailTrace_509675
  have hstable : (prefixWord ++ tailWord_509675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509675).length < 2 ^ (prefixWord ++ tailWord_509675).sum := by decide
  have hdescent : baseEnd_509675 < baseStart_509675 := by decide
  rcases family_descends (prefixWord ++ tailWord_509675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509695 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_509695 : Nat := 118140960795 + 509695 * 2 ^ 59
def prefixEnd_509695 : Nat := 4983230072969 + 3 ^ 40 * 509695 * 2
def baseEnd_509695 : Nat := 261718522193488549668461

theorem tailTrace_509695 : CollatzResearch.WordTrace tailWord_509695 prefixEnd_509695 261718522193488549668461 := by
  unfold tailWord_509695
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590103888469538820786539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12393402592313025880524359 18590103888469538820786539)
  ·
    refine ⟨27885155832704308231179809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18590103888469538820786539 27885155832704308231179809)
    ·
      refine ⟨20913866874528231173384857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27885155832704308231179809 20913866874528231173384857)
      ·
        refine ⟨15685400155896173380038643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20913866874528231173384857 15685400155896173380038643)
        ·
          refine ⟨23528100233844260070057965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15685400155896173380038643 23528100233844260070057965)
          ·
            refine ⟨8823037587691597526271737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23528100233844260070057965 8823037587691597526271737)
            ·
              refine ⟨6617278190768698144703803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8823037587691597526271737 6617278190768698144703803)
              ·
                refine ⟨9925917286153047217055705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617278190768698144703803 9925917286153047217055705)
                ·
                  refine ⟨7444437964614785412791779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9925917286153047217055705 7444437964614785412791779)
                  ·
                    refine ⟨11166656946922178119187669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7444437964614785412791779 11166656946922178119187669)
                    ·
                      refine ⟨261718522193488549668461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11166656946922178119187669 261718522193488549668461)
                      ·
                        rfl

theorem cell23_509695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_509695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509695 prefixEnd_509695 := by exact prefixLift 509695
  have htrace : WordTrace (prefixWord ++ tailWord_509695) baseStart_509695 baseEnd_509695 := by
    simpa [prefixWord, tailWord_509695, baseEnd_509695] using wordTrace_append hprefix tailTrace_509695
  have hstable : (prefixWord ++ tailWord_509695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509695).length < 2 ^ (prefixWord ++ tailWord_509695).sum := by decide
  have hdescent : baseEnd_509695 < baseStart_509695 := by decide
  rcases family_descends (prefixWord ++ tailWord_509695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509699 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 3]
def baseStart_509699 : Nat := 118140960795 + 509699 * 2 ^ 59
def prefixEnd_509699 : Nat := 4983230072969 + 3 ^ 40 * 509699 * 2
def baseEnd_509699 : Nat := 261720576116106534018443

theorem tailTrace_509699 : CollatzResearch.WordTrace tailWord_509699 prefixEnd_509699 261720576116106534018443 := by
  unfold tailWord_509699
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590249780455047503932151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12393499853636698335954767 18590249780455047503932151)
  ·
    refine ⟨27885374670682571255898227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18590249780455047503932151 27885374670682571255898227)
    ·
      refine ⟨41828062006023856883847341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27885374670682571255898227 41828062006023856883847341)
      ·
        refine ⟨15685523252258946331442753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41828062006023856883847341 15685523252258946331442753)
        ·
          refine ⟨11764142439194209748582065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15685523252258946331442753 11764142439194209748582065)
          ·
            refine ⟨8823106829395657311436549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11764142439194209748582065 8823106829395657311436549)
            ·
              refine ⟨1654332530511685745894353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8823106829395657311436549 1654332530511685745894353)
              ·
                refine ⟨1240749397883764309420765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654332530511685745894353 1240749397883764309420765)
                ·
                  refine ⟨465281024206411616032787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240749397883764309420765 465281024206411616032787)
                  ·
                    refine ⟨697921536309617424049181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465281024206411616032787 697921536309617424049181)
                    ·
                      refine ⟨261720576116106534018443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 697921536309617424049181 261720576116106534018443)
                      ·
                        rfl

theorem cell23_509699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_509699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509699 prefixEnd_509699 := by exact prefixLift 509699
  have htrace : WordTrace (prefixWord ++ tailWord_509699) baseStart_509699 baseEnd_509699 := by
    simpa [prefixWord, tailWord_509699, baseEnd_509699] using wordTrace_append hprefix tailTrace_509699
  have hstable : (prefixWord ++ tailWord_509699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509699).length < 2 ^ (prefixWord ++ tailWord_509699).sum := by decide
  have hdescent : baseEnd_509699 < baseStart_509699 := by decide
  rcases family_descends (prefixWord ++ tailWord_509699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509719 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 1, 5]
def baseStart_509719 : Nat := 118140960795 + 509719 * 2 ^ 59
def prefixEnd_509719 : Nat := 4983230072969 + 3 ^ 40 * 509719 * 2
def baseEnd_509719 : Nat := 87243615243065485256117

theorem tailTrace_509719 : CollatzResearch.WordTrace tailWord_509719 prefixEnd_509719 87243615243065485256117 := by
  unfold tailWord_509719
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590979240382590919660211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12393986160255060613106807 18590979240382590919660211)
  ·
    refine ⟨27886468860573886379490317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18590979240382590919660211 27886468860573886379490317)
    ·
      refine ⟨10457425822715207392308869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27886468860573886379490317 10457425822715207392308869)
      ·
        refine ⟨1960767341759101386057913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10457425822715207392308869 1960767341759101386057913)
        ·
          refine ⟨1470575506319326039543435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960767341759101386057913 1470575506319326039543435)
          ·
            refine ⟨2205863259478989059315153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470575506319326039543435 2205863259478989059315153)
            ·
              refine ⟨1654397444609241794486365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205863259478989059315153 1654397444609241794486365)
              ·
                refine ⟨620399041728465672932387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654397444609241794486365 620399041728465672932387)
                ·
                  refine ⟨930598562592698509398581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620399041728465672932387 930598562592698509398581)
                  ·
                    refine ⟨87243615243065485256117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 930598562592698509398581 87243615243065485256117)
                    ·
                      rfl

theorem cell23_509719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_509719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509719 prefixEnd_509719 := by exact prefixLift 509719
  have htrace : WordTrace (prefixWord ++ tailWord_509719) baseStart_509719 baseEnd_509719 := by
    simpa [prefixWord, tailWord_509719, baseEnd_509719] using wordTrace_append hprefix tailTrace_509719
  have hstable : (prefixWord ++ tailWord_509719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509719).length < 2 ^ (prefixWord ++ tailWord_509719).sum := by decide
  have hdescent : baseEnd_509719 < baseStart_509719 := by decide
  rcases family_descends (prefixWord ++ tailWord_509719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509752 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_509752 : Nat := 118140960795 + 509752 * 2 ^ 59
def prefixEnd_509752 : Nat := 4983230072969 + 3 ^ 40 * 509752 * 2
def baseEnd_509752 : Nat := 261747790590794826655699

theorem tailTrace_509752 : CollatzResearch.WordTrace tailWord_509752 prefixEnd_509752 261747790590794826655699 := by
  unfold tailWord_509752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9296091424631518777805755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12394788566175358370407673 9296091424631518777805755)
  ·
    refine ⟨13944137136947278166708633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9296091424631518777805755 13944137136947278166708633)
    ·
      refine ⟨10458102852710458625031475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13944137136947278166708633 10458102852710458625031475)
      ·
        refine ⟨15687154279065687937547213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10458102852710458625031475 15687154279065687937547213)
        ·
          refine ⟨5882682854649632976580205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15687154279065687937547213 5882682854649632976580205)
          ·
            refine ⟨2206006070493612366217577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5882682854649632976580205 2206006070493612366217577)
            ·
              refine ⟨1654504552870209274663183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206006070493612366217577 1654504552870209274663183)
              ·
                refine ⟨2481756829305313911994775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654504552870209274663183 2481756829305313911994775)
                ·
                  refine ⟨3722635243957970867992163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481756829305313911994775 3722635243957970867992163)
                  ·
                    refine ⟨5583952865936956301988245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3722635243957970867992163 5583952865936956301988245)
                    ·
                      refine ⟨261747790590794826655699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5583952865936956301988245 261747790590794826655699)
                      ·
                        rfl

theorem cell23_509752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_509752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509752 prefixEnd_509752 := by exact prefixLift 509752
  have htrace : WordTrace (prefixWord ++ tailWord_509752) baseStart_509752 baseEnd_509752 := by
    simpa [prefixWord, tailWord_509752, baseEnd_509752] using wordTrace_append hprefix tailTrace_509752
  have hstable : (prefixWord ++ tailWord_509752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509752).length < 2 ^ (prefixWord ++ tailWord_509752).sum := by decide
  have hdescent : baseEnd_509752 < baseStart_509752 := by decide
  rcases family_descends (prefixWord ++ tailWord_509752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509753 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 1, 5]
def baseStart_509753 : Nat := 118140960795 + 509753 * 2 ^ 59
def prefixEnd_509753 : Nat := 4983230072969 + 3 ^ 40 * 509753 * 2
def baseEnd_509753 : Nat := 87249434690483107581065

theorem tailTrace_509753 : CollatzResearch.WordTrace tailWord_509753 prefixEnd_509753 87249434690483107581065 := by
  unfold tailWord_509753
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592219322259414726397913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12394812881506276484265275 18592219322259414726397913)
  ·
    refine ⟨13944164491694561044798435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18592219322259414726397913 13944164491694561044798435)
    ·
      refine ⟨20916246737541841567197653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13944164491694561044798435 20916246737541841567197653)
      ·
        refine ⟨490224532911136911731195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20916246737541841567197653 490224532911136911731195)
        ·
          refine ⟨735336799366705367596793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490224532911136911731195 735336799366705367596793)
          ·
            refine ⟨551502599525029025697595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735336799366705367596793 551502599525029025697595)
            ·
              refine ⟨827253899287543538546393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551502599525029025697595 827253899287543538546393)
              ·
                refine ⟨620440424465657653909795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827253899287543538546393 620440424465657653909795)
                ·
                  refine ⟨930660636698486480864693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620440424465657653909795 930660636698486480864693)
                  ·
                    refine ⟨87249434690483107581065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 930660636698486480864693 87249434690483107581065)
                    ·
                      rfl

theorem cell23_509753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_509753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509753 prefixEnd_509753 := by exact prefixLift 509753
  have htrace : WordTrace (prefixWord ++ tailWord_509753) baseStart_509753 baseEnd_509753 := by
    simpa [prefixWord, tailWord_509753, baseEnd_509753] using wordTrace_append hprefix tailTrace_509753
  have hstable : (prefixWord ++ tailWord_509753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509753).length < 2 ^ (prefixWord ++ tailWord_509753).sum := by decide
  have hdescent : baseEnd_509753 < baseStart_509753 := by decide
  rcases family_descends (prefixWord ++ tailWord_509753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509756 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_509756 : Nat := 118140960795 + 509756 * 2 ^ 59
def prefixEnd_509756 : Nat := 4983230072969 + 3 ^ 40 * 509756 * 2
def baseEnd_509756 : Nat := 261749844513412811005681

theorem tailTrace_509756 : CollatzResearch.WordTrace tailWord_509756 prefixEnd_509756 261749844513412811005681 := by
  unfold tailWord_509756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9296164370624273119378561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12394885827499030825838081 9296164370624273119378561)
  ·
    refine ⟨6972123277968204839533921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9296164370624273119378561 6972123277968204839533921)
    ·
      refine ⟨5229092458476153629650441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6972123277968204839533921 5229092458476153629650441)
      ·
        refine ⟨3921819343857115222237831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5229092458476153629650441 3921819343857115222237831)
        ·
          refine ⟨5882729015785672833356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921819343857115222237831 5882729015785672833356747)
          ·
            refine ⟨8824093523678509250035121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882729015785672833356747 8824093523678509250035121)
            ·
              refine ⟨6618070142758881937526341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8824093523678509250035121 6618070142758881937526341)
              ·
                refine ⟨1240888151767290363286189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6618070142758881937526341 1240888151767290363286189)
                ·
                  refine ⟨465333056912733886232321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240888151767290363286189 465333056912733886232321)
                  ·
                    refine ⟨348999792684550414674241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465333056912733886232321 348999792684550414674241)
                    ·
                      refine ⟨261749844513412811005681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 348999792684550414674241 261749844513412811005681)
                      ·
                        rfl

theorem cell23_509756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_509756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509756 prefixEnd_509756 := by exact prefixLift 509756
  have htrace : WordTrace (prefixWord ++ tailWord_509756) baseStart_509756 baseEnd_509756 := by
    simpa [prefixWord, tailWord_509756, baseEnd_509756] using wordTrace_append hprefix tailTrace_509756
  have hstable : (prefixWord ++ tailWord_509756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509756).length < 2 ^ (prefixWord ++ tailWord_509756).sum := by decide
  have hdescent : baseEnd_509756 < baseStart_509756 := by decide
  rcases family_descends (prefixWord ++ tailWord_509756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509766 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_509766 : Nat := 118140960795 + 509766 * 2 ^ 59
def prefixEnd_509766 : Nat := 4983230072969 + 3 ^ 40 * 509766 * 2
def baseEnd_509766 : Nat := 87251659773319257293545

theorem tailTrace_509766 : CollatzResearch.WordTrace tailWord_509766 prefixEnd_509766 87251659773319257293545 := by
  unfold tailWord_509766
  simp only [CollatzResearch.WordTrace]
  refine ⟨581021670975384935831911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12395128980808211964414101 581021670975384935831911)
  ·
    refine ⟨871532506463077403747867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 581021670975384935831911 871532506463077403747867)
    ·
      refine ⟨1307298759694616105621801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871532506463077403747867 1307298759694616105621801)
      ·
        refine ⟨980474069770962079216351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307298759694616105621801 980474069770962079216351)
        ·
          refine ⟨1470711104656443118824527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980474069770962079216351 1470711104656443118824527)
          ·
            refine ⟨2206066656984664678236791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470711104656443118824527 2206066656984664678236791)
            ·
              refine ⟨3309099985476997017355187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206066656984664678236791 3309099985476997017355187)
              ·
                refine ⟨4963649978215495526032781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309099985476997017355187 4963649978215495526032781)
                ·
                  refine ⟨1861368741830810822262293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4963649978215495526032781 1861368741830810822262293)
                  ·
                    refine ⟨87251659773319257293545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1861368741830810822262293 87251659773319257293545)
                    ·
                      rfl

theorem cell23_509766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_509766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509766 prefixEnd_509766 := by exact prefixLift 509766
  have htrace : WordTrace (prefixWord ++ tailWord_509766) baseStart_509766 baseEnd_509766 := by
    simpa [prefixWord, tailWord_509766, baseEnd_509766] using wordTrace_append hprefix tailTrace_509766
  have hstable : (prefixWord ++ tailWord_509766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509766).length < 2 ^ (prefixWord ++ tailWord_509766).sum := by decide
  have hdescent : baseEnd_509766 < baseStart_509766 := by decide
  rcases family_descends (prefixWord ++ tailWord_509766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509792 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_509792 : Nat := 118140960795 + 509792 * 2 ^ 59
def prefixEnd_509792 : Nat := 4983230072969 + 3 ^ 40 * 509792 * 2
def baseEnd_509792 : Nat := 87256109938991556718505

theorem tailTrace_509792 : CollatzResearch.WordTrace tailWord_509792 prefixEnd_509792 87256109938991556718505 := by
  unfold tailWord_509792
  simp only [CollatzResearch.WordTrace]
  refine ⟨9296820884559062193533815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12395761179412082924711753 9296820884559062193533815)
  ·
    refine ⟨13945231326838593290300723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9296820884559062193533815 13945231326838593290300723)
    ·
      refine ⟨20917846990257889935451085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13945231326838593290300723 20917846990257889935451085)
      ·
        refine ⟨7844192621346708725794157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20917846990257889935451085 7844192621346708725794157)
        ·
          refine ⟨2941572233005015772172809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7844192621346708725794157 2941572233005015772172809)
          ·
            refine ⟨2206179174753761829129607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2941572233005015772172809 2206179174753761829129607)
            ·
              refine ⟨3309268762130642743694411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206179174753761829129607 3309268762130642743694411)
              ·
                refine ⟨4963903143195964115541617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309268762130642743694411 4963903143195964115541617)
                ·
                  refine ⟨3722927357396973086656213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963903143195964115541617 3722927357396973086656213)
                  ·
                    refine ⟨87256109938991556718505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3722927357396973086656213 87256109938991556718505)
                    ·
                      rfl

theorem cell23_509792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_509792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509792 prefixEnd_509792 := by exact prefixLift 509792
  have htrace : WordTrace (prefixWord ++ tailWord_509792) baseStart_509792 baseEnd_509792 := by
    simpa [prefixWord, tailWord_509792, baseEnd_509792] using wordTrace_append hprefix tailTrace_509792
  have hstable : (prefixWord ++ tailWord_509792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509792).length < 2 ^ (prefixWord ++ tailWord_509792).sum := by decide
  have hdescent : baseEnd_509792 < baseStart_509792 := by decide
  rcases family_descends (prefixWord ++ tailWord_509792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509796 : List Nat := [2, 3, 1, 1, 6, 1, 1, 8]
def baseStart_509796 : Nat := 118140960795 + 509796 * 2 ^ 59
def prefixEnd_509796 : Nat := 4983230072969 + 3 ^ 40 * 509796 * 2
def baseEnd_509796 : Nat := 9695199397762690907611

theorem tailTrace_509796 : CollatzResearch.WordTrace tailWord_509796 prefixEnd_509796 9695199397762690907611 := by
  unfold tailWord_509796
  simp only [CollatzResearch.WordTrace]
  refine ⟨9296893830551816535106621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12395858440735755380142161 9296893830551816535106621)
  ·
    refine ⟨3486335186456931200664983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9296893830551816535106621 3486335186456931200664983)
    ·
      refine ⟨5229502779685396800997475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486335186456931200664983 5229502779685396800997475)
      ·
        refine ⟨7844254169528095201496213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229502779685396800997475 7844254169528095201496213)
        ·
          refine ⟨367699414196629462570135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7844254169528095201496213 367699414196629462570135)
          ·
            refine ⟨551549121294944193855203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367699414196629462570135 551549121294944193855203)
            ·
              refine ⟨827323681942416290782805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551549121294944193855203 827323681942416290782805)
              ·
                refine ⟨9695199397762690907611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 827323681942416290782805 9695199397762690907611)
                ·
                  rfl

theorem cell23_509796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 8].length) (baseStart_509796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509796 prefixEnd_509796 := by exact prefixLift 509796
  have htrace : WordTrace (prefixWord ++ tailWord_509796) baseStart_509796 baseEnd_509796 := by
    simpa [prefixWord, tailWord_509796, baseEnd_509796] using wordTrace_append hprefix tailTrace_509796
  have hstable : (prefixWord ++ tailWord_509796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509796).length < 2 ^ (prefixWord ++ tailWord_509796).sum := by decide
  have hdescent : baseEnd_509796 < baseStart_509796 := by decide
  rcases family_descends (prefixWord ++ tailWord_509796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509806 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_509806 : Nat := 118140960795 + 509806 * 2 ^ 59
def prefixEnd_509806 : Nat := 4983230072969 + 3 ^ 40 * 509806 * 2
def baseEnd_509806 : Nat := 261775518546137615380451

theorem tailTrace_509806 : CollatzResearch.WordTrace tailWord_509806 prefixEnd_509806 261775518546137615380451 := by
  unfold tailWord_509806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324269048883425597259659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12396101594044936518718181 2324269048883425597259659)
  ·
    refine ⟨3486403573325138395889489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324269048883425597259659 3486403573325138395889489)
    ·
      refine ⟨2614802679993853796917117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3486403573325138395889489 2614802679993853796917117)
      ·
        refine ⟨980551004997695173843919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2614802679993853796917117 980551004997695173843919)
        ·
          refine ⟨1470826507496542760765879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980551004997695173843919 1470826507496542760765879)
          ·
            refine ⟨2206239761244814141148819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470826507496542760765879 2206239761244814141148819)
            ·
              refine ⟨3309359641867221211723229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206239761244814141148819 3309359641867221211723229)
              ·
                refine ⟨1241009865700207954396211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309359641867221211723229 1241009865700207954396211)
                ·
                  refine ⟨1861514798550311931594317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241009865700207954396211 1861514798550311931594317)
                  ·
                    refine ⟨698068049456366974347869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1861514798550311931594317 698068049456366974347869)
                    ·
                      refine ⟨261775518546137615380451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698068049456366974347869 261775518546137615380451)
                      ·
                        rfl

theorem cell23_509806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_509806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509806 prefixEnd_509806 := by exact prefixLift 509806
  have htrace : WordTrace (prefixWord ++ tailWord_509806) baseStart_509806 baseEnd_509806 := by
    simpa [prefixWord, tailWord_509806, baseEnd_509806] using wordTrace_append hprefix tailTrace_509806
  have hstable : (prefixWord ++ tailWord_509806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509806).length < 2 ^ (prefixWord ++ tailWord_509806).sum := by decide
  have hdescent : baseEnd_509806 < baseStart_509806 := by decide
  rcases family_descends (prefixWord ++ tailWord_509806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509863 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_509863 : Nat := 118140960795 + 509863 * 2 ^ 59
def prefixEnd_509863 : Nat := 4983230072969 + 3 ^ 40 * 509863 * 2
def baseEnd_509863 : Nat := 261804786943443892367689

theorem tailTrace_509863 : CollatzResearch.WordTrace tailWord_509863 prefixEnd_509863 261804786943443892367689 := by
  unfold tailWord_509863
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596231351860903512902243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12397487567907269008601495 18596231351860903512902243)
  ·
    refine ⟨27894347027791355269353365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18596231351860903512902243 27894347027791355269353365)
    ·
      refine ⟨1307547516927719778250939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27894347027791355269353365 1307547516927719778250939)
      ·
        refine ⟨1961321275391579667376409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307547516927719778250939 1961321275391579667376409)
        ·
          refine ⟨1470990956543684750532307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961321275391579667376409 1470990956543684750532307)
          ·
            refine ⟨2206486434815527125798461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470990956543684750532307 2206486434815527125798461)
            ·
              refine ⟨827432413055822672174423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2206486434815527125798461 827432413055822672174423)
              ·
                refine ⟨1241148619583734008261635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827432413055822672174423 1241148619583734008261635)
                ·
                  refine ⟨1861722929375601012392453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241148619583734008261635 1861722929375601012392453)
                  ·
                    refine ⟨349073049257925189823585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1861722929375601012392453 349073049257925189823585)
                    ·
                      refine ⟨261804786943443892367689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349073049257925189823585 261804786943443892367689)
                      ·
                        rfl

theorem cell23_509863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_509863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509863 prefixEnd_509863 := by exact prefixLift 509863
  have htrace : WordTrace (prefixWord ++ tailWord_509863) baseStart_509863 baseEnd_509863 := by
    simpa [prefixWord, tailWord_509863, baseEnd_509863] using wordTrace_append hprefix tailTrace_509863
  have hstable : (prefixWord ++ tailWord_509863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509863).length < 2 ^ (prefixWord ++ tailWord_509863).sum := by decide
  have hdescent : baseEnd_509863 < baseStart_509863 := by decide
  rcases family_descends (prefixWord ++ tailWord_509863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509899 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 2, 5]
def baseStart_509899 : Nat := 118140960795 + 509899 * 2 ^ 59
def prefixEnd_509899 : Nat := 4983230072969 + 3 ^ 40 * 509899 * 2
def baseEnd_509899 : Nat := 87274424082335250505841

theorem tailTrace_509899 : CollatzResearch.WordTrace tailWord_509899 prefixEnd_509899 87274424082335250505841 := by
  unfold tailWord_509899
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597544379730481661212751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12398362919820321107475167 18597544379730481661212751)
  ·
    refine ⟨27896316569595722491819127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18597544379730481661212751 27896316569595722491819127)
    ·
      refine ⟨41844474854393583737728691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27896316569595722491819127 41844474854393583737728691)
      ·
        refine ⟨62766712281590375606593037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41844474854393583737728691 62766712281590375606593037)
        ·
          refine ⟨23537517105596390852472389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62766712281590375606593037 23537517105596390852472389)
          ·
            refine ⟨4413284457299323284838573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23537517105596390852472389 4413284457299323284838573)
            ·
              refine ⟨1654981671487246231814465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4413284457299323284838573 1654981671487246231814465)
              ·
                refine ⟨1241236253615434673860849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654981671487246231814465 1241236253615434673860849)
                ·
                  refine ⟨930927190211576005395637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241236253615434673860849 930927190211576005395637)
                  ·
                    refine ⟨87274424082335250505841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 930927190211576005395637 87274424082335250505841)
                    ·
                      rfl

theorem cell23_509899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 5].length) (baseStart_509899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509899 prefixEnd_509899 := by exact prefixLift 509899
  have htrace : WordTrace (prefixWord ++ tailWord_509899) baseStart_509899 baseEnd_509899 := by
    simpa [prefixWord, tailWord_509899, baseEnd_509899] using wordTrace_append hprefix tailTrace_509899
  have hstable : (prefixWord ++ tailWord_509899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509899).length < 2 ^ (prefixWord ++ tailWord_509899).sum := by decide
  have hdescent : baseEnd_509899 < baseStart_509899 := by decide
  rcases family_descends (prefixWord ++ tailWord_509899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509909 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_509909 : Nat := 118140960795 + 509909 * 2 ^ 59
def prefixEnd_509909 : Nat := 4983230072969 + 3 ^ 40 * 509909 * 2
def baseEnd_509909 : Nat := 261828407053550712392477

theorem tailTrace_509909 : CollatzResearch.WordTrace tailWord_509909 prefixEnd_509909 261828407053550712392477 := by
  unfold tailWord_509909
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597909109694253369076781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12398606073129502246051187 18597909109694253369076781)
  ·
    refine ⟨6974215916135345013403793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18597909109694253369076781 6974215916135345013403793)
    ·
      refine ⟨5230661937101508760052845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6974215916135345013403793 5230661937101508760052845)
      ·
        refine ⟨1961498226413065785019817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5230661937101508760052845 1961498226413065785019817)
        ·
          refine ⟨1471123669809799338764863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961498226413065785019817 1471123669809799338764863)
          ·
            refine ⟨2206685504714699008147295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471123669809799338764863 2206685504714699008147295)
            ·
              refine ⟨3310028257072048512220943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206685504714699008147295 3310028257072048512220943)
              ·
                refine ⟨4965042385608072768331415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310028257072048512220943 4965042385608072768331415)
                ·
                  refine ⟨7447563578412109152497123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965042385608072768331415 7447563578412109152497123)
                  ·
                    refine ⟨11171345367618163728745685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7447563578412109152497123 11171345367618163728745685)
                    ·
                      refine ⟨261828407053550712392477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11171345367618163728745685 261828407053550712392477)
                      ·
                        rfl

theorem cell23_509909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_509909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509909 prefixEnd_509909 := by exact prefixLift 509909
  have htrace : WordTrace (prefixWord ++ tailWord_509909) baseStart_509909 baseEnd_509909 := by
    simpa [prefixWord, tailWord_509909, baseEnd_509909] using wordTrace_append hprefix tailTrace_509909
  have hstable : (prefixWord ++ tailWord_509909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509909).length < 2 ^ (prefixWord ++ tailWord_509909).sum := by decide
  have hdescent : baseEnd_509909 < baseStart_509909 := by decide
  rcases family_descends (prefixWord ++ tailWord_509909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509914 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_509914 : Nat := 118140960795 + 509914 * 2 ^ 59
def prefixEnd_509914 : Nat := 4983230072969 + 3 ^ 40 * 509914 * 2
def baseEnd_509914 : Nat := 261830974456823192829955

theorem tailTrace_509914 : CollatzResearch.WordTrace tailWord_509914 prefixEnd_509914 261830974456823192829955 := by
  unfold tailWord_509914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649522868669034805752199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12398727649784092815339197 4649522868669034805752199)
  ·
    refine ⟨6974284303003552208628299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4649522868669034805752199 6974284303003552208628299)
    ·
      refine ⟨10461426454505328312942449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974284303003552208628299 10461426454505328312942449)
      ·
        refine ⟨7846069840878996234706837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10461426454505328312942449 7846069840878996234706837)
        ·
          refine ⟨367784523791202948501883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7846069840878996234706837 367784523791202948501883)
          ·
            refine ⟨551676785686804422752825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367784523791202948501883 551676785686804422752825)
            ·
              refine ⟨413757589265103317064619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551676785686804422752825 413757589265103317064619)
              ·
                refine ⟨620636383897654975596929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413757589265103317064619 620636383897654975596929)
                ·
                  refine ⟨465477287923241231697697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620636383897654975596929 465477287923241231697697)
                  ·
                    refine ⟨349107965942430923773273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465477287923241231697697 349107965942430923773273)
                    ·
                      refine ⟨261830974456823192829955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349107965942430923773273 261830974456823192829955)
                      ·
                        rfl

theorem cell23_509914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_509914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509914 prefixEnd_509914 := by exact prefixLift 509914
  have htrace : WordTrace (prefixWord ++ tailWord_509914) baseStart_509914 baseEnd_509914 := by
    simpa [prefixWord, tailWord_509914, baseEnd_509914] using wordTrace_append hprefix tailTrace_509914
  have hstable : (prefixWord ++ tailWord_509914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509914).length < 2 ^ (prefixWord ++ tailWord_509914).sum := by decide
  have hdescent : baseEnd_509914 < baseStart_509914 := by decide
  rcases family_descends (prefixWord ++ tailWord_509914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509939 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3]
def baseStart_509939 : Nat := 118140960795 + 509939 * 2 ^ 59
def prefixEnd_509939 : Nat := 4983230072969 + 3 ^ 40 * 509939 * 2
def baseEnd_509939 : Nat := 261843811473185595017339

theorem tailTrace_509939 : CollatzResearch.WordTrace tailWord_509939 prefixEnd_509939 261843811473185595017339 := by
  unfold tailWord_509939
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599003299585568492668871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12399335533057045661779247 18599003299585568492668871)
  ·
    refine ⟨27898504949378352739003307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599003299585568492668871 27898504949378352739003307)
    ·
      refine ⟨41847757424067529108504961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27898504949378352739003307 41847757424067529108504961)
      ·
        refine ⟨31385818068050646831378721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41847757424067529108504961 31385818068050646831378721)
        ·
          refine ⟨23539363551037985123534041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31385818068050646831378721 23539363551037985123534041)
          ·
            refine ⟨17654522663278488842650531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23539363551037985123534041 17654522663278488842650531)
            ·
              refine ⟨26481783994917733263975797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17654522663278488842650531 26481783994917733263975797)
              ·
                refine ⟨2482667249523537493497731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26481783994917733263975797 2482667249523537493497731)
                ·
                  refine ⟨3724000874285306240246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482667249523537493497731 3724000874285306240246597)
                  ·
                    refine ⟨698250163928494920046237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3724000874285306240246597 698250163928494920046237)
                    ·
                      refine ⟨261843811473185595017339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698250163928494920046237 261843811473185595017339)
                      ·
                        rfl

theorem cell23_509939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_509939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509939 prefixEnd_509939 := by exact prefixLift 509939
  have htrace : WordTrace (prefixWord ++ tailWord_509939) baseStart_509939 baseEnd_509939 := by
    simpa [prefixWord, tailWord_509939, baseEnd_509939] using wordTrace_append hprefix tailTrace_509939
  have hstable : (prefixWord ++ tailWord_509939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509939).length < 2 ^ (prefixWord ++ tailWord_509939).sum := by decide
  have hdescent : baseEnd_509939 < baseStart_509939 := by decide
  rcases family_descends (prefixWord ++ tailWord_509939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509963 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 1, 4]
def baseStart_509963 : Nat := 118140960795 + 509963 * 2 ^ 59
def prefixEnd_509963 : Nat := 4983230072969 + 3 ^ 40 * 509963 * 2
def baseEnd_509963 : Nat := 87285378336297833705743

theorem tailTrace_509963 : CollatzResearch.WordTrace tailWord_509963 prefixEnd_509963 87285378336297833705743 := by
  unfold tailWord_509963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599878651498620591542543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12399919100999080394361695 18599878651498620591542543)
  ·
    refine ⟨27899817977247930887313815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599878651498620591542543 27899817977247930887313815)
    ·
      refine ⟨41849726965871896330970723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27899817977247930887313815 41849726965871896330970723)
      ·
        refine ⟨62774590448807844496456085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41849726965871896330970723 62774590448807844496456085)
        ·
          refine ⟨2942558927287867710771379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62774590448807844496456085 2942558927287867710771379)
          ·
            refine ⟨4413838390931801566157069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942558927287867710771379 4413838390931801566157069)
            ·
              refine ⟨1655189396599425587308901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4413838390931801566157069 1655189396599425587308901)
              ·
                refine ⟨310348011862392297620419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1655189396599425587308901 310348011862392297620419)
                ·
                  refine ⟨465522017793588446430629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310348011862392297620419 465522017793588446430629)
                  ·
                    refine ⟨87285378336297833705743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465522017793588446430629 87285378336297833705743)
                    ·
                      rfl

theorem cell23_509963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 4].length) (baseStart_509963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509963 prefixEnd_509963 := by exact prefixLift 509963
  have htrace : WordTrace (prefixWord ++ tailWord_509963) baseStart_509963 baseEnd_509963 := by
    simpa [prefixWord, tailWord_509963, baseEnd_509963] using wordTrace_append hprefix tailTrace_509963
  have hstable : (prefixWord ++ tailWord_509963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509963).length < 2 ^ (prefixWord ++ tailWord_509963).sum := by decide
  have hdescent : baseEnd_509963 < baseStart_509963 := by decide
  rcases family_descends (prefixWord ++ tailWord_509963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509969 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_509969 : Nat := 118140960795 + 509969 * 2 ^ 59
def prefixEnd_509969 : Nat := 4983230072969 + 3 ^ 40 * 509969 * 2
def baseEnd_509969 : Nat := 261859215892820477642201

theorem tailTrace_509969 : CollatzResearch.WordTrace tailWord_509969 prefixEnd_509969 261859215892820477642201 := by
  unfold tailWord_509969
  simp only [CollatzResearch.WordTrace]
  refine ⟨18600097489476883616260961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12400064992984589077507307 18600097489476883616260961)
  ·
    refine ⟨13950073117107662712195721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18600097489476883616260961 13950073117107662712195721)
    ·
      refine ⟨10462554837830747034146791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13950073117107662712195721 10462554837830747034146791)
      ·
        refine ⟨15693832256746120551220187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10462554837830747034146791 15693832256746120551220187)
        ·
          refine ⟨23540748385119180826830281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15693832256746120551220187 23540748385119180826830281)
          ·
            refine ⟨17655561288839385620122711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23540748385119180826830281 17655561288839385620122711)
            ·
              refine ⟨26483341933259078430184067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17655561288839385620122711 26483341933259078430184067)
              ·
                refine ⟨39725012899888617645276101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26483341933259078430184067 39725012899888617645276101)
                ·
                  refine ⟨7448439918729115808489269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39725012899888617645276101 7448439918729115808489269)
                  ·
                    refine ⟨698291242380854607045869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7448439918729115808489269 698291242380854607045869)
                    ·
                      refine ⟨261859215892820477642201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698291242380854607045869 261859215892820477642201)
                      ·
                        rfl

theorem cell23_509969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_509969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_509969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_509969 prefixEnd_509969 := by exact prefixLift 509969
  have htrace : WordTrace (prefixWord ++ tailWord_509969) baseStart_509969 baseEnd_509969 := by
    simpa [prefixWord, tailWord_509969, baseEnd_509969] using wordTrace_append hprefix tailTrace_509969
  have hstable : (prefixWord ++ tailWord_509969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509969).length < 2 ^ (prefixWord ++ tailWord_509969).sum := by decide
  have hdescent : baseEnd_509969 < baseStart_509969 := by decide
  rcases family_descends (prefixWord ++ tailWord_509969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510013 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 4, 3, 2]
def baseStart_510013 : Nat := 118140960795 + 510013 * 2 ^ 59
def prefixEnd_510013 : Nat := 4983230072969 + 3 ^ 40 * 510013 * 2
def baseEnd_510013 : Nat := 261881809041618305491999

theorem tailTrace_510013 : CollatzResearch.WordTrace tailWord_510013 prefixEnd_510013 261881809041618305491999 := by
  unfold tailWord_510013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601702301317479130862693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12401134867544986087241795 18601702301317479130862693)
  ·
    refine ⟨3487819181497027337036755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18601702301317479130862693 3487819181497027337036755)
    ·
      refine ⟨5231728772245541005555133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487819181497027337036755 5231728772245541005555133)
      ·
        refine ⟨1961898289592077877083175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5231728772245541005555133 1961898289592077877083175)
        ·
          refine ⟨2942847434388116815624763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961898289592077877083175 2942847434388116815624763)
          ·
            refine ⟨4414271151582175223437145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942847434388116815624763 4414271151582175223437145)
            ·
              refine ⟨3310703363686631417577859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414271151582175223437145 3310703363686631417577859)
              ·
                refine ⟨4966055045529947126366789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310703363686631417577859 4966055045529947126366789)
                ·
                  refine ⟨931135321036865086193773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4966055045529947126366789 931135321036865086193773)
                  ·
                    refine ⟨349175745388824407322665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931135321036865086193773 349175745388824407322665)
                    ·
                      refine ⟨261881809041618305491999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349175745388824407322665 261881809041618305491999)
                      ·
                        rfl

theorem cell23_510013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_510013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510013 prefixEnd_510013 := by exact prefixLift 510013
  have htrace : WordTrace (prefixWord ++ tailWord_510013) baseStart_510013 baseEnd_510013 := by
    simpa [prefixWord, tailWord_510013, baseEnd_510013] using wordTrace_append hprefix tailTrace_510013
  have hstable : (prefixWord ++ tailWord_510013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510013).length < 2 ^ (prefixWord ++ tailWord_510013).sum := by decide
  have hdescent : baseEnd_510013 < baseStart_510013 := by decide
  rcases family_descends (prefixWord ++ tailWord_510013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510063 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 3]
def baseStart_510063 : Nat := 118140960795 + 510063 * 2 ^ 59
def prefixEnd_510063 : Nat := 4983230072969 + 3 ^ 40 * 510063 * 2
def baseEnd_510063 : Nat := 261907483074343109866769

theorem tailTrace_510063 : CollatzResearch.WordTrace tailWord_510063 prefixEnd_510063 261907483074343109866769 := by
  unfold tailWord_510063
  simp only [CollatzResearch.WordTrace]
  refine ⟨18603525951136337670182843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12402350634090891780121895 18603525951136337670182843)
  ·
    refine ⟨27905288926704506505274265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18603525951136337670182843 27905288926704506505274265)
    ·
      refine ⟨20928966695028379878955699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27905288926704506505274265 20928966695028379878955699)
      ·
        refine ⟨31393450042542569818433549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20928966695028379878955699 31393450042542569818433549)
        ·
          refine ⟨11772543765953463681912581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31393450042542569818433549 11772543765953463681912581)
          ·
            refine ⟨2207351956116274440358609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11772543765953463681912581 2207351956116274440358609)
            ·
              refine ⟨1655513967087205830268957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207351956116274440358609 1655513967087205830268957)
              ·
                refine ⟨620817737657702186350859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655513967087205830268957 620817737657702186350859)
                ·
                  refine ⟨931226606486553279526289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620817737657702186350859 931226606486553279526289)
                  ·
                    refine ⟨698419954864914959644717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 931226606486553279526289 698419954864914959644717)
                    ·
                      refine ⟨261907483074343109866769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698419954864914959644717 261907483074343109866769)
                      ·
                        rfl

theorem cell23_510063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_510063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510063 prefixEnd_510063 := by exact prefixLift 510063
  have htrace : WordTrace (prefixWord ++ tailWord_510063) baseStart_510063 baseEnd_510063 := by
    simpa [prefixWord, tailWord_510063, baseEnd_510063] using wordTrace_append hprefix tailTrace_510063
  have hstable : (prefixWord ++ tailWord_510063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510063).length < 2 ^ (prefixWord ++ tailWord_510063).sum := by decide
  have hdescent : baseEnd_510063 < baseStart_510063 := by decide
  rcases family_descends (prefixWord ++ tailWord_510063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510066 : List Nat := [3, 2, 1, 2, 2, 4, 9]
def baseStart_510066 : Nat := 118140960795 + 510066 * 2 ^ 59
def prefixEnd_510066 : Nat := 4983230072969 + 3 ^ 40 * 510066 * 2
def baseEnd_510066 : Nat := 3233444734769217260855

theorem tailTrace_510066 : CollatzResearch.WordTrace tailWord_510066 prefixEnd_510066 3233444734769217260855 := by
  unfold tailWord_510066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650908842531367295635513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12402423580083646121694701 4650908842531367295635513)
  ·
    refine ⟨3488181631898525471726635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4650908842531367295635513 3488181631898525471726635)
    ·
      refine ⟨5232272447847788207589953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3488181631898525471726635 5232272447847788207589953)
      ·
        refine ⟨3924204335885841155692465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5232272447847788207589953 3924204335885841155692465)
        ·
          refine ⟨2943153251914380866769349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3924204335885841155692465 2943153251914380866769349)
          ·
            refine ⟨551841234733946412519253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2943153251914380866769349 551841234733946412519253)
            ·
              refine ⟨3233444734769217260855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 551841234733946412519253 3233444734769217260855)
              ·
                rfl

theorem cell23_510066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 9].length) (baseStart_510066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510066 prefixEnd_510066 := by exact prefixLift 510066
  have htrace : WordTrace (prefixWord ++ tailWord_510066) baseStart_510066 baseEnd_510066 := by
    simpa [prefixWord, tailWord_510066, baseEnd_510066] using wordTrace_append hprefix tailTrace_510066
  have hstable : (prefixWord ++ tailWord_510066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510066).length < 2 ^ (prefixWord ++ tailWord_510066).sum := by decide
  have hdescent : baseEnd_510066 < baseStart_510066 := by decide
  rcases family_descends (prefixWord ++ tailWord_510066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510077 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 3, 2, 2]
def baseStart_510077 : Nat := 118140960795 + 510077 * 2 ^ 59
def prefixEnd_510077 : Nat := 4983230072969 + 3 ^ 40 * 510077 * 2
def baseEnd_510077 : Nat := 261914671803506055091705

theorem tailTrace_510077 : CollatzResearch.WordTrace tailWord_510077 prefixEnd_510077 261914671803506055091705 := by
  unfold tailWord_510077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604036573085618061192485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12402691048723745374128323 18604036573085618061192485)
  ·
    refine ⟨3488256857453553386473591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18604036573085618061192485 3488256857453553386473591)
    ·
      refine ⟨5232385286180330079710387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3488256857453553386473591 5232385286180330079710387)
      ·
        refine ⟨7848577929270495119565581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232385286180330079710387 7848577929270495119565581)
        ·
          refine ⟨2943216723476435669837093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7848577929270495119565581 2943216723476435669837093)
          ·
            refine ⟨551853135651831688094455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2943216723476435669837093 551853135651831688094455)
            ·
              refine ⟨827779703477747532141683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551853135651831688094455 827779703477747532141683)
              ·
                refine ⟨1241669555216621298212525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827779703477747532141683 1241669555216621298212525)
                ·
                  refine ⟨465626083206232986829697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1241669555216621298212525 465626083206232986829697)
                  ·
                    refine ⟨349219562404674740122273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465626083206232986829697 349219562404674740122273)
                    ·
                      refine ⟨261914671803506055091705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349219562404674740122273 261914671803506055091705)
                      ·
                        rfl

theorem cell23_510077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_510077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510077 prefixEnd_510077 := by exact prefixLift 510077
  have htrace : WordTrace (prefixWord ++ tailWord_510077) baseStart_510077 baseEnd_510077 := by
    simpa [prefixWord, tailWord_510077, baseEnd_510077] using wordTrace_append hprefix tailTrace_510077
  have hstable : (prefixWord ++ tailWord_510077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510077).length < 2 ^ (prefixWord ++ tailWord_510077).sum := by decide
  have hdescent : baseEnd_510077 < baseStart_510077 := by decide
  rcases family_descends (prefixWord ++ tailWord_510077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510099 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_510099 : Nat := 118140960795 + 510099 * 2 ^ 59
def prefixEnd_510099 : Nat := 4983230072969 + 3 ^ 40 * 510099 * 2
def baseEnd_510099 : Nat := 261925968377904969016603

theorem tailTrace_510099 : CollatzResearch.WordTrace tailWord_510099 prefixEnd_510099 261925968377904969016603 := by
  unfold tailWord_510099
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604838979005915818493351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12403225986003943878995567 18604838979005915818493351)
  ·
    refine ⟨27907258468508873727740027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18604838979005915818493351 27907258468508873727740027)
    ·
      refine ⟨41860887702763310591610041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27907258468508873727740027 41860887702763310591610041)
      ·
        refine ⟨31395665777072482943707531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41860887702763310591610041 31395665777072482943707531)
        ·
          refine ⟨47093498665608724415561297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31395665777072482943707531 47093498665608724415561297)
          ·
            refine ⟨35320123999206543311670973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47093498665608724415561297 35320123999206543311670973)
            ·
              refine ⟨13245046499702453741876615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35320123999206543311670973 13245046499702453741876615)
              ·
                refine ⟨19867569749553680612814923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13245046499702453741876615 19867569749553680612814923)
                ·
                  refine ⟨29801354624330520919222385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19867569749553680612814923 29801354624330520919222385)
                  ·
                    refine ⟨22351015968247890689416789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29801354624330520919222385 22351015968247890689416789)
                    ·
                      refine ⟨261925968377904969016603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22351015968247890689416789 261925968377904969016603)
                      ·
                        rfl

theorem cell23_510099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_510099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510099 prefixEnd_510099 := by exact prefixLift 510099
  have htrace : WordTrace (prefixWord ++ tailWord_510099) baseStart_510099 baseEnd_510099 := by
    simpa [prefixWord, tailWord_510099, baseEnd_510099] using wordTrace_append hprefix tailTrace_510099
  have hstable : (prefixWord ++ tailWord_510099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510099).length < 2 ^ (prefixWord ++ tailWord_510099).sum := by decide
  have hdescent : baseEnd_510099 < baseStart_510099 := by decide
  rcases family_descends (prefixWord ++ tailWord_510099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510136 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_510136 : Nat := 118140960795 + 510136 * 2 ^ 59
def prefixEnd_510136 : Nat := 4983230072969 + 3 ^ 40 * 510136 * 2
def baseEnd_510136 : Nat := 261944967162121324253933

theorem tailTrace_510136 : CollatzResearch.WordTrace tailWord_510136 prefixEnd_510136 261944967162121324253933 := by
  unfold tailWord_510136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303094239935935568795131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12404125653247914091726841 9303094239935935568795131)
  ·
    refine ⟨13954641359903903353192697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303094239935935568795131 13954641359903903353192697)
    ·
      refine ⟨10465981019927927514894523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13954641359903903353192697 10465981019927927514894523)
      ·
        refine ⟨15698971529891891272341785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465981019927927514894523 15698971529891891272341785)
        ·
          refine ⟨11774228647418918454256339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15698971529891891272341785 11774228647418918454256339)
          ·
            refine ⟨17661342971128377681384509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774228647418918454256339 17661342971128377681384509)
            ·
              refine ⟨6623003614173141630519191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17661342971128377681384509 6623003614173141630519191)
              ·
                refine ⟨9934505421259712445778787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623003614173141630519191 9934505421259712445778787)
                ·
                  refine ⟨14901758131889568668668181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934505421259712445778787 14901758131889568668668181)
                  ·
                    refine ⟨698519912432323531343821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14901758131889568668668181 698519912432323531343821)
                    ·
                      refine ⟨261944967162121324253933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698519912432323531343821 261944967162121324253933)
                      ·
                        rfl

theorem cell23_510136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_510136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510136 prefixEnd_510136 := by exact prefixLift 510136
  have htrace : WordTrace (prefixWord ++ tailWord_510136) baseStart_510136 baseEnd_510136 := by
    simpa [prefixWord, tailWord_510136, baseEnd_510136] using wordTrace_append hprefix tailTrace_510136
  have hstable : (prefixWord ++ tailWord_510136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510136).length < 2 ^ (prefixWord ++ tailWord_510136).sum := by decide
  have hdescent : baseEnd_510136 < baseStart_510136 := by decide
  rcases family_descends (prefixWord ++ tailWord_510136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510178 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_510178 : Nat := 118140960795 + 510178 * 2 ^ 59
def prefixEnd_510178 : Nat := 4983230072969 + 3 ^ 40 * 510178 * 2
def baseEnd_510178 : Nat := 261966533349610159928741

theorem tailTrace_510178 : CollatzResearch.WordTrace tailWord_510178 prefixEnd_510178 261966533349610159928741 := by
  unfold tailWord_510178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651930086429928077654797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12405146897146474873746125 4651930086429928077654797)
  ·
    refine ⟨1744473782411223029120549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4651930086429928077654797 1744473782411223029120549)
    ·
      refine ⟨327088834202104317960103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1744473782411223029120549 327088834202104317960103)
      ·
        refine ⟨490633251303156476940155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327088834202104317960103 490633251303156476940155)
        ·
          refine ⟨735949876954734715410233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490633251303156476940155 735949876954734715410233)
          ·
            refine ⟨551962407716051036557675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735949876954734715410233 551962407716051036557675)
            ·
              refine ⟨827943611574076554836513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551962407716051036557675 827943611574076554836513)
              ·
                refine ⟨620957708680557416127385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827943611574076554836513 620957708680557416127385)
                ·
                  refine ⟨465718281510418062095539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620957708680557416127385 465718281510418062095539)
                  ·
                    refine ⟨698577422265627093143309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465718281510418062095539 698577422265627093143309)
                    ·
                      refine ⟨261966533349610159928741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698577422265627093143309 261966533349610159928741)
                      ·
                        rfl

theorem cell23_510178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_510178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510178 prefixEnd_510178 := by exact prefixLift 510178
  have htrace : WordTrace (prefixWord ++ tailWord_510178) baseStart_510178 baseEnd_510178 := by
    simpa [prefixWord, tailWord_510178, baseEnd_510178] using wordTrace_append hprefix tailTrace_510178
  have hstable : (prefixWord ++ tailWord_510178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510178).length < 2 ^ (prefixWord ++ tailWord_510178).sum := by decide
  have hdescent : baseEnd_510178 < baseStart_510178 := by decide
  rcases family_descends (prefixWord ++ tailWord_510178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510184 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_510184 : Nat := 118140960795 + 510184 * 2 ^ 59
def prefixEnd_510184 : Nat := 4983230072969 + 3 ^ 40 * 510184 * 2
def baseEnd_510184 : Nat := 261969614233537136453713

theorem tailTrace_510184 : CollatzResearch.WordTrace tailWord_510184 prefixEnd_510184 261969614233537136453713 := by
  unfold tailWord_510184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303969591848987667668803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12405292789131983556891737 9303969591848987667668803)
  ·
    refine ⟨13955954387773481501503205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9303969591848987667668803 13955954387773481501503205)
    ·
      refine ⟨2616741447707527781531851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13955954387773481501503205 2616741447707527781531851)
      ·
        refine ⟨3925112171561291672297777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616741447707527781531851 3925112171561291672297777)
        ·
          refine ⟨2943834128670968754223333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925112171561291672297777 2943834128670968754223333)
          ·
            refine ⟨551968899125806641416875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2943834128670968754223333 551968899125806641416875)
            ·
              refine ⟨827953348688709962125313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551968899125806641416875 827953348688709962125313)
              ·
                refine ⟨620965011516532471593985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827953348688709962125313 620965011516532471593985)
                ·
                  refine ⟨465723758637399353695489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620965011516532471593985 465723758637399353695489)
                  ·
                    refine ⟨349292818978049515271617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465723758637399353695489 349292818978049515271617)
                    ·
                      refine ⟨261969614233537136453713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349292818978049515271617 261969614233537136453713)
                      ·
                        rfl

theorem cell23_510184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_510184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510184 prefixEnd_510184 := by exact prefixLift 510184
  have htrace : WordTrace (prefixWord ++ tailWord_510184) baseStart_510184 baseEnd_510184 := by
    simpa [prefixWord, tailWord_510184, baseEnd_510184] using wordTrace_append hprefix tailTrace_510184
  have hstable : (prefixWord ++ tailWord_510184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510184).length < 2 ^ (prefixWord ++ tailWord_510184).sum := by decide
  have hdescent : baseEnd_510184 < baseStart_510184 := by decide
  rcases family_descends (prefixWord ++ tailWord_510184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510193 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_510193 : Nat := 118140960795 + 510193 * 2 ^ 59
def prefixEnd_510193 : Nat := 4983230072969 + 3 ^ 40 * 510193 * 2
def baseEnd_510193 : Nat := 261974235559427601241171

theorem tailTrace_510193 : CollatzResearch.WordTrace tailWord_510193 prefixEnd_510193 261974235559427601241171 := by
  unfold tailWord_510193
  simp only [CollatzResearch.WordTrace]
  refine ⟨18608267440665369872415233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12405511627110246581610155 18608267440665369872415233)
  ·
    refine ⟨13956200580499027404311425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18608267440665369872415233 13956200580499027404311425)
    ·
      refine ⟨10467150435374270553233569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13956200580499027404311425 10467150435374270553233569)
      ·
        refine ⟨7850362826530702914925177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10467150435374270553233569 7850362826530702914925177)
        ·
          refine ⟨5887772119898027186193883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7850362826530702914925177 5887772119898027186193883)
          ·
            refine ⟨8831658179847040779290825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887772119898027186193883 8831658179847040779290825)
            ·
              refine ⟨6623743634885280584468119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8831658179847040779290825 6623743634885280584468119)
              ·
                refine ⟨9935615452327920876702179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623743634885280584468119 9935615452327920876702179)
                ·
                  refine ⟨14903423178491881315053269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9935615452327920876702179 14903423178491881315053269)
                  ·
                    refine ⟨349298980745903468321561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14903423178491881315053269 349298980745903468321561)
                    ·
                      refine ⟨261974235559427601241171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349298980745903468321561 261974235559427601241171)
                      ·
                        rfl

theorem cell23_510193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_510193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510193 prefixEnd_510193 := by exact prefixLift 510193
  have htrace : WordTrace (prefixWord ++ tailWord_510193) baseStart_510193 baseEnd_510193 := by
    simpa [prefixWord, tailWord_510193, baseEnd_510193] using wordTrace_append hprefix tailTrace_510193
  have hstable : (prefixWord ++ tailWord_510193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510193).length < 2 ^ (prefixWord ++ tailWord_510193).sum := by decide
  have hdescent : baseEnd_510193 < baseStart_510193 := by decide
  rcases family_descends (prefixWord ++ tailWord_510193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510223 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 6, 2]
def baseStart_510223 : Nat := 118140960795 + 510223 * 2 ^ 59
def prefixEnd_510223 : Nat := 4983230072969 + 3 ^ 40 * 510223 * 2
def baseEnd_510223 : Nat := 261989639979062483866033

theorem tailTrace_510223 : CollatzResearch.WordTrace tailWord_510223 prefixEnd_510223 261989639979062483866033 := by
  unfold tailWord_510223
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609361630556684996007323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12406241087037789997338215 18609361630556684996007323)
  ·
    refine ⟨27914042445835027494010985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18609361630556684996007323 27914042445835027494010985)
    ·
      refine ⟨20935531834376270620508239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27914042445835027494010985 20935531834376270620508239)
      ·
        refine ⟨31403297751564405930762359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20935531834376270620508239 31403297751564405930762359)
        ·
          refine ⟨47104946627346608896143539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31403297751564405930762359 47104946627346608896143539)
          ·
            refine ⟨70657419941019913344215309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47104946627346608896143539 70657419941019913344215309)
            ·
              refine ⟨26496532477882467504080741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70657419941019913344215309 26496532477882467504080741)
              ·
                refine ⟨4968099839602962657015139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26496532477882467504080741 4968099839602962657015139)
                ·
                  refine ⟨7452149759404443985522709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968099839602962657015139 7452149759404443985522709)
                  ·
                    refine ⟨349319519972083311821377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7452149759404443985522709 349319519972083311821377)
                    ·
                      refine ⟨261989639979062483866033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349319519972083311821377 261989639979062483866033)
                      ·
                        rfl

theorem cell23_510223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6, 2].length) (baseStart_510223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510223 prefixEnd_510223 := by exact prefixLift 510223
  have htrace : WordTrace (prefixWord ++ tailWord_510223) baseStart_510223 baseEnd_510223 := by
    simpa [prefixWord, tailWord_510223, baseEnd_510223] using wordTrace_append hprefix tailTrace_510223
  have hstable : (prefixWord ++ tailWord_510223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510223).length < 2 ^ (prefixWord ++ tailWord_510223).sum := by decide
  have hdescent : baseEnd_510223 < baseStart_510223 := by decide
  rcases family_descends (prefixWord ++ tailWord_510223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510240 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_510240 : Nat := 118140960795 + 510240 * 2 ^ 59
def prefixEnd_510240 : Nat := 4983230072969 + 3 ^ 40 * 510240 * 2
def baseEnd_510240 : Nat := 261998369150188917353455

theorem tailTrace_510240 : CollatzResearch.WordTrace tailWord_510240 prefixEnd_510240 261998369150188917353455 := by
  unfold tailWord_510240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304990835747548449688087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12406654447663397932917449 9304990835747548449688087)
  ·
    refine ⟨13957486253621322674532131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9304990835747548449688087 13957486253621322674532131)
    ·
      refine ⟨20936229380431984011798197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13957486253621322674532131 20936229380431984011798197)
      ·
        refine ⟨1962771504415498501106081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20936229380431984011798197 1962771504415498501106081)
        ·
          refine ⟨1472078628311623875829561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962771504415498501106081 1472078628311623875829561)
          ·
            refine ⟨1104058971233717906872171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472078628311623875829561 1104058971233717906872171)
            ·
              refine ⟨1656088456850576860308257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104058971233717906872171 1656088456850576860308257)
              ·
                refine ⟨1242066342637932645231193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656088456850576860308257 1242066342637932645231193)
                ·
                  refine ⟨931549756978449483923395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242066342637932645231193 931549756978449483923395)
                  ·
                    refine ⟨1397324635467674225885093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931549756978449483923395 1397324635467674225885093)
                    ·
                      refine ⟨261998369150188917353455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1397324635467674225885093 261998369150188917353455)
                      ·
                        rfl

theorem cell23_510240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_510240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510240 prefixEnd_510240 := by exact prefixLift 510240
  have htrace : WordTrace (prefixWord ++ tailWord_510240) baseStart_510240 baseEnd_510240 := by
    simpa [prefixWord, tailWord_510240, baseEnd_510240] using wordTrace_append hprefix tailTrace_510240
  have hstable : (prefixWord ++ tailWord_510240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510240).length < 2 ^ (prefixWord ++ tailWord_510240).sum := by decide
  have hdescent : baseEnd_510240 < baseStart_510240 := by decide
  rcases family_descends (prefixWord ++ tailWord_510240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510313 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_510313 : Nat := 118140960795 + 510313 * 2 ^ 59
def prefixEnd_510313 : Nat := 4983230072969 + 3 ^ 40 * 510313 * 2
def baseEnd_510313 : Nat := 262035853237967131740619

theorem tailTrace_510313 : CollatzResearch.WordTrace tailWord_510313 prefixEnd_510313 262035853237967131740619 := by
  unfold tailWord_510313
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612644200230630366783593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12408429466820420244522395 18612644200230630366783593)
  ·
    refine ⟨13959483150172972775087695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18612644200230630366783593 13959483150172972775087695)
    ·
      refine ⟨20939224725259459162631543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959483150172972775087695 20939224725259459162631543)
      ·
        refine ⟨31408837087889188743947315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20939224725259459162631543 31408837087889188743947315)
        ·
          refine ⟨47113255631833783115920973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31408837087889188743947315 47113255631833783115920973)
          ·
            refine ⟨17667470861937668668470365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47113255631833783115920973 17667470861937668668470365)
            ·
              refine ⟨6625301573226625750676387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17667470861937668668470365 6625301573226625750676387)
              ·
                refine ⟨9937952359839938626014581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625301573226625750676387 9937952359839938626014581)
                ·
                  refine ⟨931683033734994246188867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9937952359839938626014581 931683033734994246188867)
                  ·
                    refine ⟨1397524550602491369283301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931683033734994246188867 1397524550602491369283301)
                    ·
                      refine ⟨262035853237967131740619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1397524550602491369283301 262035853237967131740619)
                      ·
                        rfl

theorem cell23_510313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_510313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510313 prefixEnd_510313 := by exact prefixLift 510313
  have htrace : WordTrace (prefixWord ++ tailWord_510313) baseStart_510313 baseEnd_510313 := by
    simpa [prefixWord, tailWord_510313, baseEnd_510313] using wordTrace_append hprefix tailTrace_510313
  have hstable : (prefixWord ++ tailWord_510313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510313).length < 2 ^ (prefixWord ++ tailWord_510313).sum := by decide
  have hdescent : baseEnd_510313 < baseStart_510313 := by decide
  rcases family_descends (prefixWord ++ tailWord_510313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510340 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_510340 : Nat := 118140960795 + 510340 * 2 ^ 59
def prefixEnd_510340 : Nat := 4983230072969 + 3 ^ 40 * 510340 * 2
def baseEnd_510340 : Nat := 87349905738546175367665

theorem tailTrace_510340 : CollatzResearch.WordTrace tailWord_510340 prefixEnd_510340 87349905738546175367665 := by
  unfold tailWord_510340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306814485566406989008237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12409085980755209318677649 9306814485566406989008237)
  ·
    refine ⟨3490055432087402620878089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9306814485566406989008237 3490055432087402620878089)
    ·
      refine ⟨2617541574065551965658567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3490055432087402620878089 2617541574065551965658567)
      ·
        refine ⟨3926312361098327948487851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617541574065551965658567 3926312361098327948487851)
        ·
          refine ⟨5889468541647491922731777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926312361098327948487851 5889468541647491922731777)
          ·
            refine ⟨4417101406235618942048833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889468541647491922731777 4417101406235618942048833)
            ·
              refine ⟨3312826054676714206536625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417101406235618942048833 3312826054676714206536625)
              ·
                refine ⟨2484619541007535654902469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312826054676714206536625 2484619541007535654902469)
                ·
                  refine ⟨465866163938912935294213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484619541007535654902469 465866163938912935294213)
                  ·
                    refine ⟨87349905738546175367665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465866163938912935294213 87349905738546175367665)
                    ·
                      rfl

theorem cell23_510340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_510340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510340 prefixEnd_510340 := by exact prefixLift 510340
  have htrace : WordTrace (prefixWord ++ tailWord_510340) baseStart_510340 baseEnd_510340 := by
    simpa [prefixWord, tailWord_510340, baseEnd_510340] using wordTrace_append hprefix tailTrace_510340
  have hstable : (prefixWord ++ tailWord_510340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510340).length < 2 ^ (prefixWord ++ tailWord_510340).sum := by decide
  have hdescent : baseEnd_510340 < baseStart_510340 := by decide
  rcases family_descends (prefixWord ++ tailWord_510340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510347 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 1, 1, 4]
def baseStart_510347 : Nat := 118140960795 + 510347 * 2 ^ 59
def prefixEnd_510347 : Nat := 4983230072969 + 3 ^ 40 * 510347 * 2
def baseEnd_510347 : Nat := 262053311580219998715463

theorem tailTrace_510347 : CollatzResearch.WordTrace tailWord_510347 prefixEnd_510347 262053311580219998715463 := by
  unfold tailWord_510347
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613884282107454173521295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12409256188071636115680863 18613884282107454173521295)
  ·
    refine ⟨27920826423161181260281943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18613884282107454173521295 27920826423161181260281943)
    ·
      refine ⟨41881239634741771890422915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27920826423161181260281943 41881239634741771890422915)
      ·
        refine ⟨62821859452112657835634373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41881239634741771890422915 62821859452112657835634373)
        ·
          refine ⟨11779098647271123344181445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62821859452112657835634373 11779098647271123344181445)
          ·
            refine ⟨2208580996363335627034021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11779098647271123344181445 2208580996363335627034021)
            ·
              refine ⟨414108936818125430068879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2208580996363335627034021 414108936818125430068879)
              ·
                refine ⟨621163405227188145103319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414108936818125430068879 621163405227188145103319)
                ·
                  refine ⟨931745107840782217654979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621163405227188145103319 931745107840782217654979)
                  ·
                    refine ⟨1397617661761173326482469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931745107840782217654979 1397617661761173326482469)
                    ·
                      refine ⟨262053311580219998715463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1397617661761173326482469 262053311580219998715463)
                      ·
                        rfl

theorem cell23_510347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 1, 1, 4].length) (baseStart_510347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510347 prefixEnd_510347 := by exact prefixLift 510347
  have htrace : WordTrace (prefixWord ++ tailWord_510347) baseStart_510347 baseEnd_510347 := by
    simpa [prefixWord, tailWord_510347, baseEnd_510347] using wordTrace_append hprefix tailTrace_510347
  have hstable : (prefixWord ++ tailWord_510347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510347).length < 2 ^ (prefixWord ++ tailWord_510347).sum := by decide
  have hdescent : baseEnd_510347 < baseStart_510347 := by decide
  rcases family_descends (prefixWord ++ tailWord_510347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510397 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 3]
def baseStart_510397 : Nat := 118140960795 + 510397 * 2 ^ 59
def prefixEnd_510397 : Nat := 4983230072969 + 3 ^ 40 * 510397 * 2
def baseEnd_510397 : Nat := 262078985612944803090233

theorem tailTrace_510397 : CollatzResearch.WordTrace tailWord_510397 prefixEnd_510397 262078985612944803090233 := by
  unfold tailWord_510397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615707931926312712841445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12410471954617541808560963 18615707931926312712841445)
  ·
    refine ⟨3490445237236183633657771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18615707931926312712841445 3490445237236183633657771)
    ·
      refine ⟨5235667855854275450486657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490445237236183633657771 5235667855854275450486657)
      ·
        refine ⟨3926750891890706587864993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5235667855854275450486657 3926750891890706587864993)
        ·
          refine ⟨2945063168918029940898745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3926750891890706587864993 2945063168918029940898745)
          ·
            refine ⟨2208797376688522455674059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2945063168918029940898745 2208797376688522455674059)
            ·
              refine ⟨3313196065032783683511089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208797376688522455674059 3313196065032783683511089)
              ·
                refine ⟨2484897048774587762633317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313196065032783683511089 2484897048774587762633317)
                ·
                  refine ⟨465918196645235205493747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2484897048774587762633317 465918196645235205493747)
                  ·
                    refine ⟨698877294967852808240621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465918196645235205493747 698877294967852808240621)
                    ·
                      refine ⟨262078985612944803090233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698877294967852808240621 262078985612944803090233)
                      ·
                        rfl

theorem cell23_510397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_510397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510397 prefixEnd_510397 := by exact prefixLift 510397
  have htrace : WordTrace (prefixWord ++ tailWord_510397) baseStart_510397 baseEnd_510397 := by
    simpa [prefixWord, tailWord_510397, baseEnd_510397] using wordTrace_append hprefix tailTrace_510397
  have hstable : (prefixWord ++ tailWord_510397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510397).length < 2 ^ (prefixWord ++ tailWord_510397).sum := by decide
  have hdescent : baseEnd_510397 < baseStart_510397 := by decide
  rcases family_descends (prefixWord ++ tailWord_510397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510401 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_510401 : Nat := 118140960795 + 510401 * 2 ^ 59
def prefixEnd_510401 : Nat := 4983230072969 + 3 ^ 40 * 510401 * 2
def baseEnd_510401 : Nat := 262081039535562787440215

theorem tailTrace_510401 : CollatzResearch.WordTrace tailWord_510401 prefixEnd_510401 262081039535562787440215 := by
  unfold tailWord_510401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615853823911821395987057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12410569215941214263991371 18615853823911821395987057)
  ·
    refine ⟨13961890367933866046990293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18615853823911821395987057 13961890367933866046990293)
    ·
      refine ⟨327231805498449985476335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13961890367933866046990293 327231805498449985476335)
      ·
        refine ⟨490847708247674978214503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327231805498449985476335 490847708247674978214503)
        ·
          refine ⟨736271562371512467321755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490847708247674978214503 736271562371512467321755)
          ·
            refine ⟨1104407343557268700982633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736271562371512467321755 1104407343557268700982633)
            ·
              refine ⟨828305507667951525736975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104407343557268700982633 828305507667951525736975)
              ·
                refine ⟨1242458261501927288605463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828305507667951525736975 1242458261501927288605463)
                ·
                  refine ⟨1863687392252890932908195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242458261501927288605463 1863687392252890932908195)
                  ·
                    refine ⟨2795531088379336399362293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863687392252890932908195 2795531088379336399362293)
                    ·
                      refine ⟨262081039535562787440215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2795531088379336399362293 262081039535562787440215)
                      ·
                        rfl

theorem cell23_510401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_510401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510401 prefixEnd_510401 := by exact prefixLift 510401
  have htrace : WordTrace (prefixWord ++ tailWord_510401) baseStart_510401 baseEnd_510401 := by
    simpa [prefixWord, tailWord_510401, baseEnd_510401] using wordTrace_append hprefix tailTrace_510401
  have hstable : (prefixWord ++ tailWord_510401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510401).length < 2 ^ (prefixWord ++ tailWord_510401).sum := by decide
  have hdescent : baseEnd_510401 < baseStart_510401 := by decide
  rcases family_descends (prefixWord ++ tailWord_510401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510403 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_510403 : Nat := 118140960795 + 510403 * 2 ^ 59
def prefixEnd_510403 : Nat := 4983230072969 + 3 ^ 40 * 510403 * 2
def baseEnd_510403 : Nat := 262082066496871779615205

theorem tailTrace_510403 : CollatzResearch.WordTrace tailWord_510403 prefixEnd_510403 262082066496871779615205 := by
  unfold tailWord_510403
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615926769904575737559863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12410617846603050491706575 18615926769904575737559863)
  ·
    refine ⟨27923890154856863606339795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18615926769904575737559863 27923890154856863606339795)
    ·
      refine ⟨41885835232285295409509693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27923890154856863606339795 41885835232285295409509693)
      ·
        refine ⟨15707188212106985778566135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41885835232285295409509693 15707188212106985778566135)
        ·
          refine ⟨23560782318160478667849203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15707188212106985778566135 23560782318160478667849203)
          ·
            refine ⟨35341173477240718001773805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23560782318160478667849203 35341173477240718001773805)
            ·
              refine ⟨13252940053965269250665177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35341173477240718001773805 13252940053965269250665177)
              ·
                refine ⟨9939705040473951937998883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252940053965269250665177 9939705040473951937998883)
                ·
                  refine ⟨14909557560710927906998325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939705040473951937998883 14909557560710927906998325)
                  ·
                    refine ⟨1397771021316649491281093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909557560710927906998325 1397771021316649491281093)
                    ·
                      refine ⟨262082066496871779615205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1397771021316649491281093 262082066496871779615205)
                      ·
                        rfl

theorem cell23_510403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_510403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510403 prefixEnd_510403 := by exact prefixLift 510403
  have htrace : WordTrace (prefixWord ++ tailWord_510403) baseStart_510403 baseEnd_510403 := by
    simpa [prefixWord, tailWord_510403, baseEnd_510403] using wordTrace_append hprefix tailTrace_510403
  have hstable : (prefixWord ++ tailWord_510403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510403).length < 2 ^ (prefixWord ++ tailWord_510403).sum := by decide
  have hdescent : baseEnd_510403 < baseStart_510403 := by decide
  rcases family_descends (prefixWord ++ tailWord_510403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510431 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 2, 1, 3]
def baseStart_510431 : Nat := 118140960795 + 510431 * 2 ^ 59
def prefixEnd_510431 : Nat := 4983230072969 + 3 ^ 40 * 510431 * 2
def baseEnd_510431 : Nat := 262096443955197670065077

theorem tailTrace_510431 : CollatzResearch.WordTrace tailWord_510431 prefixEnd_510431 262096443955197670065077 := by
  unfold tailWord_510431
  simp only [CollatzResearch.WordTrace]
  refine ⟨18616948013803136519579147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12411298675868757679719431 18616948013803136519579147)
  ·
    refine ⟨27925422020704704779368721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18616948013803136519579147 27925422020704704779368721)
    ·
      refine ⟨20944066515528528584526541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27925422020704704779368721 20944066515528528584526541)
      ·
        refine ⟨7854024943323198219197453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20944066515528528584526541 7854024943323198219197453)
        ·
          refine ⟨2945259353746199332199045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7854024943323198219197453 2945259353746199332199045)
          ·
            refine ⟨552236128827412374787321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2945259353746199332199045 552236128827412374787321)
            ·
              refine ⟨414177096620559281090491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552236128827412374787321 414177096620559281090491)
              ·
                refine ⟨621265644930838921635737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414177096620559281090491 621265644930838921635737)
                ·
                  refine ⟨465949233698129191226803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621265644930838921635737 465949233698129191226803)
                  ·
                    refine ⟨698923850547193786840205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 465949233698129191226803 698923850547193786840205)
                    ·
                      refine ⟨262096443955197670065077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 698923850547193786840205 262096443955197670065077)
                      ·
                        rfl

theorem cell23_510431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_510431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510431 prefixEnd_510431 := by exact prefixLift 510431
  have htrace : WordTrace (prefixWord ++ tailWord_510431) baseStart_510431 baseEnd_510431 := by
    simpa [prefixWord, tailWord_510431, baseEnd_510431] using wordTrace_append hprefix tailTrace_510431
  have hstable : (prefixWord ++ tailWord_510431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510431).length < 2 ^ (prefixWord ++ tailWord_510431).sum := by decide
  have hdescent : baseEnd_510431 < baseStart_510431 := by decide
  rcases family_descends (prefixWord ++ tailWord_510431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510440 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_510440 : Nat := 118140960795 + 510440 * 2 ^ 59
def prefixEnd_510440 : Nat := 4983230072969 + 3 ^ 40 * 510440 * 2
def baseEnd_510440 : Nat := 262101065281088134852535

theorem tailTrace_510440 : CollatzResearch.WordTrace tailWord_510440 prefixEnd_510440 262101065281088134852535 := by
  unfold tailWord_510440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308638135385265528328387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12411517513847020704437849 9308638135385265528328387)
  ·
    refine ⟨13962957203077898292492581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9308638135385265528328387 13962957203077898292492581)
    ·
      refine ⟨2618054475577105929842359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13962957203077898292492581 2618054475577105929842359)
      ·
        refine ⟨3927081713365658894763539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618054475577105929842359 3927081713365658894763539)
        ·
          refine ⟨5890622570048488342145309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927081713365658894763539 5890622570048488342145309)
          ·
            refine ⟨2208983463768183128304491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5890622570048488342145309 2208983463768183128304491)
            ·
              refine ⟨3313475195652274692456737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208983463768183128304491 3313475195652274692456737)
              ·
                refine ⟨2485106396739206019342553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313475195652274692456737 2485106396739206019342553)
                ·
                  refine ⟨1863829797554404514506915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485106396739206019342553 1863829797554404514506915)
                  ·
                    refine ⟨2795744696331606771760373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863829797554404514506915 2795744696331606771760373)
                    ·
                      refine ⟨262101065281088134852535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2795744696331606771760373 262101065281088134852535)
                      ·
                        rfl

theorem cell23_510440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_510440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510440 prefixEnd_510440 := by exact prefixLift 510440
  have htrace : WordTrace (prefixWord ++ tailWord_510440) baseStart_510440 baseEnd_510440 := by
    simpa [prefixWord, tailWord_510440, baseEnd_510440] using wordTrace_append hprefix tailTrace_510440
  have hstable : (prefixWord ++ tailWord_510440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510440).length < 2 ^ (prefixWord ++ tailWord_510440).sum := by decide
  have hdescent : baseEnd_510440 < baseStart_510440 := by decide
  rcases family_descends (prefixWord ++ tailWord_510440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510443 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 9]
def baseStart_510443 : Nat := 118140960795 + 510443 * 2 ^ 59
def prefixEnd_510443 : Nat := 4983230072969 + 3 ^ 40 * 510443 * 2
def baseEnd_510443 : Nat := 29122511747005735901669

theorem tailTrace_510443 : CollatzResearch.WordTrace tailWord_510443 prefixEnd_510443 29122511747005735901669 := by
  unfold tailWord_510443
  simp only [CollatzResearch.WordTrace]
  refine ⟨18617385689759662569015983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12411590459839775046010655 18617385689759662569015983)
  ·
    refine ⟨27926078534639493853523975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18617385689759662569015983 27926078534639493853523975)
    ·
      refine ⟨41889117801959240780285963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27926078534639493853523975 41889117801959240780285963)
      ·
        refine ⟨62833676702938861170428945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41889117801959240780285963 62833676702938861170428945)
        ·
          refine ⟨47125257527204145877821709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62833676702938861170428945 47125257527204145877821709)
          ·
            refine ⟨17671971572701554704183141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47125257527204145877821709 17671971572701554704183141)
            ·
              refine ⟨3313494669881541507034339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17671971572701554704183141 3313494669881541507034339)
              ·
                refine ⟨4970242004822312260551509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313494669881541507034339 4970242004822312260551509)
                ·
                  refine ⟨29122511747005735901669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4970242004822312260551509 29122511747005735901669)
                  ·
                    rfl

theorem cell23_510443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 9].length) (baseStart_510443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510443 prefixEnd_510443 := by exact prefixLift 510443
  have htrace : WordTrace (prefixWord ++ tailWord_510443) baseStart_510443 baseEnd_510443 := by
    simpa [prefixWord, tailWord_510443, baseEnd_510443] using wordTrace_append hprefix tailTrace_510443
  have hstable : (prefixWord ++ tailWord_510443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510443).length < 2 ^ (prefixWord ++ tailWord_510443).sum := by decide
  have hdescent : baseEnd_510443 < baseStart_510443 := by decide
  rcases family_descends (prefixWord ++ tailWord_510443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510454 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_510454 : Nat := 118140960795 + 510454 * 2 ^ 59
def prefixEnd_510454 : Nat := 4983230072969 + 3 ^ 40 * 510454 * 2
def baseEnd_510454 : Nat := 262108254010251080077471

theorem tailTrace_510454 : CollatzResearch.WordTrace tailWord_510454 prefixEnd_510454 262108254010251080077471 := by
  unfold tailWord_510454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163611680794988215479151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12411857928479874298444277 1163611680794988215479151)
  ·
    refine ⟨1745417521192482323218727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163611680794988215479151 1745417521192482323218727)
    ·
      refine ⟨2618126281788723484828091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745417521192482323218727 2618126281788723484828091)
      ·
        refine ⟨3927189422683085227242137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618126281788723484828091 3927189422683085227242137)
        ·
          refine ⟨2945392067012313920431603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927189422683085227242137 2945392067012313920431603)
          ·
            refine ⟨4418088100518470880647405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945392067012313920431603 4418088100518470880647405)
            ·
              refine ⟨1656783037694426580242777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4418088100518470880647405 1656783037694426580242777)
              ·
                refine ⟨1242587278270819935182083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656783037694426580242777 1242587278270819935182083)
                ·
                  refine ⟨1863880917406229902773125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242587278270819935182083 1863880917406229902773125)
                  ·
                    refine ⟨349477672013668106769961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863880917406229902773125 349477672013668106769961)
                    ·
                      refine ⟨262108254010251080077471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349477672013668106769961 262108254010251080077471)
                      ·
                        rfl

theorem cell23_510454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_510454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510454 prefixEnd_510454 := by exact prefixLift 510454
  have htrace : WordTrace (prefixWord ++ tailWord_510454) baseStart_510454 baseEnd_510454 := by
    simpa [prefixWord, tailWord_510454, baseEnd_510454] using wordTrace_append hprefix tailTrace_510454
  have hstable : (prefixWord ++ tailWord_510454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510454).length < 2 ^ (prefixWord ++ tailWord_510454).sum := by decide
  have hdescent : baseEnd_510454 < baseStart_510454 := by decide
  rcases family_descends (prefixWord ++ tailWord_510454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510484 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_510484 : Nat := 118140960795 + 510484 * 2 ^ 59
def prefixEnd_510484 : Nat := 4983230072969 + 3 ^ 40 * 510484 * 2
def baseEnd_510484 : Nat := 262123658429885962702333

theorem tailTrace_510484 : CollatzResearch.WordTrace tailWord_510484 prefixEnd_510484 262123658429885962702333 := by
  unfold tailWord_510484
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309440541305563285629253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12412587388407417714172337 9309440541305563285629253)
  ·
    refine ⟨1745520101494793116055485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9309440541305563285629253 1745520101494793116055485)
    ·
      refine ⟨654570038060547418520807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1745520101494793116055485 654570038060547418520807)
      ·
        refine ⟨981855057090821127781211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654570038060547418520807 981855057090821127781211)
        ·
          refine ⟨1472782585636231691671817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981855057090821127781211 1472782585636231691671817)
          ·
            refine ⟨1104586939227173768753863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472782585636231691671817 1104586939227173768753863)
            ·
              refine ⟨1656880408840760653130795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104586939227173768753863 1656880408840760653130795)
              ·
                refine ⟨2485320613261140979696193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656880408840760653130795 2485320613261140979696193)
                ·
                  refine ⟨1863990459945855734772145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485320613261140979696193 1863990459945855734772145)
                  ·
                    refine ⟨1397992844959391801079109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863990459945855734772145 1397992844959391801079109)
                    ·
                      refine ⟨262123658429885962702333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1397992844959391801079109 262123658429885962702333)
                      ·
                        rfl

theorem cell23_510484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_510484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510484 prefixEnd_510484 := by exact prefixLift 510484
  have htrace : WordTrace (prefixWord ++ tailWord_510484) baseStart_510484 baseEnd_510484 := by
    simpa [prefixWord, tailWord_510484, baseEnd_510484] using wordTrace_append hprefix tailTrace_510484
  have hstable : (prefixWord ++ tailWord_510484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510484).length < 2 ^ (prefixWord ++ tailWord_510484).sum := by decide
  have hdescent : baseEnd_510484 < baseStart_510484 := by decide
  rcases family_descends (prefixWord ++ tailWord_510484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510490 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_510490 : Nat := 118140960795 + 510490 * 2 ^ 59
def prefixEnd_510490 : Nat := 4983230072969 + 3 ^ 40 * 510490 * 2
def baseEnd_510490 : Nat := 87375579771270979742435

theorem tailTrace_510490 : CollatzResearch.WordTrace tailWord_510490 prefixEnd_510490 87375579771270979742435 := by
  unfold tailWord_510490
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654774980147347398994231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12412733280392926397317949 4654774980147347398994231)
  ·
    refine ⟨6982162470221021098491347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4654774980147347398994231 6982162470221021098491347)
    ·
      refine ⟨10473243705331531647737021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982162470221021098491347 10473243705331531647737021)
      ·
        refine ⟨3927466389499324367901383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10473243705331531647737021 3927466389499324367901383)
        ·
          refine ⟨5891199584248986551852075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927466389499324367901383 5891199584248986551852075)
          ·
            refine ⟨8836799376373479827778113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891199584248986551852075 8836799376373479827778113)
            ·
              refine ⟨6627599532280109870833585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8836799376373479827778113 6627599532280109870833585)
              ·
                refine ⟨4970699649210082403125189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627599532280109870833585 4970699649210082403125189)
                ·
                  refine ⟨932006184226890450585973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4970699649210082403125189 932006184226890450585973)
                  ·
                    refine ⟨87375579771270979742435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 932006184226890450585973 87375579771270979742435)
                    ·
                      rfl

theorem cell23_510490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_510490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510490 prefixEnd_510490 := by exact prefixLift 510490
  have htrace : WordTrace (prefixWord ++ tailWord_510490) baseStart_510490 baseEnd_510490 := by
    simpa [prefixWord, tailWord_510490, baseEnd_510490] using wordTrace_append hprefix tailTrace_510490
  have hstable : (prefixWord ++ tailWord_510490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510490).length < 2 ^ (prefixWord ++ tailWord_510490).sum := by decide
  have hdescent : baseEnd_510490 < baseStart_510490 := by decide
  rcases family_descends (prefixWord ++ tailWord_510490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510497 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_510497 : Nat := 118140960795 + 510497 * 2 ^ 59
def prefixEnd_510497 : Nat := 4983230072969 + 3 ^ 40 * 510497 * 2
def baseEnd_510497 : Nat := 262130333678394411839773

theorem tailTrace_510497 : CollatzResearch.WordTrace tailWord_510497 prefixEnd_510497 262130333678394411839773 := by
  unfold tailWord_510497
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619355231564029791481745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12412903487709353194321163 18619355231564029791481745)
  ·
    refine ⟨13964516423673022343611309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18619355231564029791481745 13964516423673022343611309)
    ·
      refine ⟨5236693658877383378854241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13964516423673022343611309 5236693658877383378854241)
      ·
        refine ⟨3927520244158037534140681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236693658877383378854241 3927520244158037534140681)
        ·
          refine ⟨2945640183118528150605511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927520244158037534140681 2945640183118528150605511)
          ·
            refine ⟨4418460274677792225908267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945640183118528150605511 4418460274677792225908267)
            ·
              refine ⟨6627690412016688338862401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418460274677792225908267 6627690412016688338862401)
              ·
                refine ⟨4970767809012516254146801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627690412016688338862401 4970767809012516254146801)
                ·
                  refine ⟨3728075856759387190610101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970767809012516254146801 3728075856759387190610101)
                  ·
                    refine ⟨349507111571192549119697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3728075856759387190610101 349507111571192549119697)
                    ·
                      refine ⟨262130333678394411839773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349507111571192549119697 262130333678394411839773)
                      ·
                        rfl

theorem cell23_510497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_510497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510497 prefixEnd_510497 := by exact prefixLift 510497
  have htrace : WordTrace (prefixWord ++ tailWord_510497) baseStart_510497 baseEnd_510497 := by
    simpa [prefixWord, tailWord_510497, baseEnd_510497] using wordTrace_append hprefix tailTrace_510497
  have hstable : (prefixWord ++ tailWord_510497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510497).length < 2 ^ (prefixWord ++ tailWord_510497).sum := by decide
  have hdescent : baseEnd_510497 < baseStart_510497 := by decide
  rcases family_descends (prefixWord ++ tailWord_510497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510509 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_510509 : Nat := 118140960795 + 510509 * 2 ^ 59
def prefixEnd_510509 : Nat := 4983230072969 + 3 ^ 40 * 510509 * 2
def baseEnd_510509 : Nat := 262136495446248364889719

theorem tailTrace_510509 : CollatzResearch.WordTrace tailWord_510509 prefixEnd_510509 262136495446248364889719 := by
  unfold tailWord_510509
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619792907520555840918581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12413195271680370560612387 18619792907520555840918581)
  ·
    refine ⟨1745605585080052110086117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18619792907520555840918581 1745605585080052110086117)
    ·
      refine ⟨327301047202509770641147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1745605585080052110086117 327301047202509770641147)
      ·
        refine ⟨490951570803764655961721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327301047202509770641147 490951570803764655961721)
        ·
          refine ⟨368213678102823491971291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490951570803764655961721 368213678102823491971291)
          ·
            refine ⟨552320517154235237956937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368213678102823491971291 552320517154235237956937)
            ·
              refine ⟨414240387865676428467703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552320517154235237956937 414240387865676428467703)
              ·
                refine ⟨621360581798514642701555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414240387865676428467703 621360581798514642701555)
                ·
                  refine ⟨932040872697771964052333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621360581798514642701555 932040872697771964052333)
                  ·
                    refine ⟨349515327261664486519625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932040872697771964052333 349515327261664486519625)
                    ·
                      refine ⟨262136495446248364889719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349515327261664486519625 262136495446248364889719)
                      ·
                        rfl

theorem cell23_510509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_510509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510509 prefixEnd_510509 := by exact prefixLift 510509
  have htrace : WordTrace (prefixWord ++ tailWord_510509) baseStart_510509 baseEnd_510509 := by
    simpa [prefixWord, tailWord_510509, baseEnd_510509] using wordTrace_append hprefix tailTrace_510509
  have hstable : (prefixWord ++ tailWord_510509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510509).length < 2 ^ (prefixWord ++ tailWord_510509).sum := by decide
  have hdescent : baseEnd_510509 < baseStart_510509 := by decide
  rcases family_descends (prefixWord ++ tailWord_510509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510527 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 4, 4, 2]
def baseStart_510527 : Nat := 118140960795 + 510527 * 2 ^ 59
def prefixEnd_510527 : Nat := 4983230072969 + 3 ^ 40 * 510527 * 2
def baseEnd_510527 : Nat := 262145738098029294464635

theorem tailTrace_510527 : CollatzResearch.WordTrace tailWord_510527 prefixEnd_510527 262145738098029294464635 := by
  unfold tailWord_510527
  simp only [CollatzResearch.WordTrace]
  refine ⟨18620449421455344915073835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12413632947636896610049223 18620449421455344915073835)
  ·
    refine ⟨27930674132183017372610753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18620449421455344915073835 27930674132183017372610753)
    ·
      refine ⟨20948005599137263029458065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27930674132183017372610753 20948005599137263029458065)
      ·
        refine ⟨15711004199352947272093549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20948005599137263029458065 15711004199352947272093549)
        ·
          refine ⟨5891626574757355227035081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15711004199352947272093549 5891626574757355227035081)
          ·
            refine ⟨4418719931068016420276311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5891626574757355227035081 4418719931068016420276311)
            ·
              refine ⟨6628079896602024630414467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418719931068016420276311 6628079896602024630414467)
              ·
                refine ⟨9942119844903036945621701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6628079896602024630414467 9942119844903036945621701)
                ·
                  refine ⟨1864147470919319427304069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9942119844903036945621701 1864147470919319427304069)
                  ·
                    refine ⟨349527650797372392619513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864147470919319427304069 349527650797372392619513)
                    ·
                      refine ⟨262145738098029294464635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349527650797372392619513 262145738098029294464635)
                      ·
                        rfl

theorem cell23_510527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_510527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510527 prefixEnd_510527 := by exact prefixLift 510527
  have htrace : WordTrace (prefixWord ++ tailWord_510527) baseStart_510527 baseEnd_510527 := by
    simpa [prefixWord, tailWord_510527, baseEnd_510527] using wordTrace_append hprefix tailTrace_510527
  have hstable : (prefixWord ++ tailWord_510527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510527).length < 2 ^ (prefixWord ++ tailWord_510527).sum := by decide
  have hdescent : baseEnd_510527 < baseStart_510527 := by decide
  rcases family_descends (prefixWord ++ tailWord_510527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510540 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_510540 : Nat := 118140960795 + 510540 * 2 ^ 59
def prefixEnd_510540 : Nat := 4983230072969 + 3 ^ 40 * 510540 * 2
def baseEnd_510540 : Nat := 262152413346537743602075

theorem tailTrace_510540 : CollatzResearch.WordTrace tailWord_510540 prefixEnd_510540 262152413346537743602075 := by
  unfold tailWord_510540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310461785204124067648537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12413949046938832090198049 9310461785204124067648537)
  ·
    refine ⟨6982846338903093050736403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9310461785204124067648537 6982846338903093050736403)
    ·
      refine ⟨10474269508354639576104605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982846338903093050736403 10474269508354639576104605)
      ·
        refine ⟨3927851065632989841039227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10474269508354639576104605 3927851065632989841039227)
        ·
          refine ⟨5891776598449484761558841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927851065632989841039227 5891776598449484761558841)
          ·
            refine ⟨4418832448837113571169131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5891776598449484761558841 4418832448837113571169131)
            ·
              refine ⟨6628248673255670356753697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418832448837113571169131 6628248673255670356753697)
              ·
                refine ⟨4971186504941752767565273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628248673255670356753697 4971186504941752767565273)
                ·
                  refine ⟨3728389878706314575673955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971186504941752767565273 3728389878706314575673955)
                  ·
                    refine ⟨5592584818059471863510933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3728389878706314575673955 5592584818059471863510933)
                    ·
                      refine ⟨262152413346537743602075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5592584818059471863510933 262152413346537743602075)
                      ·
                        rfl

theorem cell23_510540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_510540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510540 prefixEnd_510540 := by exact prefixLift 510540
  have htrace : WordTrace (prefixWord ++ tailWord_510540) baseStart_510540 baseEnd_510540 := by
    simpa [prefixWord, tailWord_510540, baseEnd_510540] using wordTrace_append hprefix tailTrace_510540
  have hstable : (prefixWord ++ tailWord_510540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510540).length < 2 ^ (prefixWord ++ tailWord_510540).sum := by decide
  have hdescent : baseEnd_510540 < baseStart_510540 := by decide
  rcases family_descends (prefixWord ++ tailWord_510540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510581 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_510581 : Nat := 118140960795 + 510581 * 2 ^ 59
def prefixEnd_510581 : Nat := 4983230072969 + 3 ^ 40 * 510581 * 2
def baseEnd_510581 : Nat := 262173466053372083189387

theorem tailTrace_510581 : CollatzResearch.WordTrace tailWord_510581 prefixEnd_510581 262173466053372083189387 := by
  unfold tailWord_510581
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622418963259712137539597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12414945975506474758359731 18622418963259712137539597)
  ·
    refine ⟨6983407111222392051577349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18622418963259712137539597 6983407111222392051577349)
    ·
      refine ⟨1309388833354198509670753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6983407111222392051577349 1309388833354198509670753)
      ·
        refine ⟨982041625015648882253065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1309388833354198509670753 982041625015648882253065)
        ·
          refine ⟨736531218761736661689799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982041625015648882253065 736531218761736661689799)
          ·
            refine ⟨1104796828142604992534699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736531218761736661689799 1104796828142604992534699)
            ·
              refine ⟨1657195242213907488802049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104796828142604992534699 1657195242213907488802049)
              ·
                refine ⟨1242896431660430616601537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657195242213907488802049 1242896431660430616601537)
                ·
                  refine ⟨932172323745322962451153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242896431660430616601537 932172323745322962451153)
                  ·
                    refine ⟨699129242808992221838365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932172323745322962451153 699129242808992221838365)
                    ·
                      refine ⟨262173466053372083189387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 699129242808992221838365 262173466053372083189387)
                      ·
                        rfl

theorem cell23_510581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_510581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510581 prefixEnd_510581 := by exact prefixLift 510581
  have htrace : WordTrace (prefixWord ++ tailWord_510581) baseStart_510581 baseEnd_510581 := by
    simpa [prefixWord, tailWord_510581, baseEnd_510581] using wordTrace_append hprefix tailTrace_510581
  have hstable : (prefixWord ++ tailWord_510581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510581).length < 2 ^ (prefixWord ++ tailWord_510581).sum := by decide
  have hdescent : baseEnd_510581 < baseStart_510581 := by decide
  rcases family_descends (prefixWord ++ tailWord_510581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510587 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 5, 2]
def baseStart_510587 : Nat := 118140960795 + 510587 * 2 ^ 59
def prefixEnd_510587 : Nat := 4983230072969 + 3 ^ 40 * 510587 * 2
def baseEnd_510587 : Nat := 262176546937299059714359

theorem tailTrace_510587 : CollatzResearch.WordTrace tailWord_510587 prefixEnd_510587 262176546937299059714359 := by
  unfold tailWord_510587
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622637801237975162258015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12415091867491983441505343 18622637801237975162258015)
  ·
    refine ⟨27933956701856962743387023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18622637801237975162258015 27933956701856962743387023)
    ·
      refine ⟨41900935052785444115080535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933956701856962743387023 41900935052785444115080535)
      ·
        refine ⟨62851402579178166172620803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41900935052785444115080535 62851402579178166172620803)
        ·
          refine ⟨94277103868767249258931205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62851402579178166172620803 94277103868767249258931205)
          ·
            refine ⟨17676956975393859236049601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94277103868767249258931205 17676956975393859236049601)
            ·
              refine ⟨13257717731545394427037201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17676956975393859236049601 13257717731545394427037201)
              ·
                refine ⟨9943288298659045820277901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13257717731545394427037201 9943288298659045820277901)
                ·
                  refine ⟨3728733111997142182604213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9943288298659045820277901 3728733111997142182604213)
                  ·
                    refine ⟨349568729249732079619145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3728733111997142182604213 349568729249732079619145)
                    ·
                      refine ⟨262176546937299059714359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349568729249732079619145 262176546937299059714359)
                      ·
                        rfl

theorem cell23_510587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5, 2].length) (baseStart_510587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510587 prefixEnd_510587 := by exact prefixLift 510587
  have htrace : WordTrace (prefixWord ++ tailWord_510587) baseStart_510587 baseEnd_510587 := by
    simpa [prefixWord, tailWord_510587, baseEnd_510587] using wordTrace_append hprefix tailTrace_510587
  have hstable : (prefixWord ++ tailWord_510587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510587).length < 2 ^ (prefixWord ++ tailWord_510587).sum := by decide
  have hdescent : baseEnd_510587 < baseStart_510587 := by decide
  rcases family_descends (prefixWord ++ tailWord_510587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510617 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_510617 : Nat := 118140960795 + 510617 * 2 ^ 59
def prefixEnd_510617 : Nat := 4983230072969 + 3 ^ 40 * 510617 * 2
def baseEnd_510617 : Nat := 262191951356933942339221

theorem tailTrace_510617 : CollatzResearch.WordTrace tailWord_510617 prefixEnd_510617 262191951356933942339221 := by
  unfold tailWord_510617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623731991129290285850105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12415821327419526857233403 18623731991129290285850105)
  ·
    refine ⟨13967798993346967714387579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18623731991129290285850105 13967798993346967714387579)
    ·
      refine ⟨20951698490020451571581369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13967798993346967714387579 20951698490020451571581369)
      ·
        refine ⟨15713773867515338678686027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20951698490020451571581369 15713773867515338678686027)
        ·
          refine ⟨23570660801273008018029041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15713773867515338678686027 23570660801273008018029041)
          ·
            refine ⟨17677995600954756013521781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23570660801273008018029041 17677995600954756013521781)
            ·
              refine ⟨1657312087589508376267667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17677995600954756013521781 1657312087589508376267667)
              ·
                refine ⟨2485968131384262564401501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657312087589508376267667 2485968131384262564401501)
                ·
                  refine ⟨932238049269098461650563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2485968131384262564401501 932238049269098461650563)
                  ·
                    refine ⟨1398357073903647692475845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 932238049269098461650563 1398357073903647692475845)
                    ·
                      refine ⟨262191951356933942339221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1398357073903647692475845 262191951356933942339221)
                      ·
                        rfl

theorem cell23_510617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_510617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510617 prefixEnd_510617 := by exact prefixLift 510617
  have htrace : WordTrace (prefixWord ++ tailWord_510617) baseStart_510617 baseEnd_510617 := by
    simpa [prefixWord, tailWord_510617, baseEnd_510617] using wordTrace_append hprefix tailTrace_510617
  have hstable : (prefixWord ++ tailWord_510617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510617).length < 2 ^ (prefixWord ++ tailWord_510617).sum := by decide
  have hdescent : baseEnd_510617 < baseStart_510617 := by decide
  rcases family_descends (prefixWord ++ tailWord_510617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510627 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 4, 4]
def baseStart_510627 : Nat := 118140960795 + 510627 * 2 ^ 59
def prefixEnd_510627 : Nat := 4983230072969 + 3 ^ 40 * 510627 * 2
def baseEnd_510627 : Nat := 87399028721159634404725

theorem tailTrace_510627 : CollatzResearch.WordTrace tailWord_510627 prefixEnd_510627 87399028721159634404725 := by
  unfold tailWord_510627
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624096721093061993714135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12416064480728707995809423 18624096721093061993714135)
  ·
    refine ⟨27936145081639592990571203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18624096721093061993714135 27936145081639592990571203)
    ·
      refine ⟨41904217622459389485856805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27936145081639592990571203 41904217622459389485856805)
      ·
        refine ⟨7857040804211135528598151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41904217622459389485856805 7857040804211135528598151)
        ·
          refine ⟨11785561206316703292897227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857040804211135528598151 11785561206316703292897227)
          ·
            refine ⟨17678341809475054939345841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785561206316703292897227 17678341809475054939345841)
            ·
              refine ⟨13258756357106291204509381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17678341809475054939345841 13258756357106291204509381)
              ·
                refine ⟨2486016816957429600845509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13258756357106291204509381 2486016816957429600845509)
                ·
                  refine ⟨466128153179518050158533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486016816957429600845509 466128153179518050158533)
                  ·
                    refine ⟨87399028721159634404725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466128153179518050158533 87399028721159634404725)
                    ·
                      rfl

theorem cell23_510627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 4].length) (baseStart_510627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510627 prefixEnd_510627 := by exact prefixLift 510627
  have htrace : WordTrace (prefixWord ++ tailWord_510627) baseStart_510627 baseEnd_510627 := by
    simpa [prefixWord, tailWord_510627, baseEnd_510627] using wordTrace_append hprefix tailTrace_510627
  have hstable : (prefixWord ++ tailWord_510627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510627).length < 2 ^ (prefixWord ++ tailWord_510627).sum := by decide
  have hdescent : baseEnd_510627 < baseStart_510627 := by decide
  rcases family_descends (prefixWord ++ tailWord_510627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510638 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_510638 : Nat := 118140960795 + 510638 * 2 ^ 59
def prefixEnd_510638 : Nat := 4983230072969 + 3 ^ 40 * 510638 * 2
def baseEnd_510638 : Nat := 262202734450678360176625

theorem tailTrace_510638 : CollatzResearch.WordTrace tailWord_510638 prefixEnd_510638 262202734450678360176625 := by
  unfold tailWord_510638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328062240506651359045571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12416331949368807248243045 2328062240506651359045571)
  ·
    refine ⟨3492093360759977038568357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2328062240506651359045571 3492093360759977038568357)
    ·
      refine ⟨654767505142495694731567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3492093360759977038568357 654767505142495694731567)
      ·
        refine ⟨982151257713743542097351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654767505142495694731567 982151257713743542097351)
        ·
          refine ⟨1473226886570615313146027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982151257713743542097351 1473226886570615313146027)
          ·
            refine ⟨2209840329855922969719041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473226886570615313146027 2209840329855922969719041)
            ·
              refine ⟨1657380247391942227289281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209840329855922969719041 1657380247391942227289281)
              ·
                refine ⟨1243035185543956670466961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657380247391942227289281 1243035185543956670466961)
                ·
                  refine ⟨932276389157967502850221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1243035185543956670466961 932276389157967502850221)
                  ·
                    refine ⟨349603645934237813568833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932276389157967502850221 349603645934237813568833)
                    ·
                      refine ⟨262202734450678360176625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349603645934237813568833 262202734450678360176625)
                      ·
                        rfl

theorem cell23_510638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_510638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510638 prefixEnd_510638 := by exact prefixLift 510638
  have htrace : WordTrace (prefixWord ++ tailWord_510638) baseStart_510638 baseEnd_510638 := by
    simpa [prefixWord, tailWord_510638, baseEnd_510638] using wordTrace_append hprefix tailTrace_510638
  have hstable : (prefixWord ++ tailWord_510638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510638).length < 2 ^ (prefixWord ++ tailWord_510638).sum := by decide
  have hdescent : baseEnd_510638 < baseStart_510638 := by decide
  rcases family_descends (prefixWord ++ tailWord_510638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510645 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_510645 : Nat := 118140960795 + 510645 * 2 ^ 59
def prefixEnd_510645 : Nat := 4983230072969 + 3 ^ 40 * 510645 * 2
def baseEnd_510645 : Nat := 262206328815259832789093

theorem tailTrace_510645 : CollatzResearch.WordTrace tailWord_510645 prefixEnd_510645 262206328815259832789093 := by
  unfold tailWord_510645
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624753235027851067869389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12416502156685234045246259 18624753235027851067869389)
  ·
    refine ⟨6984282463135444150451021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18624753235027851067869389 6984282463135444150451021)
    ·
      refine ⟨2619105923675791556419133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6984282463135444150451021 2619105923675791556419133)
      ·
        refine ⟨982164721378421833657175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2619105923675791556419133 982164721378421833657175)
        ·
          refine ⟨1473247082067632750485763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982164721378421833657175 1473247082067632750485763)
          ·
            refine ⟨2209870623101449125728645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473247082067632750485763 2209870623101449125728645)
            ·
              refine ⟨414350741831521711074121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2209870623101449125728645 414350741831521711074121)
              ·
                refine ⟨310763056373641283305591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414350741831521711074121 310763056373641283305591)
                ·
                  refine ⟨466144584560461924958387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310763056373641283305591 466144584560461924958387)
                  ·
                    refine ⟨699216876840692887437581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 466144584560461924958387 699216876840692887437581)
                    ·
                      refine ⟨262206328815259832789093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 699216876840692887437581 262206328815259832789093)
                      ·
                        rfl

theorem cell23_510645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_510645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510645 prefixEnd_510645 := by exact prefixLift 510645
  have htrace : WordTrace (prefixWord ++ tailWord_510645) baseStart_510645 baseEnd_510645 := by
    simpa [prefixWord, tailWord_510645, baseEnd_510645] using wordTrace_append hprefix tailTrace_510645
  have hstable : (prefixWord ++ tailWord_510645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510645).length < 2 ^ (prefixWord ++ tailWord_510645).sum := by decide
  have hdescent : baseEnd_510645 < baseStart_510645 := by decide
  rcases family_descends (prefixWord ++ tailWord_510645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510654 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_510654 : Nat := 118140960795 + 510654 * 2 ^ 59
def prefixEnd_510654 : Nat := 4983230072969 + 3 ^ 40 * 510654 * 2
def baseEnd_510654 : Nat := 262210950141150297576551

theorem tailTrace_510654 : CollatzResearch.WordTrace tailWord_510654 prefixEnd_510654 262210950141150297576551 := by
  unfold tailWord_510654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328135186499405700618377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12416720994663497069964677 2328135186499405700618377)
  ·
    refine ⟨1746101389874554275463783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2328135186499405700618377 1746101389874554275463783)
    ·
      refine ⟨2619152084811831413195675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746101389874554275463783 2619152084811831413195675)
      ·
        refine ⟨3928728127217747119793513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619152084811831413195675 3928728127217747119793513)
        ·
          refine ⟨2946546095413310339845135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3928728127217747119793513 2946546095413310339845135)
          ·
            refine ⟨4419819143119965509767703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946546095413310339845135 4419819143119965509767703)
            ·
              refine ⟨6629728714679948264651555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419819143119965509767703 6629728714679948264651555)
              ·
                refine ⟨9944593072019922396977333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629728714679948264651555 9944593072019922396977333)
                ·
                  refine ⟨932305600501867724716625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9944593072019922396977333 932305600501867724716625)
                  ·
                    refine ⟨699229200376400793537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 932305600501867724716625 699229200376400793537469)
                    ·
                      refine ⟨262210950141150297576551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 699229200376400793537469 262210950141150297576551)
                      ·
                        rfl

theorem cell23_510654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_510654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510654 prefixEnd_510654 := by exact prefixLift 510654
  have htrace : WordTrace (prefixWord ++ tailWord_510654) baseStart_510654 baseEnd_510654 := by
    simpa [prefixWord, tailWord_510654, baseEnd_510654] using wordTrace_append hprefix tailTrace_510654
  have hstable : (prefixWord ++ tailWord_510654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510654).length < 2 ^ (prefixWord ++ tailWord_510654).sum := by decide
  have hdescent : baseEnd_510654 < baseStart_510654 := by decide
  rcases family_descends (prefixWord ++ tailWord_510654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510664 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_510664 : Nat := 118140960795 + 510664 * 2 ^ 59
def prefixEnd_510664 : Nat := 4983230072969 + 3 ^ 40 * 510664 * 2
def baseEnd_510664 : Nat := 262216084947695258451505

theorem tailTrace_510664 : CollatzResearch.WordTrace tailWord_510664 prefixEnd_510664 262216084947695258451505 := by
  unfold tailWord_510664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312723110979508656405523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12416964147972678208540697 9312723110979508656405523)
  ·
    refine ⟨13969084666469262984608285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9312723110979508656405523 13969084666469262984608285)
    ·
      refine ⟨5238406749925973619228107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13969084666469262984608285 5238406749925973619228107)
      ·
        refine ⟨7857610124888960428842161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238406749925973619228107 7857610124888960428842161)
        ·
          refine ⟨5893207593666720321631621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7857610124888960428842161 5893207593666720321631621)
          ·
            refine ⟨1104976423812510060305929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5893207593666720321631621 1104976423812510060305929)
            ·
              refine ⟨828732317859382545229447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104976423812510060305929 828732317859382545229447)
              ·
                refine ⟨1243098476789073817844171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828732317859382545229447 1243098476789073817844171)
                ·
                  refine ⟨1864647715183610726766257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243098476789073817844171 1864647715183610726766257)
                  ·
                    refine ⟨1398485786387708045074693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1864647715183610726766257 1398485786387708045074693)
                    ·
                      refine ⟨262216084947695258451505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1398485786387708045074693 262216084947695258451505)
                      ·
                        rfl

theorem cell23_510664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_510664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510664 prefixEnd_510664 := by exact prefixLift 510664
  have htrace : WordTrace (prefixWord ++ tailWord_510664) baseStart_510664 baseEnd_510664 := by
    simpa [prefixWord, tailWord_510664, baseEnd_510664] using wordTrace_append hprefix tailTrace_510664
  have hstable : (prefixWord ++ tailWord_510664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510664).length < 2 ^ (prefixWord ++ tailWord_510664).sum := by decide
  have hdescent : baseEnd_510664 < baseStart_510664 := by decide
  rcases family_descends (prefixWord ++ tailWord_510664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510668 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_510668 : Nat := 118140960795 + 510668 * 2 ^ 59
def prefixEnd_510668 : Nat := 4983230072969 + 3 ^ 40 * 510668 * 2
def baseEnd_510668 : Nat := 262218138870313242801487

theorem tailTrace_510668 : CollatzResearch.WordTrace tailWord_510668 prefixEnd_510668 262218138870313242801487 := by
  unfold tailWord_510668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9312796056972262997978329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12417061409296350663971105 9312796056972262997978329)
  ·
    refine ⟨6984597042729197248483747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9312796056972262997978329 6984597042729197248483747)
    ·
      refine ⟨10476895564093795872725621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984597042729197248483747 10476895564093795872725621)
      ·
        refine ⟨982208959133793363068027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10476895564093795872725621 982208959133793363068027)
        ·
          refine ⟨1473313438700690044602041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982208959133793363068027 1473313438700690044602041)
          ·
            refine ⟨1104985079025517533451531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473313438700690044602041 1104985079025517533451531)
            ·
              refine ⟨1657477618538276300177297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104985079025517533451531 1657477618538276300177297)
              ·
                refine ⟨1243108213903707225132973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657477618538276300177297 1243108213903707225132973)
                ·
                  refine ⟨466165580213890209424865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243108213903707225132973 466165580213890209424865)
                  ·
                    refine ⟨349624185160417657068649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466165580213890209424865 349624185160417657068649)
                    ·
                      refine ⟨262218138870313242801487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349624185160417657068649 262218138870313242801487)
                      ·
                        rfl

theorem cell23_510668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_510668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510668 prefixEnd_510668 := by exact prefixLift 510668
  have htrace : WordTrace (prefixWord ++ tailWord_510668) baseStart_510668 baseEnd_510668 := by
    simpa [prefixWord, tailWord_510668, baseEnd_510668] using wordTrace_append hprefix tailTrace_510668
  have hstable : (prefixWord ++ tailWord_510668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510668).length < 2 ^ (prefixWord ++ tailWord_510668).sum := by decide
  have hdescent : baseEnd_510668 < baseStart_510668 := by decide
  rcases family_descends (prefixWord ++ tailWord_510668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510701 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_510701 : Nat := 118140960795 + 510701 * 2 ^ 59
def prefixEnd_510701 : Nat := 4983230072969 + 3 ^ 40 * 510701 * 2
def baseEnd_510701 : Nat := 262235083731911613688835

theorem tailTrace_510701 : CollatzResearch.WordTrace tailWord_510701 prefixEnd_510701 262235083731911613688835 := by
  unfold tailWord_510701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18626795722824972631907957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12417863815216648421271971 18626795722824972631907957)
  ·
    refine ⟨1746262099014841184241371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18626795722824972631907957 1746262099014841184241371)
    ·
      refine ⟨2619393148522261776362057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746262099014841184241371 2619393148522261776362057)
      ·
        refine ⟨1964544861391696332271543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619393148522261776362057 1964544861391696332271543)
        ·
          refine ⟨2946817292087544498407315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964544861391696332271543 2946817292087544498407315)
          ·
            refine ⟨4420225938131316747610973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946817292087544498407315 4420225938131316747610973)
            ·
              refine ⟨1657584726799243780354115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4420225938131316747610973 1657584726799243780354115)
              ·
                refine ⟨2486377090198865670531173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657584726799243780354115 2486377090198865670531173)
                ·
                  refine ⟨466195704412287313224595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2486377090198865670531173 466195704412287313224595)
                  ·
                    refine ⟨699293556618430969836893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 466195704412287313224595 699293556618430969836893)
                    ·
                      refine ⟨262235083731911613688835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 699293556618430969836893 262235083731911613688835)
                      ·
                        rfl

theorem cell23_510701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_510701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510701 prefixEnd_510701 := by exact prefixLift 510701
  have htrace : WordTrace (prefixWord ++ tailWord_510701) baseStart_510701 baseEnd_510701 := by
    simpa [prefixWord, tailWord_510701, baseEnd_510701] using wordTrace_append hprefix tailTrace_510701
  have hstable : (prefixWord ++ tailWord_510701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510701).length < 2 ^ (prefixWord ++ tailWord_510701).sum := by decide
  have hdescent : baseEnd_510701 < baseStart_510701 := by decide
  rcases family_descends (prefixWord ++ tailWord_510701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510717 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_510717 : Nat := 118140960795 + 510717 * 2 ^ 59
def prefixEnd_510717 : Nat := 4983230072969 + 3 ^ 40 * 510717 * 2
def baseEnd_510717 : Nat := 87414433140794517029587

theorem tailTrace_510717 : CollatzResearch.WordTrace tailWord_510717 prefixEnd_510717 87414433140794517029587 := by
  unfold tailWord_510717
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627379290767007364490405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12418252860511338242993603 18627379290767007364490405)
  ·
    refine ⟨3492633617018813880841951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18627379290767007364490405 3492633617018813880841951)
    ·
      refine ⟨5238950425528220821262927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3492633617018813880841951 5238950425528220821262927)
      ·
        refine ⟨7858425638292331231894391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238950425528220821262927 7858425638292331231894391)
        ·
          refine ⟨11787638457438496847841587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858425638292331231894391 11787638457438496847841587)
          ·
            refine ⟨17681457686157745271762381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787638457438496847841587 17681457686157745271762381)
            ·
              refine ⟨6630546632309154476910893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17681457686157745271762381 6630546632309154476910893)
              ·
                refine ⟨2486454987115932928841585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6630546632309154476910893 2486454987115932928841585)
                ·
                  refine ⟨1864841240336949696631189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486454987115932928841585 1864841240336949696631189)
                  ·
                    refine ⟨87414433140794517029587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1864841240336949696631189 87414433140794517029587)
                    ·
                      rfl

theorem cell23_510717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_510717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510717 prefixEnd_510717 := by exact prefixLift 510717
  have htrace : WordTrace (prefixWord ++ tailWord_510717) baseStart_510717 baseEnd_510717 := by
    simpa [prefixWord, tailWord_510717, baseEnd_510717] using wordTrace_append hprefix tailTrace_510717
  have hstable : (prefixWord ++ tailWord_510717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510717).length < 2 ^ (prefixWord ++ tailWord_510717).sum := by decide
  have hdescent : baseEnd_510717 < baseStart_510717 := by decide
  rcases family_descends (prefixWord ++ tailWord_510717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510718 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_510718 : Nat := 118140960795 + 510718 * 2 ^ 59
def prefixEnd_510718 : Nat := 4983230072969 + 3 ^ 40 * 510718 * 2
def baseEnd_510718 : Nat := 262243812903038047176257

theorem tailTrace_510718 : CollatzResearch.WordTrace tailWord_510718 prefixEnd_510718 262243812903038047176257 := by
  unfold tailWord_510718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328426970470423066909601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12418277175842256356851205 2328426970470423066909601)
  ·
    refine ⟨1746320227852817300182201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2328426970470423066909601 1746320227852817300182201)
    ·
      refine ⟨1309740170889612975136651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1746320227852817300182201 1309740170889612975136651)
      ·
        refine ⟨1964610256334419462704977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309740170889612975136651 1964610256334419462704977)
        ·
          refine ⟨1473457692250814597028733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964610256334419462704977 1473457692250814597028733)
          ·
            refine ⟨552546634594055473885775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1473457692250814597028733 552546634594055473885775)
            ·
              refine ⟨828819951891083210828663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552546634594055473885775 828819951891083210828663)
              ·
                refine ⟨1243229927836624816242995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828819951891083210828663 1243229927836624816242995)
                ·
                  refine ⟨1864844891754937224364493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243229927836624816242995 1864844891754937224364493)
                  ·
                    refine ⟨699316834408101459136685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1864844891754937224364493 699316834408101459136685)
                    ·
                      refine ⟨262243812903038047176257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 699316834408101459136685 262243812903038047176257)
                      ·
                        rfl

theorem cell23_510718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_510718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510718 prefixEnd_510718 := by exact prefixLift 510718
  have htrace : WordTrace (prefixWord ++ tailWord_510718) baseStart_510718 baseEnd_510718 := by
    simpa [prefixWord, tailWord_510718, baseEnd_510718] using wordTrace_append hprefix tailTrace_510718
  have hstable : (prefixWord ++ tailWord_510718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510718).length < 2 ^ (prefixWord ++ tailWord_510718).sum := by decide
  have hdescent : baseEnd_510718 < baseStart_510718 := by decide
  rcases family_descends (prefixWord ++ tailWord_510718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510728 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_510728 : Nat := 118140960795 + 510728 * 2 ^ 59
def prefixEnd_510728 : Nat := 4983230072969 + 3 ^ 40 * 510728 * 2
def baseEnd_510728 : Nat := 262248947709583008051211

theorem tailTrace_510728 : CollatzResearch.WordTrace tailWord_510728 prefixEnd_510728 262248947709583008051211 := by
  unfold tailWord_510728
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313890246863578121570419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12418520329151437495427225 9313890246863578121570419)
  ·
    refine ⟨13970835370295367182355629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313890246863578121570419 13970835370295367182355629)
    ·
      refine ⟨5239063263860762693383361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13970835370295367182355629 5239063263860762693383361)
      ·
        refine ⟨3929297447895572020037521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5239063263860762693383361 3929297447895572020037521)
        ·
          refine ⟨2946973085921679015028141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3929297447895572020037521 2946973085921679015028141)
          ·
            refine ⟨1105114907220629630635553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2946973085921679015028141 1105114907220629630635553)
            ·
              refine ⟨828836180415472222976665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105114907220629630635553 828836180415472222976665)
              ·
                refine ⟨621627135311604167232499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828836180415472222976665 621627135311604167232499)
                ·
                  refine ⟨932440702967406250848749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621627135311604167232499 932440702967406250848749)
                  ·
                    refine ⟨349665263612777344068281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932440702967406250848749 349665263612777344068281)
                    ·
                      refine ⟨262248947709583008051211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349665263612777344068281 262248947709583008051211)
                      ·
                        rfl

theorem cell23_510728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_510728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510728 prefixEnd_510728 := by exact prefixLift 510728
  have htrace : WordTrace (prefixWord ++ tailWord_510728) baseStart_510728 baseEnd_510728 := by
    simpa [prefixWord, tailWord_510728, baseEnd_510728] using wordTrace_append hprefix tailTrace_510728
  have hstable : (prefixWord ++ tailWord_510728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510728).length < 2 ^ (prefixWord ++ tailWord_510728).sum := by decide
  have hdescent : baseEnd_510728 < baseStart_510728 := by decide
  rcases family_descends (prefixWord ++ tailWord_510728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510737 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_510737 : Nat := 118140960795 + 510737 * 2 ^ 59
def prefixEnd_510737 : Nat := 4983230072969 + 3 ^ 40 * 510737 * 2
def baseEnd_510737 : Nat := 262253569035473472838669

theorem tailTrace_510737 : CollatzResearch.WordTrace tailWord_510737 prefixEnd_510737 262253569035473472838669 := by
  unfold tailWord_510737
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628108750694550780218465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12418739167129700520145643 18628108750694550780218465)
  ·
    refine ⟨13971081563020913085163849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18628108750694550780218465 13971081563020913085163849)
    ·
      refine ⟨10478311172265684813872887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13971081563020913085163849 10478311172265684813872887)
      ·
        refine ⟨15717466758398527220809331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478311172265684813872887 15717466758398527220809331)
        ·
          refine ⟨23576200137597790831213997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15717466758398527220809331 23576200137597790831213997)
          ·
            refine ⟨8841075051599171561705249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23576200137597790831213997 8841075051599171561705249)
            ·
              refine ⟨6630806288699378671278937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841075051599171561705249 6630806288699378671278937)
              ·
                refine ⟨4973104716524534003459203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630806288699378671278937 4973104716524534003459203)
                ·
                  refine ⟨7459657074786801005188805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973104716524534003459203 7459657074786801005188805)
                  ·
                    refine ⟨1398685701522525188472901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459657074786801005188805 1398685701522525188472901)
                    ·
                      refine ⟨262253569035473472838669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1398685701522525188472901 262253569035473472838669)
                      ·
                        rfl

theorem cell23_510737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_510737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510737 prefixEnd_510737 := by exact prefixLift 510737
  have htrace : WordTrace (prefixWord ++ tailWord_510737) baseStart_510737 baseEnd_510737 := by
    simpa [prefixWord, tailWord_510737, baseEnd_510737] using wordTrace_append hprefix tailTrace_510737
  have hstable : (prefixWord ++ tailWord_510737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510737).length < 2 ^ (prefixWord ++ tailWord_510737).sum := by decide
  have hdescent : baseEnd_510737 < baseStart_510737 := by decide
  rcases family_descends (prefixWord ++ tailWord_510737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510741 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_510741 : Nat := 118140960795 + 510741 * 2 ^ 59
def prefixEnd_510741 : Nat := 4983230072969 + 3 ^ 40 * 510741 * 2
def baseEnd_510741 : Nat := 262255622958091457188651

theorem tailTrace_510741 : CollatzResearch.WordTrace tailWord_510741 prefixEnd_510741 262255622958091457188651 := by
  unfold tailWord_510741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628254642680059463364077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12418836428453372975576051 18628254642680059463364077)
  ·
    refine ⟨6985595491005022298761529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18628254642680059463364077 6985595491005022298761529)
    ·
      refine ⟨5239196618253766724071147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6985595491005022298761529 5239196618253766724071147)
      ·
        refine ⟨7858794927380650086106721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5239196618253766724071147 7858794927380650086106721)
        ·
          refine ⟨5894096195535487564580041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7858794927380650086106721 5894096195535487564580041)
          ·
            refine ⟨4420572146651615673435031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894096195535487564580041 4420572146651615673435031)
            ·
              refine ⟨6630858219977423510152547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420572146651615673435031 6630858219977423510152547)
              ·
                refine ⟨9946287329966135265228821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630858219977423510152547 9946287329966135265228821)
                ·
                  refine ⟨466232218592162590557601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9946287329966135265228821 466232218592162590557601)
                  ·
                    refine ⟨349674163944121942918201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466232218592162590557601 349674163944121942918201)
                    ·
                      refine ⟨262255622958091457188651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349674163944121942918201 262255622958091457188651)
                      ·
                        rfl

theorem cell23_510741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_510741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510741 prefixEnd_510741 := by exact prefixLift 510741
  have htrace : WordTrace (prefixWord ++ tailWord_510741) baseStart_510741 baseEnd_510741 := by
    simpa [prefixWord, tailWord_510741, baseEnd_510741] using wordTrace_append hprefix tailTrace_510741
  have hstable : (prefixWord ++ tailWord_510741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510741).length < 2 ^ (prefixWord ++ tailWord_510741).sum := by decide
  have hdescent : baseEnd_510741 < baseStart_510741 := by decide
  rcases family_descends (prefixWord ++ tailWord_510741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510757 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_510757 : Nat := 118140960795 + 510757 * 2 ^ 59
def prefixEnd_510757 : Nat := 4983230072969 + 3 ^ 40 * 510757 * 2
def baseEnd_510757 : Nat := 262263838648563394588577

theorem tailTrace_510757 : CollatzResearch.WordTrace tailWord_510757 prefixEnd_510757 262263838648563394588577 := by
  unfold tailWord_510757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628838210622094195946525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12419225473748062797297683 18628838210622094195946525)
  ·
    refine ⟨6985814328983285323479947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18628838210622094195946525 6985814328983285323479947)
    ·
      refine ⟨10478721493474927985219921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6985814328983285323479947 10478721493474927985219921)
      ·
        refine ⟨7859041120106195988914941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10478721493474927985219921 7859041120106195988914941)
        ·
          refine ⟨2947140420039823495843103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7859041120106195988914941 2947140420039823495843103)
          ·
            refine ⟨4420710630059735243764655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947140420039823495843103 4420710630059735243764655)
            ·
              refine ⟨6631065945089602865646983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420710630059735243764655 6631065945089602865646983)
              ·
                refine ⟨9946598917634404298470475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631065945089602865646983 9946598917634404298470475)
                ·
                  refine ⟨14919898376451606447705713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946598917634404298470475 14919898376451606447705713)
                  ·
                    refine ⟨11189923782338704835779285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14919898376451606447705713 11189923782338704835779285)
                    ·
                      refine ⟨262263838648563394588577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11189923782338704835779285 262263838648563394588577)
                      ·
                        rfl

theorem cell23_510757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_510757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510757 prefixEnd_510757 := by exact prefixLift 510757
  have htrace : WordTrace (prefixWord ++ tailWord_510757) baseStart_510757 baseEnd_510757 := by
    simpa [prefixWord, tailWord_510757, baseEnd_510757] using wordTrace_append hprefix tailTrace_510757
  have hstable : (prefixWord ++ tailWord_510757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510757).length < 2 ^ (prefixWord ++ tailWord_510757).sum := by decide
  have hdescent : baseEnd_510757 < baseStart_510757 := by decide
  rcases family_descends (prefixWord ++ tailWord_510757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510787 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_510787 : Nat := 118140960795 + 510787 * 2 ^ 59
def prefixEnd_510787 : Nat := 4983230072969 + 3 ^ 40 * 510787 * 2
def baseEnd_510787 : Nat := 262279243068198277213439

theorem tailTrace_510787 : CollatzResearch.WordTrace tailWord_510787 prefixEnd_510787 262279243068198277213439 := by
  unfold tailWord_510787
  simp only [CollatzResearch.WordTrace]
  refine ⟨18629932400513409319538615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12419954933675606213025743 18629932400513409319538615)
  ·
    refine ⟨27944898600770113979307923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18629932400513409319538615 27944898600770113979307923)
    ·
      refine ⟨41917347901155170968961885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27944898600770113979307923 41917347901155170968961885)
      ·
        refine ⟨15719005462933189113360707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41917347901155170968961885 15719005462933189113360707)
        ·
          refine ⟨23578508194399783670041061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15719005462933189113360707 23578508194399783670041061)
          ·
            refine ⟨4420970286449959438132699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23578508194399783670041061 4420970286449959438132699)
            ·
              refine ⟨6631455429674939157199049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420970286449959438132699 6631455429674939157199049)
              ·
                refine ⟨4973591572256204367899287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6631455429674939157199049 4973591572256204367899287)
                ·
                  refine ⟨7460387358384306551848931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973591572256204367899287 7460387358384306551848931)
                  ·
                    refine ⟨11190581037576459827773397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460387358384306551848931 11190581037576459827773397)
                    ·
                      refine ⟨262279243068198277213439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11190581037576459827773397 262279243068198277213439)
                      ·
                        rfl

theorem cell23_510787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_510787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510787 prefixEnd_510787 := by exact prefixLift 510787
  have htrace : WordTrace (prefixWord ++ tailWord_510787) baseStart_510787 baseEnd_510787 := by
    simpa [prefixWord, tailWord_510787, baseEnd_510787] using wordTrace_append hprefix tailTrace_510787
  have hstable : (prefixWord ++ tailWord_510787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510787).length < 2 ^ (prefixWord ++ tailWord_510787).sum := by decide
  have hdescent : baseEnd_510787 < baseStart_510787 := by decide
  rcases family_descends (prefixWord ++ tailWord_510787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510841 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_510841 : Nat := 118140960795 + 510841 * 2 ^ 59
def prefixEnd_510841 : Nat := 4983230072969 + 3 ^ 40 * 510841 * 2
def baseEnd_510841 : Nat := 87435657007847021979397

theorem tailTrace_510841 : CollatzResearch.WordTrace tailWord_510841 prefixEnd_510841 87435657007847021979397 := by
  unfold tailWord_510841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631901942317776542004377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12421267961545184361336251 18631901942317776542004377)
  ·
    refine ⟨13973926456738332406503283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18631901942317776542004377 13973926456738332406503283)
    ·
      refine ⟨20960889685107498609754925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13973926456738332406503283 20960889685107498609754925)
      ·
        refine ⟨7860333631915311978658097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20960889685107498609754925 7860333631915311978658097)
        ·
          refine ⟨5895250223936483983993573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7860333631915311978658097 5895250223936483983993573)
          ·
            refine ⟨1105359416988090746998795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5895250223936483983993573 1105359416988090746998795)
            ·
              refine ⟨1658039125482136120498193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105359416988090746998795 1658039125482136120498193)
              ·
                refine ⟨1243529344111602090373645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658039125482136120498193 1243529344111602090373645)
                ·
                  refine ⟨466323504041850783890117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1243529344111602090373645 466323504041850783890117)
                  ·
                    refine ⟨87435657007847021979397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466323504041850783890117 87435657007847021979397)
                    ·
                      rfl

theorem cell23_510841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_510841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510841 prefixEnd_510841 := by exact prefixLift 510841
  have htrace : WordTrace (prefixWord ++ tailWord_510841) baseStart_510841 baseEnd_510841 := by
    simpa [prefixWord, tailWord_510841, baseEnd_510841] using wordTrace_append hprefix tailTrace_510841
  have hstable : (prefixWord ++ tailWord_510841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510841).length < 2 ^ (prefixWord ++ tailWord_510841).sum := by decide
  have hdescent : baseEnd_510841 < baseStart_510841 := by decide
  rcases family_descends (prefixWord ++ tailWord_510841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 4, 3, 2]
def baseStart_510891 : Nat := 118140960795 + 510891 * 2 ^ 59
def prefixEnd_510891 : Nat := 4983230072969 + 3 ^ 40 * 510891 * 2
def baseEnd_510891 : Nat := 262332645056265870312961

theorem tailTrace_510891 : CollatzResearch.WordTrace tailWord_510891 prefixEnd_510891 262332645056265870312961 := by
  unfold tailWord_510891
  simp only [CollatzResearch.WordTrace]
  refine ⟨18633725592136635081324527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12422483728091090054216351 18633725592136635081324527)
  ·
    refine ⟨27950588388204952621986791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18633725592136635081324527 27950588388204952621986791)
    ·
      refine ⟨41925882582307428932980187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27950588388204952621986791 41925882582307428932980187)
      ·
        refine ⟨62888823873461143399470281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41925882582307428932980187 62888823873461143399470281)
        ·
          refine ⟨47166617905095857549602711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62888823873461143399470281 47166617905095857549602711)
          ·
            refine ⟨70749926857643786324404067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47166617905095857549602711 70749926857643786324404067)
            ·
              refine ⟨106124890286465679486606101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70749926857643786324404067 106124890286465679486606101)
              ·
                refine ⟨4974604232178078725934661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106124890286465679486606101 4974604232178078725934661)
                ·
                  refine ⟨932738293533389761112749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4974604232178078725934661 932738293533389761112749)
                  ·
                    refine ⟨349776860075021160417281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932738293533389761112749 349776860075021160417281)
                    ·
                      refine ⟨262332645056265870312961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349776860075021160417281 262332645056265870312961)
                      ·
                        rfl

theorem cell23_510891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3, 2].length) (baseStart_510891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510891 prefixEnd_510891 := by exact prefixLift 510891
  have htrace : WordTrace (prefixWord ++ tailWord_510891) baseStart_510891 baseEnd_510891 := by
    simpa [prefixWord, tailWord_510891, baseEnd_510891] using wordTrace_append hprefix tailTrace_510891
  have hstable : (prefixWord ++ tailWord_510891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510891).length < 2 ^ (prefixWord ++ tailWord_510891).sum := by decide
  have hdescent : baseEnd_510891 < baseStart_510891 := by decide
  rcases family_descends (prefixWord ++ tailWord_510891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510951 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_510951 : Nat := 118140960795 + 510951 * 2 ^ 59
def prefixEnd_510951 : Nat := 4983230072969 + 3 ^ 40 * 510951 * 2
def baseEnd_510951 : Nat := 262363453895535635562685

theorem tailTrace_510951 : CollatzResearch.WordTrace tailWord_510951 prefixEnd_510951 262363453895535635562685 := by
  unfold tailWord_510951
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635913971919265328508707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12423942647946176885672471 18635913971919265328508707)
  ·
    refine ⟨27953870957878897992763061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635913971919265328508707 27953870957878897992763061)
    ·
      refine ⟨2620675402301146686821537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27953870957878897992763061 2620675402301146686821537)
      ·
        refine ⟨1965506551725860015116153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2620675402301146686821537 1965506551725860015116153)
        ·
          refine ⟨1474129913794395011337115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965506551725860015116153 1474129913794395011337115)
          ·
            refine ⟨2211194870691592517005673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474129913794395011337115 2211194870691592517005673)
            ·
              refine ⟨1658396153018694387754255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211194870691592517005673 1658396153018694387754255)
              ·
                refine ⟨2487594229528041581631383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658396153018694387754255 2487594229528041581631383)
                ·
                  refine ⟨3731391344292062372447075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487594229528041581631383 3731391344292062372447075)
                  ·
                    refine ⟨5597087016438093558670613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731391344292062372447075 5597087016438093558670613)
                    ·
                      refine ⟨262363453895535635562685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5597087016438093558670613 262363453895535635562685)
                      ·
                        rfl

theorem cell23_510951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_510951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510951 prefixEnd_510951 := by exact prefixLift 510951
  have htrace : WordTrace (prefixWord ++ tailWord_510951) baseStart_510951 baseEnd_510951 := by
    simpa [prefixWord, tailWord_510951, baseEnd_510951] using wordTrace_append hprefix tailTrace_510951
  have hstable : (prefixWord ++ tailWord_510951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510951).length < 2 ^ (prefixWord ++ tailWord_510951).sum := by decide
  have hdescent : baseEnd_510951 < baseStart_510951 := by decide
  rcases family_descends (prefixWord ++ tailWord_510951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510965 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_510965 : Nat := 118140960795 + 510965 * 2 ^ 59
def prefixEnd_510965 : Nat := 4983230072969 + 3 ^ 40 * 510965 * 2
def baseEnd_510965 : Nat := 87456880874899526929207

theorem tailTrace_510965 : CollatzResearch.WordTrace tailWord_510965 prefixEnd_510965 87456880874899526929207 := by
  unfold tailWord_510965
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636424593868545719518349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12424283062579030479678899 18636424593868545719518349)
  ·
    refine ⟨6988659222700704644819381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18636424593868545719518349 6988659222700704644819381)
    ·
      refine ⟨655186802128191060451817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6988659222700704644819381 655186802128191060451817)
      ·
        refine ⟨491390101596143295338863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655186802128191060451817 491390101596143295338863)
        ·
          refine ⟨737085152394214943008295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491390101596143295338863 737085152394214943008295)
          ·
            refine ⟨1105627728591322414512443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737085152394214943008295 1105627728591322414512443)
            ·
              refine ⟨1658441592886983621768665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105627728591322414512443 1658441592886983621768665)
              ·
                refine ⟨1243831194665237716326499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658441592886983621768665 1243831194665237716326499)
                ·
                  refine ⟨1865746791997856574489749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243831194665237716326499 1865746791997856574489749)
                  ·
                    refine ⟨87456880874899526929207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1865746791997856574489749 87456880874899526929207)
                    ·
                      rfl

theorem cell23_510965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_510965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510965 prefixEnd_510965 := by exact prefixLift 510965
  have htrace : WordTrace (prefixWord ++ tailWord_510965) baseStart_510965 baseEnd_510965 := by
    simpa [prefixWord, tailWord_510965, baseEnd_510965] using wordTrace_append hprefix tailTrace_510965
  have hstable : (prefixWord ++ tailWord_510965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510965).length < 2 ^ (prefixWord ++ tailWord_510965).sum := by decide
  have hdescent : baseEnd_510965 < baseStart_510965 := by decide
  rcases family_descends (prefixWord ++ tailWord_510965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510978 : List Nat := [3, 4, 1, 3, 1, 11]
def baseStart_510978 : Nat := 118140960795 + 510978 * 2 ^ 59
def prefixEnd_510978 : Nat := 4983230072969 + 3 ^ 40 * 510978 * 2
def baseEnd_510978 : Nat := 1079742048860934279527

theorem tailTrace_510978 : CollatzResearch.WordTrace tailWord_510978 prefixEnd_510978 1079742048860934279527 := by
  unfold tailWord_510978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659224685705362234935397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12424599161880965959827725 4659224685705362234935397)
  ·
    refine ⟨873604628569755419050387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4659224685705362234935397 873604628569755419050387)
    ·
      refine ⟨1310406942854633128575581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873604628569755419050387 1310406942854633128575581)
      ·
        refine ⟨491402603570487423215843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1310406942854633128575581 491402603570487423215843)
        ·
          refine ⟨737103905355731134823765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491402603570487423215843 737103905355731134823765)
          ·
            refine ⟨1079742048860934279527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 737103905355731134823765 1079742048860934279527)
            ·
              rfl

theorem cell23_510978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 11].length) (baseStart_510978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_510978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_510978 prefixEnd_510978 := by exact prefixLift 510978
  have htrace : WordTrace (prefixWord ++ tailWord_510978) baseStart_510978 baseEnd_510978 := by
    simpa [prefixWord, tailWord_510978, baseEnd_510978] using wordTrace_append hprefix tailTrace_510978
  have hstable : (prefixWord ++ tailWord_510978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510978).length < 2 ^ (prefixWord ++ tailWord_510978).sum := by decide
  have hdescent : baseEnd_510978 < baseStart_510978 := by decide
  rcases family_descends (prefixWord ++ tailWord_510978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511005 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_511005 : Nat := 118140960795 + 511005 * 2 ^ 59
def prefixEnd_511005 : Nat := 4983230072969 + 3 ^ 40 * 511005 * 2
def baseEnd_511005 : Nat := 262391181850878424287437

theorem tailTrace_511005 : CollatzResearch.WordTrace tailWord_511005 prefixEnd_511005 262391181850878424287437 := by
  unfold tailWord_511005
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637883513723632550974469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425255675815755033982979 18637883513723632550974469)
  ·
    refine ⟨3494603158823181103307713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18637883513723632550974469 3494603158823181103307713)
    ·
      refine ⟨2620952369117385827480785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3494603158823181103307713 2620952369117385827480785)
      ·
        refine ⟨1965714276838039370610589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2620952369117385827480785 1965714276838039370610589)
        ·
          refine ⟨737142853814264763978971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1965714276838039370610589 737142853814264763978971)
          ·
            refine ⟨1105714280721397145968457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737142853814264763978971 1105714280721397145968457)
            ·
              refine ⟨829285710541047859476343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105714280721397145968457 829285710541047859476343)
              ·
                refine ⟨1243928565811571789214515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829285710541047859476343 1243928565811571789214515)
                ·
                  refine ⟨1865892848717357683821773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243928565811571789214515 1865892848717357683821773)
                  ·
                    refine ⟨699709818269009131433165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1865892848717357683821773 699709818269009131433165)
                    ·
                      refine ⟨262391181850878424287437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 699709818269009131433165 262391181850878424287437)
                      ·
                        rfl

theorem cell23_511005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_511005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511005 prefixEnd_511005 := by exact prefixLift 511005
  have htrace : WordTrace (prefixWord ++ tailWord_511005) baseStart_511005 baseEnd_511005 := by
    simpa [prefixWord, tailWord_511005, baseEnd_511005] using wordTrace_append hprefix tailTrace_511005
  have hstable : (prefixWord ++ tailWord_511005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511005).length < 2 ^ (prefixWord ++ tailWord_511005).sum := by decide
  have hdescent : baseEnd_511005 < baseStart_511005 := by decide
  rcases family_descends (prefixWord ++ tailWord_511005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511032 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_511032 : Nat := 118140960795 + 511032 * 2 ^ 59
def prefixEnd_511032 : Nat := 4983230072969 + 3 ^ 40 * 511032 * 2
def baseEnd_511032 : Nat := 262405045828549818649813

theorem tailTrace_511032 : CollatzResearch.WordTrace tailWord_511032 prefixEnd_511032 262405045828549818649813 := by
  unfold tailWord_511032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319434142312908081103675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12425912189750544108138233 9319434142312908081103675)
  ·
    refine ⟨13979151213469362121655513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9319434142312908081103675 13979151213469362121655513)
    ·
      refine ⟨10484363410102021591241635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13979151213469362121655513 10484363410102021591241635)
      ·
        refine ⟨15726545115153032386862453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484363410102021591241635 15726545115153032386862453)
        ·
          refine ⟨1474363604545596786268355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15726545115153032386862453 1474363604545596786268355)
          ·
            refine ⟨2211545406818395179402533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474363604545596786268355 2211545406818395179402533)
            ·
              refine ⟨414664763778449096137975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2211545406818395179402533 414664763778449096137975)
              ·
                refine ⟨621997145667673644206963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414664763778449096137975 621997145667673644206963)
                ·
                  refine ⟨932995718501510466310445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621997145667673644206963 932995718501510466310445)
                  ·
                    refine ⟨349873394438066424866417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932995718501510466310445 349873394438066424866417)
                    ·
                      refine ⟨262405045828549818649813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 349873394438066424866417 262405045828549818649813)
                      ·
                        rfl

theorem cell23_511032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_511032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511032 prefixEnd_511032 := by exact prefixLift 511032
  have htrace : WordTrace (prefixWord ++ tailWord_511032) baseStart_511032 baseEnd_511032 := by
    simpa [prefixWord, tailWord_511032, baseEnd_511032] using wordTrace_append hprefix tailTrace_511032
  have hstable : (prefixWord ++ tailWord_511032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511032).length < 2 ^ (prefixWord ++ tailWord_511032).sum := by decide
  have hdescent : baseEnd_511032 < baseStart_511032 := by decide
  rcases family_descends (prefixWord ++ tailWord_511032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511038 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_511038 : Nat := 118140960795 + 511038 * 2 ^ 59
def prefixEnd_511038 : Nat := 4983230072969 + 3 ^ 40 * 511038 * 2
def baseEnd_511038 : Nat := 87469375570825598391595

theorem tailTrace_511038 : CollatzResearch.WordTrace tailWord_511038 prefixEnd_511038 87469375570825598391595 := by
  unfold tailWord_511038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329885890325509898365721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12426058081736052791283845 2329885890325509898365721)
  ·
    refine ⟨1747414417744132423774291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2329885890325509898365721 1747414417744132423774291)
    ·
      refine ⟨2621121626616198635661437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747414417744132423774291 2621121626616198635661437)
      ·
        refine ⟨982920609981074488373039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2621121626616198635661437 982920609981074488373039)
        ·
          refine ⟨1474380914971611732559559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982920609981074488373039 1474380914971611732559559)
          ·
            refine ⟨2211571372457417598839339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474380914971611732559559 2211571372457417598839339)
            ·
              refine ⟨3317357058686126398259009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211571372457417598839339 3317357058686126398259009)
              ·
                refine ⟨2488017794014594798694257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317357058686126398259009 2488017794014594798694257)
                ·
                  refine ⟨1866013345510946099020693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488017794014594798694257 1866013345510946099020693)
                  ·
                    refine ⟨87469375570825598391595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1866013345510946099020693 87469375570825598391595)
                    ·
                      rfl

theorem cell23_511038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_511038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511038 prefixEnd_511038 := by exact prefixLift 511038
  have htrace : WordTrace (prefixWord ++ tailWord_511038) baseStart_511038 baseEnd_511038 := by
    simpa [prefixWord, tailWord_511038, baseEnd_511038] using wordTrace_append hprefix tailTrace_511038
  have hstable : (prefixWord ++ tailWord_511038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511038).length < 2 ^ (prefixWord ++ tailWord_511038).sum := by decide
  have hdescent : baseEnd_511038 < baseStart_511038 := by decide
  rcases family_descends (prefixWord ++ tailWord_511038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511058 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_511058 : Nat := 118140960795 + 511058 * 2 ^ 59
def prefixEnd_511058 : Nat := 4983230072969 + 3 ^ 40 * 511058 * 2
def baseEnd_511058 : Nat := 262418396325566716924693

theorem tailTrace_511058 : CollatzResearch.WordTrace tailWord_511058 prefixEnd_511058 262418396325566716924693 := by
  unfold tailWord_511058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659954145632905650663457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12426544388354415068435885 4659954145632905650663457)
  ·
    refine ⟨3494965609224679237997593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4659954145632905650663457 3494965609224679237997593)
    ·
      refine ⟨2621224206918509428498195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3494965609224679237997593 2621224206918509428498195)
      ·
        refine ⟨3931836310377764142747293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621224206918509428498195 3931836310377764142747293)
        ·
          refine ⟨1474438616391661553530235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3931836310377764142747293 1474438616391661553530235)
          ·
            refine ⟨2211657924587492330295353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474438616391661553530235 2211657924587492330295353)
            ·
              refine ⟨1658743443440619247721515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211657924587492330295353 1658743443440619247721515)
              ·
                refine ⟨2488115165160928871582273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658743443440619247721515 2488115165160928871582273)
                ·
                  refine ⟨1866086373870696653686705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488115165160928871582273 1866086373870696653686705)
                  ·
                    refine ⟨1399564780403022490265029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866086373870696653686705 1399564780403022490265029)
                    ·
                      refine ⟨262418396325566716924693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1399564780403022490265029 262418396325566716924693)
                      ·
                        rfl

theorem cell23_511058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_511058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511058 prefixEnd_511058 := by exact prefixLift 511058
  have htrace : WordTrace (prefixWord ++ tailWord_511058) baseStart_511058 baseEnd_511058 := by
    simpa [prefixWord, tailWord_511058, baseEnd_511058] using wordTrace_append hprefix tailTrace_511058
  have hstable : (prefixWord ++ tailWord_511058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511058).length < 2 ^ (prefixWord ++ tailWord_511058).sum := by decide
  have hdescent : baseEnd_511058 < baseStart_511058 := by decide
  rcases family_descends (prefixWord ++ tailWord_511058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511081 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_511081 : Nat := 118140960795 + 511081 * 2 ^ 59
def prefixEnd_511081 : Nat := 4983230072969 + 3 ^ 40 * 511081 * 2
def baseEnd_511081 : Nat := 87476735460206708979029

theorem tailTrace_511081 : CollatzResearch.WordTrace tailWord_511081 prefixEnd_511081 87476735460206708979029 := by
  unfold tailWord_511081
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640655461448297530741097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12427103640965531687160731 18640655461448297530741097)
  ·
    refine ⟨13980491596086223148055823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18640655461448297530741097 13980491596086223148055823)
    ·
      refine ⟨20970737394129334722083735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980491596086223148055823 20970737394129334722083735)
      ·
        refine ⟨31456106091194002083125603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20970737394129334722083735 31456106091194002083125603)
        ·
          refine ⟨47184159136791003124688405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31456106091194002083125603 47184159136791003124688405)
          ·
            refine ⟨2211757459537078271469769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47184159136791003124688405 2211757459537078271469769)
            ·
              refine ⟨1658818094652808703602327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211757459537078271469769 1658818094652808703602327)
              ·
                refine ⟨2488227141979213055403491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658818094652808703602327 2488227141979213055403491)
                ·
                  refine ⟨3732340712968819583105237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488227141979213055403491 3732340712968819583105237)
                  ·
                    refine ⟨87476735460206708979029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3732340712968819583105237 87476735460206708979029)
                    ·
                      rfl

theorem cell23_511081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_511081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511081 prefixEnd_511081 := by exact prefixLift 511081
  have htrace : WordTrace (prefixWord ++ tailWord_511081) baseStart_511081 baseEnd_511081 := by
    simpa [prefixWord, tailWord_511081, baseEnd_511081] using wordTrace_append hprefix tailTrace_511081
  have hstable : (prefixWord ++ tailWord_511081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511081).length < 2 ^ (prefixWord ++ tailWord_511081).sum := by decide
  have hdescent : baseEnd_511081 < baseStart_511081 := by decide
  rcases family_descends (prefixWord ++ tailWord_511081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511085 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 5]
def baseStart_511085 : Nat := 118140960795 + 511085 * 2 ^ 59
def prefixEnd_511085 : Nat := 4983230072969 + 3 ^ 40 * 511085 * 2
def baseEnd_511085 : Nat := 29159140033693123476341

theorem tailTrace_511085 : CollatzResearch.WordTrace tailWord_511085 prefixEnd_511085 29159140033693123476341 := by
  unfold tailWord_511085
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640801353433806213886709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12427200902289204142591139 18640801353433806213886709)
  ·
    refine ⟨1747575126884419332551879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18640801353433806213886709 1747575126884419332551879)
    ·
      refine ⟨2621362690326628998827819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747575126884419332551879 2621362690326628998827819)
      ·
        refine ⟨3932044035489943498241729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621362690326628998827819 3932044035489943498241729)
        ·
          refine ⟨2949033026617457623681297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932044035489943498241729 2949033026617457623681297)
          ·
            refine ⟨2211774769963093217760973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949033026617457623681297 2211774769963093217760973)
            ·
              refine ⟨829415538736159956660365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2211774769963093217760973 829415538736159956660365)
              ·
                refine ⟨311030827026059983747637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829415538736159956660365 311030827026059983747637)
                ·
                  refine ⟨29159140033693123476341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311030827026059983747637 29159140033693123476341)
                  ·
                    rfl

theorem cell23_511085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_511085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511085 prefixEnd_511085 := by exact prefixLift 511085
  have htrace : WordTrace (prefixWord ++ tailWord_511085) baseStart_511085 baseEnd_511085 := by
    simpa [prefixWord, tailWord_511085, baseEnd_511085] using wordTrace_append hprefix tailTrace_511085
  have hstable : (prefixWord ++ tailWord_511085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511085).length < 2 ^ (prefixWord ++ tailWord_511085).sum := by decide
  have hdescent : baseEnd_511085 < baseStart_511085 := by decide
  rcases family_descends (prefixWord ++ tailWord_511085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511108 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_511108 : Nat := 118140960795 + 511108 * 2 ^ 59
def prefixEnd_511108 : Nat := 4983230072969 + 3 ^ 40 * 511108 * 2
def baseEnd_511108 : Nat := 262444070358291521299463

theorem tailTrace_511108 : CollatzResearch.WordTrace tailWord_511108 prefixEnd_511108 262444070358291521299463 := by
  unfold tailWord_511108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320820116175240570986989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12427760154900320761315985 9320820116175240570986989)
  ·
    refine ⟨3495307543565715214120121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9320820116175240570986989 3495307543565715214120121)
    ·
      refine ⟨2621480657674286410590091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3495307543565715214120121 2621480657674286410590091)
      ·
        refine ⟨3932220986511429615885137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621480657674286410590091 3932220986511429615885137)
        ·
          refine ⟨2949165739883572211913853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932220986511429615885137 2949165739883572211913853)
          ·
            refine ⟨1105937152456339579467695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2949165739883572211913853 1105937152456339579467695)
            ·
              refine ⟨1658905728684509369201543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105937152456339579467695 1658905728684509369201543)
              ·
                refine ⟨2488358593026764053802315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658905728684509369201543 2488358593026764053802315)
                ·
                  refine ⟨3732537889540146080703473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488358593026764053802315 3732537889540146080703473)
                  ·
                    refine ⟨2799403417155109560527605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732537889540146080703473 2799403417155109560527605)
                    ·
                      refine ⟨262444070358291521299463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2799403417155109560527605 262444070358291521299463)
                      ·
                        rfl

theorem cell23_511108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_511108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511108 prefixEnd_511108 := by exact prefixLift 511108
  have htrace : WordTrace (prefixWord ++ tailWord_511108) baseStart_511108 baseEnd_511108 := by
    simpa [prefixWord, tailWord_511108, baseEnd_511108] using wordTrace_append hprefix tailTrace_511108
  have hstable : (prefixWord ++ tailWord_511108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511108).length < 2 ^ (prefixWord ++ tailWord_511108).sum := by decide
  have hdescent : baseEnd_511108 < baseStart_511108 := by decide
  rcases family_descends (prefixWord ++ tailWord_511108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511235 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 1, 6]
def baseStart_511235 : Nat := 118140960795 + 511235 * 2 ^ 59
def prefixEnd_511235 : Nat := 4983230072969 + 3 ^ 40 * 511235 * 2
def baseEnd_511235 : Nat := 87503094133804174803793

theorem tailTrace_511235 : CollatzResearch.WordTrace tailWord_511235 prefixEnd_511235 87503094133804174803793 := by
  unfold tailWord_511235
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646272302890381831847159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12430848201926921221231439 18646272302890381831847159)
  ·
    refine ⟨27969408454335572747770739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18646272302890381831847159 27969408454335572747770739)
    ·
      refine ⟨41954112681503359121656109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27969408454335572747770739 41954112681503359121656109)
      ·
        refine ⟨15732792255563759670621041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41954112681503359121656109 15732792255563759670621041)
        ·
          refine ⟨11799594191672819752965781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15732792255563759670621041 11799594191672819752965781)
          ·
            refine ⟨553105977734663425920271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11799594191672819752965781 553105977734663425920271)
            ·
              refine ⟨829658966601995138880407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553105977734663425920271 829658966601995138880407)
              ·
                refine ⟨1244488449902992708320611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829658966601995138880407 1244488449902992708320611)
                ·
                  refine ⟨1866732674854489062480917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244488449902992708320611 1866732674854489062480917)
                  ·
                    refine ⟨87503094133804174803793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1866732674854489062480917 87503094133804174803793)
                    ·
                      rfl

theorem cell23_511235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 6].length) (baseStart_511235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_511235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_511235 prefixEnd_511235 := by exact prefixLift 511235
  have htrace : WordTrace (prefixWord ++ tailWord_511235) baseStart_511235 baseEnd_511235 := by
    simpa [prefixWord, tailWord_511235, baseEnd_511235] using wordTrace_append hprefix tailTrace_511235
  have hstable : (prefixWord ++ tailWord_511235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511235).length < 2 ^ (prefixWord ++ tailWord_511235).sum := by decide
  have hdescent : baseEnd_511235 < baseStart_511235 := by decide
  rcases family_descends (prefixWord ++ tailWord_511235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
