import V185TrunkScan21Chunk160

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1963838 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1963838 : Nat := 118140960795 + 1963838 * 2 ^ 59
def prefixEnd_1963838 : Nat := 4983230072969 + 3 ^ 40 * 1963838 * 2
def baseEnd_1963838 : Nat := 448174587361952314885991

theorem tailTrace_1963838 : CollatzResearch.WordTrace tailWord_1963838 prefixEnd_1963838 448174587361952314885991 := by
  unfold tailWord_1963838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953382032419724709150521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47751370839571865115469445 8953382032419724709150521)
  ·
    refine ⟨6715036524314793531862891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8953382032419724709150521 6715036524314793531862891)
    ·
      refine ⟨10072554786472190297794337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715036524314793531862891 10072554786472190297794337)
      ·
        refine ⟨7554416089854142723345753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10072554786472190297794337 7554416089854142723345753)
        ·
          refine ⟨5665812067390607042509315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7554416089854142723345753 5665812067390607042509315)
          ·
            refine ⟨8498718101085910563763973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665812067390607042509315 8498718101085910563763973)
            ·
              refine ⟨1593509643953608230705745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8498718101085910563763973 1593509643953608230705745)
              ·
                refine ⟨1195132232965206173029309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593509643953608230705745 1195132232965206173029309)
                ·
                  refine ⟨448174587361952314885991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195132232965206173029309 448174587361952314885991)
                  ·
                    rfl

theorem cell21_1963838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1963838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963838 prefixEnd_1963838 := by exact prefixLift 1963838
  have htrace : WordTrace (prefixWord ++ tailWord_1963838) baseStart_1963838 baseEnd_1963838 := by
    simpa [prefixWord, tailWord_1963838, baseEnd_1963838] using wordTrace_append hprefix tailTrace_1963838
  have hstable : (prefixWord ++ tailWord_1963838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963838).length < 2 ^ (prefixWord ++ tailWord_1963838).sum := by decide
  have hdescent : baseEnd_1963838 < baseStart_1963838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963877 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1963877 : Nat := 118140960795 + 1963877 * 2 ^ 59
def prefixEnd_1963877 : Nat := 4983230072969 + 3 ^ 40 * 1963877 * 2
def baseEnd_1963877 : Nat := 448183487693296913735911

theorem tailTrace_1963877 : CollatzResearch.WordTrace tailWord_1963877 prefixEnd_1963877 448183487693296913735911 := by
  unfold tailWord_1963877
  simp only [CollatzResearch.WordTrace]
  refine ⟨71628478706216507333873885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47752319137477671555915923 71628478706216507333873885)
  ·
    refine ⟨26860679514831190250202707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71628478706216507333873885 26860679514831190250202707)
    ·
      refine ⟨40291019272246785375304061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26860679514831190250202707 40291019272246785375304061)
      ·
        refine ⟨15109132227092544515739023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40291019272246785375304061 15109132227092544515739023)
        ·
          refine ⟨22663698340638816773608535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15109132227092544515739023 22663698340638816773608535)
          ·
            refine ⟨33995547510958225160412803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22663698340638816773608535 33995547510958225160412803)
            ·
              refine ⟨50993321266437337740619205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33995547510958225160412803 50993321266437337740619205)
              ·
                refine ⟨9561247737457000826366101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50993321266437337740619205 9561247737457000826366101)
                ·
                  refine ⟨448183487693296913735911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9561247737457000826366101 448183487693296913735911)
                  ·
                    rfl

theorem cell21_1963877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1963877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1963877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1963877 prefixEnd_1963877 := by exact prefixLift 1963877
  have htrace : WordTrace (prefixWord ++ tailWord_1963877) baseStart_1963877 baseEnd_1963877 := by
    simpa [prefixWord, tailWord_1963877, baseEnd_1963877] using wordTrace_append hprefix tailTrace_1963877
  have hstable : (prefixWord ++ tailWord_1963877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963877).length < 2 ^ (prefixWord ++ tailWord_1963877).sum := by decide
  have hdescent : baseEnd_1963877 < baseStart_1963877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964007 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 3]
def baseStart_1964007 : Nat := 118140960795 + 1964007 * 2 ^ 59
def prefixEnd_1964007 : Nat := 4983230072969 + 3 ^ 40 * 1964007 * 2
def baseEnd_1964007 : Nat := 448213155464445576568979

theorem tailTrace_1964007 : CollatzResearch.WordTrace tailWord_1964007 prefixEnd_1964007 448213155464445576568979 := by
  unfold tailWord_1964007
  simp only [CollatzResearch.WordTrace]
  refine ⟨71633220195745539536106275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47755480130497026357404183 71633220195745539536106275)
  ·
    refine ⟨107449830293618309304159413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71633220195745539536106275 107449830293618309304159413)
    ·
      refine ⟨10073421590026716497264945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107449830293618309304159413 10073421590026716497264945)
      ·
        refine ⟨7555066192520037372948709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10073421590026716497264945 7555066192520037372948709)
        ·
          refine ⟨1416574911097507007427883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7555066192520037372948709 1416574911097507007427883)
          ·
            refine ⟨2124862366646260511141825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416574911097507007427883 2124862366646260511141825)
            ·
              refine ⟨1593646774984695383356369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124862366646260511141825 1593646774984695383356369)
              ·
                refine ⟨1195235081238521537517277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593646774984695383356369 1195235081238521537517277)
                ·
                  refine ⟨448213155464445576568979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195235081238521537517277 448213155464445576568979)
                  ·
                    rfl

theorem cell21_1964007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3].length) (baseStart_1964007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964007 prefixEnd_1964007 := by exact prefixLift 1964007
  have htrace : WordTrace (prefixWord ++ tailWord_1964007) baseStart_1964007 baseEnd_1964007 := by
    simpa [prefixWord, tailWord_1964007, baseEnd_1964007] using wordTrace_append hprefix tailTrace_1964007
  have hstable : (prefixWord ++ tailWord_1964007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964007).length < 2 ^ (prefixWord ++ tailWord_1964007).sum := by decide
  have hdescent : baseEnd_1964007 < baseStart_1964007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964060 : List Nat := [2, 2, 3, 1, 3, 2, 8]
def baseStart_1964060 : Nat := 118140960795 + 1964060 * 2 ^ 59
def prefixEnd_1964060 : Nat := 4983230072969 + 3 ^ 40 * 1964060 * 2
def baseEnd_1964060 : Nat := 49802805642947695798393

theorem tailTrace_1964060 : CollatzResearch.WordTrace tailWord_1964060 prefixEnd_1964060 49802805642947695798393 := by
  unfold tailWord_1964060
  simp only [CollatzResearch.WordTrace]
  refine ⟨35817576632276764793892817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47756768843035686391857089 35817576632276764793892817)
  ·
    refine ⟨26863182474207573595419613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35817576632276764793892817 26863182474207573595419613)
    ·
      refine ⟨10073693427827840098282355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26863182474207573595419613 10073693427827840098282355)
      ·
        refine ⟨15110540141741760147423533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073693427827840098282355 15110540141741760147423533)
        ·
          refine ⟨5666452553153160055283825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15110540141741760147423533 5666452553153160055283825)
          ·
            refine ⟨4249839414864870041462869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5666452553153160055283825 4249839414864870041462869)
            ·
              refine ⟨49802805642947695798393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4249839414864870041462869 49802805642947695798393)
              ·
                rfl

theorem cell21_1964060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 8].length) (baseStart_1964060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964060 prefixEnd_1964060 := by exact prefixLift 1964060
  have htrace : WordTrace (prefixWord ++ tailWord_1964060) baseStart_1964060 baseEnd_1964060 := by
    simpa [prefixWord, tailWord_1964060, baseEnd_1964060] using wordTrace_append hprefix tailTrace_1964060
  have hstable : (prefixWord ++ tailWord_1964060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964060).length < 2 ^ (prefixWord ++ tailWord_1964060).sum := by decide
  have hdescent : baseEnd_1964060 < baseStart_1964060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964108 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_1964108 : Nat := 118140960795 + 1964108 * 2 ^ 59
def prefixEnd_1964108 : Nat := 4983230072969 + 3 ^ 40 * 1964108 * 2
def baseEnd_1964108 : Nat := 448236205040491845385439

theorem tailTrace_1964108 : CollatzResearch.WordTrace tailWord_1964108 prefixEnd_1964108 448236205040491845385439 := by
  unfold tailWord_1964108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35818451984189816892766489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47757935978919755857021985 35818451984189816892766489)
  ·
    refine ⟨26863838988142362669574867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35818451984189816892766489 26863838988142362669574867)
    ·
      refine ⟨40295758482213544004362301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26863838988142362669574867 40295758482213544004362301)
      ·
        refine ⟨15110909430830079001635863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40295758482213544004362301 15110909430830079001635863)
        ·
          refine ⟨22666364146245118502453795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110909430830079001635863 22666364146245118502453795)
          ·
            refine ⟨33999546219367677753680693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22666364146245118502453795 33999546219367677753680693)
            ·
              refine ⟨3187457458065719789407565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33999546219367677753680693 3187457458065719789407565)
              ·
                refine ⟨1195296546774644921027837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3187457458065719789407565 1195296546774644921027837)
                ·
                  refine ⟨448236205040491845385439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195296546774644921027837 448236205040491845385439)
                  ·
                    rfl

theorem cell21_1964108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_1964108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964108 prefixEnd_1964108 := by exact prefixLift 1964108
  have htrace : WordTrace (prefixWord ++ tailWord_1964108) baseStart_1964108 baseEnd_1964108 := by
    simpa [prefixWord, tailWord_1964108, baseEnd_1964108] using wordTrace_append hprefix tailTrace_1964108
  have hstable : (prefixWord ++ tailWord_1964108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964108).length < 2 ^ (prefixWord ++ tailWord_1964108).sum := by decide
  have hdescent : baseEnd_1964108 < baseStart_1964108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964119 : List Nat := [1, 1, 3, 2, 2, 1, 11]
def baseStart_1964119 : Nat := 118140960795 + 1964119 * 2 ^ 59
def prefixEnd_1964119 : Nat := 4983230072969 + 3 ^ 40 * 1964119 * 2
def baseEnd_1964119 : Nat := 49804301710039807855787

theorem tailTrace_1964119 : CollatzResearch.WordTrace tailWord_1964119 prefixEnd_1964119 49804301710039807855787 := by
  unfold tailWord_1964119
  simp only [CollatzResearch.WordTrace]
  refine ⟨71637305171339782664183411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47758203447559855109455607 71637305171339782664183411)
  ·
    refine ⟨107455957757009673996275117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71637305171339782664183411 107455957757009673996275117)
    ·
      refine ⟨40295984158878627748603169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107455957757009673996275117 40295984158878627748603169)
      ·
        refine ⟨30221988119158970811452377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40295984158878627748603169 30221988119158970811452377)
        ·
          refine ⟨22666491089369228108589283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30221988119158970811452377 22666491089369228108589283)
          ·
            refine ⟨33999736634053842162883925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22666491089369228108589283 33999736634053842162883925)
            ·
              refine ⟨49804301710039807855787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33999736634053842162883925 49804301710039807855787)
              ·
                rfl

theorem cell21_1964119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 11].length) (baseStart_1964119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964119 prefixEnd_1964119 := by exact prefixLift 1964119
  have htrace : WordTrace (prefixWord ++ tailWord_1964119) baseStart_1964119 baseEnd_1964119 := by
    simpa [prefixWord, tailWord_1964119, baseEnd_1964119] using wordTrace_append hprefix tailTrace_1964119
  have hstable : (prefixWord ++ tailWord_1964119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964119).length < 2 ^ (prefixWord ++ tailWord_1964119).sum := by decide
  have hdescent : baseEnd_1964119 < baseStart_1964119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964125 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 5]
def baseStart_1964125 : Nat := 118140960795 + 1964125 * 2 ^ 59
def prefixEnd_1964125 : Nat := 4983230072969 + 3 ^ 40 * 1964125 * 2
def baseEnd_1964125 : Nat := 448240084672103593602071

theorem tailTrace_1964125 : CollatzResearch.WordTrace tailWord_1964125 prefixEnd_1964125 448240084672103593602071 := by
  unfold tailWord_1964125
  simp only [CollatzResearch.WordTrace]
  refine ⟨71637524009318045688901829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47758349339545363792601219 71637524009318045688901829)
  ·
    refine ⟨13432035751747133566669093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71637524009318045688901829 13432035751747133566669093)
    ·
      refine ⟨2518506703452587543750455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13432035751747133566669093 2518506703452587543750455)
      ·
        refine ⟨3777760055178881315625683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518506703452587543750455 3777760055178881315625683)
        ·
          refine ⟨5666640082768321973438525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777760055178881315625683 5666640082768321973438525)
          ·
            refine ⟨2124990031038120740039447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5666640082768321973438525 2124990031038120740039447)
            ·
              refine ⟨3187485046557181110059171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124990031038120740039447 3187485046557181110059171)
              ·
                refine ⟨4781227569835771665088757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187485046557181110059171 4781227569835771665088757)
                ·
                  refine ⟨448240084672103593602071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4781227569835771665088757 448240084672103593602071)
                  ·
                    rfl

theorem cell21_1964125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_1964125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964125 prefixEnd_1964125 := by exact prefixLift 1964125
  have htrace : WordTrace (prefixWord ++ tailWord_1964125) baseStart_1964125 baseEnd_1964125 := by
    simpa [prefixWord, tailWord_1964125, baseEnd_1964125] using wordTrace_append hprefix tailTrace_1964125
  have hstable : (prefixWord ++ tailWord_1964125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964125).length < 2 ^ (prefixWord ++ tailWord_1964125).sum := by decide
  have hdescent : baseEnd_1964125 < baseStart_1964125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964350 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1964350 : Nat := 118140960795 + 1964350 * 2 ^ 59
def prefixEnd_1964350 : Nat := 4983230072969 + 3 ^ 40 * 1964350 * 2
def baseEnd_1964350 : Nat := 448291432737553202351611

theorem tailTrace_1964350 : CollatzResearch.WordTrace tailWord_1964350 prefixEnd_1964350 448291432737553202351611 := by
  unfold tailWord_1964350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955716304187863639480313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47763820289001939410561669 8955716304187863639480313)
  ·
    refine ⟨6716787228140897729610235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8955716304187863639480313 6716787228140897729610235)
    ·
      refine ⟨10075180842211346594415353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6716787228140897729610235 10075180842211346594415353)
      ·
        refine ⟨7556385631658509945811515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10075180842211346594415353 7556385631658509945811515)
        ·
          refine ⟨11334578447487764918717273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7556385631658509945811515 11334578447487764918717273)
          ·
            refine ⟨8500933835615823689037955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11334578447487764918717273 8500933835615823689037955)
            ·
              refine ⟨12751400753423735533556933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500933835615823689037955 12751400753423735533556933)
              ·
                refine ⟨2390887641266950412541925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12751400753423735533556933 2390887641266950412541925)
                ·
                  refine ⟨448291432737553202351611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2390887641266950412541925 448291432737553202351611)
                  ·
                    rfl

theorem cell21_1964350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1964350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964350 prefixEnd_1964350 := by exact prefixLift 1964350
  have htrace : WordTrace (prefixWord ++ tailWord_1964350) baseStart_1964350 baseEnd_1964350 := by
    simpa [prefixWord, tailWord_1964350, baseEnd_1964350] using wordTrace_append hprefix tailTrace_1964350
  have hstable : (prefixWord ++ tailWord_1964350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964350).length < 2 ^ (prefixWord ++ tailWord_1964350).sum := by decide
  have hdescent : baseEnd_1964350 < baseStart_1964350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964353 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 3]
def baseStart_1964353 : Nat := 118140960795 + 1964353 * 2 ^ 59
def prefixEnd_1964353 : Nat := 4983230072969 + 3 ^ 40 * 1964353 * 2
def baseEnd_1964353 : Nat := 448292117378425863801605

theorem tailTrace_1964353 : CollatzResearch.WordTrace tailWord_1964353 prefixEnd_1964353 448292117378425863801605 := by
  unfold tailWord_1964353
  simp only [CollatzResearch.WordTrace]
  refine ⟨71645839852492040628201713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47763893234994693752134475 71645839852492040628201713)
  ·
    refine ⟨53734379889369030471151285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71645839852492040628201713 53734379889369030471151285)
    ·
      refine ⟨5037598114628346606670433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53734379889369030471151285 5037598114628346606670433)
      ·
        refine ⟨3778198585971259955002825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037598114628346606670433 3778198585971259955002825)
        ·
          refine ⟨2833648939478444966252119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3778198585971259955002825 2833648939478444966252119)
          ·
            refine ⟨4250473409217667449378179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833648939478444966252119 4250473409217667449378179)
            ·
              refine ⟨6375710113826501174067269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250473409217667449378179 6375710113826501174067269)
              ·
                refine ⟨1195445646342468970137613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6375710113826501174067269 1195445646342468970137613)
                ·
                  refine ⟨448292117378425863801605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195445646342468970137613 448292117378425863801605)
                  ·
                    rfl

theorem cell21_1964353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_1964353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964353 prefixEnd_1964353 := by exact prefixLift 1964353
  have htrace : WordTrace (prefixWord ++ tailWord_1964353) baseStart_1964353 baseEnd_1964353 := by
    simpa [prefixWord, tailWord_1964353, baseEnd_1964353] using wordTrace_append hprefix tailTrace_1964353
  have hstable : (prefixWord ++ tailWord_1964353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964353).length < 2 ^ (prefixWord ++ tailWord_1964353).sum := by decide
  have hdescent : baseEnd_1964353 < baseStart_1964353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964423 : List Nat := [1, 1, 4, 2, 2, 1, 2, 8]
def baseStart_1964423 : Nat := 118140960795 + 1964423 * 2 ^ 59
def prefixEnd_1964423 : Nat := 4983230072969 + 3 ^ 40 * 1964423 * 2
def baseEnd_1964423 : Nat := 149436030777373765878265

theorem tailTrace_1964423 : CollatzResearch.WordTrace tailWord_1964423 prefixEnd_1964423 149436030777373765878265 := by
  unfold tailWord_1964423
  simp only [CollatzResearch.WordTrace]
  refine ⟨71648392962238442583249923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47765595308158961722166615 71648392962238442583249923)
  ·
    refine ⟨107472589443357663874874885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71648392962238442583249923 107472589443357663874874885)
    ·
      refine ⟨20151110520629561976539041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107472589443357663874874885 20151110520629561976539041)
      ·
        refine ⟨15113332890472171482404281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20151110520629561976539041 15113332890472171482404281)
        ·
          refine ⟨11334999667854128611803211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15113332890472171482404281 11334999667854128611803211)
          ·
            refine ⟨17002499501781192917704817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334999667854128611803211 17002499501781192917704817)
            ·
              refine ⟨12751874626335894688278613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17002499501781192917704817 12751874626335894688278613)
              ·
                refine ⟨149436030777373765878265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12751874626335894688278613 149436030777373765878265)
                ·
                  rfl

theorem cell21_1964423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_1964423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964423 prefixEnd_1964423 := by exact prefixLift 1964423
  have htrace : WordTrace (prefixWord ++ tailWord_1964423) baseStart_1964423 baseEnd_1964423 := by
    simpa [prefixWord, tailWord_1964423, baseEnd_1964423] using wordTrace_append hprefix tailTrace_1964423
  have hstable : (prefixWord ++ tailWord_1964423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964423).length < 2 ^ (prefixWord ++ tailWord_1964423).sum := by decide
  have hdescent : baseEnd_1964423 < baseStart_1964423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964440 : List Nat := [2, 1, 2, 5, 1, 2, 1, 7]
def baseStart_1964440 : Nat := 118140960795 + 1964440 * 2 ^ 59
def prefixEnd_1964440 : Nat := 4983230072969 + 3 ^ 40 * 1964440 * 2
def baseEnd_1964440 : Nat := 149437323987911015283809

theorem tailTrace_1964440 : CollatzResearch.WordTrace tailWord_1964440 prefixEnd_1964440 149437323987911015283809 := by
  unfold tailWord_1964440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35824506501588427243309387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47766008668784569657745849 35824506501588427243309387)
  ·
    refine ⟨53736759752382640864964081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35824506501588427243309387 53736759752382640864964081)
    ·
      refine ⟨40302569814286980648723061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53736759752382640864964081 40302569814286980648723061)
      ·
        refine ⟨3778365920089404435817787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40302569814286980648723061 3778365920089404435817787)
        ·
          refine ⟨5667548880134106653726681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778365920089404435817787 5667548880134106653726681)
          ·
            refine ⟨4250661660100579990295011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5667548880134106653726681 4250661660100579990295011)
            ·
              refine ⟨6375992490150869985442517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250661660100579990295011 6375992490150869985442517)
              ·
                refine ⟨149437323987911015283809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6375992490150869985442517 149437323987911015283809)
                ·
                  rfl

theorem cell21_1964440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_1964440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964440 prefixEnd_1964440 := by exact prefixLift 1964440
  have htrace : WordTrace (prefixWord ++ tailWord_1964440) baseStart_1964440 baseEnd_1964440 := by
    simpa [prefixWord, tailWord_1964440, baseEnd_1964440] using wordTrace_append hprefix tailTrace_1964440
  have hstable : (prefixWord ++ tailWord_1964440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964440).length < 2 ^ (prefixWord ++ tailWord_1964440).sum := by decide
  have hdescent : baseEnd_1964440 < baseStart_1964440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964446 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1964446 : Nat := 118140960795 + 1964446 * 2 ^ 59
def prefixEnd_1964446 : Nat := 4983230072969 + 3 ^ 40 * 1964446 * 2
def baseEnd_1964446 : Nat := 448313341245478368751415

theorem tailTrace_1964446 : CollatzResearch.WordTrace tailWord_1964446 prefixEnd_1964446 448313341245478368751415 := by
  unfold tailWord_1964446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956153980144389688917149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47766154560770078340891461 8956153980144389688917149)
  ·
    refine ⟨3358557742554146133343931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8956153980144389688917149 3358557742554146133343931)
    ·
      refine ⟨5037836613831219200015897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358557742554146133343931 5037836613831219200015897)
      ·
        refine ⟨3778377460373414400011923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037836613831219200015897 3778377460373414400011923)
        ·
          refine ⟨5667566190560121600017885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778377460373414400011923 5667566190560121600017885)
          ·
            refine ⟨2125337321460045600006707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5667566190560121600017885 2125337321460045600006707)
            ·
              refine ⟨3188005982190068400010061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125337321460045600006707 3188005982190068400010061)
              ·
                refine ⟨1195502243321275650003773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188005982190068400010061 1195502243321275650003773)
                ·
                  refine ⟨448313341245478368751415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195502243321275650003773 448313341245478368751415)
                  ·
                    rfl

theorem cell21_1964446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1964446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964446 prefixEnd_1964446 := by exact prefixLift 1964446
  have htrace : WordTrace (prefixWord ++ tailWord_1964446) baseStart_1964446 baseEnd_1964446 := by
    simpa [prefixWord, tailWord_1964446, baseEnd_1964446] using wordTrace_append hprefix tailTrace_1964446
  have hstable : (prefixWord ++ tailWord_1964446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964446).length < 2 ^ (prefixWord ++ tailWord_1964446).sum := by decide
  have hdescent : baseEnd_1964446 < baseStart_1964446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964471 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 5]
def baseStart_1964471 : Nat := 118140960795 + 1964471 * 2 ^ 59
def prefixEnd_1964471 : Nat := 4983230072969 + 3 ^ 40 * 1964471 * 2
def baseEnd_1964471 : Nat := 448319046586083880834697

theorem tailTrace_1964471 : CollatzResearch.WordTrace tailWord_1964471 prefixEnd_1964471 448319046586083880834697 := by
  unfold tailWord_1964471
  simp only [CollatzResearch.WordTrace]
  refine ⟨71650143666064546780997267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47766762444043031187331511 71650143666064546780997267)
  ·
    refine ⟨107475215499096820171495901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71650143666064546780997267 107475215499096820171495901)
    ·
      refine ⟨40303205812161307564310963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107475215499096820171495901 40303205812161307564310963)
      ·
        refine ⟨60454808718241961346466445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40303205812161307564310963 60454808718241961346466445)
        ·
          refine ⟨22670553269340735504924917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60454808718241961346466445 22670553269340735504924917)
          ·
            refine ⟨2125364369000693953586711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22670553269340735504924917 2125364369000693953586711)
            ·
              refine ⟨3188046553501040930380067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125364369000693953586711 3188046553501040930380067)
              ·
                refine ⟨4782069830251561395570101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188046553501040930380067 4782069830251561395570101)
                ·
                  refine ⟨448319046586083880834697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4782069830251561395570101 448319046586083880834697)
                  ·
                    rfl

theorem cell21_1964471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_1964471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964471 prefixEnd_1964471 := by exact prefixLift 1964471
  have htrace : WordTrace (prefixWord ++ tailWord_1964471) baseStart_1964471 baseEnd_1964471 := by
    simpa [prefixWord, tailWord_1964471, baseEnd_1964471] using wordTrace_append hprefix tailTrace_1964471
  have hstable : (prefixWord ++ tailWord_1964471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964471).length < 2 ^ (prefixWord ++ tailWord_1964471).sum := by decide
  have hdescent : baseEnd_1964471 < baseStart_1964471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964609 : List Nat := [1, 2, 5, 1, 1, 4, 2, 5]
def baseStart_1964609 : Nat := 118140960795 + 1964609 * 2 ^ 59
def prefixEnd_1964609 : Nat := 4983230072969 + 3 ^ 40 * 1964609 * 2
def baseEnd_1964609 : Nat := 149450180022075435844805

theorem tailTrace_1964609 : CollatzResearch.WordTrace tailWord_1964609 prefixEnd_1964609 149450180022075435844805 := by
  unfold tailWord_1964609
  simp only [CollatzResearch.WordTrace]
  refine ⟨71655176939564596349520881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47770117959709730899680587 71655176939564596349520881)
  ·
    refine ⟨53741382704673447262140661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71655176939564596349520881 53741382704673447262140661)
    ·
      refine ⟨5038254628563135680825687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53741382704673447262140661 5038254628563135680825687)
      ·
        refine ⟨7557381942844703521238531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038254628563135680825687 7557381942844703521238531)
        ·
          refine ⟨11336072914267055281857797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557381942844703521238531 11336072914267055281857797)
          ·
            refine ⟨2125513671425072865348337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11336072914267055281857797 2125513671425072865348337)
            ·
              refine ⟨1594135253568804649011253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125513671425072865348337 1594135253568804649011253)
              ·
                refine ⟨149450180022075435844805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1594135253568804649011253 149450180022075435844805)
                ·
                  rfl

theorem cell21_1964609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 5].length) (baseStart_1964609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964609 prefixEnd_1964609 := by exact prefixLift 1964609
  have htrace : WordTrace (prefixWord ++ tailWord_1964609) baseStart_1964609 baseEnd_1964609 := by
    simpa [prefixWord, tailWord_1964609, baseEnd_1964609] using wordTrace_append hprefix tailTrace_1964609
  have hstable : (prefixWord ++ tailWord_1964609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964609).length < 2 ^ (prefixWord ++ tailWord_1964609).sum := by decide
  have hdescent : baseEnd_1964609 < baseStart_1964609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964620 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_1964620 : Nat := 118140960795 + 1964620 * 2 ^ 59
def prefixEnd_1964620 : Nat := 4983230072969 + 3 ^ 40 * 1964620 * 2
def baseEnd_1964620 : Nat := 448353050416092732851059

theorem tailTrace_1964620 : CollatzResearch.WordTrace tailWord_1964620 prefixEnd_1964620 448353050416092732851059 := by
  unfold tailWord_1964620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827789071262372614085657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47770385428349830152114209 35827789071262372614085657)
  ·
    refine ⟨26870841803446779460564243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35827789071262372614085657 26870841803446779460564243)
    ·
      refine ⟨40306262705170169190846365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26870841803446779460564243 40306262705170169190846365)
      ·
        refine ⟨15114848514438813446567387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40306262705170169190846365 15114848514438813446567387)
        ·
          refine ⟨22672272771658220169851081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114848514438813446567387 22672272771658220169851081)
          ·
            refine ⟨17004204578743665127388311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22672272771658220169851081 17004204578743665127388311)
            ·
              refine ⟨25506306868115497691082467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17004204578743665127388311 25506306868115497691082467)
              ·
                refine ⟨38259460302173246536623701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25506306868115497691082467 38259460302173246536623701)
                ·
                  refine ⟨448353050416092732851059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38259460302173246536623701 448353050416092732851059)
                  ·
                    rfl

theorem cell21_1964620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_1964620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964620 prefixEnd_1964620 := by exact prefixLift 1964620
  have htrace : WordTrace (prefixWord ++ tailWord_1964620) baseStart_1964620 baseEnd_1964620 := by
    simpa [prefixWord, tailWord_1964620, baseEnd_1964620] using wordTrace_append hprefix tailTrace_1964620
  have hstable : (prefixWord ++ tailWord_1964620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964620).length < 2 ^ (prefixWord ++ tailWord_1964620).sum := by decide
  have hdescent : baseEnd_1964620 < baseStart_1964620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964623 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 3]
def baseStart_1964623 : Nat := 118140960795 + 1964623 * 2 ^ 59
def prefixEnd_1964623 : Nat := 4983230072969 + 3 ^ 40 * 1964623 * 2
def baseEnd_1964623 : Nat := 448353735056965394301053

theorem tailTrace_1964623 : CollatzResearch.WordTrace tailWord_1964623 prefixEnd_1964623 448353735056965394301053 := by
  unfold tailWord_1964623
  simp only [CollatzResearch.WordTrace]
  refine ⟨71655687561513876740530523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47770458374342584493687015 71655687561513876740530523)
  ·
    refine ⟨107483531342270815110795785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71655687561513876740530523 107483531342270815110795785)
    ·
      refine ⟨80612648506703111333096839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107483531342270815110795785 80612648506703111333096839)
      ·
        refine ⟨120918972760054666999645259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80612648506703111333096839 120918972760054666999645259)
        ·
          refine ⟨181378459140082000499467889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120918972760054666999645259 181378459140082000499467889)
          ·
            refine ⟨136033844355061500374600917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181378459140082000499467889 136033844355061500374600917)
            ·
              refine ⟨3188293227071753915029709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 136033844355061500374600917 3188293227071753915029709)
              ·
                refine ⟨1195609960151907718136141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188293227071753915029709 1195609960151907718136141)
                ·
                  refine ⟨448353735056965394301053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195609960151907718136141 448353735056965394301053)
                  ·
                    rfl

theorem cell21_1964623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3].length) (baseStart_1964623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964623 prefixEnd_1964623 := by exact prefixLift 1964623
  have htrace : WordTrace (prefixWord ++ tailWord_1964623) baseStart_1964623 baseEnd_1964623 := by
    simpa [prefixWord, tailWord_1964623, baseEnd_1964623] using wordTrace_append hprefix tailTrace_1964623
  have hstable : (prefixWord ++ tailWord_1964623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964623).length < 2 ^ (prefixWord ++ tailWord_1964623).sum := by decide
  have hdescent : baseEnd_1964623 < baseStart_1964623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964654 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1964654 : Nat := 118140960795 + 1964654 * 2 ^ 59
def prefixEnd_1964654 : Nat := 4983230072969 + 3 ^ 40 * 1964654 * 2
def baseEnd_1964654 : Nat := 448360809679316229284323

theorem tailTrace_1964654 : CollatzResearch.WordTrace tailWord_1964654 prefixEnd_1964654 448360809679316229284323 := by
  unfold tailWord_1964654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957102278050196129363627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47771212149601046023272677 8957102278050196129363627)
  ·
    refine ⟨13435653417075294194045441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8957102278050196129363627 13435653417075294194045441)
    ·
      refine ⟨10076740062806470645534081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13435653417075294194045441 10076740062806470645534081)
      ·
        refine ⟨7557555047104852984150561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10076740062806470645534081 7557555047104852984150561)
        ·
          refine ⟨5668166285328639738112921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7557555047104852984150561 5668166285328639738112921)
          ·
            refine ⟨4251124713996479803584691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668166285328639738112921 4251124713996479803584691)
            ·
              refine ⟨6376687070994719705377037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251124713996479803584691 6376687070994719705377037)
              ·
                refine ⟨2391257651623019889516389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6376687070994719705377037 2391257651623019889516389)
                ·
                  refine ⟨448360809679316229284323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391257651623019889516389 448360809679316229284323)
                  ·
                    rfl

theorem cell21_1964654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1964654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964654 prefixEnd_1964654 := by exact prefixLift 1964654
  have htrace : WordTrace (prefixWord ++ tailWord_1964654) baseStart_1964654 baseEnd_1964654 := by
    simpa [prefixWord, tailWord_1964654, baseEnd_1964654] using wordTrace_append hprefix tailTrace_1964654
  have hstable : (prefixWord ++ tailWord_1964654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964654).length < 2 ^ (prefixWord ++ tailWord_1964654).sum := by decide
  have hdescent : baseEnd_1964654 < baseStart_1964654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964823 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 4]
def baseStart_1964823 : Nat := 118140960795 + 1964823 * 2 ^ 59
def prefixEnd_1964823 : Nat := 4983230072969 + 3 ^ 40 * 1964823 * 2
def baseEnd_1964823 : Nat := 448399377781809490967311

theorem tailTrace_1964823 : CollatzResearch.WordTrace tailWord_1964823 prefixEnd_1964823 448399377781809490967311 := by
  unfold tailWord_1964823
  simp only [CollatzResearch.WordTrace]
  refine ⟨71662982160789310897811123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47775321440526207265207415 71662982160789310897811123)
  ·
    refine ⟨107494473241183966346716685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71662982160789310897811123 107494473241183966346716685)
    ·
      refine ⟨40310427465443987380018757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107494473241183966346716685 40310427465443987380018757)
      ·
        refine ⟨7558205149770747633753517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40310427465443987380018757 7558205149770747633753517)
        ·
          refine ⟨2834326931164030362657569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7558205149770747633753517 2834326931164030362657569)
          ·
            refine ⟨2125745198373022771993177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834326931164030362657569 2125745198373022771993177)
            ·
              refine ⟨1594308898779767078994883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125745198373022771993177 1594308898779767078994883)
              ·
                refine ⟨2391463348169650618492325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594308898779767078994883 2391463348169650618492325)
                ·
                  refine ⟨448399377781809490967311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391463348169650618492325 448399377781809490967311)
                  ·
                    rfl

theorem cell21_1964823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 4].length) (baseStart_1964823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1964823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1964823 prefixEnd_1964823 := by exact prefixLift 1964823
  have htrace : WordTrace (prefixWord ++ tailWord_1964823) baseStart_1964823 baseEnd_1964823 := by
    simpa [prefixWord, tailWord_1964823, baseEnd_1964823] using wordTrace_append hprefix tailTrace_1964823
  have hstable : (prefixWord ++ tailWord_1964823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964823).length < 2 ^ (prefixWord ++ tailWord_1964823).sum := by decide
  have hdescent : baseEnd_1964823 < baseStart_1964823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965059 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_1965059 : Nat := 118140960795 + 1965059 * 2 ^ 59
def prefixEnd_1965059 : Nat := 4983230072969 + 3 ^ 40 * 1965059 * 2
def baseEnd_1965059 : Nat := 448453236197125525033495

theorem tailTrace_1965059 : CollatzResearch.WordTrace tailWord_1965059 prefixEnd_1965059 448453236197125525033495 := by
  unfold tailWord_1965059
  simp only [CollatzResearch.WordTrace]
  refine ⟨71671589787934323203402231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47781059858622882135601487 71671589787934323203402231)
  ·
    refine ⟨107507384681901484805103347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71671589787934323203402231 107507384681901484805103347)
    ·
      refine ⟨161261077022852227207655021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107507384681901484805103347 161261077022852227207655021)
      ·
        refine ⟨60472903883569585202870633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161261077022852227207655021 60472903883569585202870633)
        ·
          refine ⟨45354677912677188902152975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60472903883569585202870633 45354677912677188902152975)
          ·
            refine ⟨68032016869015783353229463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45354677912677188902152975 68032016869015783353229463)
            ·
              refine ⟨102048025303523675029844195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68032016869015783353229463 102048025303523675029844195)
              ·
                refine ⟨153072037955285512544766293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102048025303523675029844195 153072037955285512544766293)
                ·
                  refine ⟨448453236197125525033495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 153072037955285512544766293 448453236197125525033495)
                  ·
                    rfl

theorem cell21_1965059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_1965059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965059 prefixEnd_1965059 := by exact prefixLift 1965059
  have htrace : WordTrace (prefixWord ++ tailWord_1965059) baseStart_1965059 baseEnd_1965059 := by
    simpa [prefixWord, tailWord_1965059, baseEnd_1965059] using wordTrace_append hprefix tailTrace_1965059
  have hstable : (prefixWord ++ tailWord_1965059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965059).length < 2 ^ (prefixWord ++ tailWord_1965059).sum := by decide
  have hdescent : baseEnd_1965059 < baseStart_1965059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965079 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 3]
def baseStart_1965079 : Nat := 118140960795 + 1965079 * 2 ^ 59
def prefixEnd_1965079 : Nat := 4983230072969 + 3 ^ 40 * 1965079 * 2
def baseEnd_1965079 : Nat := 448457800469609934700121

theorem tailTrace_1965079 : CollatzResearch.WordTrace tailWord_1965079 prefixEnd_1965079 448457800469609934700121 := by
  unfold tailWord_1965079
  simp only [CollatzResearch.WordTrace]
  refine ⟨71672319247861866619130291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47781546165241244412753527 71672319247861866619130291)
  ·
    refine ⟨107508478871792799928695437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71672319247861866619130291 107508478871792799928695437)
    ·
      refine ⟨40315679576922299973260789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107508478871792799928695437 40315679576922299973260789)
      ·
        refine ⟨3779594960336465622493199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40315679576922299973260789 3779594960336465622493199)
        ·
          refine ⟨5669392440504698433739799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779594960336465622493199 5669392440504698433739799)
          ·
            refine ⟨8504088660757047650609699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669392440504698433739799 8504088660757047650609699)
            ·
              refine ⟨12756132991135571475914549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504088660757047650609699 12756132991135571475914549)
              ·
                refine ⟨1195887467918959825866989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12756132991135571475914549 1195887467918959825866989)
                ·
                  refine ⟨448457800469609934700121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195887467918959825866989 448457800469609934700121)
                  ·
                    rfl

theorem cell21_1965079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3].length) (baseStart_1965079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965079 prefixEnd_1965079 := by exact prefixLift 1965079
  have htrace : WordTrace (prefixWord ++ tailWord_1965079) baseStart_1965079 baseEnd_1965079 := by
    simpa [prefixWord, tailWord_1965079, baseEnd_1965079] using wordTrace_append hprefix tailTrace_1965079
  have hstable : (prefixWord ++ tailWord_1965079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965079).length < 2 ^ (prefixWord ++ tailWord_1965079).sum := by decide
  have hdescent : baseEnd_1965079 < baseStart_1965079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965152 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_1965152 : Nat := 118140960795 + 1965152 * 2 ^ 59
def prefixEnd_1965152 : Nat := 4983230072969 + 3 ^ 40 * 1965152 * 2
def baseEnd_1965152 : Nat := 448474460064178029983305

theorem tailTrace_1965152 : CollatzResearch.WordTrace tailWord_1965152 prefixEnd_1965152 448474460064178029983305 := by
  unfold tailWord_1965152
  simp only [CollatzResearch.WordTrace]
  refine ⟨35837490888298700043268855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47783321184398266724358473 35837490888298700043268855)
  ·
    refine ⟨53756236332448050064903283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35837490888298700043268855 53756236332448050064903283)
    ·
      refine ⟨80634354498672075097354925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53756236332448050064903283 80634354498672075097354925)
      ·
        refine ⟨30237882937002028161508097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80634354498672075097354925 30237882937002028161508097)
        ·
          refine ⟨22678412202751521121131073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30237882937002028161508097 22678412202751521121131073)
          ·
            refine ⟨17008809152063640840848305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22678412202751521121131073 17008809152063640840848305)
            ·
              refine ⟨12756606864047730630636229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17008809152063640840848305 12756606864047730630636229)
              ·
                refine ⟨2391863787008949493244293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12756606864047730630636229 2391863787008949493244293)
                ·
                  refine ⟨448474460064178029983305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391863787008949493244293 448474460064178029983305)
                  ·
                    rfl

theorem cell21_1965152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_1965152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965152 prefixEnd_1965152 := by exact prefixLift 1965152
  have htrace : WordTrace (prefixWord ++ tailWord_1965152) baseStart_1965152 baseEnd_1965152 := by
    simpa [prefixWord, tailWord_1965152, baseEnd_1965152] using wordTrace_append hprefix tailTrace_1965152
  have hstable : (prefixWord ++ tailWord_1965152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965152).length < 2 ^ (prefixWord ++ tailWord_1965152).sum := by decide
  have hdescent : baseEnd_1965152 < baseStart_1965152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965262 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1965262 : Nat := 118140960795 + 1965262 * 2 ^ 59
def prefixEnd_1965262 : Nat := 4983230072969 + 3 ^ 40 * 1965262 * 2
def baseEnd_1965262 : Nat := 448499563562842283149747

theorem tailTrace_1965262 : CollatzResearch.WordTrace tailWord_1965262 prefixEnd_1965262 448499563562842283149747 := by
  unfold tailWord_1965262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959874225774861109130255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47785995870799259248694693 8959874225774861109130255)
  ·
    refine ⟨13439811338662291663695383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8959874225774861109130255 13439811338662291663695383)
    ·
      refine ⟨20159717007993437495543075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13439811338662291663695383 20159717007993437495543075)
      ·
        refine ⟨30239575511990156243314613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20159717007993437495543075 30239575511990156243314613)
        ·
          refine ⟨2834960204249077147810745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30239575511990156243314613 2834960204249077147810745)
          ·
            refine ⟨2126220153186807860858059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834960204249077147810745 2126220153186807860858059)
            ·
              refine ⟨3189330229780211791287089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126220153186807860858059 3189330229780211791287089)
              ·
                refine ⟨2391997672335158843465317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3189330229780211791287089 2391997672335158843465317)
                ·
                  refine ⟨448499563562842283149747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2391997672335158843465317 448499563562842283149747)
                  ·
                    rfl

theorem cell21_1965262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1965262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965262 prefixEnd_1965262 := by exact prefixLift 1965262
  have htrace : WordTrace (prefixWord ++ tailWord_1965262) baseStart_1965262 baseEnd_1965262 := by
    simpa [prefixWord, tailWord_1965262, baseEnd_1965262] using wordTrace_append hprefix tailTrace_1965262
  have hstable : (prefixWord ++ tailWord_1965262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965262).length < 2 ^ (prefixWord ++ tailWord_1965262).sum := by decide
  have hdescent : baseEnd_1965262 < baseStart_1965262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965338 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1965338 : Nat := 118140960795 + 1965338 * 2 ^ 59
def prefixEnd_1965338 : Nat := 4983230072969 + 3 ^ 40 * 1965338 * 2
def baseEnd_1965338 : Nat := 448516907798283039882925

theorem tailTrace_1965338 : CollatzResearch.WordTrace tailWord_1965338 prefixEnd_1965338 448516907798283039882925 := by
  unfold tailWord_1965338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920441438480888463202167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47787843835949035901872445 17920441438480888463202167)
  ·
    refine ⟨26880662157721332694803251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17920441438480888463202167 26880662157721332694803251)
    ·
      refine ⟨40320993236581999042204877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26880662157721332694803251 40320993236581999042204877)
      ·
        refine ⟨15120372463718249640826829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40320993236581999042204877 15120372463718249640826829)
        ·
          refine ⟨5670139673894343615310061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15120372463718249640826829 5670139673894343615310061)
          ·
            refine ⟨2126302377710378855741273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5670139673894343615310061 2126302377710378855741273)
            ·
              refine ⟨1594726783282784141805955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2126302377710378855741273 1594726783282784141805955)
              ·
                refine ⟨2392090174924176212708933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594726783282784141805955 2392090174924176212708933)
                ·
                  refine ⟨448516907798283039882925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392090174924176212708933 448516907798283039882925)
                  ·
                    rfl

theorem cell21_1965338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1965338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965338 prefixEnd_1965338 := by exact prefixLift 1965338
  have htrace : WordTrace (prefixWord ++ tailWord_1965338) baseStart_1965338 baseEnd_1965338 := by
    simpa [prefixWord, tailWord_1965338, baseEnd_1965338] using wordTrace_append hprefix tailTrace_1965338
  have hstable : (prefixWord ++ tailWord_1965338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965338).length < 2 ^ (prefixWord ++ tailWord_1965338).sum := by decide
  have hdescent : baseEnd_1965338 < baseStart_1965338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965383 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 3]
def baseStart_1965383 : Nat := 118140960795 + 1965383 * 2 ^ 59
def prefixEnd_1965383 : Nat := 4983230072969 + 3 ^ 40 * 1965383 * 2
def baseEnd_1965383 : Nat := 448527177411372961632833

theorem tailTrace_1965383 : CollatzResearch.WordTrace tailWord_1965383 prefixEnd_1965383 448527177411372961632833 := by
  unfold tailWord_1965383
  simp only [CollatzResearch.WordTrace]
  refine ⟨71683407038760526538196803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47788938025840351025464535 71683407038760526538196803)
  ·
    refine ⟨107525110558140789807295205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71683407038760526538196803 107525110558140789807295205)
    ·
      refine ⟨20160958229651398088867851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107525110558140789807295205 20160958229651398088867851)
      ·
        refine ⟨30241437344477097133301777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20160958229651398088867851 30241437344477097133301777)
        ·
          refine ⟨22681078008357822849976333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30241437344477097133301777 22681078008357822849976333)
          ·
            refine ⟨8505404253134183568741125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22681078008357822849976333 8505404253134183568741125)
            ·
              refine ⟨1594763297462659419138961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8505404253134183568741125 1594763297462659419138961)
              ·
                refine ⟨1196072473096994564354221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594763297462659419138961 1196072473096994564354221)
                ·
                  refine ⟨448527177411372961632833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196072473096994564354221 448527177411372961632833)
                  ·
                    rfl

theorem cell21_1965383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3].length) (baseStart_1965383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965383 prefixEnd_1965383 := by exact prefixLift 1965383
  have htrace : WordTrace (prefixWord ++ tailWord_1965383) baseStart_1965383 baseEnd_1965383 := by
    simpa [prefixWord, tailWord_1965383, baseEnd_1965383] using wordTrace_append hprefix tailTrace_1965383
  have hstable : (prefixWord ++ tailWord_1965383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965383).length < 2 ^ (prefixWord ++ tailWord_1965383).sum := by decide
  have hdescent : baseEnd_1965383 < baseStart_1965383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965411 : List Nat := [1, 1, 1, 5, 2, 3, 3, 5]
def baseStart_1965411 : Nat := 118140960795 + 1965411 * 2 ^ 59
def prefixEnd_1965411 : Nat := 4983230072969 + 3 ^ 40 * 1965411 * 2
def baseEnd_1965411 : Nat := 149511189130950378388703

theorem tailTrace_1965411 : CollatzResearch.WordTrace tailWord_1965411 prefixEnd_1965411 149511189130950378388703 := by
  unfold tailWord_1965411
  simp only [CollatzResearch.WordTrace]
  refine ⟨71684428282659087320216087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47789618855106058213477391 71684428282659087320216087)
  ·
    refine ⟨107526642423988630980324131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71684428282659087320216087 107526642423988630980324131)
    ·
      refine ⟨161289963635982946470486197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107526642423988630980324131 161289963635982946470486197)
      ·
        refine ⟨15120934090873401231608081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161289963635982946470486197 15120934090873401231608081)
        ·
          refine ⟨11340700568155050923706061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15120934090873401231608081 11340700568155050923706061)
          ·
            refine ⟨4252762713058144096389773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11340700568155050923706061 4252762713058144096389773)
            ·
              refine ⟨1594786017396804036146165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4252762713058144096389773 1594786017396804036146165)
              ·
                refine ⟨149511189130950378388703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1594786017396804036146165 149511189130950378388703)
                ·
                  rfl

theorem cell21_1965411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 5].length) (baseStart_1965411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965411 prefixEnd_1965411 := by exact prefixLift 1965411
  have htrace : WordTrace (prefixWord ++ tailWord_1965411) baseStart_1965411 baseEnd_1965411 := by
    simpa [prefixWord, tailWord_1965411, baseEnd_1965411] using wordTrace_append hprefix tailTrace_1965411
  have hstable : (prefixWord ++ tailWord_1965411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965411).length < 2 ^ (prefixWord ++ tailWord_1965411).sum := by decide
  have hdescent : baseEnd_1965411 < baseStart_1965411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965484 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_1965484 : Nat := 118140960795 + 1965484 * 2 ^ 59
def prefixEnd_1965484 : Nat := 4983230072969 + 3 ^ 40 * 1965484 * 2
def baseEnd_1965484 : Nat := 448550226987419230449293

theorem tailTrace_1965484 : CollatzResearch.WordTrace tailWord_1965484 prefixEnd_1965484 448550226987419230449293 := by
  unfold tailWord_1965484
  simp only [CollatzResearch.WordTrace]
  refine ⟨35843545405697310393811753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47791393874263080525082337 35843545405697310393811753)
  ·
    refine ⟨26882659054272982795358815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35843545405697310393811753 26882659054272982795358815)
    ·
      refine ⟨40323988581409474193038223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26882659054272982795358815 40323988581409474193038223)
      ·
        refine ⟨60485982872114211289557335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40323988581409474193038223 60485982872114211289557335)
        ·
          refine ⟨90728974308171316934336003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60485982872114211289557335 90728974308171316934336003)
          ·
            refine ⟨136093461462256975401504005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90728974308171316934336003 136093461462256975401504005)
            ·
              refine ⟨25517524024173182887782001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136093461462256975401504005 25517524024173182887782001)
              ·
                refine ⟨19138143018129887165836501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25517524024173182887782001 19138143018129887165836501)
                ·
                  refine ⟨448550226987419230449293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19138143018129887165836501 448550226987419230449293)
                  ·
                    rfl

theorem cell21_1965484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_1965484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965484 prefixEnd_1965484 := by exact prefixLift 1965484
  have htrace : WordTrace (prefixWord ++ tailWord_1965484) baseStart_1965484 baseEnd_1965484 := by
    simpa [prefixWord, tailWord_1965484, baseEnd_1965484] using wordTrace_append hprefix tailTrace_1965484
  have hstable : (prefixWord ++ tailWord_1965484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965484).length < 2 ^ (prefixWord ++ tailWord_1965484).sum := by decide
  have hdescent : baseEnd_1965484 < baseStart_1965484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965546 : List Nat := [3, 1, 3, 1, 4, 9]
def baseStart_1965546 : Nat := 118140960795 + 1965546 * 2 ^ 59
def prefixEnd_1965546 : Nat := 4983230072969 + 3 ^ 40 * 1965546 * 2
def baseEnd_1965546 : Nat := 16613495416004477793179

theorem tailTrace_1965546 : CollatzResearch.WordTrace tailWord_1965546 prefixEnd_1965546 16613495416004477793179 := by
  unfold tailWord_1965546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17922338034292501344095123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47792901424780003584253661 17922338034292501344095123)
  ·
    refine ⟨26883507051438752016142685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17922338034292501344095123 26883507051438752016142685)
    ·
      refine ⟨10081315144289532006053507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26883507051438752016142685 10081315144289532006053507)
      ·
        refine ⟨15121972716434298009080261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10081315144289532006053507 15121972716434298009080261)
        ·
          refine ⟨2835369884331430876702549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15121972716434298009080261 2835369884331430876702549)
          ·
            refine ⟨16613495416004477793179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2835369884331430876702549 16613495416004477793179)
            ·
              rfl

theorem cell21_1965546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 9].length) (baseStart_1965546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965546 prefixEnd_1965546 := by exact prefixLift 1965546
  have htrace : WordTrace (prefixWord ++ tailWord_1965546) baseStart_1965546 baseEnd_1965546 := by
    simpa [prefixWord, tailWord_1965546, baseEnd_1965546] using wordTrace_append hprefix tailTrace_1965546
  have hstable : (prefixWord ++ tailWord_1965546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965546).length < 2 ^ (prefixWord ++ tailWord_1965546).sum := by decide
  have hdescent : baseEnd_1965546 < baseStart_1965546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965625 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 4]
def baseStart_1965625 : Nat := 118140960795 + 1965625 * 2 ^ 59
def prefixEnd_1965625 : Nat := 4983230072969 + 3 ^ 40 * 1965625 * 2
def baseEnd_1965625 : Nat := 448582405108434318599005

theorem tailTrace_1965625 : CollatzResearch.WordTrace tailWord_1965625 prefixEnd_1965625 448582405108434318599005 := by
  unfold tailWord_1965625
  simp only [CollatzResearch.WordTrace]
  refine ⟨71692233503883801868506329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47794822335922534579004219 71692233503883801868506329)
  ·
    refine ⟨53769175127912851401379747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71692233503883801868506329 53769175127912851401379747)
    ·
      refine ⟨80653762691869277102069621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53769175127912851401379747 80653762691869277102069621)
      ·
        refine ⟨7561290252362744728319027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80653762691869277102069621 7561290252362744728319027)
        ·
          refine ⟨11341935378544117092478541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561290252362744728319027 11341935378544117092478541)
          ·
            refine ⟨4253225766954043909679453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11341935378544117092478541 4253225766954043909679453)
            ·
              refine ⟨1594959662607766466129795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4253225766954043909679453 1594959662607766466129795)
              ·
                refine ⟨2392439493911649699194693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594959662607766466129795 2392439493911649699194693)
                ·
                  refine ⟨448582405108434318599005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392439493911649699194693 448582405108434318599005)
                  ·
                    rfl

theorem cell21_1965625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_1965625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965625 prefixEnd_1965625 := by exact prefixLift 1965625
  have htrace : WordTrace (prefixWord ++ tailWord_1965625) baseStart_1965625 baseEnd_1965625 := by
    simpa [prefixWord, tailWord_1965625, baseEnd_1965625] using wordTrace_append hprefix tailTrace_1965625
  have hstable : (prefixWord ++ tailWord_1965625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965625).length < 2 ^ (prefixWord ++ tailWord_1965625).sum := by decide
  have hdescent : baseEnd_1965625 < baseStart_1965625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965645 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1965645 : Nat := 118140960795 + 1965645 * 2 ^ 59
def prefixEnd_1965645 : Nat := 4983230072969 + 3 ^ 40 * 1965645 * 2
def baseEnd_1965645 : Nat := 448586969380918728265631

theorem tailTrace_1965645 : CollatzResearch.WordTrace tailWord_1965645 prefixEnd_1965645 448586969380918728265631 := by
  unfold tailWord_1965645
  simp only [CollatzResearch.WordTrace]
  refine ⟨71692962963811345284234389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47795308642540896856156259 71692962963811345284234389)
  ·
    refine ⟨3360607638928656810198487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71692962963811345284234389 3360607638928656810198487)
    ·
      refine ⟨5040911458392985215297731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360607638928656810198487 5040911458392985215297731)
      ·
        refine ⟨7561367187589477822946597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040911458392985215297731 7561367187589477822946597)
        ·
          refine ⟨1417756347673027091802487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7561367187589477822946597 1417756347673027091802487)
          ·
            refine ⟨2126634521509540637703731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417756347673027091802487 2126634521509540637703731)
            ·
              refine ⟨3189951782264310956555597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126634521509540637703731 3189951782264310956555597)
              ·
                refine ⟨1196231918349116608708349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3189951782264310956555597 1196231918349116608708349)
                ·
                  refine ⟨448586969380918728265631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196231918349116608708349 448586969380918728265631)
                  ·
                    rfl

theorem cell21_1965645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1965645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965645 prefixEnd_1965645 := by exact prefixLift 1965645
  have htrace : WordTrace (prefixWord ++ tailWord_1965645) baseStart_1965645 baseEnd_1965645 := by
    simpa [prefixWord, tailWord_1965645, baseEnd_1965645] using wordTrace_append hprefix tailTrace_1965645
  have hstable : (prefixWord ++ tailWord_1965645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965645).length < 2 ^ (prefixWord ++ tailWord_1965645).sum := by decide
  have hdescent : baseEnd_1965645 < baseStart_1965645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965667 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_1965667 : Nat := 118140960795 + 1965667 * 2 ^ 59
def prefixEnd_1965667 : Nat := 4983230072969 + 3 ^ 40 * 1965667 * 2
def baseEnd_1965667 : Nat := 448591990080651578898919

theorem tailTrace_1965667 : CollatzResearch.WordTrace tailWord_1965667 prefixEnd_1965667 448591990080651578898919 := by
  unfold tailWord_1965667
  simp only [CollatzResearch.WordTrace]
  refine ⟨71693765369731643041535255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47795843579821095361023503 71693765369731643041535255)
  ·
    refine ⟨107540648054597464562302883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71693765369731643041535255 107540648054597464562302883)
    ·
      refine ⟨161310972081896196843454325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107540648054597464562302883 161310972081896196843454325)
      ·
        refine ⟨15122903632677768454073843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161310972081896196843454325 15122903632677768454073843)
        ·
          refine ⟨22684355449016652681110765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15122903632677768454073843 22684355449016652681110765)
          ·
            refine ⟨8506633293381244755416537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22684355449016652681110765 8506633293381244755416537)
            ·
              refine ⟨6379974970035933566562403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506633293381244755416537 6379974970035933566562403)
              ·
                refine ⟨9569962455053900349843605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379974970035933566562403 9569962455053900349843605)
                ·
                  refine ⟨448591990080651578898919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9569962455053900349843605 448591990080651578898919)
                  ·
                    rfl

theorem cell21_1965667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_1965667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965667 prefixEnd_1965667 := by exact prefixLift 1965667
  have htrace : WordTrace (prefixWord ++ tailWord_1965667) baseStart_1965667 baseEnd_1965667 := by
    simpa [prefixWord, tailWord_1965667, baseEnd_1965667] using wordTrace_append hprefix tailTrace_1965667
  have hstable : (prefixWord ++ tailWord_1965667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965667).length < 2 ^ (prefixWord ++ tailWord_1965667).sum := by decide
  have hdescent : baseEnd_1965667 < baseStart_1965667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965743 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_1965743 : Nat := 118140960795 + 1965743 * 2 ^ 59
def prefixEnd_1965743 : Nat := 4983230072969 + 3 ^ 40 * 1965743 * 2
def baseEnd_1965743 : Nat := 448609334316092335632097

theorem tailTrace_1965743 : CollatzResearch.WordTrace tailWord_1965743 prefixEnd_1965743 448609334316092335632097 := by
  unfold tailWord_1965743
  simp only [CollatzResearch.WordTrace]
  refine ⟨71696537317456308021301883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47797691544970872014201255 71696537317456308021301883)
  ·
    refine ⟨107544805976184462031952825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71696537317456308021301883 107544805976184462031952825)
    ·
      refine ⟨80658604482138346523964619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107544805976184462031952825 80658604482138346523964619)
      ·
        refine ⟨120987906723207519785946929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80658604482138346523964619 120987906723207519785946929)
        ·
          refine ⟨90740930042405639839460197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120987906723207519785946929 90740930042405639839460197)
          ·
            refine ⟨17013924382951057469898787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90740930042405639839460197 17013924382951057469898787)
            ·
              refine ⟨25520886574426586204848181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17013924382951057469898787 25520886574426586204848181)
              ·
                refine ⟨2392583116352492456704517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25520886574426586204848181 2392583116352492456704517)
                ·
                  refine ⟨448609334316092335632097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392583116352492456704517 448609334316092335632097)
                  ·
                    rfl

theorem cell21_1965743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_1965743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965743 prefixEnd_1965743 := by exact prefixLift 1965743
  have htrace : WordTrace (prefixWord ++ tailWord_1965743) baseStart_1965743 baseEnd_1965743 := by
    simpa [prefixWord, tailWord_1965743, baseEnd_1965743] using wordTrace_append hprefix tailTrace_1965743
  have hstable : (prefixWord ++ tailWord_1965743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965743).length < 2 ^ (prefixWord ++ tailWord_1965743).sum := by decide
  have hdescent : baseEnd_1965743 < baseStart_1965743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965805 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1965805 : Nat := 118140960795 + 1965805 * 2 ^ 59
def prefixEnd_1965805 : Nat := 4983230072969 + 3 ^ 40 * 1965805 * 2
def baseEnd_1965805 : Nat := 448623483560794005598637

theorem tailTrace_1965805 : CollatzResearch.WordTrace tailWord_1965805 prefixEnd_1965805 448623483560794005598637 := by
  unfold tailWord_1965805
  simp only [CollatzResearch.WordTrace]
  refine ⟨71698798643231692610058869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47799199095487795073372579 71698798643231692610058869)
  ·
    refine ⟨6721762372802971182193019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71698798643231692610058869 6721762372802971182193019)
    ·
      refine ⟨10082643559204456773289529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6721762372802971182193019 10082643559204456773289529)
      ·
        refine ⟨7561982669403342579967147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10082643559204456773289529 7561982669403342579967147)
        ·
          refine ⟨11342974004105013869950721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561982669403342579967147 11342974004105013869950721)
          ·
            refine ⟨8507230503078760402463041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11342974004105013869950721 8507230503078760402463041)
            ·
              refine ⟨6380422877309070301847281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8507230503078760402463041 6380422877309070301847281)
              ·
                refine ⟨4785317157981802726385461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6380422877309070301847281 4785317157981802726385461)
                ·
                  refine ⟨448623483560794005598637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4785317157981802726385461 448623483560794005598637)
                  ·
                    rfl

theorem cell21_1965805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1965805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965805 prefixEnd_1965805 := by exact prefixLift 1965805
  have htrace : WordTrace (prefixWord ++ tailWord_1965805) baseStart_1965805 baseEnd_1965805 := by
    simpa [prefixWord, tailWord_1965805, baseEnd_1965805] using wordTrace_append hprefix tailTrace_1965805
  have hstable : (prefixWord ++ tailWord_1965805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965805).length < 2 ^ (prefixWord ++ tailWord_1965805).sum := by decide
  have hdescent : baseEnd_1965805 < baseStart_1965805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965850 : List Nat := [3, 1, 1, 3, 2, 3, 2, 6]
def baseStart_1965850 : Nat := 118140960795 + 1965850 * 2 ^ 59
def prefixEnd_1965850 : Nat := 4983230072969 + 3 ^ 40 * 1965850 * 2
def baseEnd_1965850 : Nat := 149544584391294642449515

theorem tailTrace_1965850 : CollatzResearch.WordTrace tailWord_1965850 prefixEnd_1965850 149544584391294642449515 := by
  unfold tailWord_1965850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17925109982017166323861751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47800293285379110196964669 17925109982017166323861751)
  ·
    refine ⟨26887664973025749485792627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17925109982017166323861751 26887664973025749485792627)
    ·
      refine ⟨40331497459538624228688941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26887664973025749485792627 40331497459538624228688941)
      ·
        refine ⟨15124311547326984085758353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40331497459538624228688941 15124311547326984085758353)
        ·
          refine ⟨11343233660495238064318765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15124311547326984085758353 11343233660495238064318765)
          ·
            refine ⟨4253712622685714274119537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11343233660495238064318765 4253712622685714274119537)
            ·
              refine ⟨3190284467014285705589653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4253712622685714274119537 3190284467014285705589653)
              ·
                refine ⟨149544584391294642449515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190284467014285705589653 149544584391294642449515)
                ·
                  rfl

theorem cell21_1965850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_1965850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965850 prefixEnd_1965850 := by exact prefixLift 1965850
  have htrace : WordTrace (prefixWord ++ tailWord_1965850) baseStart_1965850 baseEnd_1965850 := by
    simpa [prefixWord, tailWord_1965850, baseEnd_1965850] using wordTrace_append hprefix tailTrace_1965850
  have hstable : (prefixWord ++ tailWord_1965850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965850).length < 2 ^ (prefixWord ++ tailWord_1965850).sum := by decide
  have hdescent : baseEnd_1965850 < baseStart_1965850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965895 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_1965895 : Nat := 118140960795 + 1965895 * 2 ^ 59
def prefixEnd_1965895 : Nat := 4983230072969 + 3 ^ 40 * 1965895 * 2
def baseEnd_1965895 : Nat := 448644022786973849098453

theorem tailTrace_1965895 : CollatzResearch.WordTrace tailWord_1965895 prefixEnd_1965895 448644022786973849098453 := by
  unfold tailWord_1965895
  simp only [CollatzResearch.WordTrace]
  refine ⟨71702081212905637980835139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47801387475270425320556759 71702081212905637980835139)
  ·
    refine ⟨107553121819358456971252709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71702081212905637980835139 107553121819358456971252709)
    ·
      refine ⟨20166210341129710682109883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107553121819358456971252709 20166210341129710682109883)
      ·
        refine ⟨30249315511694566023164825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20166210341129710682109883 30249315511694566023164825)
        ·
          refine ⟨22686986633770924517373619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30249315511694566023164825 22686986633770924517373619)
          ·
            refine ⟨34030479950656386776060429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22686986633770924517373619 34030479950656386776060429)
            ·
              refine ⟨12761429981496145041022661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34030479950656386776060429 12761429981496145041022661)
              ·
                refine ⟨2392768121530527195191749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12761429981496145041022661 2392768121530527195191749)
                ·
                  refine ⟨448644022786973849098453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2392768121530527195191749 448644022786973849098453)
                  ·
                    rfl

theorem cell21_1965895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_1965895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965895 prefixEnd_1965895 := by exact prefixLift 1965895
  have htrace : WordTrace (prefixWord ++ tailWord_1965895) baseStart_1965895 baseEnd_1965895 := by
    simpa [prefixWord, tailWord_1965895, baseEnd_1965895] using wordTrace_append hprefix tailTrace_1965895
  have hstable : (prefixWord ++ tailWord_1965895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965895).length < 2 ^ (prefixWord ++ tailWord_1965895).sum := by decide
  have hdescent : baseEnd_1965895 < baseStart_1965895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965957 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 3]
def baseStart_1965957 : Nat := 118140960795 + 1965957 * 2 ^ 59
def prefixEnd_1965957 : Nat := 4983230072969 + 3 ^ 40 * 1965957 * 2
def baseEnd_1965957 : Nat := 448658172031675519064993

theorem tailTrace_1965957 : CollatzResearch.WordTrace tailWord_1965957 prefixEnd_1965957 448658172031675519064993 := by
  unfold tailWord_1965957
  simp only [CollatzResearch.WordTrace]
  refine ⟨71704342538681022569592125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47802895025787348379728083 71704342538681022569592125)
  ·
    refine ⟨26889128452005383463597047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71704342538681022569592125 26889128452005383463597047)
    ·
      refine ⟨40333692678008075195395571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26889128452005383463597047 40333692678008075195395571)
      ·
        refine ⟨60500539017012112793093357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40333692678008075195395571 60500539017012112793093357)
        ·
          refine ⟨22687702131379542297410009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60500539017012112793093357 22687702131379542297410009)
          ·
            refine ⟨17015776598534656723057507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22687702131379542297410009 17015776598534656723057507)
            ·
              refine ⟨25523664897801985084586261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17015776598534656723057507 25523664897801985084586261)
              ·
                refine ⟨1196421792084468050839981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25523664897801985084586261 1196421792084468050839981)
                ·
                  refine ⟨448658172031675519064993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196421792084468050839981 448658172031675519064993)
                  ·
                    rfl

theorem cell21_1965957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_1965957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965957 prefixEnd_1965957 := by exact prefixLift 1965957
  have htrace : WordTrace (prefixWord ++ tailWord_1965957) baseStart_1965957 baseEnd_1965957 := by
    simpa [prefixWord, tailWord_1965957, baseEnd_1965957] using wordTrace_append hprefix tailTrace_1965957
  have hstable : (prefixWord ++ tailWord_1965957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965957).length < 2 ^ (prefixWord ++ tailWord_1965957).sum := by decide
  have hdescent : baseEnd_1965957 < baseStart_1965957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965991 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 3]
def baseStart_1965991 : Nat := 118140960795 + 1965991 * 2 ^ 59
def prefixEnd_1965991 : Nat := 4983230072969 + 3 ^ 40 * 1965991 * 2
def baseEnd_1965991 : Nat := 448665931294899015498257

theorem tailTrace_1965991 : CollatzResearch.WordTrace tailWord_1965991 prefixEnd_1965991 448665931294899015498257 := by
  unfold tailWord_1965991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71705582620557846376329827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47803721747038564250886551 71705582620557846376329827)
  ·
    refine ⟨107558373930836769564494741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71705582620557846376329827 107558373930836769564494741)
    ·
      refine ⟨5041798778007973573335691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107558373930836769564494741 5041798778007973573335691)
      ·
        refine ⟨7562698167011960360003537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5041798778007973573335691 7562698167011960360003537)
        ·
          refine ⟨5672023625258970270002653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7562698167011960360003537 5672023625258970270002653)
          ·
            refine ⟨2127008859472113851250995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5672023625258970270002653 2127008859472113851250995)
            ·
              refine ⟨3190513289208170776876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127008859472113851250995 3190513289208170776876493)
              ·
                refine ⟨1196442483453064041328685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3190513289208170776876493 1196442483453064041328685)
                ·
                  refine ⟨448665931294899015498257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196442483453064041328685 448665931294899015498257)
                  ·
                    rfl

theorem cell21_1965991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3].length) (baseStart_1965991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1965991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1965991 prefixEnd_1965991 := by exact prefixLift 1965991
  have htrace : WordTrace (prefixWord ++ tailWord_1965991) baseStart_1965991 baseEnd_1965991 := by
    simpa [prefixWord, tailWord_1965991, baseEnd_1965991] using wordTrace_append hprefix tailTrace_1965991
  have hstable : (prefixWord ++ tailWord_1965991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965991).length < 2 ^ (prefixWord ++ tailWord_1965991).sum := by decide
  have hdescent : baseEnd_1965991 < baseStart_1965991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966092 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1966092 : Nat := 118140960795 + 1966092 * 2 ^ 59
def prefixEnd_1966092 : Nat := 4983230072969 + 3 ^ 40 * 1966092 * 2
def baseEnd_1966092 : Nat := 448688980870945284314717

theorem tailTrace_1966092 : CollatzResearch.WordTrace tailWord_1966092 prefixEnd_1966092 448688980870945284314717 := by
  unfold tailWord_1966092
  simp only [CollatzResearch.WordTrace]
  refine ⟨35854633196595970312878265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47806177595461293750504353 35854633196595970312878265)
  ·
    refine ⟨26890974897446977734658699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35854633196595970312878265 26890974897446977734658699)
    ·
      refine ⟨40336462346170466601988049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26890974897446977734658699 40336462346170466601988049)
      ·
        refine ⟨30252346759627849951491037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40336462346170466601988049 30252346759627849951491037)
        ·
          refine ⟨11344630034860443731809139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30252346759627849951491037 11344630034860443731809139)
          ·
            refine ⟨17016945052290665597713709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11344630034860443731809139 17016945052290665597713709)
            ·
              refine ⟨6381354394608999599142641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17016945052290665597713709 6381354394608999599142641)
              ·
                refine ⟨4786015795956749699356981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6381354394608999599142641 4786015795956749699356981)
                ·
                  refine ⟨448688980870945284314717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786015795956749699356981 448688980870945284314717)
                  ·
                    rfl

theorem cell21_1966092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1966092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966092 prefixEnd_1966092 := by exact prefixLift 1966092
  have htrace : WordTrace (prefixWord ++ tailWord_1966092) baseStart_1966092 baseEnd_1966092 := by
    simpa [prefixWord, tailWord_1966092, baseEnd_1966092] using wordTrace_append hprefix tailTrace_1966092
  have hstable : (prefixWord ++ tailWord_1966092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966092).length < 2 ^ (prefixWord ++ tailWord_1966092).sum := by decide
  have hdescent : baseEnd_1966092 < baseStart_1966092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966126 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1966126 : Nat := 118140960795 + 1966126 * 2 ^ 59
def prefixEnd_1966126 : Nat := 4983230072969 + 3 ^ 40 * 1966126 * 2
def baseEnd_1966126 : Nat := 448696740134168780747981

theorem tailTrace_1966126 : CollatzResearch.WordTrace tailWord_1966126 prefixEnd_1966126 448696740134168780747981 := by
  unfold tailWord_1966126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963813309383595554061779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47807004316712509621662821 8963813309383595554061779)
  ·
    refine ⟨13445719964075393331092669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8963813309383595554061779 13445719964075393331092669)
    ·
      refine ⟨5042144986528272499159751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13445719964075393331092669 5042144986528272499159751)
      ·
        refine ⟨7563217479792408748739627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042144986528272499159751 7563217479792408748739627)
        ·
          refine ⟨11344826219688613123109441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563217479792408748739627 11344826219688613123109441)
          ·
            refine ⟨8508619664766459842332081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11344826219688613123109441 8508619664766459842332081)
            ·
              refine ⟨6381464748574844881749061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8508619664766459842332081 6381464748574844881749061)
              ·
                refine ⟨1196524640357783415327949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6381464748574844881749061 1196524640357783415327949)
                ·
                  refine ⟨448696740134168780747981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196524640357783415327949 448696740134168780747981)
                  ·
                    rfl

theorem cell21_1966126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1966126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966126 prefixEnd_1966126 := by exact prefixLift 1966126
  have htrace : WordTrace (prefixWord ++ tailWord_1966126) baseStart_1966126 baseEnd_1966126 := by
    simpa [prefixWord, tailWord_1966126, baseEnd_1966126] using wordTrace_append hprefix tailTrace_1966126
  have hstable : (prefixWord ++ tailWord_1966126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966126).length < 2 ^ (prefixWord ++ tailWord_1966126).sum := by decide
  have hdescent : baseEnd_1966126 < baseStart_1966126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966140 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_1966140 : Nat := 118140960795 + 1966140 * 2 ^ 59
def prefixEnd_1966140 : Nat := 4983230072969 + 3 ^ 40 * 1966140 * 2
def baseEnd_1966140 : Nat := 448699935124907867514619

theorem tailTrace_1966140 : CollatzResearch.WordTrace tailWord_1966140 prefixEnd_1966140 448699935124907867514619 := by
  unfold tailWord_1966140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35855508548509022411751937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47807344731345363215669249 35855508548509022411751937)
  ·
    refine ⟨26891631411381766808813953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35855508548509022411751937 26891631411381766808813953)
    ·
      refine ⟨20168723558536325106610465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26891631411381766808813953 20168723558536325106610465)
      ·
        refine ⟨15126542668902243829957849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20168723558536325106610465 15126542668902243829957849)
        ·
          refine ⟨11344907001676682872468387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15126542668902243829957849 11344907001676682872468387)
          ·
            refine ⟨17017360502515024308702581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11344907001676682872468387 17017360502515024308702581)
            ·
              refine ⟨1595377547110783528940867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17017360502515024308702581 1595377547110783528940867)
              ·
                refine ⟨2393066320666175293411301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595377547110783528940867 2393066320666175293411301)
                ·
                  refine ⟨448699935124907867514619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393066320666175293411301 448699935124907867514619)
                  ·
                    rfl

theorem cell21_1966140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_1966140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966140 prefixEnd_1966140 := by exact prefixLift 1966140
  have htrace : WordTrace (prefixWord ++ tailWord_1966140) baseStart_1966140 baseEnd_1966140 := by
    simpa [prefixWord, tailWord_1966140, baseEnd_1966140] using wordTrace_append hprefix tailTrace_1966140
  have hstable : (prefixWord ++ tailWord_1966140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966140).length < 2 ^ (prefixWord ++ tailWord_1966140).sum := by decide
  have hdescent : baseEnd_1966140 < baseStart_1966140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966199 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_1966199 : Nat := 118140960795 + 1966199 * 2 ^ 59
def prefixEnd_1966199 : Nat := 4983230072969 + 3 ^ 40 * 1966199 * 2
def baseEnd_1966199 : Nat := 448713399728736876031165

theorem tailTrace_1966199 : CollatzResearch.WordTrace tailWord_1966199 prefixEnd_1966199 448713399728736876031165 := by
  unfold tailWord_1966199
  simp only [CollatzResearch.WordTrace]
  refine ⟨71713169003804297899901651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47808779335869531933267767 71713169003804297899901651)
  ·
    refine ⟨107569753505706446849852477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71713169003804297899901651 107569753505706446849852477)
    ·
      refine ⟨40338657564639917568694679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107569753505706446849852477 40338657564639917568694679)
      ·
        refine ⟨60507986346959876353042019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40338657564639917568694679 60507986346959876353042019)
        ·
          refine ⟨90761979520439814529563029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60507986346959876353042019 90761979520439814529563029)
          ·
            refine ⟨4254467790020616306073267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90761979520439814529563029 4254467790020616306073267)
            ·
              refine ⟨6381701685030924459109901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254467790020616306073267 6381701685030924459109901)
              ·
                refine ⟨2393138131886596672166213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6381701685030924459109901 2393138131886596672166213)
                ·
                  refine ⟨448713399728736876031165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393138131886596672166213 448713399728736876031165)
                  ·
                    rfl

theorem cell21_1966199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_1966199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966199 prefixEnd_1966199 := by exact prefixLift 1966199
  have htrace : WordTrace (prefixWord ++ tailWord_1966199) baseStart_1966199 baseEnd_1966199 := by
    simpa [prefixWord, tailWord_1966199, baseEnd_1966199] using wordTrace_append hprefix tailTrace_1966199
  have hstable : (prefixWord ++ tailWord_1966199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966199).length < 2 ^ (prefixWord ++ tailWord_1966199).sum := by decide
  have hdescent : baseEnd_1966199 < baseStart_1966199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966213 : List Nat := [1, 3, 1, 1, 5, 1, 2, 7]
def baseStart_1966213 : Nat := 118140960795 + 1966213 * 2 ^ 59
def prefixEnd_1966213 : Nat := 4983230072969 + 3 ^ 40 * 1966213 * 2
def baseEnd_1966213 : Nat := 149572198239825320932601

theorem tailTrace_1966213 : CollatzResearch.WordTrace tailWord_1966213 prefixEnd_1966213 149572198239825320932601 := by
  unfold tailWord_1966213
  simp only [CollatzResearch.WordTrace]
  refine ⟨71713679625753578290911293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47809119750502385527274195 71713679625753578290911293)
  ·
    refine ⟨26892629859657591859091735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71713679625753578290911293 26892629859657591859091735)
    ·
      refine ⟨40338944789486387788637603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26892629859657591859091735 40338944789486387788637603)
      ·
        refine ⟨60508417184229581682956405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40338944789486387788637603 60508417184229581682956405)
        ·
          refine ⟨5672664111021523282777163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60508417184229581682956405 5672664111021523282777163)
          ·
            refine ⟨8508996166532284924165745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672664111021523282777163 8508996166532284924165745)
            ·
              refine ⟨6381747124899213693124309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8508996166532284924165745 6381747124899213693124309)
              ·
                refine ⟨149572198239825320932601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6381747124899213693124309 149572198239825320932601)
                ·
                  rfl

theorem cell21_1966213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_1966213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966213 prefixEnd_1966213 := by exact prefixLift 1966213
  have htrace : WordTrace (prefixWord ++ tailWord_1966213) baseStart_1966213 baseEnd_1966213 := by
    simpa [prefixWord, tailWord_1966213, baseEnd_1966213] using wordTrace_append hprefix tailTrace_1966213
  have hstable : (prefixWord ++ tailWord_1966213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966213).length < 2 ^ (prefixWord ++ tailWord_1966213).sum := by decide
  have hdescent : baseEnd_1966213 < baseStart_1966213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966247 : List Nat := [1, 1, 6, 2, 2, 2, 1, 6]
def baseStart_1966247 : Nat := 118140960795 + 1966247 * 2 ^ 59
def prefixEnd_1966247 : Nat := 4983230072969 + 3 ^ 40 * 1966247 * 2
def baseEnd_1966247 : Nat := 149574784660899819743689

theorem tailTrace_1966247 : CollatzResearch.WordTrace tailWord_1966247 prefixEnd_1966247 149574784660899819743689 := by
  unfold tailWord_1966247
  simp only [CollatzResearch.WordTrace]
  refine ⟨71714919707630402097648995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47809946471753601398432663 71714919707630402097648995)
  ·
    refine ⟨107572379561445603146473493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71714919707630402097648995 107572379561445603146473493)
    ·
      refine ⟨5042455291942762647490945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107572379561445603146473493 5042455291942762647490945)
      ·
        refine ⟨3781841468957071985618209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5042455291942762647490945 3781841468957071985618209)
        ·
          refine ⟨2836381101717803989213657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781841468957071985618209 2836381101717803989213657)
          ·
            refine ⟨2127285826288352991910243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836381101717803989213657 2127285826288352991910243)
            ·
              refine ⟨3190928739432529487865365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127285826288352991910243 3190928739432529487865365)
              ·
                refine ⟨149574784660899819743689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3190928739432529487865365 149574784660899819743689)
                ·
                  rfl

theorem cell21_1966247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 6].length) (baseStart_1966247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966247 prefixEnd_1966247 := by exact prefixLift 1966247
  have htrace : WordTrace (prefixWord ++ tailWord_1966247) baseStart_1966247 baseEnd_1966247 := by
    simpa [prefixWord, tailWord_1966247, baseEnd_1966247] using wordTrace_append hprefix tailTrace_1966247
  have hstable : (prefixWord ++ tailWord_1966247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966247).length < 2 ^ (prefixWord ++ tailWord_1966247).sum := by decide
  have hdescent : baseEnd_1966247 < baseStart_1966247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966368 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_1966368 : Nat := 118140960795 + 1966368 * 2 ^ 59
def prefixEnd_1966368 : Nat := 4983230072969 + 3 ^ 40 * 1966368 * 2
def baseEnd_1966368 : Nat := 448751967831230137714153

theorem tailTrace_1966368 : CollatzResearch.WordTrace tailWord_1966368 prefixEnd_1966368 448751967831230137714153 := by
  unfold tailWord_1966368
  simp only [CollatzResearch.WordTrace]
  refine ⟨35859666470096019881401879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47812888626794693175202505 35859666470096019881401879)
  ·
    refine ⟨53789499705144029822102819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35859666470096019881401879 53789499705144029822102819)
    ·
      refine ⟨80684249557716044733154229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53789499705144029822102819 80684249557716044733154229)
      ·
        refine ⟨7564148396035879193733209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80684249557716044733154229 7564148396035879193733209)
        ·
          refine ⟨5673111297026909395299907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7564148396035879193733209 5673111297026909395299907)
          ·
            refine ⟨8509666945540364092949861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673111297026909395299907 8509666945540364092949861)
            ·
              refine ⟨1595562552288818267428099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8509666945540364092949861 1595562552288818267428099)
              ·
                refine ⟨2393343828433227401142149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595562552288818267428099 2393343828433227401142149)
                ·
                  refine ⟨448751967831230137714153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393343828433227401142149 448751967831230137714153)
                  ·
                    rfl

theorem cell21_1966368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_1966368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966368 prefixEnd_1966368 := by exact prefixLift 1966368
  have htrace : WordTrace (prefixWord ++ tailWord_1966368) baseStart_1966368 baseEnd_1966368 := by
    simpa [prefixWord, tailWord_1966368, baseEnd_1966368] using wordTrace_append hprefix tailTrace_1966368
  have hstable : (prefixWord ++ tailWord_1966368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966368).length < 2 ^ (prefixWord ++ tailWord_1966368).sum := by decide
  have hdescent : baseEnd_1966368 < baseStart_1966368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966424 : List Nat := [2, 1, 2, 2, 1, 1, 2, 10]
def baseStart_1966424 : Nat := 118140960795 + 1966424 * 2 ^ 59
def prefixEnd_1966424 : Nat := 4983230072969 + 3 ^ 40 * 1966424 * 2
def baseEnd_1966424 : Nat := 149588249264728828260235

theorem tailTrace_1966424 : CollatzResearch.WordTrace tailWord_1966424 prefixEnd_1966424 149588249264728828260235 := by
  unfold tailWord_1966424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860687713994580663421163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47814250285326107551228217 35860687713994580663421163)
  ·
    refine ⟨53791031570991870995131745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35860687713994580663421163 53791031570991870995131745)
    ·
      refine ⟨40343273678243903246348809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53791031570991870995131745 40343273678243903246348809)
      ·
        refine ⟨30257455258682927434761607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40343273678243903246348809 30257455258682927434761607)
        ·
          refine ⟨45386182888024391152142411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30257455258682927434761607 45386182888024391152142411)
          ·
            refine ⟨68079274332036586728213617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45386182888024391152142411 68079274332036586728213617)
            ·
              refine ⟨51059455749027440046160213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68079274332036586728213617 51059455749027440046160213)
              ·
                refine ⟨149588249264728828260235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51059455749027440046160213 149588249264728828260235)
                ·
                  rfl

theorem cell21_1966424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_1966424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966424 prefixEnd_1966424 := by exact prefixLift 1966424
  have htrace : WordTrace (prefixWord ++ tailWord_1966424) baseStart_1966424 baseEnd_1966424 := by
    simpa [prefixWord, tailWord_1966424, baseEnd_1966424] using wordTrace_append hprefix tailTrace_1966424
  have hstable : (prefixWord ++ tailWord_1966424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966424).length < 2 ^ (prefixWord ++ tailWord_1966424).sum := by decide
  have hdescent : baseEnd_1966424 < baseStart_1966424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966441 : List Nat := [1, 2, 1, 1, 1, 3, 7, 5]
def baseStart_1966441 : Nat := 118140960795 + 1966441 * 2 ^ 59
def prefixEnd_1966441 : Nat := 4983230072969 + 3 ^ 40 * 1966441 * 2
def baseEnd_1966441 : Nat := 149589542475266077665779

theorem tailTrace_1966441 : CollatzResearch.WordTrace tailWord_1966441 prefixEnd_1966441 149589542475266077665779 := by
  unfold tailWord_1966441
  simp only [CollatzResearch.WordTrace]
  refine ⟨71721995468927573230211177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47814663645951715486807451 71721995468927573230211177)
  ·
    refine ⟨53791496601695679922658383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71721995468927573230211177 53791496601695679922658383)
    ·
      refine ⟨80687244902543519883987575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53791496601695679922658383 80687244902543519883987575)
      ·
        refine ⟨121030867353815279825981363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80687244902543519883987575 121030867353815279825981363)
        ·
          refine ⟨181546301030722919738972045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121030867353815279825981363 181546301030722919738972045)
          ·
            refine ⟨68079862886521094902114517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181546301030722919738972045 68079862886521094902114517)
            ·
              refine ⟨1595621786402838161768309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68079862886521094902114517 1595621786402838161768309)
              ·
                refine ⟨149589542475266077665779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1595621786402838161768309 149589542475266077665779)
                ·
                  rfl

theorem cell21_1966441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 5].length) (baseStart_1966441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966441 prefixEnd_1966441 := by exact prefixLift 1966441
  have htrace : WordTrace (prefixWord ++ tailWord_1966441) baseStart_1966441 baseEnd_1966441 := by
    simpa [prefixWord, tailWord_1966441, baseEnd_1966441] using wordTrace_append hprefix tailTrace_1966441
  have hstable : (prefixWord ++ tailWord_1966441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966441).length < 2 ^ (prefixWord ++ tailWord_1966441).sum := by decide
  have hdescent : baseEnd_1966441 < baseStart_1966441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966472 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_1966472 : Nat := 118140960795 + 1966472 * 2 ^ 59
def prefixEnd_1966472 : Nat := 4983230072969 + 3 ^ 40 * 1966472 * 2
def baseEnd_1966472 : Nat := 448775702048149067980607

theorem tailTrace_1966472 : CollatzResearch.WordTrace tailWord_1966472 prefixEnd_1966472 448775702048149067980607 := by
  unfold tailWord_1966472
  simp only [CollatzResearch.WordTrace]
  refine ⟨35861563065907632762294835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47815417421210177016393113 35861563065907632762294835)
  ·
    refine ⟨53792344598861449143442253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35861563065907632762294835 53792344598861449143442253)
    ·
      refine ⟨20172129224573043428790845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53792344598861449143442253 20172129224573043428790845)
      ·
        refine ⟨7564548459214891285796567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20172129224573043428790845 7564548459214891285796567)
        ·
          refine ⟨11346822688822336928694851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564548459214891285796567 11346822688822336928694851)
          ·
            refine ⟨17020234033233505393042277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11346822688822336928694851 17020234033233505393042277)
            ·
              refine ⟨3191293881231282261195427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17020234033233505393042277 3191293881231282261195427)
              ·
                refine ⟨4786940821846923391793141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191293881231282261195427 4786940821846923391793141)
                ·
                  refine ⟨448775702048149067980607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4786940821846923391793141 448775702048149067980607)
                  ·
                    rfl

theorem cell21_1966472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_1966472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966472 prefixEnd_1966472 := by exact prefixLift 1966472
  have htrace : WordTrace (prefixWord ++ tailWord_1966472) baseStart_1966472 baseEnd_1966472 := by
    simpa [prefixWord, tailWord_1966472, baseEnd_1966472] using wordTrace_append hprefix tailTrace_1966472
  have hstable : (prefixWord ++ tailWord_1966472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966472).length < 2 ^ (prefixWord ++ tailWord_1966472).sum := by decide
  have hdescent : baseEnd_1966472 < baseStart_1966472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966593 : List Nat := [1, 2, 4, 1, 3, 1, 3, 6]
def baseStart_1966593 : Nat := 118140960795 + 1966593 * 2 ^ 59
def prefixEnd_1966593 : Nat := 4983230072969 + 3 ^ 40 * 1966593 * 2
def baseEnd_1966593 : Nat := 149601105298893248821231

theorem tailTrace_1966593 : CollatzResearch.WordTrace tailWord_1966593 prefixEnd_1966593 149601105298893248821231 := by
  unfold tailWord_1966593
  simp only [CollatzResearch.WordTrace]
  refine ⟨71727539364376903189744433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47818359576251268793162955 71727539364376903189744433)
  ·
    refine ⟨53795654523282677392308325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71727539364376903189744433 53795654523282677392308325)
    ·
      refine ⟨10086685223115502011057811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53795654523282677392308325 10086685223115502011057811)
      ·
        refine ⟨15130027834673253016586717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10086685223115502011057811 15130027834673253016586717)
        ·
          refine ⟨5673760438002469881220019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15130027834673253016586717 5673760438002469881220019)
          ·
            refine ⟨8510640657003704821830029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673760438002469881220019 8510640657003704821830029)
            ·
              refine ⟨3191490246376389308186261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8510640657003704821830029 3191490246376389308186261)
              ·
                refine ⟨149601105298893248821231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3191490246376389308186261 149601105298893248821231)
                ·
                  rfl

theorem cell21_1966593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 6].length) (baseStart_1966593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966593 prefixEnd_1966593 := by exact prefixLift 1966593
  have htrace : WordTrace (prefixWord ++ tailWord_1966593) baseStart_1966593 baseEnd_1966593 := by
    simpa [prefixWord, tailWord_1966593, baseEnd_1966593] using wordTrace_append hprefix tailTrace_1966593
  have hstable : (prefixWord ++ tailWord_1966593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966593).length < 2 ^ (prefixWord ++ tailWord_1966593).sum := by decide
  have hdescent : baseEnd_1966593 < baseStart_1966593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966655 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 4]
def baseStart_1966655 : Nat := 118140960795 + 1966655 * 2 ^ 59
def prefixEnd_1966655 : Nat := 4983230072969 + 3 ^ 40 * 1966655 * 2
def baseEnd_1966655 : Nat := 448817465141381416430233

theorem tailTrace_1966655 : CollatzResearch.WordTrace tailWord_1966655 prefixEnd_1966655 448817465141381416430233 := by
  unfold tailWord_1966655
  simp only [CollatzResearch.WordTrace]
  refine ⟨71729800690152287778501419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47819867126768191852334279 71729800690152287778501419)
  ·
    refine ⟨107594701035228431667752129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71729800690152287778501419 107594701035228431667752129)
    ·
      refine ⟨80696025776421323750814097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107594701035228431667752129 80696025776421323750814097)
      ·
        refine ⟨60522019332315992813110573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80696025776421323750814097 60522019332315992813110573)
        ·
          refine ⟨22695757249618497304916465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60522019332315992813110573 22695757249618497304916465)
          ·
            refine ⟨17021817937213872978687349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22695757249618497304916465 17021817937213872978687349)
            ·
              refine ⟨1595795431613800591751939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17021817937213872978687349 1595795431613800591751939)
              ·
                refine ⟨2393693147420700887627909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595795431613800591751939 2393693147420700887627909)
                ·
                  refine ⟨448817465141381416430233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393693147420700887627909 448817465141381416430233)
                  ·
                    rfl

theorem cell21_1966655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4].length) (baseStart_1966655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966655 prefixEnd_1966655 := by exact prefixLift 1966655
  have htrace : WordTrace (prefixWord ++ tailWord_1966655) baseStart_1966655 baseEnd_1966655 := by
    simpa [prefixWord, tailWord_1966655, baseEnd_1966655] using wordTrace_append hprefix tailTrace_1966655
  have hstable : (prefixWord ++ tailWord_1966655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966655).length < 2 ^ (prefixWord ++ tailWord_1966655).sum := by decide
  have hdescent : baseEnd_1966655 < baseStart_1966655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966700 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_1966700 : Nat := 118140960795 + 1966700 * 2 ^ 59
def prefixEnd_1966700 : Nat := 4983230072969 + 3 ^ 40 * 1966700 * 2
def baseEnd_1966700 : Nat := 448827734754471338180141

theorem tailTrace_1966700 : CollatzResearch.WordTrace tailWord_1966700 prefixEnd_1966700 448827734754471338180141 := by
  unfold tailWord_1966700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35865720987494630231944777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47820961316659506975926369 35865720987494630231944777)
  ·
    refine ⟨26899290740620972673958583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35865720987494630231944777 26899290740620972673958583)
    ·
      refine ⟨40348936110931459010937875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26899290740620972673958583 40348936110931459010937875)
      ·
        refine ⟨60523404166397188516406813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40348936110931459010937875 60523404166397188516406813)
        ·
          refine ⟨22696276562398945693652555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60523404166397188516406813 22696276562398945693652555)
          ·
            refine ⟨34044414843598418540478833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22696276562398945693652555 34044414843598418540478833)
            ·
              refine ⟨25533311132698813905359125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34044414843598418540478833 25533311132698813905359125)
              ·
                refine ⟨1196873959345256901813709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25533311132698813905359125 1196873959345256901813709)
                ·
                  refine ⟨448827734754471338180141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196873959345256901813709 448827734754471338180141)
                  ·
                    rfl

theorem cell21_1966700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_1966700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966700 prefixEnd_1966700 := by exact prefixLift 1966700
  have htrace : WordTrace (prefixWord ++ tailWord_1966700) baseStart_1966700 baseEnd_1966700 := by
    simpa [prefixWord, tailWord_1966700, baseEnd_1966700] using wordTrace_append hprefix tailTrace_1966700
  have hstable : (prefixWord ++ tailWord_1966700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966700).length < 2 ^ (prefixWord ++ tailWord_1966700).sum := by decide
  have hdescent : baseEnd_1966700 < baseStart_1966700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966807 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 4]
def baseStart_1966807 : Nat := 118140960795 + 1966807 * 2 ^ 59
def prefixEnd_1966807 : Nat := 4983230072969 + 3 ^ 40 * 1966807 * 2
def baseEnd_1966807 : Nat := 448852153612262929896589

theorem tailTrace_1966807 : CollatzResearch.WordTrace tailWord_1966807 prefixEnd_1966807 448852153612262929896589 := by
  unfold tailWord_1966807
  simp only [CollatzResearch.WordTrace]
  refine ⟨71735344585601617738034675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47823563057067745158689783 71735344585601617738034675)
  ·
    refine ⟨107603016878402426607052013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71735344585601617738034675 107603016878402426607052013)
    ·
      refine ⟨40351131329400909977644505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107603016878402426607052013 40351131329400909977644505)
      ·
        refine ⟨30263348497050682483233379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40351131329400909977644505 30263348497050682483233379)
        ·
          refine ⟨45395022745576023724850069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30263348497050682483233379 45395022745576023724850069)
          ·
            refine ⟨2127891691198876112102347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45395022745576023724850069 2127891691198876112102347)
            ·
              refine ⟨3191837536798314168153521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127891691198876112102347 3191837536798314168153521)
              ·
                refine ⟨2393878152598735626115141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191837536798314168153521 2393878152598735626115141)
                ·
                  refine ⟨448852153612262929896589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393878152598735626115141 448852153612262929896589)
                  ·
                    rfl

theorem cell21_1966807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_1966807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966807 prefixEnd_1966807 := by exact prefixLift 1966807
  have htrace : WordTrace (prefixWord ++ tailWord_1966807) baseStart_1966807 baseEnd_1966807 := by
    simpa [prefixWord, tailWord_1966807, baseEnd_1966807] using wordTrace_append hprefix tailTrace_1966807
  have hstable : (prefixWord ++ tailWord_1966807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966807).length < 2 ^ (prefixWord ++ tailWord_1966807).sum := by decide
  have hdescent : baseEnd_1966807 < baseStart_1966807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966824 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_1966824 : Nat := 118140960795 + 1966824 * 2 ^ 59
def prefixEnd_1966824 : Nat := 4983230072969 + 3 ^ 40 * 1966824 * 2
def baseEnd_1966824 : Nat := 448856033243874678113221

theorem tailTrace_1966824 : CollatzResearch.WordTrace tailWord_1966824 prefixEnd_1966824 448856033243874678113221 := by
  unfold tailWord_1966824
  simp only [CollatzResearch.WordTrace]
  refine ⟨35867982313270014820701763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47823976417693353094269017 35867982313270014820701763)
  ·
    refine ⟨53801973469905022231052645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35867982313270014820701763 53801973469905022231052645)
    ·
      refine ⟨10087870025607191668322371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53801973469905022231052645 10087870025607191668322371)
      ·
        refine ⟨15131805038410787502483557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10087870025607191668322371 15131805038410787502483557)
        ·
          refine ⟨2837213444702022656715667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15131805038410787502483557 2837213444702022656715667)
          ·
            refine ⟨4255820167053033985073501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837213444702022656715667 4255820167053033985073501)
            ·
              refine ⟨1595932562644887744402563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4255820167053033985073501 1595932562644887744402563)
              ·
                refine ⟨2393898843967331616603845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595932562644887744402563 2393898843967331616603845)
                ·
                  refine ⟨448856033243874678113221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2393898843967331616603845 448856033243874678113221)
                  ·
                    rfl

theorem cell21_1966824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_1966824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966824 prefixEnd_1966824 := by exact prefixLift 1966824
  have htrace : WordTrace (prefixWord ++ tailWord_1966824) baseStart_1966824 baseEnd_1966824 := by
    simpa [prefixWord, tailWord_1966824, baseEnd_1966824] using wordTrace_append hprefix tailTrace_1966824
  have hstable : (prefixWord ++ tailWord_1966824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966824).length < 2 ^ (prefixWord ++ tailWord_1966824).sum := by decide
  have hdescent : baseEnd_1966824 < baseStart_1966824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966869 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 3]
def baseStart_1966869 : Nat := 118140960795 + 1966869 * 2 ^ 59
def prefixEnd_1966869 : Nat := 4983230072969 + 3 ^ 40 * 1966869 * 2
def baseEnd_1966869 : Nat := 448866302856964599863129

theorem tailTrace_1966869 : CollatzResearch.WordTrace tailWord_1966869 prefixEnd_1966869 448866302856964599863129 := by
  unfold tailWord_1966869
  simp only [CollatzResearch.WordTrace]
  refine ⟨71737605911377002326791661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47825070607584668217861107 71737605911377002326791661)
  ·
    refine ⟨26901602216766375872546873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71737605911377002326791661 26901602216766375872546873)
    ·
      refine ⟨20176201662574781904410155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26901602216766375872546873 20176201662574781904410155)
      ·
        refine ⟨30264302493862172856615233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20176201662574781904410155 30264302493862172856615233)
        ·
          refine ⟨22698226870396629642461425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30264302493862172856615233 22698226870396629642461425)
          ·
            refine ⟨17023670152797472231846069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22698226870396629642461425 17023670152797472231846069)
            ·
              refine ⟨1595969076824763021735569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17023670152797472231846069 1595969076824763021735569)
              ·
                refine ⟨1196976807618572266301677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595969076824763021735569 1196976807618572266301677)
                ·
                  refine ⟨448866302856964599863129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1196976807618572266301677 448866302856964599863129)
                  ·
                    rfl

theorem cell21_1966869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_1966869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966869 prefixEnd_1966869 := by exact prefixLift 1966869
  have htrace : WordTrace (prefixWord ++ tailWord_1966869) baseStart_1966869 baseEnd_1966869 := by
    simpa [prefixWord, tailWord_1966869, baseEnd_1966869] using wordTrace_append hprefix tailTrace_1966869
  have hstable : (prefixWord ++ tailWord_1966869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966869).length < 2 ^ (prefixWord ++ tailWord_1966869).sum := by decide
  have hdescent : baseEnd_1966869 < baseStart_1966869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966880 : List Nat := [2, 1, 1, 5, 1, 2, 1, 8]
def baseStart_1966880 : Nat := 118140960795 + 1966880 * 2 ^ 59
def prefixEnd_1966880 : Nat := 4983230072969 + 3 ^ 40 * 1966880 * 2
def baseEnd_1966880 : Nat := 149622937735610341726591

theorem tailTrace_1966880 : CollatzResearch.WordTrace tailWord_1966880 prefixEnd_1966880 149622937735610341726591 := by
  unfold tailWord_1966880
  simp only [CollatzResearch.WordTrace]
  refine ⟨35869003557168575602721047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47825338076224767470294729 35869003557168575602721047)
  ·
    refine ⟨53803505335752863404081571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35869003557168575602721047 53803505335752863404081571)
    ·
      refine ⟨80705258003629295106122357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53803505335752863404081571 80705258003629295106122357)
      ·
        refine ⟨7566117937840246416198971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80705258003629295106122357 7566117937840246416198971)
        ·
          refine ⟨11349176906760369624298457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566117937840246416198971 11349176906760369624298457)
          ·
            refine ⟨8511882680070277218223843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11349176906760369624298457 8511882680070277218223843)
            ·
              refine ⟨12767824020105415827335765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8511882680070277218223843 12767824020105415827335765)
              ·
                refine ⟨149622937735610341726591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12767824020105415827335765 149622937735610341726591)
                ·
                  rfl

theorem cell21_1966880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_1966880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966880 prefixEnd_1966880 := by exact prefixLift 1966880
  have htrace : WordTrace (prefixWord ++ tailWord_1966880) baseStart_1966880 baseEnd_1966880 := by
    simpa [prefixWord, tailWord_1966880, baseEnd_1966880] using wordTrace_append hprefix tailTrace_1966880
  have hstable : (prefixWord ++ tailWord_1966880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966880).length < 2 ^ (prefixWord ++ tailWord_1966880).sum := by decide
  have hdescent : baseEnd_1966880 < baseStart_1966880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966970 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1966970 : Nat := 118140960795 + 1966970 * 2 ^ 59
def prefixEnd_1966970 : Nat := 4983230072969 + 3 ^ 40 * 1966970 * 2
def baseEnd_1966970 : Nat := 448889352433010868679589

theorem tailTrace_1966970 : CollatzResearch.WordTrace tailWord_1966970 prefixEnd_1966970 448889352433010868679589 := by
  unfold tailWord_1966970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17935322421002774144054591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47827526456007397717478909 17935322421002774144054591)
  ·
    refine ⟨26902983631504161216081887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17935322421002774144054591 26902983631504161216081887)
    ·
      refine ⟨40354475447256241824122831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902983631504161216081887 40354475447256241824122831)
      ·
        refine ⟨60531713170884362736184247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40354475447256241824122831 60531713170884362736184247)
        ·
          refine ⟨90797569756326544104276371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60531713170884362736184247 90797569756326544104276371)
          ·
            refine ⟨136196354634489816156414557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90797569756326544104276371 136196354634489816156414557)
            ·
              refine ⟨51073632987933681058655459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136196354634489816156414557 51073632987933681058655459)
              ·
                refine ⟨76610449481900521587983189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51073632987933681058655459 76610449481900521587983189)
                ·
                  refine ⟨448889352433010868679589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76610449481900521587983189 448889352433010868679589)
                  ·
                    rfl

theorem cell21_1966970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1966970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1966970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1966970 prefixEnd_1966970 := by exact prefixLift 1966970
  have htrace : WordTrace (prefixWord ++ tailWord_1966970) baseStart_1966970 baseEnd_1966970 := by
    simpa [prefixWord, tailWord_1966970, baseEnd_1966970] using wordTrace_append hprefix tailTrace_1966970
  have hstable : (prefixWord ++ tailWord_1966970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966970).length < 2 ^ (prefixWord ++ tailWord_1966970).sum := by decide
  have hdescent : baseEnd_1966970 < baseStart_1966970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967032 : List Nat := [2, 1, 2, 1, 2, 6, 7]
def baseStart_1967032 : Nat := 118140960795 + 1967032 * 2 ^ 59
def prefixEnd_1967032 : Nat := 4983230072969 + 3 ^ 40 * 1967032 * 2
def baseEnd_1967032 : Nat := 49878166853079170960681

theorem tailTrace_1967032 : CollatzResearch.WordTrace tailWord_1967032 prefixEnd_1967032 49878166853079170960681 := by
  unfold tailWord_1967032
  simp only [CollatzResearch.WordTrace]
  refine ⟨35871775504893240582487675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47829034006524320776650233 35871775504893240582487675)
  ·
    refine ⟨53807663257339860873731513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35871775504893240582487675 53807663257339860873731513)
    ·
      refine ⟨40355747443004895655298635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53807663257339860873731513 40355747443004895655298635)
      ·
        refine ⟨60533621164507343482947953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40355747443004895655298635 60533621164507343482947953)
        ·
          refine ⟨45400215873380507612210965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60533621164507343482947953 45400215873380507612210965)
          ·
            refine ⟨2128135119064711294322389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45400215873380507612210965 2128135119064711294322389)
            ·
              refine ⟨49878166853079170960681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2128135119064711294322389 49878166853079170960681)
              ·
                rfl

theorem cell21_1967032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 7].length) (baseStart_1967032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967032 prefixEnd_1967032 := by exact prefixLift 1967032
  have htrace : WordTrace (prefixWord ++ tailWord_1967032) baseStart_1967032 baseEnd_1967032 := by
    simpa [prefixWord, tailWord_1967032, baseEnd_1967032] using wordTrace_append hprefix tailTrace_1967032
  have hstable : (prefixWord ++ tailWord_1967032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967032).length < 2 ^ (prefixWord ++ tailWord_1967032).sum := by decide
  have hdescent : baseEnd_1967032 < baseStart_1967032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967125 : List Nat := [1, 3, 2, 1, 4, 2, 3, 5]
def baseStart_1967125 : Nat := 118140960795 + 1967125 * 2 ^ 59
def prefixEnd_1967125 : Nat := 4983230072969 + 3 ^ 40 * 1967125 * 2
def baseEnd_1967125 : Nat := 149641575181588347865313

theorem tailTrace_1967125 : CollatzResearch.WordTrace tailWord_1967125 prefixEnd_1967125 149641575181588347865313 := by
  unfold tailWord_1967125
  simp only [CollatzResearch.WordTrace]
  refine ⟨71746942998449558048110829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47831295332299705365407219 71746942998449558048110829)
  ·
    refine ⟨26905103624418584268041561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71746942998449558048110829 26905103624418584268041561)
    ·
      refine ⟨20178827718313938201031171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26905103624418584268041561 20178827718313938201031171)
      ·
        refine ⟨30268241577470907301546757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20178827718313938201031171 30268241577470907301546757)
        ·
          refine ⟨5675295295775795119040017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30268241577470907301546757 5675295295775795119040017)
          ·
            refine ⟨4256471471831846339280013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675295295775795119040017 4256471471831846339280013)
            ·
              refine ⟨1596176801936942377230005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256471471831846339280013 1596176801936942377230005)
              ·
                refine ⟨149641575181588347865313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1596176801936942377230005 149641575181588347865313)
                ·
                  rfl

theorem cell21_1967125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 5].length) (baseStart_1967125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967125 prefixEnd_1967125 := by exact prefixLift 1967125
  have htrace : WordTrace (prefixWord ++ tailWord_1967125) baseStart_1967125 baseEnd_1967125 := by
    simpa [prefixWord, tailWord_1967125, baseEnd_1967125] using wordTrace_append hprefix tailTrace_1967125
  have hstable : (prefixWord ++ tailWord_1967125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967125).length < 2 ^ (prefixWord ++ tailWord_1967125).sum := by decide
  have hdescent : baseEnd_1967125 < baseStart_1967125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967153 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_1967153 : Nat := 118140960795 + 1967153 * 2 ^ 59
def prefixEnd_1967153 : Nat := 4983230072969 + 3 ^ 40 * 1967153 * 2
def baseEnd_1967153 : Nat := 448931115526243217129215

theorem tailTrace_1967153 : CollatzResearch.WordTrace tailWord_1967153 prefixEnd_1967153 448931115526243217129215 := by
  unfold tailWord_1967153
  simp only [CollatzResearch.WordTrace]
  refine ⟨71747964242348118830130113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47831976161565412553420075 71747964242348118830130113)
  ·
    refine ⟨53810973181761089122597585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71747964242348118830130113 53810973181761089122597585)
    ·
      refine ⟨40358229886320816841948189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53810973181761089122597585 40358229886320816841948189)
      ·
        refine ⟨15134336207370306315730571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40358229886320816841948189 15134336207370306315730571)
        ·
          refine ⟨22701504311055459473595857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134336207370306315730571 22701504311055459473595857)
          ·
            refine ⟨17026128233291594605196893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22701504311055459473595857 17026128233291594605196893)
            ·
              refine ⟨6384798087484347976948835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17026128233291594605196893 6384798087484347976948835)
              ·
                refine ⟨9577197131226521965423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6384798087484347976948835 9577197131226521965423253)
                ·
                  refine ⟨448931115526243217129215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9577197131226521965423253 448931115526243217129215)
                  ·
                    rfl

theorem cell21_1967153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_1967153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967153 prefixEnd_1967153 := by exact prefixLift 1967153
  have htrace : WordTrace (prefixWord ++ tailWord_1967153) baseStart_1967153 baseEnd_1967153 := by
    simpa [prefixWord, tailWord_1967153, baseEnd_1967153] using wordTrace_append hprefix tailTrace_1967153
  have hstable : (prefixWord ++ tailWord_1967153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967153).length < 2 ^ (prefixWord ++ tailWord_1967153).sum := by decide
  have hdescent : baseEnd_1967153 < baseStart_1967153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967156 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1967156 : Nat := 118140960795 + 1967156 * 2 ^ 59
def prefixEnd_1967156 : Nat := 4983230072969 + 3 ^ 40 * 1967156 * 2
def baseEnd_1967156 : Nat := 448931800167115878579209

theorem tailTrace_1967156 : CollatzResearch.WordTrace tailWord_1967156 prefixEnd_1967156 448931800167115878579209 := by
  unfold tailWord_1967156
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874036830668625171244661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47832049107558166894992881 35874036830668625171244661)
  ·
    refine ⟨3363190952875183609804187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35874036830668625171244661 3363190952875183609804187)
    ·
      refine ⟨5044786429312775414706281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363190952875183609804187 5044786429312775414706281)
      ·
        refine ⟨3783589821984581561029711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5044786429312775414706281 3783589821984581561029711)
        ·
          refine ⟨5675384732976872341544567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783589821984581561029711 5675384732976872341544567)
          ·
            refine ⟨8513077099465308512316851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675384732976872341544567 8513077099465308512316851)
            ·
              refine ⟨12769615649197962768475277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513077099465308512316851 12769615649197962768475277)
              ·
                refine ⟨4788605868449236038178229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12769615649197962768475277 4788605868449236038178229)
                ·
                  refine ⟨448931800167115878579209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4788605868449236038178229 448931800167115878579209)
                  ·
                    rfl

theorem cell21_1967156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1967156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967156 prefixEnd_1967156 := by exact prefixLift 1967156
  have htrace : WordTrace (prefixWord ++ tailWord_1967156) baseStart_1967156 baseEnd_1967156 := by
    simpa [prefixWord, tailWord_1967156, baseEnd_1967156] using wordTrace_append hprefix tailTrace_1967156
  have hstable : (prefixWord ++ tailWord_1967156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967156).length < 2 ^ (prefixWord ++ tailWord_1967156).sum := by decide
  have hdescent : baseEnd_1967156 < baseStart_1967156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967167 : List Nat := [1, 1, 2, 2, 3, 1, 1, 10]
def baseStart_1967167 : Nat := 118140960795 + 1967167 * 2 ^ 59
def prefixEnd_1967167 : Nat := 4983230072969 + 3 ^ 40 * 1967167 * 2
def baseEnd_1967167 : Nat := 149644770172327434631951

theorem tailTrace_1967167 : CollatzResearch.WordTrace tailWord_1967167 prefixEnd_1967167 149644770172327434631951 := by
  unfold tailWord_1967167
  simp only [CollatzResearch.WordTrace]
  refine ⟨71748474864297399221139755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47832316576198266147426503 71748474864297399221139755)
  ·
    refine ⟨107622712296446098831709633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71748474864297399221139755 107622712296446098831709633)
    ·
      refine ⟨80717034222334574123782225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107622712296446098831709633 80717034222334574123782225)
      ·
        refine ⟨60537775666750930592836669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80717034222334574123782225 60537775666750930592836669)
        ·
          refine ⟨22701665875031598972313751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60537775666750930592836669 22701665875031598972313751)
          ·
            refine ⟨34052498812547398458470627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22701665875031598972313751 34052498812547398458470627)
            ·
              refine ⟨51078748218821097687705941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34052498812547398458470627 51078748218821097687705941)
              ·
                refine ⟨149644770172327434631951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51078748218821097687705941 149644770172327434631951)
                ·
                  rfl

theorem cell21_1967167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_1967167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967167 prefixEnd_1967167 := by exact prefixLift 1967167
  have htrace : WordTrace (prefixWord ++ tailWord_1967167) baseStart_1967167 baseEnd_1967167 := by
    simpa [prefixWord, tailWord_1967167, baseEnd_1967167] using wordTrace_append hprefix tailTrace_1967167
  have hstable : (prefixWord ++ tailWord_1967167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967167).length < 2 ^ (prefixWord ++ tailWord_1967167).sum := by decide
  have hdescent : baseEnd_1967167 < baseStart_1967167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967221 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 4]
def baseStart_1967221 : Nat := 118140960795 + 1967221 * 2 ^ 59
def prefixEnd_1967221 : Nat := 4983230072969 + 3 ^ 40 * 1967221 * 2
def baseEnd_1967221 : Nat := 448946634052690209995743

theorem tailTrace_1967221 : CollatzResearch.WordTrace tailWord_1967221 prefixEnd_1967221 448946634052690209995743 := by
  unfold tailWord_1967221
  simp only [CollatzResearch.WordTrace]
  refine ⟨71750444406101766443605517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47833629604067844295737011 71750444406101766443605517)
  ·
    refine ⟨26906416652288162416352069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71750444406101766443605517 26906416652288162416352069)
    ·
      refine ⟨5044953122304030453066013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26906416652288162416352069 5044953122304030453066013)
      ·
        refine ⟨1891857420864011419899755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5044953122304030453066013 1891857420864011419899755)
        ·
          refine ⟨2837786131296017129849633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891857420864011419899755 2837786131296017129849633)
          ·
            refine ⟨2128339598472012847387225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2837786131296017129849633 2128339598472012847387225)
            ·
              refine ⟨1596254698854009635540419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128339598472012847387225 1596254698854009635540419)
              ·
                refine ⟨2394382048281014453310629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596254698854009635540419 2394382048281014453310629)
                ·
                  refine ⟨448946634052690209995743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394382048281014453310629 448946634052690209995743)
                  ·
                    rfl

theorem cell21_1967221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_1967221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967221 prefixEnd_1967221 := by exact prefixLift 1967221
  have htrace : WordTrace (prefixWord ++ tailWord_1967221) baseStart_1967221 baseEnd_1967221 := by
    simpa [prefixWord, tailWord_1967221, baseEnd_1967221] using wordTrace_append hprefix tailTrace_1967221
  have hstable : (prefixWord ++ tailWord_1967221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967221).length < 2 ^ (prefixWord ++ tailWord_1967221).sum := by decide
  have hdescent : baseEnd_1967221 < baseStart_1967221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967263 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_1967263 : Nat := 118140960795 + 1967263 * 2 ^ 59
def prefixEnd_1967263 : Nat := 4983230072969 + 3 ^ 40 * 1967263 * 2
def baseEnd_1967263 : Nat := 448956219024907470295657

theorem tailTrace_1967263 : CollatzResearch.WordTrace tailWord_1967263 prefixEnd_1967263 448956219024907470295657 := by
  unfold tailWord_1967263
  simp only [CollatzResearch.WordTrace]
  refine ⟨71751976271949607616634443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47834650847966405077756295 71751976271949607616634443)
  ·
    refine ⟨107627964407924411424951665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71751976271949607616634443 107627964407924411424951665)
    ·
      refine ⟨80720973305943308568713749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107627964407924411424951665 80720973305943308568713749)
      ·
        refine ⟨3783795623716092589158457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80720973305943308568713749 3783795623716092589158457)
        ·
          refine ⟨2837846717787069441868843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3783795623716092589158457 2837846717787069441868843)
          ·
            refine ⟨4256770076680604162803265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837846717787069441868843 4256770076680604162803265)
            ·
              refine ⟨3192577557510453122102449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256770076680604162803265 3192577557510453122102449)
              ·
                refine ⟨2394433168132839841576837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192577557510453122102449 2394433168132839841576837)
                ·
                  refine ⟨448956219024907470295657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394433168132839841576837 448956219024907470295657)
                  ·
                    rfl

theorem cell21_1967263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_1967263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967263 prefixEnd_1967263 := by exact prefixLift 1967263
  have htrace : WordTrace (prefixWord ++ tailWord_1967263) baseStart_1967263 baseEnd_1967263 := by
    simpa [prefixWord, tailWord_1967263, baseEnd_1967263] using wordTrace_append hprefix tailTrace_1967263
  have hstable : (prefixWord ++ tailWord_1967263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967263).length < 2 ^ (prefixWord ++ tailWord_1967263).sum := by decide
  have hdescent : baseEnd_1967263 < baseStart_1967263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967381 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1967381 : Nat := 118140960795 + 1967381 * 2 ^ 59
def prefixEnd_1967381 : Nat := 4983230072969 + 3 ^ 40 * 1967381 * 2
def baseEnd_1967381 : Nat := 448983148232565487328749

theorem tailTrace_1967381 : CollatzResearch.WordTrace tailWord_1967381 prefixEnd_1967381 448983148232565487328749 := by
  unfold tailWord_1967381
  simp only [CollatzResearch.WordTrace]
  refine ⟨71756280085522113769429997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47837520057014742512953331 71756280085522113769429997)
  ·
    refine ⟨26908605032070792663536249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71756280085522113769429997 26908605032070792663536249)
    ·
      refine ⟨20181453774053094497652187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26908605032070792663536249 20181453774053094497652187)
      ·
        refine ⟨30272180661079641746478281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20181453774053094497652187 30272180661079641746478281)
        ·
          refine ⟨22704135495809731309858711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30272180661079641746478281 22704135495809731309858711)
          ·
            refine ⟨34056203243714596964788067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22704135495809731309858711 34056203243714596964788067)
            ·
              refine ⟨51084304865571895447182101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34056203243714596964788067 51084304865571895447182101)
              ·
                refine ⟨2394576790573682599086661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51084304865571895447182101 2394576790573682599086661)
                ·
                  refine ⟨448983148232565487328749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394576790573682599086661 448983148232565487328749)
                  ·
                    rfl

theorem cell21_1967381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1967381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967381 prefixEnd_1967381 := by exact prefixLift 1967381
  have htrace : WordTrace (prefixWord ++ tailWord_1967381) baseStart_1967381 baseEnd_1967381 := by
    simpa [prefixWord, tailWord_1967381, baseEnd_1967381] using wordTrace_append hprefix tailTrace_1967381
  have hstable : (prefixWord ++ tailWord_1967381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967381).length < 2 ^ (prefixWord ++ tailWord_1967381).sum := by decide
  have hdescent : baseEnd_1967381 < baseStart_1967381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967390 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1967390 : Nat := 118140960795 + 1967390 * 2 ^ 59
def prefixEnd_1967390 : Nat := 4983230072969 + 3 ^ 40 * 1967390 * 2
def baseEnd_1967390 : Nat := 448985202155183471678731

theorem tailTrace_1967390 : CollatzResearch.WordTrace tailWord_1967390 prefixEnd_1967390 448985202155183471678731 := by
  unfold tailWord_1967390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969576042811188538313453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47837738894993005537671749 8969576042811188538313453)
  ·
    refine ⟨3363591016054195701867545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8969576042811188538313453 3363591016054195701867545)
    ·
      refine ⟨2522693262040646776400659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3363591016054195701867545 2522693262040646776400659)
      ·
        refine ⟨3784039893060970164600989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522693262040646776400659 3784039893060970164600989)
        ·
          refine ⟨1419014959897863811725371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3784039893060970164600989 1419014959897863811725371)
          ·
            refine ⟨2128522439846795717588057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419014959897863811725371 2128522439846795717588057)
            ·
              refine ⟨1596391829885096788191043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128522439846795717588057 1596391829885096788191043)
              ·
                refine ⟨2394587744827645182286565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596391829885096788191043 2394587744827645182286565)
                ·
                  refine ⟨448985202155183471678731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2394587744827645182286565 448985202155183471678731)
                  ·
                    rfl

theorem cell21_1967390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1967390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967390 prefixEnd_1967390 := by exact prefixLift 1967390
  have htrace : WordTrace (prefixWord ++ tailWord_1967390) baseStart_1967390 baseEnd_1967390 := by
    simpa [prefixWord, tailWord_1967390, baseEnd_1967390] using wordTrace_append hprefix tailTrace_1967390
  have hstable : (prefixWord ++ tailWord_1967390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967390).length < 2 ^ (prefixWord ++ tailWord_1967390).sum := by decide
  have hdescent : baseEnd_1967390 < baseStart_1967390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967395 : List Nat := [1, 1, 1, 4, 2, 3, 1, 8]
def baseStart_1967395 : Nat := 118140960795 + 1967395 * 2 ^ 59
def prefixEnd_1967395 : Nat := 4983230072969 + 3 ^ 40 * 1967395 * 2
def baseEnd_1967395 : Nat := 149662114407768191365129

theorem tailTrace_1967395 : CollatzResearch.WordTrace tailWord_1967395 prefixEnd_1967395 149662114407768191365129 := by
  unfold tailWord_1967395
  simp only [CollatzResearch.WordTrace]
  refine ⟨71756790707471394160439639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47837860471647596106959759 71756790707471394160439639)
  ·
    refine ⟨107635186061207091240659459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71756790707471394160439639 107635186061207091240659459)
    ·
      refine ⟨161452779091810636860989189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107635186061207091240659459 161452779091810636860989189)
      ·
        refine ⟨30272396079714494411435473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161452779091810636860989189 30272396079714494411435473)
        ·
          refine ⟨22704297059785870808576605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30272396079714494411435473 22704297059785870808576605)
          ·
            refine ⟨8514111397419701553216227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22704297059785870808576605 8514111397419701553216227)
            ·
              refine ⟨12771167096129552329824341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8514111397419701553216227 12771167096129552329824341)
              ·
                refine ⟨149662114407768191365129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12771167096129552329824341 149662114407768191365129)
                ·
                  rfl

theorem cell21_1967395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_1967395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967395 prefixEnd_1967395 := by exact prefixLift 1967395
  have htrace : WordTrace (prefixWord ++ tailWord_1967395) baseStart_1967395 baseEnd_1967395 := by
    simpa [prefixWord, tailWord_1967395, baseEnd_1967395] using wordTrace_append hprefix tailTrace_1967395
  have hstable : (prefixWord ++ tailWord_1967395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967395).length < 2 ^ (prefixWord ++ tailWord_1967395).sum := by decide
  have hdescent : baseEnd_1967395 < baseStart_1967395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967412 : List Nat := [2, 5, 1, 1, 1, 1, 1, 9]
def baseStart_1967412 : Nat := 118140960795 + 1967412 * 2 ^ 59
def prefixEnd_1967412 : Nat := 4983230072969 + 3 ^ 40 * 1967412 * 2
def baseEnd_1967412 : Nat := 149663407618305440770673

theorem tailTrace_1967412 : CollatzResearch.WordTrace tailWord_1967412 prefixEnd_1967412 149663407618305440770673 := by
  unfold tailWord_1967412
  simp only [CollatzResearch.WordTrace]
  refine ⟨35878705374204903031904245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47838273832273204042538993 35878705374204903031904245)
  ·
    refine ⟨3363628628831709659241023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35878705374204903031904245 3363628628831709659241023)
    ·
      refine ⟨5045442943247564488861535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363628628831709659241023 5045442943247564488861535)
      ·
        refine ⟨7568164414871346733292303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045442943247564488861535 7568164414871346733292303)
        ·
          refine ⟨11352246622307020099938455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7568164414871346733292303 11352246622307020099938455)
          ·
            refine ⟨17028369933460530149907683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11352246622307020099938455 17028369933460530149907683)
            ·
              refine ⟨25542554900190795224861525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17028369933460530149907683 25542554900190795224861525)
              ·
                refine ⟨149663407618305440770673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25542554900190795224861525 149663407618305440770673)
                ·
                  rfl

theorem cell21_1967412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_1967412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967412 prefixEnd_1967412 := by exact prefixLift 1967412
  have htrace : WordTrace (prefixWord ++ tailWord_1967412) baseStart_1967412 baseEnd_1967412 := by
    simpa [prefixWord, tailWord_1967412, baseEnd_1967412] using wordTrace_append hprefix tailTrace_1967412
  have hstable : (prefixWord ++ tailWord_1967412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967412).length < 2 ^ (prefixWord ++ tailWord_1967412).sum := by decide
  have hdescent : baseEnd_1967412 < baseStart_1967412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967443 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 3]
def baseStart_1967443 : Nat := 118140960795 + 1967443 * 2 ^ 59
def prefixEnd_1967443 : Nat := 4983230072969 + 3 ^ 40 * 1967443 * 2
def baseEnd_1967443 : Nat := 448997297477267157295289

theorem tailTrace_1967443 : CollatzResearch.WordTrace tailWord_1967443 prefixEnd_1967443 448997297477267157295289 := by
  unfold tailWord_1967443
  simp only [CollatzResearch.WordTrace]
  refine ⟨71758541411297498358186983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47839027607531665572124655 71758541411297498358186983)
  ·
    refine ⟨107637812116946247537280475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71758541411297498358186983 107637812116946247537280475)
    ·
      refine ⟨161456718175419371305920713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107637812116946247537280475 161456718175419371305920713)
      ·
        refine ⟨121092538631564528479440535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161456718175419371305920713 121092538631564528479440535)
        ·
          refine ⟨181638807947346792719160803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121092538631564528479440535 181638807947346792719160803)
          ·
            refine ⟨272458211921020189078741205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181638807947346792719160803 272458211921020189078741205)
            ·
              refine ⟨6385739341898910681532997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 272458211921020189078741205 6385739341898910681532997)
              ·
                refine ⟨1197326126606045752787437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6385739341898910681532997 1197326126606045752787437)
                ·
                  refine ⟨448997297477267157295289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197326126606045752787437 448997297477267157295289)
                  ·
                    rfl

theorem cell21_1967443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3].length) (baseStart_1967443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967443 prefixEnd_1967443 := by exact prefixLift 1967443
  have htrace : WordTrace (prefixWord ++ tailWord_1967443) baseStart_1967443 baseEnd_1967443 := by
    simpa [prefixWord, tailWord_1967443, baseEnd_1967443] using wordTrace_append hprefix tailTrace_1967443
  have hstable : (prefixWord ++ tailWord_1967443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967443).length < 2 ^ (prefixWord ++ tailWord_1967443).sum := by decide
  have hdescent : baseEnd_1967443 < baseStart_1967443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967477 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 3]
def baseStart_1967477 : Nat := 118140960795 + 1967477 * 2 ^ 59
def prefixEnd_1967477 : Nat := 4983230072969 + 3 ^ 40 * 1967477 * 2
def baseEnd_1967477 : Nat := 449005056740490653728553

theorem tailTrace_1967477 : CollatzResearch.WordTrace tailWord_1967477 prefixEnd_1967477 449005056740490653728553 := by
  unfold tailWord_1967477
  simp only [CollatzResearch.WordTrace]
  refine ⟨71759781493174322164924685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47839854328782881443283123 71759781493174322164924685)
  ·
    refine ⟨26909918059940370811846757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71759781493174322164924685 26909918059940370811846757)
    ·
      refine ⟨5045609636238819527221267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26909918059940370811846757 5045609636238819527221267)
      ·
        refine ⟨7568414454358229290831901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045609636238819527221267 7568414454358229290831901)
        ·
          refine ⟨2838155420384335984061963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7568414454358229290831901 2838155420384335984061963)
          ·
            refine ⟨4257233130576503976092945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838155420384335984061963 4257233130576503976092945)
            ·
              refine ⟨3192924847932377982069709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257233130576503976092945 3192924847932377982069709)
              ·
                refine ⟨1197346817974641743276141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3192924847932377982069709 1197346817974641743276141)
                ·
                  refine ⟨449005056740490653728553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197346817974641743276141 449005056740490653728553)
                  ·
                    rfl

theorem cell21_1967477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_1967477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967477 prefixEnd_1967477 := by exact prefixLift 1967477
  have htrace : WordTrace (prefixWord ++ tailWord_1967477) baseStart_1967477 baseEnd_1967477 := by
    simpa [prefixWord, tailWord_1967477, baseEnd_1967477] using wordTrace_append hprefix tailTrace_1967477
  have hstable : (prefixWord ++ tailWord_1967477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967477).length < 2 ^ (prefixWord ++ tailWord_1967477).sum := by decide
  have hdescent : baseEnd_1967477 < baseStart_1967477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967564 : List Nat := [2, 2, 1, 4, 2, 2, 2, 6]
def baseStart_1967564 : Nat := 118140960795 + 1967564 * 2 ^ 59
def prefixEnd_1967564 : Nat := 4983230072969 + 3 ^ 40 * 1967564 * 2
def baseEnd_1967564 : Nat := 149674970441932611926125

theorem tailTrace_1967564 : CollatzResearch.WordTrace tailWord_1967564 prefixEnd_1967564 149674970441932611926125 := by
  unfold tailWord_1967564
  simp only [CollatzResearch.WordTrace]
  refine ⟨35881477321929568011670873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47841969762572757348894497 35881477321929568011670873)
  ·
    refine ⟨26911107991447176008753155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35881477321929568011670873 26911107991447176008753155)
    ·
      refine ⟨40366661987170764013129733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26911107991447176008753155 40366661987170764013129733)
      ·
        refine ⟨7568749122594518252461825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40366661987170764013129733 7568749122594518252461825)
        ·
          refine ⟨5676561841945888689346369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7568749122594518252461825 5676561841945888689346369)
          ·
            refine ⟨4257421381459416517009777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676561841945888689346369 4257421381459416517009777)
            ·
              refine ⟨3193066036094562387757333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257421381459416517009777 3193066036094562387757333)
              ·
                refine ⟨149674970441932611926125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3193066036094562387757333 149674970441932611926125)
                ·
                  rfl

theorem cell21_1967564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_1967564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967564 prefixEnd_1967564 := by exact prefixLift 1967564
  have htrace : WordTrace (prefixWord ++ tailWord_1967564) baseStart_1967564 baseEnd_1967564 := by
    simpa [prefixWord, tailWord_1967564, baseEnd_1967564] using wordTrace_append hprefix tailTrace_1967564
  have hstable : (prefixWord ++ tailWord_1967564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967564).length < 2 ^ (prefixWord ++ tailWord_1967564).sum := by decide
  have hdescent : baseEnd_1967564 < baseStart_1967564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967612 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 3]
def baseStart_1967612 : Nat := 118140960795 + 1967612 * 2 ^ 59
def prefixEnd_1967612 : Nat := 4983230072969 + 3 ^ 40 * 1967612 * 2
def baseEnd_1967612 : Nat := 449035865579760418978277

theorem tailTrace_1967612 : CollatzResearch.WordTrace tailWord_1967612 prefixEnd_1967612 449035865579760418978277 := by
  unfold tailWord_1967612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35882352673842620110544545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47843136898456826814059393 35882352673842620110544545)
  ·
    refine ⟨26911764505381965082908409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35882352673842620110544545 26911764505381965082908409)
    ·
      refine ⟨20183823379036473812181307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26911764505381965082908409 20183823379036473812181307)
      ·
        refine ⟨30275735068554710718271961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20183823379036473812181307 30275735068554710718271961)
        ·
          refine ⟨22706801301416033038703971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30275735068554710718271961 22706801301416033038703971)
          ·
            refine ⟨34060201952124049558055957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22706801301416033038703971 34060201952124049558055957)
            ·
              refine ⟨1596571966505814823033873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34060201952124049558055957 1596571966505814823033873)
              ·
                refine ⟨1197428974879361117275405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596571966505814823033873 1197428974879361117275405)
                ·
                  refine ⟨449035865579760418978277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197428974879361117275405 449035865579760418978277)
                  ·
                    rfl

theorem cell21_1967612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_1967612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967612 prefixEnd_1967612 := by exact prefixLift 1967612
  have htrace : WordTrace (prefixWord ++ tailWord_1967612) baseStart_1967612 baseEnd_1967612 := by
    simpa [prefixWord, tailWord_1967612, baseEnd_1967612] using wordTrace_append hprefix tailTrace_1967612
  have hstable : (prefixWord ++ tailWord_1967612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967612).length < 2 ^ (prefixWord ++ tailWord_1967612).sum := by decide
  have hdescent : baseEnd_1967612 < baseStart_1967612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967629 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1967629 : Nat := 118140960795 + 1967629 * 2 ^ 59
def prefixEnd_1967629 : Nat := 4983230072969 + 3 ^ 40 * 1967629 * 2
def baseEnd_1967629 : Nat := 449039745211372167194909

theorem tailTrace_1967629 : CollatzResearch.WordTrace tailWord_1967629 prefixEnd_1967629 449039745211372167194909 := by
  unfold tailWord_1967629
  simp only [CollatzResearch.WordTrace]
  refine ⟨71765325388623652124457941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47843550259082434749638627 71765325388623652124457941)
  ·
    refine ⟨1681999813795866846666983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 71765325388623652124457941 1681999813795866846666983)
    ·
      refine ⟨2522999720693800270000475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681999813795866846666983 2522999720693800270000475)
      ·
        refine ⟨3784499581040700405000713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522999720693800270000475 3784499581040700405000713)
        ·
          refine ⟨2838374685780525303750535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3784499581040700405000713 2838374685780525303750535)
          ·
            refine ⟨4257562028670787955625803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838374685780525303750535 4257562028670787955625803)
            ·
              refine ⟨6386343043006181933438705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257562028670787955625803 6386343043006181933438705)
              ·
                refine ⟨4789757282254636450079029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386343043006181933438705 4789757282254636450079029)
                ·
                  refine ⟨449039745211372167194909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4789757282254636450079029 449039745211372167194909)
                  ·
                    rfl

theorem cell21_1967629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1967629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967629 prefixEnd_1967629 := by exact prefixLift 1967629
  have htrace : WordTrace (prefixWord ++ tailWord_1967629) baseStart_1967629 baseEnd_1967629 := by
    simpa [prefixWord, tailWord_1967629, baseEnd_1967629] using wordTrace_append hprefix tailTrace_1967629
  have hstable : (prefixWord ++ tailWord_1967629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967629).length < 2 ^ (prefixWord ++ tailWord_1967629).sum := by decide
  have hdescent : baseEnd_1967629 < baseStart_1967629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967671 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 3]
def baseStart_1967671 : Nat := 118140960795 + 1967671 * 2 ^ 59
def prefixEnd_1967671 : Nat := 4983230072969 + 3 ^ 40 * 1967671 * 2
def baseEnd_1967671 : Nat := 449049330183589427494823

theorem tailTrace_1967671 : CollatzResearch.WordTrace tailWord_1967671 prefixEnd_1967671 449049330183589427494823 := by
  unfold tailWord_1967671
  simp only [CollatzResearch.WordTrace]
  refine ⟨71766857254471493297486867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47844571502980995531657911 71766857254471493297486867)
  ·
    refine ⟨107650285881707239946230301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71766857254471493297486867 107650285881707239946230301)
    ·
      refine ⟨40368857205640214979836363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107650285881707239946230301 40368857205640214979836363)
      ·
        refine ⟨60553285808460322469754545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40368857205640214979836363 60553285808460322469754545)
        ·
          refine ⟨45414964356345241852315909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60553285808460322469754545 45414964356345241852315909)
          ·
            refine ⟨8515305816814732847309233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45414964356345241852315909 8515305816814732847309233)
            ·
              refine ⟨6386479362611049635481925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515305816814732847309233 6386479362611049635481925)
              ·
                refine ⟨1197464880489571806652861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6386479362611049635481925 1197464880489571806652861)
                ·
                  refine ⟨449049330183589427494823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197464880489571806652861 449049330183589427494823)
                  ·
                    rfl

theorem cell21_1967671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3].length) (baseStart_1967671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967671 prefixEnd_1967671 := by exact prefixLift 1967671
  have htrace : WordTrace (prefixWord ++ tailWord_1967671) baseStart_1967671 baseEnd_1967671 := by
    simpa [prefixWord, tailWord_1967671, baseEnd_1967671] using wordTrace_append hprefix tailTrace_1967671
  have hstable : (prefixWord ++ tailWord_1967671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967671).length < 2 ^ (prefixWord ++ tailWord_1967671).sum := by decide
  have hdescent : baseEnd_1967671 < baseStart_1967671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967775 : List Nat := [1, 1, 2, 7, 10]
def baseStart_1967775 : Nat := 118140960795 + 1967775 * 2 ^ 59
def prefixEnd_1967775 : Nat := 4983230072969 + 3 ^ 40 * 1967775 * 2
def baseEnd_1967775 : Nat := 5544111906179115527917

theorem tailTrace_1967775 : CollatzResearch.WordTrace tailWord_1967775 prefixEnd_1967775 5544111906179115527917 := by
  unfold tailWord_1967775
  simp only [CollatzResearch.WordTrace]
  refine ⟨71770650446094719059272779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47847100297396479372848519 71770650446094719059272779)
  ·
    refine ⟨107655975669142078588909169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71770650446094719059272779 107655975669142078588909169)
    ·
      refine ⟨80741981751856558941681877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107655975669142078588909169 80741981751856558941681877)
      ·
        refine ⟨1892390197309138100195669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80741981751856558941681877 1892390197309138100195669)
        ·
          refine ⟨5544111906179115527917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1892390197309138100195669 5544111906179115527917)
          ·
            rfl

theorem cell21_1967775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 10].length) (baseStart_1967775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967775 prefixEnd_1967775 := by exact prefixLift 1967775
  have htrace : WordTrace (prefixWord ++ tailWord_1967775) baseStart_1967775 baseEnd_1967775 := by
    simpa [prefixWord, tailWord_1967775, baseEnd_1967775] using wordTrace_append hprefix tailTrace_1967775
  have hstable : (prefixWord ++ tailWord_1967775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967775).length < 2 ^ (prefixWord ++ tailWord_1967775).sum := by decide
  have hdescent : baseEnd_1967775 < baseStart_1967775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967806 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1967806 : Nat := 118140960795 + 1967806 * 2 ^ 59
def prefixEnd_1967806 : Nat := 4983230072969 + 3 ^ 40 * 1967806 * 2
def baseEnd_1967806 : Nat := 449080139022859192744547

theorem tailTrace_1967806 : CollatzResearch.WordTrace tailWord_1967806 prefixEnd_1967806 449080139022859192744547 := by
  unfold tailWord_1967806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971472638622801419206409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47847854072654940902434181 8971472638622801419206409)
  ·
    refine ⟨6728604478967101064404807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8971472638622801419206409 6728604478967101064404807)
    ·
      refine ⟨10092906718450651596607211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6728604478967101064404807 10092906718450651596607211)
      ·
        refine ⟨15139360077675977394910817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10092906718450651596607211 15139360077675977394910817)
        ·
          refine ⟨11354520058256983046183113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15139360077675977394910817 11354520058256983046183113)
          ·
            refine ⟨8515890043692737284637335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11354520058256983046183113 8515890043692737284637335)
            ·
              refine ⟨12773835065539105926956003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8515890043692737284637335 12773835065539105926956003)
              ·
                refine ⟨19160752598308658890434005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12773835065539105926956003 19160752598308658890434005)
                ·
                  refine ⟨449080139022859192744547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19160752598308658890434005 449080139022859192744547)
                  ·
                    rfl

theorem cell21_1967806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1967806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967806 prefixEnd_1967806 := by exact prefixLift 1967806
  have htrace : WordTrace (prefixWord ++ tailWord_1967806) baseStart_1967806 baseEnd_1967806 := by
    simpa [prefixWord, tailWord_1967806, baseEnd_1967806] using wordTrace_append hprefix tailTrace_1967806
  have hstable : (prefixWord ++ tailWord_1967806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967806).length < 2 ^ (prefixWord ++ tailWord_1967806).sum := by decide
  have hdescent : baseEnd_1967806 < baseStart_1967806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967854 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1967854 : Nat := 118140960795 + 1967854 * 2 ^ 59
def prefixEnd_1967854 : Nat := 4983230072969 + 3 ^ 40 * 1967854 * 2
def baseEnd_1967854 : Nat := 449091093276821775944449

theorem tailTrace_1967854 : CollatzResearch.WordTrace tailWord_1967854 prefixEnd_1967854 449091093276821775944449 := by
  unfold tailWord_1967854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971691476601064443924827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47849021208539010367599077 8971691476601064443924827)
  ·
    refine ⟨13457537214901596665887241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8971691476601064443924827 13457537214901596665887241)
    ·
      refine ⟨10093152911176197499415431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13457537214901596665887241 10093152911176197499415431)
      ·
        refine ⟨15139729366764296249123147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093152911176197499415431 15139729366764296249123147)
        ·
          refine ⟨22709594050146444373684721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139729366764296249123147 22709594050146444373684721)
          ·
            refine ⟨17032195537609833280263541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22709594050146444373684721 17032195537609833280263541)
            ·
              refine ⟨1596768331650921870024707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17032195537609833280263541 1596768331650921870024707)
              ·
                refine ⟨2395152497476382805037061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596768331650921870024707 2395152497476382805037061)
                ·
                  refine ⟨449091093276821775944449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395152497476382805037061 449091093276821775944449)
                  ·
                    rfl

theorem cell21_1967854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1967854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967854 prefixEnd_1967854 := by exact prefixLift 1967854
  have htrace : WordTrace (prefixWord ++ tailWord_1967854) baseStart_1967854 baseEnd_1967854 := by
    simpa [prefixWord, tailWord_1967854, baseEnd_1967854] using wordTrace_append hprefix tailTrace_1967854
  have hstable : (prefixWord ++ tailWord_1967854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967854).length < 2 ^ (prefixWord ++ tailWord_1967854).sum := by decide
  have hdescent : baseEnd_1967854 < baseStart_1967854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967896 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_1967896 : Nat := 118140960795 + 1967896 * 2 ^ 59
def prefixEnd_1967896 : Nat := 4983230072969 + 3 ^ 40 * 1967896 * 2
def baseEnd_1967896 : Nat := 449100678249039036244363

theorem tailTrace_1967896 : CollatzResearch.WordTrace tailWord_1967896 prefixEnd_1967896 449100678249039036244363 := by
  unfold tailWord_1967896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887531839328178362213771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47850042452437571149618361 35887531839328178362213771)
  ·
    refine ⟨53831297758992267543320657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35887531839328178362213771 53831297758992267543320657)
    ·
      refine ⟨40373473319244200657490493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53831297758992267543320657 40373473319244200657490493)
      ·
        refine ⟨15140052494716575246558935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40373473319244200657490493 15140052494716575246558935)
        ·
          refine ⟨22710078742074862869838403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15140052494716575246558935 22710078742074862869838403)
          ·
            refine ⟨34065118113112294304757605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22710078742074862869838403 34065118113112294304757605)
            ·
              refine ⟨6387209646208555182142051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34065118113112294304757605 6387209646208555182142051)
              ·
                refine ⟨9580814469312832773213077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387209646208555182142051 9580814469312832773213077)
                ·
                  refine ⟨449100678249039036244363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9580814469312832773213077 449100678249039036244363)
                  ·
                    rfl

theorem cell21_1967896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_1967896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967896 prefixEnd_1967896 := by exact prefixLift 1967896
  have htrace : WordTrace (prefixWord ++ tailWord_1967896) baseStart_1967896 baseEnd_1967896 := by
    simpa [prefixWord, tailWord_1967896, baseEnd_1967896] using wordTrace_append hprefix tailTrace_1967896
  have hstable : (prefixWord ++ tailWord_1967896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967896).length < 2 ^ (prefixWord ++ tailWord_1967896).sum := by decide
  have hdescent : baseEnd_1967896 < baseStart_1967896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967902 : List Nat := [4, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1967902 : Nat := 118140960795 + 1967902 * 2 ^ 59
def prefixEnd_1967902 : Nat := 4983230072969 + 3 ^ 40 * 1967902 * 2
def baseEnd_1967902 : Nat := 149700682510261453048117

theorem tailTrace_1967902 : CollatzResearch.WordTrace tailWord_1967902 prefixEnd_1967902 149700682510261453048117 := by
  unfold tailWord_1967902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8971910314579327468643245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47850188344423079832763973 8971910314579327468643245)
  ·
    refine ⟨3364466367967247800741217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8971910314579327468643245 3364466367967247800741217)
    ·
      refine ⟨2523349775975435850555913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364466367967247800741217 2523349775975435850555913)
      ·
        refine ⟨1892512331981576887916935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2523349775975435850555913 1892512331981576887916935)
        ·
          refine ⟨2838768497972365331875403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892512331981576887916935 2838768497972365331875403)
          ·
            refine ⟨4258152746958547997813105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838768497972365331875403 4258152746958547997813105)
            ·
              refine ⟨3193614560218910998359829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4258152746958547997813105 3193614560218910998359829)
              ·
                refine ⟨149700682510261453048117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3193614560218910998359829 149700682510261453048117)
                ·
                  rfl

theorem cell21_1967902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1967902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1967902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1967902 prefixEnd_1967902 := by exact prefixLift 1967902
  have htrace : WordTrace (prefixWord ++ tailWord_1967902) baseStart_1967902 baseEnd_1967902 := by
    simpa [prefixWord, tailWord_1967902, baseEnd_1967902] using wordTrace_append hprefix tailTrace_1967902
  have hstable : (prefixWord ++ tailWord_1967902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967902).length < 2 ^ (prefixWord ++ tailWord_1967902).sum := by decide
  have hdescent : baseEnd_1967902 < baseStart_1967902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968017 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_1968017 : Nat := 118140960795 + 1968017 * 2 ^ 59
def prefixEnd_1968017 : Nat := 4983230072969 + 3 ^ 40 * 1968017 * 2
def baseEnd_1968017 : Nat := 449128292097569714727449

theorem tailTrace_1968017 : CollatzResearch.WordTrace tailWord_1968017 prefixEnd_1968017 449128292097569714727449 := by
  unfold tailWord_1968017
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779476911217994389582305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47852984607478662926388203 71779476911217994389582305)
  ·
    refine ⟨53834607683413495792186729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71779476911217994389582305 53834607683413495792186729)
    ·
      refine ⟨40375955762560121844140047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53834607683413495792186729 40375955762560121844140047)
      ·
        refine ⟨60563933643840182766210071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40375955762560121844140047 60563933643840182766210071)
        ·
          refine ⟨90845900465760274149315107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60563933643840182766210071 90845900465760274149315107)
          ·
            refine ⟨136268850698640411223972661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90845900465760274149315107 136268850698640411223972661)
            ·
              refine ⟨12775204752997538552247437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136268850698640411223972661 12775204752997538552247437)
              ·
                refine ⟨4790701782374076957092789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12775204752997538552247437 4790701782374076957092789)
                ·
                  refine ⟨449128292097569714727449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4790701782374076957092789 449128292097569714727449)
                  ·
                    rfl

theorem cell21_1968017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_1968017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968017 prefixEnd_1968017 := by exact prefixLift 1968017
  have htrace : WordTrace (prefixWord ++ tailWord_1968017) baseStart_1968017 baseEnd_1968017 := by
    simpa [prefixWord, tailWord_1968017, baseEnd_1968017] using wordTrace_append hprefix tailTrace_1968017
  have hstable : (prefixWord ++ tailWord_1968017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968017).length < 2 ^ (prefixWord ++ tailWord_1968017).sum := by decide
  have hdescent : baseEnd_1968017 < baseStart_1968017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968082 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_1968082 : Nat := 118140960795 + 1968082 * 2 ^ 59
def prefixEnd_1968082 : Nat := 4983230072969 + 3 ^ 40 * 1968082 * 2
def baseEnd_1968082 : Nat := 449143125983144046143983

theorem tailTrace_1968082 : CollatzResearch.WordTrace tailWord_1968082 prefixEnd_1968082 449143125983144046143983 := by
  unfold tailWord_1968082
  simp only [CollatzResearch.WordTrace]
  refine ⟨17945461913995627622674625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47854565103988340327132333 17945461913995627622674625)
  ·
    refine ⟨13459096435496720717005969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17945461913995627622674625 13459096435496720717005969)
    ·
      refine ⟨10094322326622540537754477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13459096435496720717005969 10094322326622540537754477)
      ·
        refine ⟨3785370872483452701657929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10094322326622540537754477 3785370872483452701657929)
        ·
          refine ⟨2839028154362589526243447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785370872483452701657929 2839028154362589526243447)
          ·
            refine ⟨4258542231543884289365171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839028154362589526243447 4258542231543884289365171)
            ·
              refine ⟨6387813347315826434047757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4258542231543884289365171 6387813347315826434047757)
              ·
                refine ⟨2395430005243434912767909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6387813347315826434047757 2395430005243434912767909)
                ·
                  refine ⟨449143125983144046143983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395430005243434912767909 449143125983144046143983)
                  ·
                    rfl

theorem cell21_1968082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_1968082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968082 prefixEnd_1968082 := by exact prefixLift 1968082
  have htrace : WordTrace (prefixWord ++ tailWord_1968082) baseStart_1968082 baseEnd_1968082 := by
    simpa [prefixWord, tailWord_1968082, baseEnd_1968082] using wordTrace_append hprefix tailTrace_1968082
  have hstable : (prefixWord ++ tailWord_1968082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968082).length < 2 ^ (prefixWord ++ tailWord_1968082).sum := by decide
  have hdescent : baseEnd_1968082 < baseStart_1968082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968107 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_1968107 : Nat := 118140960795 + 1968107 * 2 ^ 59
def prefixEnd_1968107 : Nat := 4983230072969 + 3 ^ 40 * 1968107 * 2
def baseEnd_1968107 : Nat := 449148831323749558227265

theorem tailTrace_1968107 : CollatzResearch.WordTrace tailWord_1968107 prefixEnd_1968107 449148831323749558227265 := by
  unfold tailWord_1968107
  simp only [CollatzResearch.WordTrace]
  refine ⟨71782759480891939760358575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47855172987261293173572383 71782759480891939760358575)
  ·
    refine ⟨107674139221337909640537863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71782759480891939760358575 107674139221337909640537863)
    ·
      refine ⟨161511208832006864460806795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107674139221337909640537863 161511208832006864460806795)
      ·
        refine ⟨242266813248010296691210193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161511208832006864460806795 242266813248010296691210193)
        ·
          refine ⟨181700109936007722518407645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242266813248010296691210193 181700109936007722518407645)
          ·
            refine ⟨68137541226002895944402867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181700109936007722518407645 68137541226002895944402867)
            ·
              refine ⟨102206311839004343916604301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68137541226002895944402867 102206311839004343916604301)
              ·
                refine ⟨38327366939626628968726613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102206311839004343916604301 38327366939626628968726613)
                ·
                  refine ⟨449148831323749558227265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38327366939626628968726613 449148831323749558227265)
                  ·
                    rfl

theorem cell21_1968107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_1968107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968107 prefixEnd_1968107 := by exact prefixLift 1968107
  have htrace : WordTrace (prefixWord ++ tailWord_1968107) baseStart_1968107 baseEnd_1968107 := by
    simpa [prefixWord, tailWord_1968107, baseEnd_1968107] using wordTrace_append hprefix tailTrace_1968107
  have hstable : (prefixWord ++ tailWord_1968107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968107).length < 2 ^ (prefixWord ++ tailWord_1968107).sum := by decide
  have hdescent : baseEnd_1968107 < baseStart_1968107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968220 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_1968220 : Nat := 118140960795 + 1968220 * 2 ^ 59
def prefixEnd_1968220 : Nat := 4983230072969 + 3 ^ 40 * 1968220 * 2
def baseEnd_1968220 : Nat := 449174619463286472843701

theorem tailTrace_1968220 : CollatzResearch.WordTrace tailWord_1968220 prefixEnd_1968220 449174619463286472843701 := by
  unfold tailWord_1968220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35893440464741280029611057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47857920619655040039481409 35893440464741280029611057)
  ·
    refine ⟨26920080348555960022208293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35893440464741280029611057 26920080348555960022208293)
    ·
      refine ⟨5047515065354242504164055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26920080348555960022208293 5047515065354242504164055)
      ·
        refine ⟨7571272598031363756246083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047515065354242504164055 7571272598031363756246083)
        ·
          refine ⟨11356908897047045634369125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7571272598031363756246083 11356908897047045634369125)
          ·
            refine ⟨2129420418196321056444211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11356908897047045634369125 2129420418196321056444211)
            ·
              refine ⟨3194130627294481584666317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129420418196321056444211 3194130627294481584666317)
              ·
                refine ⟨1197798985235430594249869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194130627294481584666317 1197798985235430594249869)
                ·
                  refine ⟨449174619463286472843701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1197798985235430594249869 449174619463286472843701)
                  ·
                    rfl

theorem cell21_1968220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_1968220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968220 prefixEnd_1968220 := by exact prefixLift 1968220
  have htrace : WordTrace (prefixWord ++ tailWord_1968220) baseStart_1968220 baseEnd_1968220 := by
    simpa [prefixWord, tailWord_1968220, baseEnd_1968220] using wordTrace_append hprefix tailTrace_1968220
  have hstable : (prefixWord ++ tailWord_1968220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968220).length < 2 ^ (prefixWord ++ tailWord_1968220).sum := by decide
  have hdescent : baseEnd_1968220 < baseStart_1968220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968324 : List Nat := [2, 3, 3, 1, 2, 2, 3, 5]
def baseStart_1968324 : Nat := 118140960795 + 1968324 * 2 ^ 59
def prefixEnd_1968324 : Nat := 4983230072969 + 3 ^ 40 * 1968324 * 2
def baseEnd_1968324 : Nat := 149732784560068467703385

theorem tailTrace_1968324 : CollatzResearch.WordTrace tailWord_1968324 prefixEnd_1968324 149732784560068467703385 := by
  unfold tailWord_1968324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35895337060552892910504013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47860449414070523880672017 35895337060552892910504013)
  ·
    refine ⟨13460751397707334841439005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35895337060552892910504013 13460751397707334841439005)
    ·
      refine ⟨5047781774140250565539627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13460751397707334841439005 5047781774140250565539627)
      ·
        refine ⟨7571672661210375848309441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047781774140250565539627 7571672661210375848309441)
        ·
          refine ⟨5678754495907781886232081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7571672661210375848309441 5678754495907781886232081)
          ·
            refine ⟨4259065871930836414674061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5678754495907781886232081 4259065871930836414674061)
            ·
              refine ⟨1597149701974063655502773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259065871930836414674061 1597149701974063655502773)
              ·
                refine ⟨149732784560068467703385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1597149701974063655502773 149732784560068467703385)
                ·
                  rfl

theorem cell21_1968324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_1968324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968324 prefixEnd_1968324 := by exact prefixLift 1968324
  have htrace : WordTrace (prefixWord ++ tailWord_1968324) baseStart_1968324 baseEnd_1968324 := by
    simpa [prefixWord, tailWord_1968324, baseEnd_1968324] using wordTrace_append hprefix tailTrace_1968324
  have hstable : (prefixWord ++ tailWord_1968324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968324).length < 2 ^ (prefixWord ++ tailWord_1968324).sum := by decide
  have hdescent : baseEnd_1968324 < baseStart_1968324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968335 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_1968335 : Nat := 118140960795 + 1968335 * 2 ^ 59
def prefixEnd_1968335 : Nat := 4983230072969 + 3 ^ 40 * 1968335 * 2
def baseEnd_1968335 : Nat := 449200864030071828426799

theorem tailTrace_1968335 : CollatzResearch.WordTrace tailWord_1968335 prefixEnd_1968335 449200864030071828426799 := by
  unfold tailWord_1968335
  simp only [CollatzResearch.WordTrace]
  refine ⟨71791075324065934699658459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47860716882710623133105639 71791075324065934699658459)
  ·
    refine ⟨107686612986098902049487689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71791075324065934699658459 107686612986098902049487689)
    ·
      refine ⟨80764959739574176537115767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107686612986098902049487689 80764959739574176537115767)
      ·
        refine ⟨121147439609361264805673651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80764959739574176537115767 121147439609361264805673651)
        ·
          refine ⟨181721159414041897208510477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121147439609361264805673651 181721159414041897208510477)
          ·
            refine ⟨68145434780265711453191429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181721159414041897208510477 68145434780265711453191429)
            ·
              refine ⟨12777269021299820897473393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68145434780265711453191429 12777269021299820897473393)
              ·
                refine ⟨9582951765974865673105045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12777269021299820897473393 9582951765974865673105045)
                ·
                  refine ⟨449200864030071828426799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9582951765974865673105045 449200864030071828426799)
                  ·
                    rfl

theorem cell21_1968335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_1968335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968335 prefixEnd_1968335 := by exact prefixLift 1968335
  have htrace : WordTrace (prefixWord ++ tailWord_1968335) baseStart_1968335 baseEnd_1968335 := by
    simpa [prefixWord, tailWord_1968335, baseEnd_1968335] using wordTrace_append hprefix tailTrace_1968335
  have hstable : (prefixWord ++ tailWord_1968335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968335).length < 2 ^ (prefixWord ++ tailWord_1968335).sum := by decide
  have hdescent : baseEnd_1968335 < baseStart_1968335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968355 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 5]
def baseStart_1968355 : Nat := 118140960795 + 1968355 * 2 ^ 59
def prefixEnd_1968355 : Nat := 4983230072969 + 3 ^ 40 * 1968355 * 2
def baseEnd_1968355 : Nat := 449205428302556238093425

theorem tailTrace_1968355 : CollatzResearch.WordTrace tailWord_1968355 prefixEnd_1968355 449205428302556238093425 := by
  unfold tailWord_1968355
  simp only [CollatzResearch.WordTrace]
  refine ⟨71791804783993478115386519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47861203189328985410257679 71791804783993478115386519)
  ·
    refine ⟨107687707175990217173079779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71791804783993478115386519 107687707175990217173079779)
    ·
      refine ⟨161531560763985325759619669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107687707175990217173079779 161531560763985325759619669)
      ·
        refine ⟨1892947977702953036245543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 161531560763985325759619669 1892947977702953036245543)
        ·
          refine ⟨2839421966554429554368315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892947977702953036245543 2839421966554429554368315)
          ·
            refine ⟨4259132949831644331552473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839421966554429554368315 4259132949831644331552473)
            ·
              refine ⟨3194349712373733248664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259132949831644331552473 3194349712373733248664355)
              ·
                refine ⟨4791524568560599872996533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3194349712373733248664355 4791524568560599872996533)
                ·
                  refine ⟨449205428302556238093425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791524568560599872996533 449205428302556238093425)
                  ·
                    rfl

theorem cell21_1968355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_1968355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968355 prefixEnd_1968355 := by exact prefixLift 1968355
  have htrace : WordTrace (prefixWord ++ tailWord_1968355) baseStart_1968355 baseEnd_1968355 := by
    simpa [prefixWord, tailWord_1968355, baseEnd_1968355] using wordTrace_append hprefix tailTrace_1968355
  have hstable : (prefixWord ++ tailWord_1968355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968355).length < 2 ^ (prefixWord ++ tailWord_1968355).sum := by decide
  have hdescent : baseEnd_1968355 < baseStart_1968355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968366 : List Nat := [4, 1, 2, 1, 1, 1, 1, 10]
def baseStart_1968366 : Nat := 118140960795 + 1968366 * 2 ^ 59
def prefixEnd_1968366 : Nat := 4983230072969 + 3 ^ 40 * 1968366 * 2
def baseEnd_1968366 : Nat := 149735979550807554470023

theorem tailTrace_1968366 : CollatzResearch.WordTrace tailWord_1968366 prefixEnd_1968366 149735979550807554470023 := by
  unfold tailWord_1968366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8974025748369203374254619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47861470657969084662691301 8974025748369203374254619)
  ·
    refine ⟨13461038622553805061381929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8974025748369203374254619 13461038622553805061381929)
    ·
      refine ⟨10095778966915353796036447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13461038622553805061381929 10095778966915353796036447)
      ·
        refine ⟨15143668450373030694054671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095778966915353796036447 15143668450373030694054671)
        ·
          refine ⟨22715502675559546041082007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15143668450373030694054671 22715502675559546041082007)
          ·
            refine ⟨34073254013339319061623011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22715502675559546041082007 34073254013339319061623011)
            ·
              refine ⟨51109881020008978592434517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34073254013339319061623011 51109881020008978592434517)
              ·
                refine ⟨149735979550807554470023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51109881020008978592434517 149735979550807554470023)
                ·
                  rfl

theorem cell21_1968366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_1968366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968366 prefixEnd_1968366 := by exact prefixLift 1968366
  have htrace : WordTrace (prefixWord ++ tailWord_1968366) baseStart_1968366 baseEnd_1968366 := by
    simpa [prefixWord, tailWord_1968366, baseEnd_1968366] using wordTrace_append hprefix tailTrace_1968366
  have hstable : (prefixWord ++ tailWord_1968366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968366).length < 2 ^ (prefixWord ++ tailWord_1968366).sum := by decide
  have hdescent : baseEnd_1968366 < baseStart_1968366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968411 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 6]
def baseStart_1968411 : Nat := 118140960795 + 1968411 * 2 ^ 59
def prefixEnd_1968411 : Nat := 4983230072969 + 3 ^ 40 * 1968411 * 2
def baseEnd_1968411 : Nat := 449218208265512585159977

theorem tailTrace_1968411 : CollatzResearch.WordTrace tailWord_1968411 prefixEnd_1968411 449218208265512585159977 := by
  unfold tailWord_1968411
  simp only [CollatzResearch.WordTrace]
  refine ⟨71793847271790599679425087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47862564847860399786283391 71793847271790599679425087)
  ·
    refine ⟨107690770907685899519137631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71793847271790599679425087 107690770907685899519137631)
    ·
      refine ⟨161536156361528849278706447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107690770907685899519137631 161536156361528849278706447)
      ·
        refine ⟨242304234542293273918059671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161536156361528849278706447 242304234542293273918059671)
        ·
          refine ⟨363456351813439910877089507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242304234542293273918059671 363456351813439910877089507)
          ·
            refine ⟨545184527720159866315634261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363456351813439910877089507 545184527720159866315634261)
            ·
              refine ⟨6388881184220623433386339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 545184527720159866315634261 6388881184220623433386339)
              ·
                refine ⟨9583321776330935150079509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388881184220623433386339 9583321776330935150079509)
                ·
                  refine ⟨449218208265512585159977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9583321776330935150079509 449218208265512585159977)
                  ·
                    rfl

theorem cell21_1968411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_1968411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968411 prefixEnd_1968411 := by exact prefixLift 1968411
  have htrace : WordTrace (prefixWord ++ tailWord_1968411) baseStart_1968411 baseEnd_1968411 := by
    simpa [prefixWord, tailWord_1968411, baseEnd_1968411] using wordTrace_append hprefix tailTrace_1968411
  have hstable : (prefixWord ++ tailWord_1968411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968411).length < 2 ^ (prefixWord ++ tailWord_1968411).sum := by decide
  have hdescent : baseEnd_1968411 < baseStart_1968411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968442 : List Nat := [3, 1, 1, 1, 4, 2, 2, 7]
def baseStart_1968442 : Nat := 118140960795 + 1968442 * 2 ^ 59
def prefixEnd_1968442 : Nat := 4983230072969 + 3 ^ 40 * 1968442 * 2
def baseEnd_1968442 : Nat := 149741760962621140047749

theorem tailTrace_1968442 : CollatzResearch.WordTrace tailWord_1968442 prefixEnd_1968442 149741760962621140047749 := by
  unfold tailWord_1968442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948744483669572993450895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47863318623118861315869053 17948744483669572993450895)
  ·
    refine ⟨26923116725504359490176343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948744483669572993450895 26923116725504359490176343)
    ·
      refine ⟨40384675088256539235264515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26923116725504359490176343 40384675088256539235264515)
      ·
        refine ⟨60577012632384808852896773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40384675088256539235264515 60577012632384808852896773)
        ·
          refine ⟨11358189868572151659918145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60577012632384808852896773 11358189868572151659918145)
          ·
            refine ⟨8518642401429113744938609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358189868572151659918145 8518642401429113744938609)
            ·
              refine ⟨6388981801071835308703957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518642401429113744938609 6388981801071835308703957)
              ·
                refine ⟨149741760962621140047749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6388981801071835308703957 149741760962621140047749)
                ·
                  rfl

theorem cell21_1968442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_1968442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968442 prefixEnd_1968442 := by exact prefixLift 1968442
  have htrace : WordTrace (prefixWord ++ tailWord_1968442) baseStart_1968442 baseEnd_1968442 := by
    simpa [prefixWord, tailWord_1968442, baseEnd_1968442] using wordTrace_append hprefix tailTrace_1968442
  have hstable : (prefixWord ++ tailWord_1968442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968442).length < 2 ^ (prefixWord ++ tailWord_1968442).sum := by decide
  have hdescent : baseEnd_1968442 < baseStart_1968442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968490 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1968490 : Nat := 118140960795 + 1968490 * 2 ^ 59
def prefixEnd_1968490 : Nat := 4983230072969 + 3 ^ 40 * 1968490 * 2
def baseEnd_1968490 : Nat := 449236237141826003343149

theorem tailTrace_1968490 : CollatzResearch.WordTrace tailWord_1968490 prefixEnd_1968490 449236237141826003343149 := by
  unfold tailWord_1968490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17949182159626099042887731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47864485759002930781033949 17949182159626099042887731)
  ·
    refine ⟨26923773239439148564331597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17949182159626099042887731 26923773239439148564331597)
    ·
      refine ⟨10096414964789680711624349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26923773239439148564331597 10096414964789680711624349)
      ·
        refine ⟨3786155611796130266859131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10096414964789680711624349 3786155611796130266859131)
        ·
          refine ⟨5679233417694195400288697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3786155611796130266859131 5679233417694195400288697)
          ·
            refine ⟨4259425063270646550216523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5679233417694195400288697 4259425063270646550216523)
            ·
              refine ⟨6389137594905969825324785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259425063270646550216523 6389137594905969825324785)
              ·
                refine ⟨4791853196179477368993589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6389137594905969825324785 4791853196179477368993589)
                ·
                  refine ⟨449236237141826003343149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4791853196179477368993589 449236237141826003343149)
                  ·
                    rfl

theorem cell21_1968490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1968490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968490 prefixEnd_1968490 := by exact prefixLift 1968490
  have htrace : WordTrace (prefixWord ++ tailWord_1968490) baseStart_1968490 baseEnd_1968490 := by
    simpa [prefixWord, tailWord_1968490, baseEnd_1968490] using wordTrace_append hprefix tailTrace_1968490
  have hstable : (prefixWord ++ tailWord_1968490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968490).length < 2 ^ (prefixWord ++ tailWord_1968490).sum := by decide
  have hdescent : baseEnd_1968490 < baseStart_1968490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968521 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 4]
def baseStart_1968521 : Nat := 118140960795 + 1968521 * 2 ^ 59
def prefixEnd_1968521 : Nat := 4983230072969 + 3 ^ 40 * 1968521 * 2
def baseEnd_1968521 : Nat := 449243311764176838326419

theorem tailTrace_1968521 : CollatzResearch.WordTrace tailWord_1968521 prefixEnd_1968521 449243311764176838326419 := by
  unfold tailWord_1968521
  simp only [CollatzResearch.WordTrace]
  refine ⟨71797859301392088465929417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47865239534261392310619611 71797859301392088465929417)
  ·
    refine ⟨53848394476044066349447063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71797859301392088465929417 53848394476044066349447063)
    ·
      refine ⟨80772591714066099524170595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53848394476044066349447063 80772591714066099524170595)
      ·
        refine ⟨121158887571099149286255893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80772591714066099524170595 121158887571099149286255893)
        ·
          refine ⟨5679322854895272622793245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121158887571099149286255893 5679322854895272622793245)
          ·
            refine ⟨2129746070585727233547467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5679322854895272622793245 2129746070585727233547467)
            ·
              refine ⟨3194619105878590850321201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129746070585727233547467 3194619105878590850321201)
              ·
                refine ⟨2395964329408943137740901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3194619105878590850321201 2395964329408943137740901)
                ·
                  refine ⟨449243311764176838326419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2395964329408943137740901 449243311764176838326419)
                  ·
                    rfl

theorem cell21_1968521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_1968521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968521 prefixEnd_1968521 := by exact prefixLift 1968521
  have htrace : WordTrace (prefixWord ++ tailWord_1968521) baseStart_1968521 baseEnd_1968521 := by
    simpa [prefixWord, tailWord_1968521, baseEnd_1968521] using wordTrace_append hprefix tailTrace_1968521
  have hstable : (prefixWord ++ tailWord_1968521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968521).length < 2 ^ (prefixWord ++ tailWord_1968521).sum := by decide
  have hdescent : baseEnd_1968521 < baseStart_1968521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968552 : List Nat := [2, 1, 6, 1, 1, 1, 4, 5]
def baseStart_1968552 : Nat := 118140960795 + 1968552 * 2 ^ 59
def prefixEnd_1968552 : Nat := 4983230072969 + 3 ^ 40 * 1968552 * 2
def baseEnd_1968552 : Nat := 149750128795509224436563

theorem tailTrace_1968552 : CollatzResearch.WordTrace tailWord_1968552 prefixEnd_1968552 149750128795509224436563 := by
  unfold tailWord_1968552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35899494982139890380153955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47865993309519853840205273 35899494982139890380153955)
  ·
    refine ⟨53849242473209835570230933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35899494982139890380153955 53849242473209835570230933)
    ·
      refine ⟨2524183240931711042354575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53849242473209835570230933 2524183240931711042354575)
      ·
        refine ⟨3786274861397566563531863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524183240931711042354575 3786274861397566563531863)
        ·
          refine ⟨5679412292096349845297795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3786274861397566563531863 5679412292096349845297795)
          ·
            refine ⟨8519118438144524767946693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679412292096349845297795 8519118438144524767946693)
            ·
              refine ⟨1597334707152098393990005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8519118438144524767946693 1597334707152098393990005)
              ·
                refine ⟨149750128795509224436563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1597334707152098393990005 149750128795509224436563)
                ·
                  rfl

theorem cell21_1968552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_1968552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968552 prefixEnd_1968552 := by exact prefixLift 1968552
  have htrace : WordTrace (prefixWord ++ tailWord_1968552) baseStart_1968552 baseEnd_1968552 := by
    simpa [prefixWord, tailWord_1968552, baseEnd_1968552] using wordTrace_append hprefix tailTrace_1968552
  have hstable : (prefixWord ++ tailWord_1968552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968552).length < 2 ^ (prefixWord ++ tailWord_1968552).sum := by decide
  have hdescent : baseEnd_1968552 < baseStart_1968552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968583 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 3]
def baseStart_1968583 : Nat := 118140960795 + 1968583 * 2 ^ 59
def prefixEnd_1968583 : Nat := 4983230072969 + 3 ^ 40 * 1968583 * 2
def baseEnd_1968583 : Nat := 449257461008878508292959

theorem tailTrace_1968583 : CollatzResearch.WordTrace tailWord_1968583 prefixEnd_1968583 449257461008878508292959 := by
  unfold tailWord_1968583
  simp only [CollatzResearch.WordTrace]
  refine ⟨71800120627167473054686403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47866747084778315369790935 71800120627167473054686403)
  ·
    refine ⟨107700180940751209582029605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71800120627167473054686403 107700180940751209582029605)
    ·
      refine ⟨20193783926390851796630551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107700180940751209582029605 20193783926390851796630551)
      ·
        refine ⟨30290675889586277694945827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20193783926390851796630551 30290675889586277694945827)
        ·
          refine ⟨45436013834379416542418741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30290675889586277694945827 45436013834379416542418741)
          ·
            refine ⟨4259626296973070300851757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45436013834379416542418741 4259626296973070300851757)
            ·
              refine ⟨1597359861364901362819409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259626296973070300851757 1597359861364901362819409)
              ·
                refine ⟨1198019896023676022114557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597359861364901362819409 1198019896023676022114557)
                ·
                  refine ⟨449257461008878508292959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198019896023676022114557 449257461008878508292959)
                  ·
                    rfl

theorem cell21_1968583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3].length) (baseStart_1968583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968583 prefixEnd_1968583 := by exact prefixLift 1968583
  have htrace : WordTrace (prefixWord ++ tailWord_1968583) baseStart_1968583 baseEnd_1968583 := by
    simpa [prefixWord, tailWord_1968583, baseEnd_1968583] using wordTrace_append hprefix tailTrace_1968583
  have hstable : (prefixWord ++ tailWord_1968583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968583).length < 2 ^ (prefixWord ++ tailWord_1968583).sum := by decide
  have hdescent : baseEnd_1968583 < baseStart_1968583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968597 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1968597 : Nat := 118140960795 + 1968597 * 2 ^ 59
def prefixEnd_1968597 : Nat := 4983230072969 + 3 ^ 40 * 1968597 * 2
def baseEnd_1968597 : Nat := 449260655999617595059597

theorem tailTrace_1968597 : CollatzResearch.WordTrace tailWord_1968597 prefixEnd_1968597 449260655999617595059597 := by
  unfold tailWord_1968597
  simp only [CollatzResearch.WordTrace]
  refine ⟨71800631249116753445696045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47867087499411168963797363 71800631249116753445696045)
  ·
    refine ⟨26925236718418782542136017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71800631249116753445696045 26925236718418782542136017)
    ·
      refine ⟨20193927538814086906602013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26925236718418782542136017 20193927538814086906602013)
      ·
        refine ⟨7572722827055282589975755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20193927538814086906602013 7572722827055282589975755)
        ·
          refine ⟨11359084240582923884963633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572722827055282589975755 11359084240582923884963633)
          ·
            refine ⟨8519313180437192913722725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11359084240582923884963633 8519313180437192913722725)
            ·
              refine ⟨1597371221331973671323011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8519313180437192913722725 1597371221331973671323011)
              ·
                refine ⟨2396056831997960506984517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597371221331973671323011 2396056831997960506984517)
                ·
                  refine ⟨449260655999617595059597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396056831997960506984517 449260655999617595059597)
                  ·
                    rfl

theorem cell21_1968597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1968597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968597 prefixEnd_1968597 := by exact prefixLift 1968597
  have htrace : WordTrace (prefixWord ++ tailWord_1968597) baseStart_1968597 baseEnd_1968597 := by
    simpa [prefixWord, tailWord_1968597, baseEnd_1968597] using wordTrace_append hprefix tailTrace_1968597
  have hstable : (prefixWord ++ tailWord_1968597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968597).length < 2 ^ (prefixWord ++ tailWord_1968597).sum := by decide
  have hdescent : baseEnd_1968597 < baseStart_1968597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968608 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_1968608 : Nat := 118140960795 + 1968608 * 2 ^ 59
def prefixEnd_1968608 : Nat := 4983230072969 + 3 ^ 40 * 1968608 * 2
def baseEnd_1968608 : Nat := 449263166349484020376241

theorem tailTrace_1968608 : CollatzResearch.WordTrace tailWord_1968608 prefixEnd_1968608 449263166349484020376241 := by
  unfold tailWord_1968608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35900516226038451162173239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47867354968051268216230985 35900516226038451162173239)
  ·
    refine ⟨53850774339057676743259859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35900516226038451162173239 53850774339057676743259859)
    ·
      refine ⟨80776161508586515114889789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53850774339057676743259859 80776161508586515114889789)
      ·
        refine ⟨30291060565719943168083671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80776161508586515114889789 30291060565719943168083671)
        ·
          refine ⟨45436590848579914752125507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30291060565719943168083671 45436590848579914752125507)
          ·
            refine ⟨68154886272869872128188261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45436590848579914752125507 68154886272869872128188261)
            ·
              refine ⟨12779041176163101024035299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68154886272869872128188261 12779041176163101024035299)
              ·
                refine ⟨19168561764244651536052949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779041176163101024035299 19168561764244651536052949)
                ·
                  refine ⟨449263166349484020376241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19168561764244651536052949 449263166349484020376241)
                  ·
                    rfl

theorem cell21_1968608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_1968608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968608 prefixEnd_1968608 := by exact prefixLift 1968608
  have htrace : WordTrace (prefixWord ++ tailWord_1968608) baseStart_1968608 baseEnd_1968608 := by
    simpa [prefixWord, tailWord_1968608, baseEnd_1968608] using wordTrace_append hprefix tailTrace_1968608
  have hstable : (prefixWord ++ tailWord_1968608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968608).length < 2 ^ (prefixWord ++ tailWord_1968608).sum := by decide
  have hdescent : baseEnd_1968608 < baseStart_1968608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968676 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1968676 : Nat := 118140960795 + 1968676 * 2 ^ 59
def prefixEnd_1968676 : Nat := 4983230072969 + 3 ^ 40 * 1968676 * 2
def baseEnd_1968676 : Nat := 449278684875931013242769

theorem tailTrace_1968676 : CollatzResearch.WordTrace tailWord_1968676 prefixEnd_1968676 449278684875931013242769 := by
  unfold tailWord_1968676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35901756307915274968910941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47869008410553699958547921 35901756307915274968910941)
  ·
    refine ⟨13463158615468228113341603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35901756307915274968910941 13463158615468228113341603)
    ·
      refine ⟨20194737923202342170012405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463158615468228113341603 20194737923202342170012405)
      ·
        refine ⟨1893256680300219578438663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20194737923202342170012405 1893256680300219578438663)
        ·
          refine ⟨2839885020450329367657995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893256680300219578438663 2839885020450329367657995)
          ·
            refine ⟨4259827530675494051486993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839885020450329367657995 4259827530675494051486993)
            ·
              refine ⟨3194870648006620538615245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259827530675494051486993 3194870648006620538615245)
              ·
                refine ⟨1198076493002482701980717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194870648006620538615245 1198076493002482701980717)
                ·
                  refine ⟨449278684875931013242769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198076493002482701980717 449278684875931013242769)
                  ·
                    rfl

theorem cell21_1968676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1968676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968676 prefixEnd_1968676 := by exact prefixLift 1968676
  have htrace : WordTrace (prefixWord ++ tailWord_1968676) baseStart_1968676 baseEnd_1968676 := by
    simpa [prefixWord, tailWord_1968676, baseEnd_1968676] using wordTrace_append hprefix tailTrace_1968676
  have hstable : (prefixWord ++ tailWord_1968676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968676).length < 2 ^ (prefixWord ++ tailWord_1968676).sum := by decide
  have hdescent : baseEnd_1968676 < baseStart_1968676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968701 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1968701 : Nat := 118140960795 + 1968701 * 2 ^ 59
def prefixEnd_1968701 : Nat := 4983230072969 + 3 ^ 40 * 1968701 * 2
def baseEnd_1968701 : Nat := 449284390216536525326051

theorem tailTrace_1968701 : CollatzResearch.WordTrace tailWord_1968701 prefixEnd_1968701 449284390216536525326051 := by
  unfold tailWord_1968701
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804424440739979207481957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869616293826652804987971 71804424440739979207481957)
  ·
    refine ⟨13463329582638746101402867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71804424440739979207481957 13463329582638746101402867)
    ·
      refine ⟨20194994373958119152104301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463329582638746101402867 20194994373958119152104301)
      ·
        refine ⟨7573122890234294682039113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20194994373958119152104301 7573122890234294682039113)
        ·
          refine ⟨5679842167675721011529335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7573122890234294682039113 5679842167675721011529335)
          ·
            refine ⟨8519763251513581517294003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5679842167675721011529335 8519763251513581517294003)
            ·
              refine ⟨12779644877270372275941005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8519763251513581517294003 12779644877270372275941005)
              ·
                refine ⟨4792366828976389603477877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12779644877270372275941005 4792366828976389603477877)
                ·
                  refine ⟨449284390216536525326051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4792366828976389603477877 449284390216536525326051)
                  ·
                    rfl

theorem cell21_1968701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1968701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968701 prefixEnd_1968701 := by exact prefixLift 1968701
  have htrace : WordTrace (prefixWord ++ tailWord_1968701) baseStart_1968701 baseEnd_1968701 := by
    simpa [prefixWord, tailWord_1968701, baseEnd_1968701] using wordTrace_append hprefix tailTrace_1968701
  have hstable : (prefixWord ++ tailWord_1968701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968701).length < 2 ^ (prefixWord ++ tailWord_1968701).sum := by decide
  have hdescent : baseEnd_1968701 < baseStart_1968701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968715 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_1968715 : Nat := 118140960795 + 1968715 * 2 ^ 59
def prefixEnd_1968715 : Nat := 4983230072969 + 3 ^ 40 * 1968715 * 2
def baseEnd_1968715 : Nat := 449287585207275612092689

theorem tailTrace_1968715 : CollatzResearch.WordTrace tailWord_1968715 prefixEnd_1968715 449287585207275612092689 := by
  unfold tailWord_1968715
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804935062689259598491599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869956708459506398994399 71804935062689259598491599)
  ·
    refine ⟨107707402594033889397737399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71804935062689259598491599 107707402594033889397737399)
    ·
      refine ⟨161561103891050834096606099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107707402594033889397737399 161561103891050834096606099)
      ·
        refine ⟨242341655836576251144909149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161561103891050834096606099 242341655836576251144909149)
        ·
          refine ⟨90878120938716094179340931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242341655836576251144909149 90878120938716094179340931)
          ·
            refine ⟨136317181408074141269011397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90878120938716094179340931 136317181408074141269011397)
            ·
              refine ⟨25559471514013901487939637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136317181408074141269011397 25559471514013901487939637)
              ·
                refine ⟨2396200454438803264494341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25559471514013901487939637 2396200454438803264494341)
                ·
                  refine ⟨449287585207275612092689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396200454438803264494341 449287585207275612092689)
                  ·
                    rfl

theorem cell21_1968715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_1968715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968715 prefixEnd_1968715 := by exact prefixLift 1968715
  have htrace : WordTrace (prefixWord ++ tailWord_1968715) baseStart_1968715 baseEnd_1968715 := by
    simpa [prefixWord, tailWord_1968715, baseEnd_1968715] using wordTrace_append hprefix tailTrace_1968715
  have hstable : (prefixWord ++ tailWord_1968715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968715).length < 2 ^ (prefixWord ++ tailWord_1968715).sum := by decide
  have hdescent : baseEnd_1968715 < baseStart_1968715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968881 : List Nat := [1, 2, 2, 2, 2, 2, 2, 8]
def baseStart_1968881 : Nat := 118140960795 + 1968881 * 2 ^ 59
def prefixEnd_1968881 : Nat := 4983230072969 + 3 ^ 40 * 1968881 * 2
def baseEnd_1968881 : Nat := 149775156222965404108561

theorem tailTrace_1968881 : CollatzResearch.WordTrace tailWord_1968881 prefixEnd_1968881 149775156222965404108561 := by
  unfold tailWord_1968881
  simp only [CollatzResearch.WordTrace]
  refine ⟨71810989580087869949034497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47873993053391913299356331 71810989580087869949034497)
  ·
    refine ⟨53858242185065902461775873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71810989580087869949034497 53858242185065902461775873)
    ·
      refine ⟨40393681638799426846331905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53858242185065902461775873 40393681638799426846331905)
      ·
        refine ⟨30295261229099570134748929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40393681638799426846331905 30295261229099570134748929)
        ·
          refine ⟨22721445921824677601061697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30295261229099570134748929 22721445921824677601061697)
          ·
            refine ⟨17041084441368508200796273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22721445921824677601061697 17041084441368508200796273)
            ·
              refine ⟨12780813331026381150597205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17041084441368508200796273 12780813331026381150597205)
              ·
                refine ⟨149775156222965404108561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12780813331026381150597205 149775156222965404108561)
                ·
                  rfl

theorem cell21_1968881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 8].length) (baseStart_1968881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968881 prefixEnd_1968881 := by exact prefixLift 1968881
  have htrace : WordTrace (prefixWord ++ tailWord_1968881) baseStart_1968881 baseEnd_1968881 := by
    simpa [prefixWord, tailWord_1968881, baseEnd_1968881] using wordTrace_append hprefix tailTrace_1968881
  have hstable : (prefixWord ++ tailWord_1968881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968881).length < 2 ^ (prefixWord ++ tailWord_1968881).sum := by decide
  have hdescent : baseEnd_1968881 < baseStart_1968881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968980 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1968980 : Nat := 118140960795 + 1968980 * 2 ^ 59
def prefixEnd_1968980 : Nat := 4983230072969 + 3 ^ 40 * 1968980 * 2
def baseEnd_1968980 : Nat := 449348061817694040175481

theorem tailTrace_1968980 : CollatzResearch.WordTrace tailWord_1968980 prefixEnd_1968980 449348061817694040175481 := by
  unfold tailWord_1968980
  simp only [CollatzResearch.WordTrace]
  refine ⟨35907300203364604928444197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47876400271152806571258929 35907300203364604928444197)
  ·
    refine ⟨6732618788130863424083287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35907300203364604928444197 6732618788130863424083287)
    ·
      refine ⟨10098928182196295136124931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6732618788130863424083287 10098928182196295136124931)
      ·
        refine ⟨15148392273294442704187397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10098928182196295136124931 15148392273294442704187397)
        ·
          refine ⟨2840323551242708007035137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15148392273294442704187397 2840323551242708007035137)
          ·
            refine ⟨2130242663432031005276353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840323551242708007035137 2130242663432031005276353)
            ·
              refine ⟨1597681997574023253957265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130242663432031005276353 1597681997574023253957265)
              ·
                refine ⟨1198261498180517440467949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597681997574023253957265 1198261498180517440467949)
                ·
                  refine ⟨449348061817694040175481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198261498180517440467949 449348061817694040175481)
                  ·
                    rfl

theorem cell21_1968980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1968980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1968980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1968980 prefixEnd_1968980 := by exact prefixLift 1968980
  have htrace : WordTrace (prefixWord ++ tailWord_1968980) baseStart_1968980 baseEnd_1968980 := by
    simpa [prefixWord, tailWord_1968980, baseEnd_1968980] using wordTrace_append hprefix tailTrace_1968980
  have hstable : (prefixWord ++ tailWord_1968980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968980).length < 2 ^ (prefixWord ++ tailWord_1968980).sum := by decide
  have hdescent : baseEnd_1968980 < baseStart_1968980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969033 : List Nat := [1, 2, 1, 1, 5, 3, 8]
def baseStart_1969033 : Nat := 118140960795 + 1969033 * 2 ^ 59
def prefixEnd_1969033 : Nat := 4983230072969 + 3 ^ 40 * 1969033 * 2
def baseEnd_1969033 : Nat := 49928906348864191754671

theorem tailTrace_1969033 : CollatzResearch.WordTrace tailWord_1969033 prefixEnd_1969033 49928906348864191754671 := by
  unfold tailWord_1969033
  simp only [CollatzResearch.WordTrace]
  refine ⟨71816533475537199908567753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47877688983691466605711835 71816533475537199908567753)
  ·
    refine ⟨53862400106652899931425815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71816533475537199908567753 53862400106652899931425815)
    ·
      refine ⟨80793600159979349897138723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53862400106652899931425815 80793600159979349897138723)
      ·
        refine ⟨121190400239969024845708085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80793600159979349897138723 121190400239969024845708085)
        ·
          refine ⟨11361600022497096079285133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121190400239969024845708085 11361600022497096079285133)
          ·
            refine ⟨4260600008436411029731925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11361600022497096079285133 4260600008436411029731925)
            ·
              refine ⟨49928906348864191754671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4260600008436411029731925 49928906348864191754671)
              ·
                rfl

theorem cell21_1969033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 8].length) (baseStart_1969033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969033 prefixEnd_1969033 := by exact prefixLift 1969033
  have htrace : WordTrace (prefixWord ++ tailWord_1969033) baseStart_1969033 baseEnd_1969033 := by
    simpa [prefixWord, tailWord_1969033, baseEnd_1969033] using wordTrace_append hprefix tailTrace_1969033
  have hstable : (prefixWord ++ tailWord_1969033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969033).length < 2 ^ (prefixWord ++ tailWord_1969033).sum := by decide
  have hdescent : baseEnd_1969033 < baseStart_1969033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969101 : List Nat := [1, 6, 3, 1, 1, 1, 2, 6]
def baseStart_1969101 : Nat := 118140960795 + 1969101 * 2 ^ 59
def prefixEnd_1969101 : Nat := 4983230072969 + 3 ^ 40 * 1969101 * 2
def baseEnd_1969101 : Nat := 149791891888741572886189

theorem tailTrace_1969101 : CollatzResearch.WordTrace tailWord_1969101 prefixEnd_1969101 149791891888741572886189 := by
  unfold tailWord_1969101
  simp only [CollatzResearch.WordTrace]
  refine ⟨71819013639290847522043157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47879342426193898348028771 71819013639290847522043157)
  ·
    refine ⟨3366516264341758477595773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71819013639290847522043157 3366516264341758477595773)
    ·
      refine ⟨1262443599128159429098415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3366516264341758477595773 1262443599128159429098415)
      ·
        refine ⟨1893665398692239143647623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262443599128159429098415 1893665398692239143647623)
        ·
          refine ⟨2840498098038358715471435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893665398692239143647623 2840498098038358715471435)
          ·
            refine ⟨4260747147057538073207153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840498098038358715471435 4260747147057538073207153)
            ·
              refine ⟨3195560360293153554905365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260747147057538073207153 3195560360293153554905365)
              ·
                refine ⟨149791891888741572886189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3195560360293153554905365 149791891888741572886189)
                ·
                  rfl

theorem cell21_1969101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 6].length) (baseStart_1969101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969101 prefixEnd_1969101 := by exact prefixLift 1969101
  have htrace : WordTrace (prefixWord ++ tailWord_1969101) baseStart_1969101 baseEnd_1969101 := by
    simpa [prefixWord, tailWord_1969101, baseEnd_1969101] using wordTrace_append hprefix tailTrace_1969101
  have hstable : (prefixWord ++ tailWord_1969101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969101).length < 2 ^ (prefixWord ++ tailWord_1969101).sum := by decide
  have hdescent : baseEnd_1969101 < baseStart_1969101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969112 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_1969112 : Nat := 118140960795 + 1969112 * 2 ^ 59
def prefixEnd_1969112 : Nat := 4983230072969 + 3 ^ 40 * 1969112 * 2
def baseEnd_1969112 : Nat := 449378186016091143975211

theorem tailTrace_1969112 : CollatzResearch.WordTrace tailWord_1969112 prefixEnd_1969112 449378186016091143975211 := by
  unfold tailWord_1969112
  simp only [CollatzResearch.WordTrace]
  refine ⟨35909707421125498200346795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47879609894833997600462393 35909707421125498200346795)
  ·
    refine ⟨53864561131688247300520193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35909707421125498200346795 53864561131688247300520193)
    ·
      refine ⟨40398420848766185475390145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53864561131688247300520193 40398420848766185475390145)
      ·
        refine ⟨30298815636574639106542609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40398420848766185475390145 30298815636574639106542609)
        ·
          refine ⟨22724111727430979329906957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30298815636574639106542609 22724111727430979329906957)
          ·
            refine ⟨8521541897786617248715109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22724111727430979329906957 8521541897786617248715109)
            ·
              refine ⟨1597789105834990734134083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8521541897786617248715109 1597789105834990734134083)
              ·
                refine ⟨2396683658752486101201125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597789105834990734134083 2396683658752486101201125)
                ·
                  refine ⟨449378186016091143975211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396683658752486101201125 449378186016091143975211)
                  ·
                    rfl

theorem cell21_1969112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_1969112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969112 prefixEnd_1969112 := by exact prefixLift 1969112
  have htrace : WordTrace (prefixWord ++ tailWord_1969112) baseStart_1969112 baseEnd_1969112 := by
    simpa [prefixWord, tailWord_1969112, baseEnd_1969112] using wordTrace_append hprefix tailTrace_1969112
  have hstable : (prefixWord ++ tailWord_1969112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969112).length < 2 ^ (prefixWord ++ tailWord_1969112).sum := by decide
  have hdescent : baseEnd_1969112 < baseStart_1969112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969157 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 3]
def baseStart_1969157 : Nat := 118140960795 + 1969157 * 2 ^ 59
def prefixEnd_1969157 : Nat := 4983230072969 + 3 ^ 40 * 1969157 * 2
def baseEnd_1969157 : Nat := 449388455629181065725119

theorem tailTrace_1969157 : CollatzResearch.WordTrace tailWord_1969157 prefixEnd_1969157 449388455629181065725119 := by
  unfold tailWord_1969157
  simp only [CollatzResearch.WordTrace]
  refine ⟨71821056127087969086081725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47880704084725312724054483 71821056127087969086081725)
  ·
    refine ⟨26932896047657988407280647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71821056127087969086081725 26932896047657988407280647)
    ·
      refine ⟨40399344071486982610920971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26932896047657988407280647 40399344071486982610920971)
      ·
        refine ⟨60599016107230473916381457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40399344071486982610920971 60599016107230473916381457)
        ·
          refine ⟨45449262080422855437286093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60599016107230473916381457 45449262080422855437286093)
          ·
            refine ⟨17043473280158570788982285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45449262080422855437286093 17043473280158570788982285)
            ·
              refine ⟨6391302480059464045868357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17043473280158570788982285 6391302480059464045868357)
              ·
                refine ⟨1198369215011149508600317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6391302480059464045868357 1198369215011149508600317)
                ·
                  refine ⟨449388455629181065725119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198369215011149508600317 449388455629181065725119)
                  ·
                    rfl

theorem cell21_1969157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_1969157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969157 prefixEnd_1969157 := by exact prefixLift 1969157
  have htrace : WordTrace (prefixWord ++ tailWord_1969157) baseStart_1969157 baseEnd_1969157 := by
    simpa [prefixWord, tailWord_1969157, baseEnd_1969157] using wordTrace_append hprefix tailTrace_1969157
  have hstable : (prefixWord ++ tailWord_1969157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969157).length < 2 ^ (prefixWord ++ tailWord_1969157).sum := by decide
  have hdescent : baseEnd_1969157 < baseStart_1969157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969191 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 3]
def baseStart_1969191 : Nat := 118140960795 + 1969191 * 2 ^ 59
def prefixEnd_1969191 : Nat := 4983230072969 + 3 ^ 40 * 1969191 * 2
def baseEnd_1969191 : Nat := 449396214892404562158383

theorem tailTrace_1969191 : CollatzResearch.WordTrace tailWord_1969191 prefixEnd_1969191 449396214892404562158383 := by
  unfold tailWord_1969191
  simp only [CollatzResearch.WordTrace]
  refine ⟨71822296208964792892819427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47881530805976528595212951 71822296208964792892819427)
  ·
    refine ⟨107733444313447189339229141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71822296208964792892819427 107733444313447189339229141)
    ·
      refine ⟨2525002601096418500138183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107733444313447189339229141 2525002601096418500138183)
      ·
        refine ⟨3787503901644627750207275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525002601096418500138183 3787503901644627750207275)
        ·
          refine ⟨5681255852466941625310913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787503901644627750207275 5681255852466941625310913)
          ·
            refine ⟨4260941889350206218983185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5681255852466941625310913 4260941889350206218983185)
            ·
              refine ⟨3195706417012654664237389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4260941889350206218983185 3195706417012654664237389)
              ·
                refine ⟨1198389906379745499089021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3195706417012654664237389 1198389906379745499089021)
                ·
                  refine ⟨449396214892404562158383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198389906379745499089021 449396214892404562158383)
                  ·
                    rfl

theorem cell21_1969191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3].length) (baseStart_1969191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969191 prefixEnd_1969191 := by exact prefixLift 1969191
  have htrace : WordTrace (prefixWord ++ tailWord_1969191) baseStart_1969191 baseEnd_1969191 := by
    simpa [prefixWord, tailWord_1969191, baseEnd_1969191] using wordTrace_append hprefix tailTrace_1969191
  have hstable : (prefixWord ++ tailWord_1969191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969191).length < 2 ^ (prefixWord ++ tailWord_1969191).sum := by decide
  have hdescent : baseEnd_1969191 < baseStart_1969191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969216 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_1969216 : Nat := 118140960795 + 1969216 * 2 ^ 59
def prefixEnd_1969216 : Nat := 4983230072969 + 3 ^ 40 * 1969216 * 2
def baseEnd_1969216 : Nat := 449401920233010074241665

theorem tailTrace_1969216 : CollatzResearch.WordTrace tailWord_1969216 prefixEnd_1969216 449401920233010074241665 := by
  unfold tailWord_1969216
  simp only [CollatzResearch.WordTrace]
  refine ⟨35911604016937111081239751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47882138689249481441653001 35911604016937111081239751)
  ·
    refine ⟨53867406025405666621859627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35911604016937111081239751 53867406025405666621859627)
    ·
      refine ⟨80801109038108499932789441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53867406025405666621859627 80801109038108499932789441)
      ·
        refine ⟨60600831778581374949592081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80801109038108499932789441 60600831778581374949592081)
        ·
          refine ⟨45450623833936031212194061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60600831778581374949592081 45450623833936031212194061)
          ·
            refine ⟨17043983937726011704572773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45450623833936031212194061 17043983937726011704572773)
            ·
              refine ⟨3195746988323627194607395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17043983937726011704572773 3195746988323627194607395)
              ·
                refine ⟨4793620482485440791911093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3195746988323627194607395 4793620482485440791911093)
                ·
                  refine ⟨449401920233010074241665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4793620482485440791911093 449401920233010074241665)
                  ·
                    rfl

theorem cell21_1969216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_1969216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969216 prefixEnd_1969216 := by exact prefixLift 1969216
  have htrace : WordTrace (prefixWord ++ tailWord_1969216) baseStart_1969216 baseEnd_1969216 := by
    simpa [prefixWord, tailWord_1969216, baseEnd_1969216] using wordTrace_append hprefix tailTrace_1969216
  have hstable : (prefixWord ++ tailWord_1969216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969216).length < 2 ^ (prefixWord ++ tailWord_1969216).sum := by decide
  have hdescent : baseEnd_1969216 < baseStart_1969216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969222 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1969222 : Nat := 118140960795 + 1969222 * 2 ^ 59
def prefixEnd_1969222 : Nat := 4983230072969 + 3 ^ 40 * 1969222 * 2
def baseEnd_1969222 : Nat := 449403289514755397141653

theorem tailTrace_1969222 : CollatzResearch.WordTrace tailWord_1969222 prefixEnd_1969222 449403289514755397141653 := by
  unfold tailWord_1969222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244482089745390162099935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47882284581234990124798613 2244482089745390162099935)
  ·
    refine ⟨3366723134618085243149903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244482089745390162099935 3366723134618085243149903)
    ·
      refine ⟨5050084701927127864724855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366723134618085243149903 5050084701927127864724855)
      ·
        refine ⟨7575127052890691797087283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5050084701927127864724855 7575127052890691797087283)
        ·
          refine ⟨11362690579336037695630925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575127052890691797087283 11362690579336037695630925)
          ·
            refine ⟨4261008967251014135861597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11362690579336037695630925 4261008967251014135861597)
            ·
              refine ⟨1597878362719130300948099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4261008967251014135861597 1597878362719130300948099)
              ·
                refine ⟨2396817544078695451422149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597878362719130300948099 2396817544078695451422149)
                ·
                  refine ⟨449403289514755397141653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396817544078695451422149 449403289514755397141653)
                  ·
                    rfl

theorem cell21_1969222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1969222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969222 prefixEnd_1969222 := by exact prefixLift 1969222
  have htrace : WordTrace (prefixWord ++ tailWord_1969222) baseStart_1969222 baseEnd_1969222 := by
    simpa [prefixWord, tailWord_1969222, baseEnd_1969222] using wordTrace_append hprefix tailTrace_1969222
  have hstable : (prefixWord ++ tailWord_1969222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969222).length < 2 ^ (prefixWord ++ tailWord_1969222).sum := by decide
  have hdescent : baseEnd_1969222 < baseStart_1969222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969261 : List Nat := [1, 5, 1, 1, 2, 2, 9]
def baseStart_1969261 : Nat := 118140960795 + 1969261 * 2 ^ 59
def prefixEnd_1969261 : Nat := 4983230072969 + 3 ^ 40 * 1969261 * 2
def baseEnd_1969261 : Nat := 49934687760677777332397

theorem tailTrace_1969261 : CollatzResearch.WordTrace tailWord_1969261 prefixEnd_1969261 49934687760677777332397 := by
  unfold tailWord_1969261
  simp only [CollatzResearch.WordTrace]
  refine ⟨71824849318711194847867637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47883232879140796565245091 71824849318711194847867637)
  ·
    refine ⟨6733579623629174516987591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71824849318711194847867637 6733579623629174516987591)
    ·
      refine ⟨10100369435443761775481387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6733579623629174516987591 10100369435443761775481387)
      ·
        refine ⟨15150554153165642663222081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10100369435443761775481387 15150554153165642663222081)
        ·
          refine ⟨11362915614874231997416561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15150554153165642663222081 11362915614874231997416561)
          ·
            refine ⟨8522186711155673998062421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11362915614874231997416561 8522186711155673998062421)
            ·
              refine ⟨49934687760677777332397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8522186711155673998062421 49934687760677777332397)
              ·
                rfl

theorem cell21_1969261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 9].length) (baseStart_1969261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969261 prefixEnd_1969261 := by exact prefixLift 1969261
  have htrace : WordTrace (prefixWord ++ tailWord_1969261) baseStart_1969261 baseEnd_1969261 := by
    simpa [prefixWord, tailWord_1969261, baseEnd_1969261] using wordTrace_append hprefix tailTrace_1969261
  have hstable : (prefixWord ++ tailWord_1969261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969261).length < 2 ^ (prefixWord ++ tailWord_1969261).sum := by decide
  have hdescent : baseEnd_1969261 < baseStart_1969261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969281 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 4]
def baseStart_1969281 : Nat := 118140960795 + 1969281 * 2 ^ 59
def prefixEnd_1969281 : Nat := 4983230072969 + 3 ^ 40 * 1969281 * 2
def baseEnd_1969281 : Nat := 449416754118584405658199

theorem tailTrace_1969281 : CollatzResearch.WordTrace tailWord_1969281 prefixEnd_1969281 449416754118584405658199 := by
  unfold tailWord_1969281
  simp only [CollatzResearch.WordTrace]
  refine ⟨71825578778638738263595697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47883719185759158842397131 71825578778638738263595697)
  ·
    refine ⟨53869184083979053697696773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71825578778638738263595697 53869184083979053697696773)
    ·
      refine ⟨10100472015746072568318145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53869184083979053697696773 10100472015746072568318145)
      ·
        refine ⟨7575354011809554426238609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100472015746072568318145 7575354011809554426238609)
        ·
          refine ⟨5681515508857165819678957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575354011809554426238609 5681515508857165819678957)
          ·
            refine ⟨2130568315821437182379609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5681515508857165819678957 2130568315821437182379609)
            ·
              refine ⟨1597926236866077886784707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130568315821437182379609 1597926236866077886784707)
              ·
                refine ⟨2396889355299116830177061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597926236866077886784707 2396889355299116830177061)
                ·
                  refine ⟨449416754118584405658199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2396889355299116830177061 449416754118584405658199)
                  ·
                    rfl

theorem cell21_1969281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_1969281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969281 prefixEnd_1969281 := by exact prefixLift 1969281
  have htrace : WordTrace (prefixWord ++ tailWord_1969281) baseStart_1969281 baseEnd_1969281 := by
    simpa [prefixWord, tailWord_1969281, baseEnd_1969281] using wordTrace_append hprefix tailTrace_1969281
  have hstable : (prefixWord ++ tailWord_1969281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969281).length < 2 ^ (prefixWord ++ tailWord_1969281).sum := by decide
  have hdescent : baseEnd_1969281 < baseStart_1969281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969309 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 3]
def baseStart_1969309 : Nat := 118140960795 + 1969309 * 2 ^ 59
def prefixEnd_1969309 : Nat := 4983230072969 + 3 ^ 40 * 1969309 * 2
def baseEnd_1969309 : Nat := 449423144100062579191475

theorem tailTrace_1969309 : CollatzResearch.WordTrace tailWord_1969309 prefixEnd_1969309 449423144100062579191475 := by
  unfold tailWord_1969309
  simp only [CollatzResearch.WordTrace]
  refine ⟨71826600022537299045614981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47884400015024866030409987 71826600022537299045614981)
  ·
    refine ⟨13467487504225743571052809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71826600022537299045614981 13467487504225743571052809)
    ·
      refine ⟨10100615628169307678289607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13467487504225743571052809 10100615628169307678289607)
      ·
        refine ⟨15150923442253961517434411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10100615628169307678289607 15150923442253961517434411)
        ·
          refine ⟨22726385163380942276151617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15150923442253961517434411 22726385163380942276151617)
          ·
            refine ⟨17044788872535706707113713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22726385163380942276151617 17044788872535706707113713)
            ·
              refine ⟨12783591654401780030335285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17044788872535706707113713 12783591654401780030335285)
              ·
                refine ⟨1198461717600166877843933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12783591654401780030335285 1198461717600166877843933)
                ·
                  refine ⟨449423144100062579191475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198461717600166877843933 449423144100062579191475)
                  ·
                    rfl

theorem cell21_1969309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_1969309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969309 prefixEnd_1969309 := by exact prefixLift 1969309
  have htrace : WordTrace (prefixWord ++ tailWord_1969309) baseStart_1969309 baseEnd_1969309 := by
    simpa [prefixWord, tailWord_1969309, baseEnd_1969309] using wordTrace_append hprefix tailTrace_1969309
  have hstable : (prefixWord ++ tailWord_1969309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969309).length < 2 ^ (prefixWord ++ tailWord_1969309).sum := by decide
  have hdescent : baseEnd_1969309 < baseStart_1969309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969320 : List Nat := [2, 1, 18]
def baseStart_1969320 : Nat := 118140960795 + 1969320 * 2 ^ 59
def prefixEnd_1969320 : Nat := 4983230072969 + 3 ^ 40 * 1969320 * 2
def baseEnd_1969320 : Nat := 616496096639134436911

theorem tailTrace_1969320 : CollatzResearch.WordTrace tailWord_1969320 prefixEnd_1969320 616496096639134436911 := by
  unfold tailWord_1969320
  simp only [CollatzResearch.WordTrace]
  refine ⟨35913500612748723962132707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47884667483664965282843609 35913500612748723962132707)
  ·
    refine ⟨53870250919123085943199061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35913500612748723962132707 53870250919123085943199061)
    ·
      refine ⟨616496096639134436911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 53870250919123085943199061 616496096639134436911)
      ·
        rfl

theorem cell21_1969320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 18].length) (baseStart_1969320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969320 prefixEnd_1969320 := by exact prefixLift 1969320
  have htrace : WordTrace (prefixWord ++ tailWord_1969320) baseStart_1969320 baseEnd_1969320 := by
    simpa [prefixWord, tailWord_1969320, baseEnd_1969320] using wordTrace_append hprefix tailTrace_1969320
  have hstable : (prefixWord ++ tailWord_1969320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969320).length < 2 ^ (prefixWord ++ tailWord_1969320).sum := by decide
  have hdescent : baseEnd_1969320 < baseStart_1969320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969337 : List Nat := [1, 2, 1, 4, 1, 3, 3, 6]
def baseStart_1969337 : Nat := 118140960795 + 1969337 * 2 ^ 59
def prefixEnd_1969337 : Nat := 4983230072969 + 3 ^ 40 * 1969337 * 2
def baseEnd_1969337 : Nat := 149809844693846917574917

theorem tailTrace_1969337 : CollatzResearch.WordTrace tailWord_1969337 prefixEnd_1969337 149809844693846917574917 := by
  unfold tailWord_1969337
  simp only [CollatzResearch.WordTrace]
  refine ⟨71827621266435859827634265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47885080844290573218422843 71827621266435859827634265)
  ·
    refine ⟨53870715949826894870725699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71827621266435859827634265 53870715949826894870725699)
    ·
      refine ⟨80806073924740342306088549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53870715949826894870725699 80806073924740342306088549)
      ·
        refine ⟨15151138860888814182391603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80806073924740342306088549 15151138860888814182391603)
        ·
          refine ⟨22726708291333221273587405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151138860888814182391603 22726708291333221273587405)
          ·
            refine ⟨8522515609249957977595277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22726708291333221273587405 8522515609249957977595277)
            ·
              refine ⟨3195943353468734241598229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8522515609249957977595277 3195943353468734241598229)
              ·
                refine ⟨149809844693846917574917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3195943353468734241598229 149809844693846917574917)
                ·
                  rfl

theorem cell21_1969337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_1969337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969337 prefixEnd_1969337 := by exact prefixLift 1969337
  have htrace : WordTrace (prefixWord ++ tailWord_1969337) baseStart_1969337 baseEnd_1969337 := by
    simpa [prefixWord, tailWord_1969337, baseEnd_1969337] using wordTrace_append hprefix tailTrace_1969337
  have hstable : (prefixWord ++ tailWord_1969337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969337).length < 2 ^ (prefixWord ++ tailWord_1969337).sum := by decide
  have hdescent : baseEnd_1969337 < baseStart_1969337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969354 : List Nat := [3, 1, 2, 1, 3, 3, 3, 5]
def baseStart_1969354 : Nat := 118140960795 + 1969354 * 2 ^ 59
def prefixEnd_1969354 : Nat := 4983230072969 + 3 ^ 40 * 1969354 * 2
def baseEnd_1969354 : Nat := 149811137904384166980461

theorem tailTrace_1969354 : CollatzResearch.WordTrace tailWord_1969354 prefixEnd_1969354 149811137904384166980461 := by
  unfold tailWord_1969354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17957060326843567932750779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47885494204916181154002077 17957060326843567932750779)
  ·
    refine ⟨26935590490265351899126169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17957060326843567932750779 26935590490265351899126169)
    ·
      refine ⟨20201692867699013924344627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26935590490265351899126169 20201692867699013924344627)
      ·
        refine ⟨30302539301548520886516941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20201692867699013924344627 30302539301548520886516941)
        ·
          refine ⟨11363452238080695332443853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30302539301548520886516941 11363452238080695332443853)
          ·
            refine ⟨4261294589280260749666445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11363452238080695332443853 4261294589280260749666445)
            ·
              refine ⟨1597985470980097781124917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4261294589280260749666445 1597985470980097781124917)
              ·
                refine ⟨149811137904384166980461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1597985470980097781124917 149811137904384166980461)
                ·
                  rfl

theorem cell21_1969354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_1969354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969354 prefixEnd_1969354 := by exact prefixLift 1969354
  have htrace : WordTrace (prefixWord ++ tailWord_1969354) baseStart_1969354 baseEnd_1969354 := by
    simpa [prefixWord, tailWord_1969354, baseEnd_1969354] using wordTrace_append hprefix tailTrace_1969354
  have hstable : (prefixWord ++ tailWord_1969354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969354).length < 2 ^ (prefixWord ++ tailWord_1969354).sum := by decide
  have hdescent : baseEnd_1969354 < baseStart_1969354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969472 : List Nat := [2, 1, 1, 2, 2, 1, 3, 9]
def baseStart_1969472 : Nat := 118140960795 + 1969472 * 2 ^ 59
def prefixEnd_1969472 : Nat := 4983230072969 + 3 ^ 40 * 1969472 * 2
def baseEnd_1969472 : Nat := 149820114306936839324825

theorem tailTrace_1969472 : CollatzResearch.WordTrace tailWord_1969472 prefixEnd_1969472 149820114306936839324825 := by
  unfold tailWord_1969472
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916272560473388941899335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47888363413964518589199113 35916272560473388941899335)
  ·
    refine ⟨53874408840710083412849003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35916272560473388941899335 53874408840710083412849003)
    ·
      refine ⟨80811613261065125119273505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53874408840710083412849003 80811613261065125119273505)
      ·
        refine ⟨60608709945798843839455129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80811613261065125119273505 60608709945798843839455129)
        ·
          refine ⟨45456532459349132879591347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60608709945798843839455129 45456532459349132879591347)
          ·
            refine ⟨68184798689023699319387021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45456532459349132879591347 68184798689023699319387021)
            ·
              refine ⟨25569299508383887244770133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68184798689023699319387021 25569299508383887244770133)
              ·
                refine ⟨149820114306936839324825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25569299508383887244770133 149820114306936839324825)
                ·
                  rfl

theorem cell21_1969472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_1969472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969472 prefixEnd_1969472 := by exact prefixLift 1969472
  have htrace : WordTrace (prefixWord ++ tailWord_1969472) baseStart_1969472 baseEnd_1969472 := by
    simpa [prefixWord, tailWord_1969472, baseEnd_1969472] using wordTrace_append hprefix tailTrace_1969472
  have hstable : (prefixWord ++ tailWord_1969472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969472).length < 2 ^ (prefixWord ++ tailWord_1969472).sum := by decide
  have hdescent : baseEnd_1969472 < baseStart_1969472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969503 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_1969503 : Nat := 118140960795 + 1969503 * 2 ^ 59
def prefixEnd_1969503 : Nat := 4983230072969 + 3 ^ 40 * 1969503 * 2
def baseEnd_1969503 : Nat := 449467417543161352957745

theorem tailTrace_1969503 : CollatzResearch.WordTrace tailWord_1969503 prefixEnd_1969503 449467417543161352957745 := by
  unfold tailWord_1969503
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833675783834470178177163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47889117189222980118784775 71833675783834470178177163)
  ·
    refine ⟨107750513675751705267265745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71833675783834470178177163 107750513675751705267265745)
    ·
      refine ⟨80812885256813778950449309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107750513675751705267265745 80812885256813778950449309)
      ·
        refine ⟨30304831971305167106418491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80812885256813778950449309 30304831971305167106418491)
        ·
          refine ⟨45457247956957750659627737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30304831971305167106418491 45457247956957750659627737)
          ·
            refine ⟨34092935967718312994720803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45457247956957750659627737 34092935967718312994720803)
            ·
              refine ⟨51139403951577469492081205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34092935967718312994720803 51139403951577469492081205)
              ·
                refine ⟨4794319120460387764882613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51139403951577469492081205 4794319120460387764882613)
                ·
                  refine ⟨449467417543161352957745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794319120460387764882613 449467417543161352957745)
                  ·
                    rfl

theorem cell21_1969503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_1969503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969503 prefixEnd_1969503 := by exact prefixLift 1969503
  have htrace : WordTrace (prefixWord ++ tailWord_1969503) baseStart_1969503 baseEnd_1969503 := by
    simpa [prefixWord, tailWord_1969503, baseEnd_1969503] using wordTrace_append hprefix tailTrace_1969503
  have hstable : (prefixWord ++ tailWord_1969503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969503).length < 2 ^ (prefixWord ++ tailWord_1969503).sum := by decide
  have hdescent : baseEnd_1969503 < baseStart_1969503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969548 : List Nat := [2, 2, 1, 2, 1, 3, 10]
def baseStart_1969548 : Nat := 118140960795 + 1969548 * 2 ^ 59
def prefixEnd_1969548 : Nat := 4983230072969 + 3 ^ 40 * 1969548 * 2
def baseEnd_1969548 : Nat := 49941965239583474967517

theorem tailTrace_1969548 : CollatzResearch.WordTrace tailWord_1969548 prefixEnd_1969548 49941965239583474967517 := by
  unfold tailWord_1969548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35917658534335721431782649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47890211379114295242376865 35917658534335721431782649)
  ·
    refine ⟨26938243900751791073836987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35917658534335721431782649 26938243900751791073836987)
    ·
      refine ⟨40407365851127686610755481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26938243900751791073836987 40407365851127686610755481)
      ·
        refine ⟨30305524388345764958066611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40407365851127686610755481 30305524388345764958066611)
        ·
          refine ⟨45458286582518647437099917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30305524388345764958066611 45458286582518647437099917)
          ·
            refine ⟨17046857468444492788912469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45458286582518647437099917 17046857468444492788912469)
            ·
              refine ⟨49941965239583474967517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17046857468444492788912469 49941965239583474967517)
              ·
                rfl

theorem cell21_1969548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 10].length) (baseStart_1969548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969548 prefixEnd_1969548 := by exact prefixLift 1969548
  have htrace : WordTrace (prefixWord ++ tailWord_1969548) baseStart_1969548 baseEnd_1969548 := by
    simpa [prefixWord, tailWord_1969548, baseEnd_1969548] using wordTrace_append hprefix tailTrace_1969548
  have hstable : (prefixWord ++ tailWord_1969548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969548).length < 2 ^ (prefixWord ++ tailWord_1969548).sum := by decide
  have hdescent : baseEnd_1969548 < baseStart_1969548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969554 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1969554 : Nat := 118140960795 + 1969554 * 2 ^ 59
def prefixEnd_1969554 : Nat := 4983230072969 + 3 ^ 40 * 1969554 * 2
def baseEnd_1969554 : Nat := 449479056437996597607641

theorem tailTrace_1969554 : CollatzResearch.WordTrace tailWord_1969554 prefixEnd_1969554 449479056437996597607641 := by
  unfold tailWord_1969554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17958883976662426472070929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47890357271099803925522477 17958883976662426472070929)
  ·
    refine ⟨13469162982496819854053197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17958883976662426472070929 13469162982496819854053197)
    ·
      refine ⟨5050936118436307445269949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13469162982496819854053197 5050936118436307445269949)
      ·
        refine ⟨1894101044413615291976231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5050936118436307445269949 1894101044413615291976231)
        ·
          refine ⟨2841151566620422937964347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894101044413615291976231 2841151566620422937964347)
          ·
            refine ⟨4261727349930634406946521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841151566620422937964347 4261727349930634406946521)
            ·
              refine ⟨3196295512447975805209891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261727349930634406946521 3196295512447975805209891)
              ·
                refine ⟨4794443268671963707814837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196295512447975805209891 4794443268671963707814837)
                ·
                  refine ⟨449479056437996597607641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4794443268671963707814837 449479056437996597607641)
                  ·
                    rfl

theorem cell21_1969554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1969554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969554 prefixEnd_1969554 := by exact prefixLift 1969554
  have htrace : WordTrace (prefixWord ++ tailWord_1969554) baseStart_1969554 baseEnd_1969554 := by
    simpa [prefixWord, tailWord_1969554, baseEnd_1969554] using wordTrace_append hprefix tailTrace_1969554
  have hstable : (prefixWord ++ tailWord_1969554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969554).length < 2 ^ (prefixWord ++ tailWord_1969554).sum := by decide
  have hdescent : baseEnd_1969554 < baseStart_1969554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969610 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1969610 : Nat := 118140960795 + 1969610 * 2 ^ 59
def prefixEnd_1969610 : Nat := 4983230072969 + 3 ^ 40 * 1969610 * 2
def baseEnd_1969610 : Nat := 449491836400952944674193

theorem tailTrace_1969610 : CollatzResearch.WordTrace tailWord_1969610 prefixEnd_1969610 449491836400952944674193 := by
  unfold tailWord_1969610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17959394598611706863080571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47891718929631218301548189 17959394598611706863080571)
  ·
    refine ⟨26939091897917560294620857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17959394598611706863080571 26939091897917560294620857)
    ·
      refine ⟨20204318923438170220965643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26939091897917560294620857 20204318923438170220965643)
      ·
        refine ⟨30306478385157255331448465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20204318923438170220965643 30306478385157255331448465)
        ·
          refine ⟨22729858788867941498586349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30306478385157255331448465 22729858788867941498586349)
          ·
            refine ⟨8523697045825478061969881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22729858788867941498586349 8523697045825478061969881)
            ·
              refine ⟨6392772784369108546477411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8523697045825478061969881 6392772784369108546477411)
              ·
                refine ⟨9589159176553662819716117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6392772784369108546477411 9589159176553662819716117)
                ·
                  refine ⟨449491836400952944674193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9589159176553662819716117 449491836400952944674193)
                  ·
                    rfl

theorem cell21_1969610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1969610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969610 prefixEnd_1969610 := by exact prefixLift 1969610
  have htrace : WordTrace (prefixWord ++ tailWord_1969610) baseStart_1969610 baseEnd_1969610 := by
    simpa [prefixWord, tailWord_1969610, baseEnd_1969610] using wordTrace_append hprefix tailTrace_1969610
  have hstable : (prefixWord ++ tailWord_1969610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969610).length < 2 ^ (prefixWord ++ tailWord_1969610).sum := by decide
  have hdescent : baseEnd_1969610 < baseStart_1969610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969624 : List Nat := [2, 1, 2, 2, 2, 1, 3, 8]
def baseStart_1969624 : Nat := 118140960795 + 1969624 * 2 ^ 59
def prefixEnd_1969624 : Nat := 4983230072969 + 3 ^ 40 * 1969624 * 2
def baseEnd_1969624 : Nat := 149831677130564010480277

theorem tailTrace_1969624 : CollatzResearch.WordTrace tailWord_1969624 prefixEnd_1969624 149831677130564010480277 := by
  unfold tailWord_1969624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35919044508198053921665963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47892059344264071895554617 35919044508198053921665963)
  ·
    refine ⟨53878566762297080882498945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35919044508198053921665963 53878566762297080882498945)
    ·
      refine ⟨40408925071722810661874209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53878566762297080882498945 40408925071722810661874209)
      ·
        refine ⟨30306693803792107996405657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40408925071722810661874209 30306693803792107996405657)
        ·
          refine ⟨22730020352844080997304243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30306693803792107996405657 22730020352844080997304243)
          ·
            refine ⟨34095030529266121495956365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22730020352844080997304243 34095030529266121495956365)
            ·
              refine ⟨12785636448474795560983637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34095030529266121495956365 12785636448474795560983637)
              ·
                refine ⟨149831677130564010480277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12785636448474795560983637 149831677130564010480277)
                ·
                  rfl

theorem cell21_1969624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_1969624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969624 prefixEnd_1969624 := by exact prefixLift 1969624
  have htrace : WordTrace (prefixWord ++ tailWord_1969624) baseStart_1969624 baseEnd_1969624 := by
    simpa [prefixWord, tailWord_1969624, baseEnd_1969624] using wordTrace_append hprefix tailTrace_1969624
  have hstable : (prefixWord ++ tailWord_1969624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969624).length < 2 ^ (prefixWord ++ tailWord_1969624).sum := by decide
  have hdescent : baseEnd_1969624 < baseStart_1969624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969765 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 3]
def baseStart_1969765 : Nat := 118140960795 + 1969765 * 2 ^ 59
def prefixEnd_1969765 : Nat := 4983230072969 + 3 ^ 40 * 1969765 * 2
def baseEnd_1969765 : Nat := 449527209512707119590543

theorem tailTrace_1969765 : CollatzResearch.WordTrace tailWord_1969765 prefixEnd_1969765 449527209512707119590543 := by
  unfold tailWord_1969765
  simp only [CollatzResearch.WordTrace]
  refine ⟨71843231708885288924214749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47895487805923525949476499 71843231708885288924214749)
  ·
    refine ⟨26941211890831983346580531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71843231708885288924214749 26941211890831983346580531)
    ·
      refine ⟨40411817836247975019870797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26941211890831983346580531 40411817836247975019870797)
      ·
        refine ⟨15154431688592990632451549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40411817836247975019870797 15154431688592990632451549)
        ·
          refine ⟨5682911883222371487169331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15154431688592990632451549 5682911883222371487169331)
          ·
            refine ⟨8524367824833557230753997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682911883222371487169331 8524367824833557230753997)
            ·
              refine ⟨3196637934312583961532749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8524367824833557230753997 3196637934312583961532749)
              ·
                refine ⟨1198739225367218985574781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3196637934312583961532749 1198739225367218985574781)
                ·
                  refine ⟨449527209512707119590543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198739225367218985574781 449527209512707119590543)
                  ·
                    rfl

theorem cell21_1969765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_1969765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969765 prefixEnd_1969765 := by exact prefixLift 1969765
  have htrace : WordTrace (prefixWord ++ tailWord_1969765) baseStart_1969765 baseEnd_1969765 := by
    simpa [prefixWord, tailWord_1969765, baseEnd_1969765] using wordTrace_append hprefix tailTrace_1969765
  have hstable : (prefixWord ++ tailWord_1969765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969765).length < 2 ^ (prefixWord ++ tailWord_1969765).sum := by decide
  have hdescent : baseEnd_1969765 < baseStart_1969765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969776 : List Nat := [2, 1, 1, 1, 6, 1, 9]
def baseStart_1969776 : Nat := 118140960795 + 1969776 * 2 ^ 59
def prefixEnd_1969776 : Nat := 4983230072969 + 3 ^ 40 * 1969776 * 2
def baseEnd_1969776 : Nat := 49947746651397060545243

theorem tailTrace_1969776 : CollatzResearch.WordTrace tailWord_1969776 prefixEnd_1969776 49947746651397060545243 := by
  unfold tailWord_1969776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921816455922718901432591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47895755274563625201910121 35921816455922718901432591)
  ·
    refine ⟨53882724683884078352148887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35921816455922718901432591 53882724683884078352148887)
    ·
      refine ⟨80824087025826117528223331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53882724683884078352148887 80824087025826117528223331)
      ·
        refine ⟨121236130538739176292334997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80824087025826117528223331 121236130538739176292334997)
        ·
          refine ⟨5682943619003398888703203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121236130538739176292334997 5682943619003398888703203)
          ·
            refine ⟨8524415428505098333054805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5682943619003398888703203 8524415428505098333054805)
            ·
              refine ⟨49947746651397060545243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8524415428505098333054805 49947746651397060545243)
              ·
                rfl

theorem cell21_1969776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 9].length) (baseStart_1969776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969776 prefixEnd_1969776 := by exact prefixLift 1969776
  have htrace : WordTrace (prefixWord ++ tailWord_1969776) baseStart_1969776 baseEnd_1969776 := by
    simpa [prefixWord, tailWord_1969776, baseEnd_1969776] using wordTrace_append hprefix tailTrace_1969776
  have hstable : (prefixWord ++ tailWord_1969776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969776).length < 2 ^ (prefixWord ++ tailWord_1969776).sum := by decide
  have hdescent : baseEnd_1969776 < baseStart_1969776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969793 : List Nat := [1, 2, 4, 2, 1, 3, 2, 6]
def baseStart_1969793 : Nat := 118140960795 + 1969793 * 2 ^ 59
def prefixEnd_1969793 : Nat := 4983230072969 + 3 ^ 40 * 1969793 * 2
def baseEnd_1969793 : Nat := 149844533164728431041273

theorem tailTrace_1969793 : CollatzResearch.WordTrace tailWord_1969793 prefixEnd_1969793 149844533164728431041273 := by
  unfold tailWord_1969793
  simp only [CollatzResearch.WordTrace]
  refine ⟨71844252952783849706234033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47896168635189233137489355 71844252952783849706234033)
  ·
    refine ⟨53883189714587887279675525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71844252952783849706234033 53883189714587887279675525)
    ·
      refine ⟨10103098071485228864939161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53883189714587887279675525 10103098071485228864939161)
      ·
        refine ⟨7577323553613921648704371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10103098071485228864939161 7577323553613921648704371)
        ·
          refine ⟨11365985330420882473056557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577323553613921648704371 11365985330420882473056557)
          ·
            refine ⟨4262244498907830927396209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11365985330420882473056557 4262244498907830927396209)
            ·
              refine ⟨3196683374180873195547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4262244498907830927396209 3196683374180873195547157)
              ·
                refine ⟨149844533164728431041273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3196683374180873195547157 149844533164728431041273)
                ·
                  rfl

theorem cell21_1969793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 6].length) (baseStart_1969793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969793 prefixEnd_1969793 := by exact prefixLift 1969793
  have htrace : WordTrace (prefixWord ++ tailWord_1969793) baseStart_1969793 baseEnd_1969793 := by
    simpa [prefixWord, tailWord_1969793, baseEnd_1969793] using wordTrace_append hprefix tailTrace_1969793
  have hstable : (prefixWord ++ tailWord_1969793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969793).length < 2 ^ (prefixWord ++ tailWord_1969793).sum := by decide
  have hdescent : baseEnd_1969793 < baseStart_1969793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969900 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_1969900 : Nat := 118140960795 + 1969900 * 2 ^ 59
def prefixEnd_1969900 : Nat := 4983230072969 + 3 ^ 40 * 1969900 * 2
def baseEnd_1969900 : Nat := 449558018351976884840267

theorem tailTrace_1969900 : CollatzResearch.WordTrace tailWord_1969900 prefixEnd_1969900 449558018351976884840267 := by
  unfold tailWord_1969900
  simp only [CollatzResearch.WordTrace]
  refine ⟨35924077781698103490189577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47898770375597471320252769 35924077781698103490189577)
  ·
    refine ⟨26943058336273577617642183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35924077781698103490189577 26943058336273577617642183)
    ·
      refine ⟨40414587504410366426463275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26943058336273577617642183 40414587504410366426463275)
      ·
        refine ⟨60621881256615549639694913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40414587504410366426463275 60621881256615549639694913)
        ·
          refine ⟨45466410942461662229771185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60621881256615549639694913 45466410942461662229771185)
          ·
            refine ⟨34099808206846246672328389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45466410942461662229771185 34099808206846246672328389)
            ·
              refine ⟨6393714038783671251061573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34099808206846246672328389 6393714038783671251061573)
              ·
                refine ⟨1198821382271938359574045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6393714038783671251061573 1198821382271938359574045)
                ·
                  refine ⟨449558018351976884840267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198821382271938359574045 449558018351976884840267)
                  ·
                    rfl

theorem cell21_1969900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_1969900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969900 prefixEnd_1969900 := by exact prefixLift 1969900
  have htrace : WordTrace (prefixWord ++ tailWord_1969900) baseStart_1969900 baseEnd_1969900 := by
    simpa [prefixWord, tailWord_1969900, baseEnd_1969900] using wordTrace_append hprefix tailTrace_1969900
  have hstable : (prefixWord ++ tailWord_1969900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969900).length < 2 ^ (prefixWord ++ tailWord_1969900).sum := by decide
  have hdescent : baseEnd_1969900 < baseStart_1969900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969926 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1969926 : Nat := 118140960795 + 1969926 * 2 ^ 59
def prefixEnd_1969926 : Nat := 4983230072969 + 3 ^ 40 * 1969926 * 2
def baseEnd_1969926 : Nat := 449563951906206617406881

theorem tailTrace_1969926 : CollatzResearch.WordTrace tailWord_1969926 prefixEnd_1969926 449563951906206617406881 := by
  unfold tailWord_1969926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245284495665687919400801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47899402574201342280550421 2245284495665687919400801)
  ·
    refine ⟨1683963371749265939550601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2245284495665687919400801 1683963371749265939550601)
    ·
      refine ⟨1262972528811949454662951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1683963371749265939550601 1262972528811949454662951)
      ·
        refine ⟨1894458793217924181994427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262972528811949454662951 1894458793217924181994427)
        ·
          refine ⟨2841688189826886272991641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894458793217924181994427 2841688189826886272991641)
          ·
            refine ⟨2131266142370164704743731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2841688189826886272991641 2131266142370164704743731)
            ·
              refine ⟨3196899213555247057115597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131266142370164704743731 3196899213555247057115597)
              ·
                refine ⟨1198837205083217646418349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3196899213555247057115597 1198837205083217646418349)
                ·
                  refine ⟨449563951906206617406881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198837205083217646418349 449563951906206617406881)
                  ·
                    rfl

theorem cell21_1969926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1969926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969926 prefixEnd_1969926 := by exact prefixLift 1969926
  have htrace : WordTrace (prefixWord ++ tailWord_1969926) baseStart_1969926 baseEnd_1969926 := by
    simpa [prefixWord, tailWord_1969926, baseEnd_1969926] using wordTrace_append hprefix tailTrace_1969926
  have hstable : (prefixWord ++ tailWord_1969926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969926).length < 2 ^ (prefixWord ++ tailWord_1969926).sum := by decide
  have hdescent : baseEnd_1969926 < baseStart_1969926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969928 : List Nat := [2, 1, 3, 2, 2, 1, 3, 7]
def baseStart_1969928 : Nat := 118140960795 + 1969928 * 2 ^ 59
def prefixEnd_1969928 : Nat := 4983230072969 + 3 ^ 40 * 1969928 * 2
def baseEnd_1969928 : Nat := 149854802777818352791181

theorem tailTrace_1969928 : CollatzResearch.WordTrace tailWord_1969928 prefixEnd_1969928 149854802777818352791181 := by
  unfold tailWord_1969928
  simp only [CollatzResearch.WordTrace]
  refine ⟨35924588403647383881199219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47899451204863178508265625 35924588403647383881199219)
  ·
    refine ⟨53886882605471075821798829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35924588403647383881199219 53886882605471075821798829)
    ·
      refine ⟨20207580977051653433174561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53886882605471075821798829 20207580977051653433174561)
      ·
        refine ⟨15155685732788740074880921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20207580977051653433174561 15155685732788740074880921)
        ·
          refine ⟨11366764299591555056160691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15155685732788740074880921 11366764299591555056160691)
          ·
            refine ⟨17050146449387332584241037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366764299591555056160691 17050146449387332584241037)
            ·
              refine ⟨6393804918520249719090389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17050146449387332584241037 6393804918520249719090389)
              ·
                refine ⟨149854802777818352791181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6393804918520249719090389 149854802777818352791181)
                ·
                  rfl

theorem cell21_1969928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_1969928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1969928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1969928 prefixEnd_1969928 := by exact prefixLift 1969928
  have htrace : WordTrace (prefixWord ++ tailWord_1969928) baseStart_1969928 baseEnd_1969928 := by
    simpa [prefixWord, tailWord_1969928, baseEnd_1969928] using wordTrace_append hprefix tailTrace_1969928
  have hstable : (prefixWord ++ tailWord_1969928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969928).length < 2 ^ (prefixWord ++ tailWord_1969928).sum := by decide
  have hdescent : baseEnd_1969928 < baseStart_1969928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970004 : List Nat := [2, 4, 1, 1, 3, 10]
def baseStart_1970004 : Nat := 118140960795 + 1970004 * 2 ^ 59
def prefixEnd_1970004 : Nat := 4983230072969 + 3 ^ 40 * 1970004 * 2
def baseEnd_1970004 : Nat := 16651176021070215374323

theorem tailTrace_1970004 : CollatzResearch.WordTrace tailWord_1970004 prefixEnd_1970004 16651176021070215374323 := by
  unfold tailWord_1970004
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925974377509716371082533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47901299170012955161443377 35925974377509716371082533)
  ·
    refine ⟨6736120195783071819577975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35925974377509716371082533 6736120195783071819577975)
    ·
      refine ⟨10104180293674607729366963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736120195783071819577975 10104180293674607729366963)
      ·
        refine ⟨15156270440511911594050445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104180293674607729366963 15156270440511911594050445)
        ·
          refine ⟨5683601415191966847768917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15156270440511911594050445 5683601415191966847768917)
          ·
            refine ⟨16651176021070215374323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5683601415191966847768917 16651176021070215374323)
            ·
              rfl

theorem cell21_1970004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 10].length) (baseStart_1970004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970004 prefixEnd_1970004 := by exact prefixLift 1970004
  have htrace : WordTrace (prefixWord ++ tailWord_1970004) baseStart_1970004 baseEnd_1970004 := by
    simpa [prefixWord, tailWord_1970004, baseEnd_1970004] using wordTrace_append hprefix tailTrace_1970004
  have hstable : (prefixWord ++ tailWord_1970004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970004).length < 2 ^ (prefixWord ++ tailWord_1970004).sum := by decide
  have hdescent : baseEnd_1970004 < baseStart_1970004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970007 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_1970007 : Nat := 118140960795 + 1970007 * 2 ^ 59
def prefixEnd_1970007 : Nat := 4983230072969 + 3 ^ 40 * 1970007 * 2
def baseEnd_1970007 : Nat := 449582437209768476556715

theorem tailTrace_1970007 : CollatzResearch.WordTrace tailWord_1970007 prefixEnd_1970007 449582437209768476556715 := by
  unfold tailWord_1970007
  simp only [CollatzResearch.WordTrace]
  refine ⟨71852058174008564254524275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47901372116005709503016183 71852058174008564254524275)
  ·
    refine ⟨107778087261012846381786413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71852058174008564254524275 107778087261012846381786413)
    ·
      refine ⟨40416782722879817393169905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107778087261012846381786413 40416782722879817393169905)
      ·
        refine ⟨30312587042159863044877429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40416782722879817393169905 30312587042159863044877429)
        ·
          refine ⟨2841805035202487160457259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30312587042159863044877429 2841805035202487160457259)
          ·
            refine ⟨4262707552803730740685889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841805035202487160457259 4262707552803730740685889)
            ·
              refine ⟨3197030664602798055514417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4262707552803730740685889 3197030664602798055514417)
              ·
                refine ⟨2397772998452098541635813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197030664602798055514417 2397772998452098541635813)
                ·
                  refine ⟨449582437209768476556715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397772998452098541635813 449582437209768476556715)
                  ·
                    rfl

theorem cell21_1970007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_1970007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970007 prefixEnd_1970007 := by exact prefixLift 1970007
  have htrace : WordTrace (prefixWord ++ tailWord_1970007) baseStart_1970007 baseEnd_1970007 := by
    simpa [prefixWord, tailWord_1970007, baseEnd_1970007] using wordTrace_append hprefix tailTrace_1970007
  have hstable : (prefixWord ++ tailWord_1970007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970007).length < 2 ^ (prefixWord ++ tailWord_1970007).sum := by decide
  have hdescent : baseEnd_1970007 < baseStart_1970007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970052 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1970052 : Nat := 118140960795 + 1970052 * 2 ^ 59
def prefixEnd_1970052 : Nat := 4983230072969 + 3 ^ 40 * 1970052 * 2
def baseEnd_1970052 : Nat := 449592706822858398306623

theorem tailTrace_1970052 : CollatzResearch.WordTrace tailWord_1970052 prefixEnd_1970052 449592706822858398306623 := by
  unfold tailWord_1970052
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926849729422768469956205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47902466305897024626608273 35926849729422768469956205)
  ·
    refine ⟨13472568648533538176233577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35926849729422768469956205 13472568648533538176233577)
    ·
      refine ⟨10104426486400153632175183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13472568648533538176233577 10104426486400153632175183)
      ·
        refine ⟨15156639729600230448262775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104426486400153632175183 15156639729600230448262775)
        ·
          refine ⟨22734959594400345672394163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15156639729600230448262775 22734959594400345672394163)
          ·
            refine ⟨34102439391600518508591245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22734959594400345672394163 34102439391600518508591245)
            ·
              refine ⟨12788414771850194440721717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34102439391600518508591245 12788414771850194440721717)
              ·
                refine ⟨1198913884860955728817661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12788414771850194440721717 1198913884860955728817661)
                ·
                  refine ⟨449592706822858398306623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198913884860955728817661 449592706822858398306623)
                  ·
                    rfl

theorem cell21_1970052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1970052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970052 prefixEnd_1970052 := by exact prefixLift 1970052
  have htrace : WordTrace (prefixWord ++ tailWord_1970052) baseStart_1970052 baseEnd_1970052 := by
    simpa [prefixWord, tailWord_1970052, baseEnd_1970052] using wordTrace_append hprefix tailTrace_1970052
  have hstable : (prefixWord ++ tailWord_1970052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970052).length < 2 ^ (prefixWord ++ tailWord_1970052).sum := by decide
  have hdescent : baseEnd_1970052 < baseStart_1970052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970097 : List Nat := [1, 2, 2, 4, 2, 1, 4, 5]
def baseStart_1970097 : Nat := 118140960795 + 1970097 * 2 ^ 59
def prefixEnd_1970097 : Nat := 4983230072969 + 3 ^ 40 * 1970097 * 2
def baseEnd_1970097 : Nat := 149867658811982773352177

theorem tailTrace_1970097 : CollatzResearch.WordTrace tailWord_1970097 prefixEnd_1970097 149867658811982773352177 := by
  unfold tailWord_1970097
  simp only [CollatzResearch.WordTrace]
  refine ⟨71855340743682509625300545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47903560495788339750200363 71855340743682509625300545)
  ·
    refine ⟨53891505557761882218975409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71855340743682509625300545 53891505557761882218975409)
    ·
      refine ⟨40418629168321411664231557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53891505557761882218975409 40418629168321411664231557)
      ·
        refine ⟨7578492969060264687043417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40418629168321411664231557 7578492969060264687043417)
        ·
          refine ⟨5683869726795198515282563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7578492969060264687043417 5683869726795198515282563)
          ·
            refine ⟨8525804590192797772923845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683869726795198515282563 8525804590192797772923845)
            ·
              refine ⟨1598588360661149582423221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8525804590192797772923845 1598588360661149582423221)
              ·
                refine ⟨149867658811982773352177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1598588360661149582423221 149867658811982773352177)
                ·
                  rfl

theorem cell21_1970097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 5].length) (baseStart_1970097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970097 prefixEnd_1970097 := by exact prefixLift 1970097
  have htrace : WordTrace (prefixWord ++ tailWord_1970097) baseStart_1970097 baseEnd_1970097 := by
    simpa [prefixWord, tailWord_1970097, baseEnd_1970097] using wordTrace_append hprefix tailTrace_1970097
  have hstable : (prefixWord ++ tailWord_1970097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970097).length < 2 ^ (prefixWord ++ tailWord_1970097).sum := by decide
  have hdescent : baseEnd_1970097 < baseStart_1970097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970134 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1970134 : Nat := 118140960795 + 1970134 * 2 ^ 59
def prefixEnd_1970134 : Nat := 4983230072969 + 3 ^ 40 * 1970134 * 2
def baseEnd_1970134 : Nat := 449611420340044477939789

theorem tailTrace_1970134 : CollatzResearch.WordTrace tailWord_1970134 prefixEnd_1970134 449611420340044477939789 := by
  unfold tailWord_1970134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491043140284279059024841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47904460163032309962931637 4491043140284279059024841)
  ·
    refine ⟨3368282355213209294268631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4491043140284279059024841 3368282355213209294268631)
    ·
      refine ⟨5052423532819813941402947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368282355213209294268631 5052423532819813941402947)
      ·
        refine ⟨7578635299229720912104421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5052423532819813941402947 7578635299229720912104421)
        ·
          refine ⟨1420994118605572671019579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7578635299229720912104421 1420994118605572671019579)
          ·
            refine ⟨2131491177908359006529369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420994118605572671019579 2131491177908359006529369)
            ·
              refine ⟨1598618383431269254897027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131491177908359006529369 1598618383431269254897027)
              ·
                refine ⟨2397927575146903882345541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598618383431269254897027 2397927575146903882345541)
                ·
                  refine ⟨449611420340044477939789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2397927575146903882345541 449611420340044477939789)
                  ·
                    rfl

theorem cell21_1970134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1970134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970134 prefixEnd_1970134 := by exact prefixLift 1970134
  have htrace : WordTrace (prefixWord ++ tailWord_1970134) baseStart_1970134 baseEnd_1970134 := by
    simpa [prefixWord, tailWord_1970134, baseEnd_1970134] using wordTrace_append hprefix tailTrace_1970134
  have hstable : (prefixWord ++ tailWord_1970134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970134).length < 2 ^ (prefixWord ++ tailWord_1970134).sum := by decide
  have hdescent : baseEnd_1970134 < baseStart_1970134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970232 : List Nat := [2, 1, 2, 1, 6, 1, 8]
def baseStart_1970232 : Nat := 118140960795 + 1970232 * 2 ^ 59
def prefixEnd_1970232 : Nat := 4983230072969 + 3 ^ 40 * 1970232 * 2
def baseEnd_1970232 : Nat := 49959309475024231700695

theorem tailTrace_1970232 : CollatzResearch.WordTrace tailWord_1970232 prefixEnd_1970232 49959309475024231700695 := by
  unfold tailWord_1970232
  simp only [CollatzResearch.WordTrace]
  refine ⟨35930132299096713840732475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47906843065462285120976633 35930132299096713840732475)
  ·
    refine ⟨53895198448645070761098713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35930132299096713840732475 53895198448645070761098713)
    ·
      refine ⟨40421398836483803070824035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53895198448645070761098713 40421398836483803070824035)
      ·
        refine ⟨60632098254725704606236053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40421398836483803070824035 60632098254725704606236053)
        ·
          refine ⟨2842129605690267403417315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60632098254725704606236053 2842129605690267403417315)
          ·
            refine ⟨4263194408535401105125973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842129605690267403417315 4263194408535401105125973)
            ·
              refine ⟨49959309475024231700695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4263194408535401105125973 49959309475024231700695)
              ·
                rfl

theorem cell21_1970232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 8].length) (baseStart_1970232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970232 prefixEnd_1970232 := by exact prefixLift 1970232
  have htrace : WordTrace (prefixWord ++ tailWord_1970232) baseStart_1970232 baseEnd_1970232 := by
    simpa [prefixWord, tailWord_1970232, baseEnd_1970232] using wordTrace_append hprefix tailTrace_1970232
  have hstable : (prefixWord ++ tailWord_1970232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970232).length < 2 ^ (prefixWord ++ tailWord_1970232).sum := by decide
  have hdescent : baseEnd_1970232 < baseStart_1970232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970277 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_1970277 : Nat := 118140960795 + 1970277 * 2 ^ 59
def prefixEnd_1970277 : Nat := 4983230072969 + 3 ^ 40 * 1970277 * 2
def baseEnd_1970277 : Nat := 449644054888308007056163

theorem tailTrace_1970277 : CollatzResearch.WordTrace tailWord_1970277 prefixEnd_1970277 449644054888308007056163 := by
  unfold tailWord_1970277
  simp only [CollatzResearch.WordTrace]
  refine ⟨71861905883030400366853085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47907937255353600244568723 71861905883030400366853085)
  ·
    refine ⟨26948214706136400137569907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71861905883030400366853085 26948214706136400137569907)
    ·
      refine ⟨40422322059204600206354861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26948214706136400137569907 40422322059204600206354861)
      ·
        refine ⟨15158370772201725077383073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40422322059204600206354861 15158370772201725077383073)
        ·
          refine ⟨11368778079151293808037305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15158370772201725077383073 11368778079151293808037305)
          ·
            refine ⟨8526583559363470356027979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368778079151293808037305 8526583559363470356027979)
            ·
              refine ⟨12789875339045205534041969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526583559363470356027979 12789875339045205534041969)
              ·
                refine ⟨9592406504283904150531477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12789875339045205534041969 9592406504283904150531477)
                ·
                  refine ⟨449644054888308007056163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9592406504283904150531477 449644054888308007056163)
                  ·
                    rfl

theorem cell21_1970277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_1970277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970277 prefixEnd_1970277 := by exact prefixLift 1970277
  have htrace : WordTrace (prefixWord ++ tailWord_1970277) baseStart_1970277 baseEnd_1970277 := by
    simpa [prefixWord, tailWord_1970277, baseEnd_1970277] using wordTrace_append hprefix tailTrace_1970277
  have hstable : (prefixWord ++ tailWord_1970277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970277).length < 2 ^ (prefixWord ++ tailWord_1970277).sum := by decide
  have hdescent : baseEnd_1970277 < baseStart_1970277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970294 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1970294 : Nat := 118140960795 + 1970294 * 2 ^ 59
def prefixEnd_1970294 : Nat := 4983230072969 + 3 ^ 40 * 1970294 * 2
def baseEnd_1970294 : Nat := 449647934519919755272795

theorem tailTrace_1970294 : CollatzResearch.WordTrace tailWord_1970294 prefixEnd_1970294 449647934519919755272795 := by
  unfold tailWord_1970294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491407870248050766888871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47908350615979208180147957 4491407870248050766888871)
  ·
    refine ⟨6737111805372076150333307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491407870248050766888871 6737111805372076150333307)
    ·
      refine ⟨10105667708058114225499961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6737111805372076150333307 10105667708058114225499961)
      ·
        refine ⟨7579250781043585669124971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10105667708058114225499961 7579250781043585669124971)
        ·
          refine ⟨11368876171565378503687457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7579250781043585669124971 11368876171565378503687457)
          ·
            refine ⟨8526657128674033877765593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368876171565378503687457 8526657128674033877765593)
            ·
              refine ⟨6394992846505525408324195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8526657128674033877765593 6394992846505525408324195)
              ·
                refine ⟨9592489269758288112486293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394992846505525408324195 9592489269758288112486293)
                ·
                  refine ⟨449647934519919755272795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9592489269758288112486293 449647934519919755272795)
                  ·
                    rfl

theorem cell21_1970294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1970294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970294 prefixEnd_1970294 := by exact prefixLift 1970294
  have htrace : WordTrace (prefixWord ++ tailWord_1970294) baseStart_1970294 baseEnd_1970294 := by
    simpa [prefixWord, tailWord_1970294, baseEnd_1970294] using wordTrace_append hprefix tailTrace_1970294
  have hstable : (prefixWord ++ tailWord_1970294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970294).length < 2 ^ (prefixWord ++ tailWord_1970294).sum := by decide
  have hdescent : baseEnd_1970294 < baseStart_1970294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970297 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 3]
def baseStart_1970297 : Nat := 118140960795 + 1970297 * 2 ^ 59
def prefixEnd_1970297 : Nat := 4983230072969 + 3 ^ 40 * 1970297 * 2
def baseEnd_1970297 : Nat := 449648619160792416722789

theorem tailTrace_1970297 : CollatzResearch.WordTrace tailWord_1970297 prefixEnd_1970297 449648619160792416722789 := by
  unfold tailWord_1970297
  simp only [CollatzResearch.WordTrace]
  refine ⟨71862635342957943782581145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47908423561971962521720763 71862635342957943782581145)
  ·
    refine ⟨53896976507218457836935859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71862635342957943782581145 53896976507218457836935859)
    ·
      refine ⟨80845464760827686755403789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53896976507218457836935859 80845464760827686755403789)
      ·
        refine ⟨30317049285310382533276421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80845464760827686755403789 30317049285310382533276421)
        ·
          refine ⟨5684446740995696724989329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30317049285310382533276421 5684446740995696724989329)
          ·
            refine ⟨4263335055746772543741997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5684446740995696724989329 4263335055746772543741997)
            ·
              refine ⟨1598750645905039703903249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4263335055746772543741997 1598750645905039703903249)
              ·
                refine ⟨1199062984428779777927437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598750645905039703903249 1199062984428779777927437)
                ·
                  refine ⟨449648619160792416722789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199062984428779777927437 449648619160792416722789)
                  ·
                    rfl

theorem cell21_1970297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_1970297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970297 prefixEnd_1970297 := by exact prefixLift 1970297
  have htrace : WordTrace (prefixWord ++ tailWord_1970297) baseStart_1970297 baseEnd_1970297 := by
    simpa [prefixWord, tailWord_1970297, baseEnd_1970297] using wordTrace_append hprefix tailTrace_1970297
  have hstable : (prefixWord ++ tailWord_1970297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970297).length < 2 ^ (prefixWord ++ tailWord_1970297).sum := by decide
  have hdescent : baseEnd_1970297 < baseStart_1970297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970308 : List Nat := [2, 3, 2, 1, 2, 1, 4, 6]
def baseStart_1970308 : Nat := 118140960795 + 1970308 * 2 ^ 59
def prefixEnd_1970308 : Nat := 4983230072969 + 3 ^ 40 * 1970308 * 2
def baseEnd_1970308 : Nat := 149883709836886280679811

theorem tailTrace_1970308 : CollatzResearch.WordTrace tailWord_1970308 prefixEnd_1970308 149883709836886280679811 := by
  unfold tailWord_1970308
  simp only [CollatzResearch.WordTrace]
  refine ⟨35931518272959046330615789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47908691030612061774154385 35931518272959046330615789)
  ·
    refine ⟨13474319352359642373980921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35931518272959046330615789 13474319352359642373980921)
    ·
      refine ⟨10105739514269731780485691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13474319352359642373980921 10105739514269731780485691)
      ·
        refine ⟨15158609271404597670728537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10105739514269731780485691 15158609271404597670728537)
        ·
          refine ⟨11368956953553448253046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15158609271404597670728537 11368956953553448253046403)
          ·
            refine ⟨17053435430330172379569605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11368956953553448253046403 17053435430330172379569605)
            ·
              refine ⟨3197519143186907321169301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17053435430330172379569605 3197519143186907321169301)
              ·
                refine ⟨149883709836886280679811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3197519143186907321169301 149883709836886280679811)
                ·
                  rfl

theorem cell21_1970308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_1970308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970308 prefixEnd_1970308 := by exact prefixLift 1970308
  have htrace : WordTrace (prefixWord ++ tailWord_1970308) baseStart_1970308 baseEnd_1970308 := by
    simpa [prefixWord, tailWord_1970308, baseEnd_1970308] using wordTrace_append hprefix tailTrace_1970308
  have hstable : (prefixWord ++ tailWord_1970308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970308).length < 2 ^ (prefixWord ++ tailWord_1970308).sum := by decide
  have hdescent : baseEnd_1970308 < baseStart_1970308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970390 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1970390 : Nat := 118140960795 + 1970390 * 2 ^ 59
def prefixEnd_1970390 : Nat := 4983230072969 + 3 ^ 40 * 1970390 * 2
def baseEnd_1970390 : Nat := 449669843027844921672599

theorem tailTrace_1970390 : CollatzResearch.WordTrace tailWord_1970390 prefixEnd_1970390 449669843027844921672599 := by
  unfold tailWord_1970390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491626708226313791607289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47910684887747347110477749 4491626708226313791607289)
  ·
    refine ⟨3368720031169735343705467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4491626708226313791607289 3368720031169735343705467)
    ·
      refine ⟨5053080046754603015558201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368720031169735343705467 5053080046754603015558201)
      ·
        refine ⟨3789810035065952261668651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5053080046754603015558201 3789810035065952261668651)
        ·
          refine ⟨5684715052598928392502977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789810035065952261668651 5684715052598928392502977)
          ·
            refine ⟨4263536289449196294377233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5684715052598928392502977 4263536289449196294377233)
            ·
              refine ⟨3197652217086897220782925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263536289449196294377233 3197652217086897220782925)
              ·
                refine ⟨1199119581407586457793597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3197652217086897220782925 1199119581407586457793597)
                ·
                  refine ⟨449669843027844921672599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199119581407586457793597 449669843027844921672599)
                  ·
                    rfl

theorem cell21_1970390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1970390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970390 prefixEnd_1970390 := by exact prefixLift 1970390
  have htrace : WordTrace (prefixWord ++ tailWord_1970390) baseStart_1970390 baseEnd_1970390 := by
    simpa [prefixWord, tailWord_1970390, baseEnd_1970390] using wordTrace_append hprefix tailTrace_1970390
  have hstable : (prefixWord ++ tailWord_1970390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970390).length < 2 ^ (prefixWord ++ tailWord_1970390).sum := by decide
  have hdescent : baseEnd_1970390 < baseStart_1970390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970415 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_1970415 : Nat := 118140960795 + 1970415 * 2 ^ 59
def prefixEnd_1970415 : Nat := 4983230072969 + 3 ^ 40 * 1970415 * 2
def baseEnd_1970415 : Nat := 449675548368450433755881

theorem tailTrace_1970415 : CollatzResearch.WordTrace tailWord_1970415 prefixEnd_1970415 449675548368450433755881 := by
  unfold tailWord_1970415
  simp only [CollatzResearch.WordTrace]
  refine ⟨71866939156530449935376699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47911292771020299956917799 71866939156530449935376699)
  ·
    refine ⟨107800408734795674903065049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71866939156530449935376699 107800408734795674903065049)
    ·
      refine ⟨80850306551096756177298787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107800408734795674903065049 80850306551096756177298787)
      ·
        refine ⟨121275459826645134265948181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80850306551096756177298787 121275459826645134265948181)
        ·
          refine ⟨5684787179373990668716321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121275459826645134265948181 5684787179373990668716321)
          ·
            refine ⟨4263590384530493001537241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5684787179373990668716321 4263590384530493001537241)
            ·
              refine ⟨3197692788397869751152931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4263590384530493001537241 3197692788397869751152931)
              ·
                refine ⟨4796539182596804626729397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197692788397869751152931 4796539182596804626729397)
                ·
                  refine ⟨449675548368450433755881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4796539182596804626729397 449675548368450433755881)
                  ·
                    rfl

theorem cell21_1970415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_1970415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970415 prefixEnd_1970415 := by exact prefixLift 1970415
  have htrace : WordTrace (prefixWord ++ tailWord_1970415) baseStart_1970415 baseEnd_1970415 := by
    simpa [prefixWord, tailWord_1970415, baseEnd_1970415] using wordTrace_append hprefix tailTrace_1970415
  have hstable : (prefixWord ++ tailWord_1970415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970415).length < 2 ^ (prefixWord ++ tailWord_1970415).sum := by decide
  have hdescent : baseEnd_1970415 < baseStart_1970415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970429 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1970429 : Nat := 118140960795 + 1970429 * 2 ^ 59
def prefixEnd_1970429 : Nat := 4983230072969 + 3 ^ 40 * 1970429 * 2
def baseEnd_1970429 : Nat := 449678743359189520522519

theorem tailTrace_1970429 : CollatzResearch.WordTrace tailWord_1970429 prefixEnd_1970429 449678743359189520522519 := by
  unfold tailWord_1970429
  simp only [CollatzResearch.WordTrace]
  refine ⟨71867449778479730326386341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47911633185653153550924227 71867449778479730326386341)
  ·
    refine ⟨13475146833464949436197439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71867449778479730326386341 13475146833464949436197439)
    ·
      refine ⟨20212720250197424154296159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13475146833464949436197439 20212720250197424154296159)
      ·
        refine ⟨30319080375296136231444239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212720250197424154296159 30319080375296136231444239)
        ·
          refine ⟨45478620562944204347166359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30319080375296136231444239 45478620562944204347166359)
          ·
            refine ⟨68217930844416306520749539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45478620562944204347166359 68217930844416306520749539)
            ·
              refine ⟨102326896266624459781124309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68217930844416306520749539 102326896266624459781124309)
              ·
                refine ⟨2398286631249010776120101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102326896266624459781124309 2398286631249010776120101)
                ·
                  refine ⟨449678743359189520522519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398286631249010776120101 449678743359189520522519)
                  ·
                    rfl

theorem cell21_1970429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1970429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970429 prefixEnd_1970429 := by exact prefixLift 1970429
  have htrace : WordTrace (prefixWord ++ tailWord_1970429) baseStart_1970429 baseEnd_1970429 := by
    simpa [prefixWord, tailWord_1970429, baseEnd_1970429] using wordTrace_append hprefix tailTrace_1970429
  have hstable : (prefixWord ++ tailWord_1970429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970429).length < 2 ^ (prefixWord ++ tailWord_1970429).sum := by decide
  have hdescent : baseEnd_1970429 < baseStart_1970429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970443 : List Nat := [1, 1, 1, 1, 5, 2, 3, 7]
def baseStart_1970443 : Nat := 118140960795 + 1970443 * 2 ^ 59
def prefixEnd_1970443 : Nat := 4983230072969 + 3 ^ 40 * 1970443 * 2
def baseEnd_1970443 : Nat := 149893979449976202429719

theorem tailTrace_1970443 : CollatzResearch.WordTrace tailWord_1970443 prefixEnd_1970443 149893979449976202429719 := by
  unfold tailWord_1970443
  simp only [CollatzResearch.WordTrace]
  refine ⟨71867960400429010717395983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47911973600286007144930655 71867960400429010717395983)
  ·
    refine ⟨107801940600643516076093975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71867960400429010717395983 107801940600643516076093975)
    ·
      refine ⟨161702910900965274114140963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107801940600643516076093975 161702910900965274114140963)
      ·
        refine ⟨242554366351447911171211445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161702910900965274114140963 242554366351447911171211445)
        ·
          refine ⟨22739471845448241672301073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 242554366351447911171211445 22739471845448241672301073)
          ·
            refine ⟨17054603884086181254225805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22739471845448241672301073 17054603884086181254225805)
            ·
              refine ⟨6395476456532317970334677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17054603884086181254225805 6395476456532317970334677)
              ·
                refine ⟨149893979449976202429719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6395476456532317970334677 149893979449976202429719)
                ·
                  rfl

theorem cell21_1970443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_1970443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970443 prefixEnd_1970443 := by exact prefixLift 1970443
  have htrace : WordTrace (prefixWord ++ tailWord_1970443) baseStart_1970443 baseEnd_1970443 := by
    simpa [prefixWord, tailWord_1970443, baseEnd_1970443] using wordTrace_append hprefix tailTrace_1970443
  have hstable : (prefixWord ++ tailWord_1970443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970443).length < 2 ^ (prefixWord ++ tailWord_1970443).sum := by decide
  have hdescent : baseEnd_1970443 < baseStart_1970443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970536 : List Nat := [2, 1, 4, 2, 2, 1, 3, 6]
def baseStart_1970536 : Nat := 118140960795 + 1970536 * 2 ^ 59
def prefixEnd_1970536 : Nat := 4983230072969 + 3 ^ 40 * 1970536 * 2
def baseEnd_1970536 : Nat := 149901054072327037412989

theorem tailTrace_1970536 : CollatzResearch.WordTrace tailWord_1970536 prefixEnd_1970536 149901054072327037412989 := by
  unfold tailWord_1970536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35935676194546043800265731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47914234926061391733687641 35935676194546043800265731)
  ·
    refine ⟨53903514291819065700398597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35935676194546043800265731 53903514291819065700398597)
    ·
      refine ⟨10106908929716074818824737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53903514291819065700398597 10106908929716074818824737)
      ·
        refine ⟨7580181697287056114118553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10106908929716074818824737 7580181697287056114118553)
        ·
          refine ⟨5685136272965292085588915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7580181697287056114118553 5685136272965292085588915)
          ·
            refine ⟨8527704409447938128383373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685136272965292085588915 8527704409447938128383373)
            ·
              refine ⟨3197889153542976798143765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8527704409447938128383373 3197889153542976798143765)
              ·
                refine ⟨149901054072327037412989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3197889153542976798143765 149901054072327037412989)
                ·
                  rfl

theorem cell21_1970536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_1970536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970536 prefixEnd_1970536 := by exact prefixLift 1970536
  have htrace : WordTrace (prefixWord ++ tailWord_1970536) baseStart_1970536 baseEnd_1970536 := by
    simpa [prefixWord, tailWord_1970536, baseEnd_1970536] using wordTrace_append hprefix tailTrace_1970536
  have hstable : (prefixWord ++ tailWord_1970536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970536).length < 2 ^ (prefixWord ++ tailWord_1970536).sum := by decide
  have hdescent : baseEnd_1970536 < baseStart_1970536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970584 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_1970584 : Nat := 118140960795 + 1970584 * 2 ^ 59
def prefixEnd_1970584 : Nat := 4983230072969 + 3 ^ 40 * 1970584 * 2
def baseEnd_1970584 : Nat := 449714116470943695438869

theorem tailTrace_1970584 : CollatzResearch.WordTrace tailWord_1970584 prefixEnd_1970584 449714116470943695438869 := by
  unfold tailWord_1970584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35936551546459095899139403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47915402061945461198852537 35936551546459095899139403)
  ·
    refine ⟨53904827319688643848709105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35936551546459095899139403 53904827319688643848709105)
    ·
      refine ⟨40428620489766482886531829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53904827319688643848709105 40428620489766482886531829)
      ·
        refine ⟨3790183170915607770612359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40428620489766482886531829 3790183170915607770612359)
        ·
          refine ⟨5685274756373411655918539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790183170915607770612359 5685274756373411655918539)
          ·
            refine ⟨8527912134560117483877809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5685274756373411655918539 8527912134560117483877809)
            ·
              refine ⟨6395934100920088112908357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8527912134560117483877809 6395934100920088112908357)
              ·
                refine ⟨1199237643922516521170317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6395934100920088112908357 1199237643922516521170317)
                ·
                  refine ⟨449714116470943695438869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199237643922516521170317 449714116470943695438869)
                  ·
                    rfl

theorem cell21_1970584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_1970584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970584 prefixEnd_1970584 := by exact prefixLift 1970584
  have htrace : WordTrace (prefixWord ++ tailWord_1970584) baseStart_1970584 baseEnd_1970584 := by
    simpa [prefixWord, tailWord_1970584, baseEnd_1970584] using wordTrace_append hprefix tailTrace_1970584
  have hstable : (prefixWord ++ tailWord_1970584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970584).length < 2 ^ (prefixWord ++ tailWord_1970584).sum := by decide
  have hdescent : baseEnd_1970584 < baseStart_1970584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970657 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 4]
def baseStart_1970657 : Nat := 118140960795 + 1970657 * 2 ^ 59
def prefixEnd_1970657 : Nat := 4983230072969 + 3 ^ 40 * 1970657 * 2
def baseEnd_1970657 : Nat := 449730776065511790722053

theorem tailTrace_1970657 : CollatzResearch.WordTrace tailWord_1970657 prefixEnd_1970657 449730776065511790722053 := by
  unfold tailWord_1970657
  simp only [CollatzResearch.WordTrace]
  refine ⟨71875765621653725265686225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47917177081102483510457483 71875765621653725265686225)
  ·
    refine ⟨53906824216240293949264669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71875765621653725265686225 53906824216240293949264669)
    ·
      refine ⟨20215059081090110230974251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53906824216240293949264669 20215059081090110230974251)
      ·
        refine ⟨30322588621635165346461377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20215059081090110230974251 30322588621635165346461377)
        ·
          refine ⟨22741941466226374009846033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30322588621635165346461377 22741941466226374009846033)
          ·
            refine ⟨17056456099669780507384525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22741941466226374009846033 17056456099669780507384525)
            ·
              refine ⟨6396171037376167690269197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17056456099669780507384525 6396171037376167690269197)
              ·
                refine ⟨2398564139016062883850949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6396171037376167690269197 2398564139016062883850949)
                ·
                  refine ⟨449730776065511790722053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398564139016062883850949 449730776065511790722053)
                  ·
                    rfl

theorem cell21_1970657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_1970657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970657 prefixEnd_1970657 := by exact prefixLift 1970657
  have htrace : WordTrace (prefixWord ++ tailWord_1970657) baseStart_1970657 baseEnd_1970657 := by
    simpa [prefixWord, tailWord_1970657, baseEnd_1970657] using wordTrace_append hprefix tailTrace_1970657
  have hstable : (prefixWord ++ tailWord_1970657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970657).length < 2 ^ (prefixWord ++ tailWord_1970657).sum := by decide
  have hdescent : baseEnd_1970657 < baseStart_1970657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970818 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1970818 : Nat := 118140960795 + 1970818 * 2 ^ 59
def prefixEnd_1970818 : Nat := 4983230072969 + 3 ^ 40 * 1970818 * 2
def baseEnd_1970818 : Nat := 449767518459011288538391

theorem tailTrace_1970818 : CollatzResearch.WordTrace tailWord_1970818 prefixEnd_1970818 449767518459011288538391 := by
  unfold tailWord_1970818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970409443517612440574277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47921091849380299841531405 17970409443517612440574277)
  ·
    refine ⟨3369451770659552332607677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17970409443517612440574277 3369451770659552332607677)
    ·
      refine ⟨1263544413997332124727879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3369451770659552332607677 1263544413997332124727879)
      ·
        refine ⟨1895316620995998187091819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263544413997332124727879 1895316620995998187091819)
        ·
          refine ⟨2842974931493997280637729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895316620995998187091819 2842974931493997280637729)
          ·
            refine ⟨2132231198620497960478297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2842974931493997280637729 2132231198620497960478297)
            ·
              refine ⟨1599173398965373470358723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132231198620497960478297 1599173398965373470358723)
              ·
                refine ⟨2398760098448060205538085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599173398965373470358723 2398760098448060205538085)
                ·
                  refine ⟨449767518459011288538391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398760098448060205538085 449767518459011288538391)
                  ·
                    rfl

theorem cell21_1970818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1970818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970818 prefixEnd_1970818 := by exact prefixLift 1970818
  have htrace : WordTrace (prefixWord ++ tailWord_1970818) baseStart_1970818 baseEnd_1970818 := by
    simpa [prefixWord, tailWord_1970818, baseEnd_1970818] using wordTrace_append hprefix tailTrace_1970818
  have hstable : (prefixWord ++ tailWord_1970818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970818).length < 2 ^ (prefixWord ++ tailWord_1970818).sum := by decide
  have hdescent : baseEnd_1970818 < baseStart_1970818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970823 : List Nat := [1, 1, 4, 2, 1, 2, 4, 6]
def baseStart_1970823 : Nat := 118140960795 + 1970823 * 2 ^ 59
def prefixEnd_1970823 : Nat := 4983230072969 + 3 ^ 40 * 1970823 * 2
def baseEnd_1970823 : Nat := 149922886509044130318349

theorem tailTrace_1970823 : CollatzResearch.WordTrace tailWord_1970823 prefixEnd_1970823 149922886509044130318349 := by
  unfold tailWord_1970823
  simp only [CollatzResearch.WordTrace]
  refine ⟨71881820139052335616229123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47921213426034890410819415 71881820139052335616229123)
  ·
    refine ⟨107822730208578503424343685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71881820139052335616229123 107822730208578503424343685)
    ·
      refine ⟨20216761914108469392064441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107822730208578503424343685 20216761914108469392064441)
      ·
        refine ⟨15162571435581352044048331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216761914108469392064441 15162571435581352044048331)
        ·
          refine ⟨22743857153372028066072497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162571435581352044048331 22743857153372028066072497)
          ·
            refine ⟨17057892865029021049554373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22743857153372028066072497 17057892865029021049554373)
            ·
              refine ⟨3198354912192941446791445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17057892865029021049554373 3198354912192941446791445)
              ·
                refine ⟨149922886509044130318349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3198354912192941446791445 149922886509044130318349)
                ·
                  rfl

theorem cell21_1970823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 6].length) (baseStart_1970823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970823 prefixEnd_1970823 := by exact prefixLift 1970823
  have htrace : WordTrace (prefixWord ++ tailWord_1970823) baseStart_1970823 baseEnd_1970823 := by
    simpa [prefixWord, tailWord_1970823, baseEnd_1970823] using wordTrace_append hprefix tailTrace_1970823
  have hstable : (prefixWord ++ tailWord_1970823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970823).length < 2 ^ (prefixWord ++ tailWord_1970823).sum := by decide
  have hdescent : baseEnd_1970823 < baseStart_1970823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970826 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1970826 : Nat := 118140960795 + 1970826 * 2 ^ 59
def prefixEnd_1970826 : Nat := 4983230072969 + 3 ^ 40 * 1970826 * 2
def baseEnd_1970826 : Nat := 449769344168005052405041

theorem tailTrace_1970826 : CollatzResearch.WordTrace tailWord_1970826 prefixEnd_1970826 449769344168005052405041 := by
  unfold tailWord_1970826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970482389510366782147083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47921286372027644752392221 17970482389510366782147083)
  ·
    refine ⟨26955723584265550173220625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17970482389510366782147083 26955723584265550173220625)
    ·
      refine ⟨20216792688199162629915469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26955723584265550173220625 20216792688199162629915469)
      ·
        refine ⟨7581297258074685986218301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20216792688199162629915469 7581297258074685986218301)
        ·
          refine ⟨2842986471778007244831863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7581297258074685986218301 2842986471778007244831863)
          ·
            refine ⟨4264479707667010867247795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842986471778007244831863 4264479707667010867247795)
            ·
              refine ⟨6396719561500516300871693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264479707667010867247795 6396719561500516300871693)
              ·
                refine ⟨2398769835562693612826885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6396719561500516300871693 2398769835562693612826885)
                ·
                  refine ⟨449769344168005052405041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2398769835562693612826885 449769344168005052405041)
                  ·
                    rfl

theorem cell21_1970826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1970826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970826 prefixEnd_1970826 := by exact prefixLift 1970826
  have htrace : WordTrace (prefixWord ++ tailWord_1970826) baseStart_1970826 baseEnd_1970826 := by
    simpa [prefixWord, tailWord_1970826, baseEnd_1970826] using wordTrace_append hprefix tailTrace_1970826
  have hstable : (prefixWord ++ tailWord_1970826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970826).length < 2 ^ (prefixWord ++ tailWord_1970826).sum := by decide
  have hdescent : baseEnd_1970826 < baseStart_1970826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970930 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_1970930 : Nat := 118140960795 + 1970930 * 2 ^ 59
def prefixEnd_1970930 : Nat := 4983230072969 + 3 ^ 40 * 1970930 * 2
def baseEnd_1970930 : Nat := 449793078384923982671495

theorem tailTrace_1970930 : CollatzResearch.WordTrace tailWord_1970930 prefixEnd_1970930 449793078384923982671495 := by
  unfold tailWord_1970930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971430687416173222593561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47923815166443128593582829 17971430687416173222593561)
  ·
    refine ⟨13478573015562129916945171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17971430687416173222593561 13478573015562129916945171)
    ·
      refine ⟨20217859523343194875417757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13478573015562129916945171 20217859523343194875417757)
      ·
        refine ⟨7581697321253698078281659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20217859523343194875417757 7581697321253698078281659)
        ·
          refine ⟨11372545981880547117422489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7581697321253698078281659 11372545981880547117422489)
          ·
            refine ⟨8529409486410410338066867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11372545981880547117422489 8529409486410410338066867)
            ·
              refine ⟨12794114229615615507100301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529409486410410338066867 12794114229615615507100301)
              ·
                refine ⟨4797792836105855815162613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12794114229615615507100301 4797792836105855815162613)
                ·
                  refine ⟨449793078384923982671495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4797792836105855815162613 449793078384923982671495)
                  ·
                    rfl

theorem cell21_1970930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_1970930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970930 prefixEnd_1970930 := by exact prefixLift 1970930
  have htrace : WordTrace (prefixWord ++ tailWord_1970930) baseStart_1970930 baseEnd_1970930 := by
    simpa [prefixWord, tailWord_1970930, baseEnd_1970930] using wordTrace_append hprefix tailTrace_1970930
  have hstable : (prefixWord ++ tailWord_1970930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970930).length < 2 ^ (prefixWord ++ tailWord_1970930).sum := by decide
  have hdescent : baseEnd_1970930 < baseStart_1970930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970975 : List Nat := [1, 1, 2, 4, 2, 4, 7]
def baseStart_1970975 : Nat := 118140960795 + 1970975 * 2 ^ 59
def prefixEnd_1970975 : Nat := 4983230072969 + 3 ^ 40 * 1970975 * 2
def baseEnd_1970975 : Nat := 49978149777557100491267

theorem tailTrace_1970975 : CollatzResearch.WordTrace tailWord_1970975 prefixEnd_1970975 49978149777557100491267 := by
  unfold tailWord_1970975
  simp only [CollatzResearch.WordTrace]
  refine ⟨71887364034501665575762379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47924909356334443717174919 71887364034501665575762379)
  ·
    refine ⟨107831046051752498363643569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71887364034501665575762379 107831046051752498363643569)
    ·
      refine ⟨80873284538814373772732677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107831046051752498363643569 80873284538814373772732677)
      ·
        refine ⟨15163740851027695082387377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80873284538814373772732677 15163740851027695082387377)
        ·
          refine ⟨11372805638270771311790533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15163740851027695082387377 11372805638270771311790533)
          ·
            refine ⟨2132401057175769620960725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11372805638270771311790533 2132401057175769620960725)
            ·
              refine ⟨49978149777557100491267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2132401057175769620960725 49978149777557100491267)
              ·
                rfl

theorem cell21_1970975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 7].length) (baseStart_1970975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1970975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1970975 prefixEnd_1970975 := by exact prefixLift 1970975
  have htrace : WordTrace (prefixWord ++ tailWord_1970975) baseStart_1970975 baseEnd_1970975 := by
    simpa [prefixWord, tailWord_1970975, baseEnd_1970975] using wordTrace_append hprefix tailTrace_1970975
  have hstable : (prefixWord ++ tailWord_1970975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970975).length < 2 ^ (prefixWord ++ tailWord_1970975).sum := by decide
  have hdescent : baseEnd_1970975 < baseStart_1970975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971034 : List Nat := [3, 1, 1, 2, 1, 13]
def baseStart_1971034 : Nat := 118140960795 + 1971034 * 2 ^ 59
def prefixEnd_1971034 : Nat := 4983230072969 + 3 ^ 40 * 1971034 * 2
def baseEnd_1971034 : Nat := 16659881948216404182887

theorem tailTrace_1971034 : CollatzResearch.WordTrace tailWord_1971034 prefixEnd_1971034 16659881948216404182887 := by
  unfold tailWord_1971034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972378985321979663040039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47926343960858612434773437 17972378985321979663040039)
  ·
    refine ⟨26958568477982969494560059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17972378985321979663040039 26958568477982969494560059)
    ·
      refine ⟨40437852716974454241840089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26958568477982969494560059 40437852716974454241840089)
      ·
        refine ⟨30328389537730840681380067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40437852716974454241840089 30328389537730840681380067)
        ·
          refine ⟨45492584306596261022070101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30328389537730840681380067 45492584306596261022070101)
          ·
            refine ⟨16659881948216404182887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45492584306596261022070101 16659881948216404182887)
            ·
              rfl

theorem cell21_1971034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 13].length) (baseStart_1971034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971034 prefixEnd_1971034 := by exact prefixLift 1971034
  have htrace : WordTrace (prefixWord ++ tailWord_1971034) baseStart_1971034 baseEnd_1971034 := by
    simpa [prefixWord, tailWord_1971034, baseEnd_1971034] using wordTrace_append hprefix tailTrace_1971034
  have hstable : (prefixWord ++ tailWord_1971034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971034).length < 2 ^ (prefixWord ++ tailWord_1971034).sum := by decide
  have hdescent : baseEnd_1971034 < baseStart_1971034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971065 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_1971065 : Nat := 118140960795 + 1971065 * 2 ^ 59
def prefixEnd_1971065 : Nat := 4983230072969 + 3 ^ 40 * 1971065 * 2
def baseEnd_1971065 : Nat := 449823887224193747921219

theorem tailTrace_1971065 : CollatzResearch.WordTrace tailWord_1971065 prefixEnd_1971065 449823887224193747921219 := by
  unfold tailWord_1971065
  simp only [CollatzResearch.WordTrace]
  refine ⟨71890646604175610946538649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47927097736117073964359099 71890646604175610946538649)
  ·
    refine ⟨53917984953131708209903987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71890646604175610946538649 53917984953131708209903987)
    ·
      refine ⟨80876977429697562314855981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53917984953131708209903987 80876977429697562314855981)
      ·
        refine ⟨30328866536136585868070993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80876977429697562314855981 30328866536136585868070993)
        ·
          refine ⟨22746649902102439401053245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30328866536136585868070993 22746649902102439401053245)
          ·
            refine ⟨8529993713288414775394967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22746649902102439401053245 8529993713288414775394967)
            ·
              refine ⟨12794990569932622163092451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529993713288414775394967 12794990569932622163092451)
              ·
                refine ⟨19192485854898933244638677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12794990569932622163092451 19192485854898933244638677)
                ·
                  refine ⟨449823887224193747921219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19192485854898933244638677 449823887224193747921219)
                  ·
                    rfl

theorem cell21_1971065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_1971065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971065 prefixEnd_1971065 := by exact prefixLift 1971065
  have htrace : WordTrace (prefixWord ++ tailWord_1971065) baseStart_1971065 baseEnd_1971065 := by
    simpa [prefixWord, tailWord_1971065, baseEnd_1971065] using wordTrace_append hprefix tailTrace_1971065
  have hstable : (prefixWord ++ tailWord_1971065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971065).length < 2 ^ (prefixWord ++ tailWord_1971065).sum := by decide
  have hdescent : baseEnd_1971065 < baseStart_1971065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971074 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1971074 : Nat := 118140960795 + 1971074 * 2 ^ 59
def prefixEnd_1971074 : Nat := 4983230072969 + 3 ^ 40 * 1971074 * 2
def baseEnd_1971074 : Nat := 449825941146811732271201

theorem tailTrace_1971074 : CollatzResearch.WordTrace tailWord_1971074 prefixEnd_1971074 449825941146811732271201 := by
  unfold tailWord_1971074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17972743715285751370904069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47927316574095336989077517 17972743715285751370904069)
  ·
    refine ⟨3369889446616078382044513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17972743715285751370904069 3369889446616078382044513)
    ·
      refine ⟨2527417084962058786533385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3369889446616078382044513 2527417084962058786533385)
      ·
        refine ⟨1895562813721544089900039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2527417084962058786533385 1895562813721544089900039)
        ·
          refine ⟨2843344220582316134850059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895562813721544089900039 2843344220582316134850059)
          ·
            refine ⟨4265016330873474202275089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843344220582316134850059 4265016330873474202275089)
            ·
              refine ⟨3198762248155105651706317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4265016330873474202275089 3198762248155105651706317)
              ·
                refine ⟨1199535843058164619389869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198762248155105651706317 1199535843058164619389869)
                ·
                  refine ⟨449825941146811732271201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199535843058164619389869 449825941146811732271201)
                  ·
                    rfl

theorem cell21_1971074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1971074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971074 prefixEnd_1971074 := by exact prefixLift 1971074
  have htrace : WordTrace (prefixWord ++ tailWord_1971074) baseStart_1971074 baseEnd_1971074 := by
    simpa [prefixWord, tailWord_1971074, baseEnd_1971074] using wordTrace_append hprefix tailTrace_1971074
  have hstable : (prefixWord ++ tailWord_1971074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971074).length < 2 ^ (prefixWord ++ tailWord_1971074).sum := by decide
  have hdescent : baseEnd_1971074 < baseStart_1971074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971113 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 4]
def baseStart_1971113 : Nat := 118140960795 + 1971113 * 2 ^ 59
def prefixEnd_1971113 : Nat := 4983230072969 + 3 ^ 40 * 1971113 * 2
def baseEnd_1971113 : Nat := 449834841478156331121121

theorem tailTrace_1971113 : CollatzResearch.WordTrace tailWord_1971113 prefixEnd_1971113 449834841478156331121121 := by
  unfold tailWord_1971113
  simp only [CollatzResearch.WordTrace]
  refine ⟨71892397308001715144285993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47928264872001143429523995 71892397308001715144285993)
  ·
    refine ⟨53919297981001286358214495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71892397308001715144285993 53919297981001286358214495)
    ·
      refine ⟨80878946971501929537321743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53919297981001286358214495 80878946971501929537321743)
      ·
        refine ⟨121318420457252894305982615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80878946971501929537321743 121318420457252894305982615)
        ·
          refine ⟨181977630685879341458973923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121318420457252894305982615 181977630685879341458973923)
          ·
            refine ⟨272966446028819012188460885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181977630685879341458973923 272966446028819012188460885)
            ·
              refine ⟨1599412769700111399541763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 272966446028819012188460885 1599412769700111399541763)
              ·
                refine ⟨2399119154550167099312645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599412769700111399541763 2399119154550167099312645)
                ·
                  refine ⟨449834841478156331121121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399119154550167099312645 449834841478156331121121)
                  ·
                    rfl

theorem cell21_1971113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_1971113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971113 prefixEnd_1971113 := by exact prefixLift 1971113
  have htrace : WordTrace (prefixWord ++ tailWord_1971113) baseStart_1971113 baseEnd_1971113 := by
    simpa [prefixWord, tailWord_1971113, baseEnd_1971113] using wordTrace_append hprefix tailTrace_1971113
  have hstable : (prefixWord ++ tailWord_1971113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971113).length < 2 ^ (prefixWord ++ tailWord_1971113).sum := by decide
  have hdescent : baseEnd_1971113 < baseStart_1971113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971127 : List Nat := [1, 1, 3, 1, 3, 1, 6, 5]
def baseStart_1971127 : Nat := 118140960795 + 1971127 * 2 ^ 59
def prefixEnd_1971127 : Nat := 4983230072969 + 3 ^ 40 * 1971127 * 2
def baseEnd_1971127 : Nat := 149946012156298472629253

theorem tailTrace_1971127 : CollatzResearch.WordTrace tailWord_1971127 prefixEnd_1971127 149946012156298472629253 := by
  unfold tailWord_1971127
  simp only [CollatzResearch.WordTrace]
  refine ⟨71892907929950995535295635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47928605286633997023530423 71892907929950995535295635)
  ·
    refine ⟨107839361894926493302943453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71892907929950995535295635 107839361894926493302943453)
    ·
      refine ⟨40439760710597434988603795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107839361894926493302943453 40439760710597434988603795)
      ·
        refine ⟨60659641065896152482905693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40439760710597434988603795 60659641065896152482905693)
        ·
          refine ⟨22747365399711057181089635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60659641065896152482905693 22747365399711057181089635)
          ·
            refine ⟨34121048099566585771634453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22747365399711057181089635 34121048099566585771634453)
            ·
              refine ⟨1599424129667183708045365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34121048099566585771634453 1599424129667183708045365)
              ·
                refine ⟨149946012156298472629253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1599424129667183708045365 149946012156298472629253)
                ·
                  rfl

theorem cell21_1971127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 5].length) (baseStart_1971127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971127 prefixEnd_1971127 := by exact prefixLift 1971127
  have htrace : WordTrace (prefixWord ++ tailWord_1971127) baseStart_1971127 baseEnd_1971127 := by
    simpa [prefixWord, tailWord_1971127, baseEnd_1971127] using wordTrace_append hprefix tailTrace_1971127
  have hstable : (prefixWord ++ tailWord_1971127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971127).length < 2 ^ (prefixWord ++ tailWord_1971127).sum := by decide
  have hdescent : baseEnd_1971127 < baseStart_1971127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971133 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 3]
def baseStart_1971133 : Nat := 118140960795 + 1971133 * 2 ^ 59
def prefixEnd_1971133 : Nat := 4983230072969 + 3 ^ 40 * 1971133 * 2
def baseEnd_1971133 : Nat := 449839405750640740787747

theorem tailTrace_1971133 : CollatzResearch.WordTrace tailWord_1971133 prefixEnd_1971133 449839405750640740787747 := by
  unfold tailWord_1971133
  simp only [CollatzResearch.WordTrace]
  refine ⟨71893126767929258560014053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47928751178619505706676035 71893126767929258560014053)
  ·
    refine ⟨13479961268986735980002635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71893126767929258560014053 13479961268986735980002635)
    ·
      refine ⟨20219941903480103970003953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13479961268986735980002635 20219941903480103970003953)
      ·
        refine ⟨15164956427610077977502965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20219941903480103970003953 15164956427610077977502965)
        ·
          refine ⟨1421714665088444810390903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15164956427610077977502965 1421714665088444810390903)
          ·
            refine ⟨2132571997632667215586355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421714665088444810390903 2132571997632667215586355)
            ·
              refine ⟨3198857996449000823379533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132571997632667215586355 3198857996449000823379533)
              ·
                refine ⟨1199571748668375308767325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198857996449000823379533 1199571748668375308767325)
                ·
                  refine ⟨449839405750640740787747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199571748668375308767325 449839405750640740787747)
                  ·
                    rfl

theorem cell21_1971133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_1971133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971133 prefixEnd_1971133 := by exact prefixLift 1971133
  have htrace : WordTrace (prefixWord ++ tailWord_1971133) baseStart_1971133 baseEnd_1971133 := by
    simpa [prefixWord, tailWord_1971133, baseEnd_1971133] using wordTrace_append hprefix tailTrace_1971133
  have hstable : (prefixWord ++ tailWord_1971133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971133).length < 2 ^ (prefixWord ++ tailWord_1971133).sum := by decide
  have hdescent : baseEnd_1971133 < baseStart_1971133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971144 : List Nat := [2, 1, 3, 1, 6, 1, 7]
def baseStart_1971144 : Nat := 118140960795 + 1971144 * 2 ^ 59
def prefixEnd_1971144 : Nat := 4983230072969 + 3 ^ 40 * 1971144 * 2
def baseEnd_1971144 : Nat := 49982435122278574011599

theorem tailTrace_1971144 : CollatzResearch.WordTrace tailWord_1971144 prefixEnd_1971144 49982435122278574011599 := by
  unfold tailWord_1971144
  simp only [CollatzResearch.WordTrace]
  refine ⟨35946763985444703719332243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47929018647259604959109657 35946763985444703719332243)
  ·
    refine ⟨53920145978167055578998365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35946763985444703719332243 53920145978167055578998365)
    ·
      refine ⟨20220054741812645842124387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53920145978167055578998365 20220054741812645842124387)
      ·
        refine ⟨30330082112718968763186581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20220054741812645842124387 30330082112718968763186581)
        ·
          refine ⟨1421722599033701660774371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30330082112718968763186581 1421722599033701660774371)
          ·
            refine ⟨2132583898550552491161557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421722599033701660774371 2132583898550552491161557)
            ·
              refine ⟨49982435122278574011599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2132583898550552491161557 49982435122278574011599)
              ·
                rfl

theorem cell21_1971144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 7].length) (baseStart_1971144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971144 prefixEnd_1971144 := by exact prefixLift 1971144
  have htrace : WordTrace (prefixWord ++ tailWord_1971144) baseStart_1971144 baseEnd_1971144 := by
    simpa [prefixWord, tailWord_1971144, baseEnd_1971144] using wordTrace_append hprefix tailTrace_1971144
  have hstable : (prefixWord ++ tailWord_1971144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971144).length < 2 ^ (prefixWord ++ tailWord_1971144).sum := by decide
  have hdescent : baseEnd_1971144 < baseStart_1971144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971234 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1971234 : Nat := 118140960795 + 1971234 * 2 ^ 59
def prefixEnd_1971234 : Nat := 4983230072969 + 3 ^ 40 * 1971234 * 2
def baseEnd_1971234 : Nat := 449862455326687009604207

theorem tailTrace_1971234 : CollatzResearch.WordTrace tailWord_1971234 prefixEnd_1971234 449862455326687009604207 := by
  unfold tailWord_1971234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974202635140838202360189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47931207027042235206293837 17974202635140838202360189)
  ·
    refine ⟨6740325988177814325885071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17974202635140838202360189 6740325988177814325885071)
    ·
      refine ⟨10110488982266721488827607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740325988177814325885071 10110488982266721488827607)
      ·
        refine ⟨15165733473400082233241411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110488982266721488827607 15165733473400082233241411)
        ·
          refine ⟨22748600210100123349862117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15165733473400082233241411 22748600210100123349862117)
          ·
            refine ⟨4265362539393773128099147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22748600210100123349862117 4265362539393773128099147)
            ·
              refine ⟨6398043809090659692148721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4265362539393773128099147 6398043809090659692148721)
              ·
                refine ⟨4798532856817994769111541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6398043809090659692148721 4798532856817994769111541)
                ·
                  refine ⟨449862455326687009604207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4798532856817994769111541 449862455326687009604207)
                  ·
                    rfl

theorem cell21_1971234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1971234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971234 prefixEnd_1971234 := by exact prefixLift 1971234
  have htrace : WordTrace (prefixWord ++ tailWord_1971234) baseStart_1971234 baseEnd_1971234 := by
    simpa [prefixWord, tailWord_1971234, baseEnd_1971234] using wordTrace_append hprefix tailTrace_1971234
  have hstable : (prefixWord ++ tailWord_1971234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971234).length < 2 ^ (prefixWord ++ tailWord_1971234).sum := by decide
  have hdescent : baseEnd_1971234 < baseStart_1971234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971265 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_1971265 : Nat := 118140960795 + 1971265 * 2 ^ 59
def prefixEnd_1971265 : Nat := 4983230072969 + 3 ^ 40 * 1971265 * 2
def baseEnd_1971265 : Nat := 449869529949037844587477

theorem tailTrace_1971265 : CollatzResearch.WordTrace tailWord_1971265 prefixEnd_1971265 449869529949037844587477 := by
  unfold tailWord_1971265
  simp only [CollatzResearch.WordTrace]
  refine ⟨71897941203451045103819249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47931960802300696735879499 71897941203451045103819249)
  ·
    refine ⟨53923455902588283827864437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71897941203451045103819249 53923455902588283827864437)
    ·
      refine ⟨5055323990867651608862291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53923455902588283827864437 5055323990867651608862291)
      ·
        refine ⟨7582985986301477413293437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055323990867651608862291 7582985986301477413293437)
        ·
          refine ⟨2843619744863054029985039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7582985986301477413293437 2843619744863054029985039)
          ·
            refine ⟨4265429617294581044977559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843619744863054029985039 4265429617294581044977559)
            ·
              refine ⟨6398144425941871567466339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4265429617294581044977559 6398144425941871567466339)
              ·
                refine ⟨9597216638912807351199509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398144425941871567466339 9597216638912807351199509)
                ·
                  refine ⟨449869529949037844587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9597216638912807351199509 449869529949037844587477)
                  ·
                    rfl

theorem cell21_1971265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_1971265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971265 prefixEnd_1971265 := by exact prefixLift 1971265
  have htrace : WordTrace (prefixWord ++ tailWord_1971265) baseStart_1971265 baseEnd_1971265 := by
    simpa [prefixWord, tailWord_1971265, baseEnd_1971265] using wordTrace_append hprefix tailTrace_1971265
  have hstable : (prefixWord ++ tailWord_1971265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971265).length < 2 ^ (prefixWord ++ tailWord_1971265).sum := by decide
  have hdescent : baseEnd_1971265 < baseStart_1971265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971282 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1971282 : Nat := 118140960795 + 1971282 * 2 ^ 59
def prefixEnd_1971282 : Nat := 4983230072969 + 3 ^ 40 * 1971282 * 2
def baseEnd_1971282 : Nat := 449873409580649592804109

theorem tailTrace_1971282 : CollatzResearch.WordTrace tailWord_1971282 prefixEnd_1971282 449873409580649592804109 := by
  unfold tailWord_1971282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17974640311097364251797025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47932374162926304671458733 17974640311097364251797025)
  ·
    refine ⟨13480980233323023188847769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17974640311097364251797025 13480980233323023188847769)
    ·
      refine ⟨10110735174992267391635827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13480980233323023188847769 10110735174992267391635827)
      ·
        refine ⟨15166102762488401087453741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110735174992267391635827 15166102762488401087453741)
        ·
          refine ⟨5687288535933150407795153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15166102762488401087453741 5687288535933150407795153)
          ·
            refine ⟨4265466401949862805846365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5687288535933150407795153 4265466401949862805846365)
            ·
              refine ⟨1599549900731198552192387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4265466401949862805846365 1599549900731198552192387)
              ·
                refine ⟨2399324851096797828288581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599549900731198552192387 2399324851096797828288581)
                ·
                  refine ⟨449873409580649592804109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399324851096797828288581 449873409580649592804109)
                  ·
                    rfl

theorem cell21_1971282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1971282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971282 prefixEnd_1971282 := by exact prefixLift 1971282
  have htrace : WordTrace (prefixWord ++ tailWord_1971282) baseStart_1971282 baseEnd_1971282 := by
    simpa [prefixWord, tailWord_1971282, baseEnd_1971282] using wordTrace_append hprefix tailTrace_1971282
  have hstable : (prefixWord ++ tailWord_1971282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971282).length < 2 ^ (prefixWord ++ tailWord_1971282).sum := by decide
  have hdescent : baseEnd_1971282 < baseStart_1971282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971324 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_1971324 : Nat := 118140960795 + 1971324 * 2 ^ 59
def prefixEnd_1971324 : Nat := 4983230072969 + 3 ^ 40 * 1971324 * 2
def baseEnd_1971324 : Nat := 449882994552866853104023

theorem tailTrace_1971324 : CollatzResearch.WordTrace tailWord_1971324 prefixEnd_1971324 449882994552866853104023 := by
  unfold tailWord_1971324
  simp only [CollatzResearch.WordTrace]
  refine ⟨35950046555118649090108513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47933395406824865453478017 35950046555118649090108513)
  ·
    refine ⟨26962534916338986817581385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35950046555118649090108513 26962534916338986817581385)
    ·
      refine ⟨20221901187254240113186039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26962534916338986817581385 20221901187254240113186039)
      ·
        refine ⟨30332851780881360169779059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20221901187254240113186039 30332851780881360169779059)
        ·
          refine ⟨45499277671322040254668589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30332851780881360169779059 45499277671322040254668589)
          ·
            refine ⟨17062229126745765095500721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45499277671322040254668589 17062229126745765095500721)
            ·
              refine ⟨12796671845059323821625541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17062229126745765095500721 12796671845059323821625541)
              ·
                refine ⟨2399375970948623216554789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12796671845059323821625541 2399375970948623216554789)
                ·
                  refine ⟨449882994552866853104023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399375970948623216554789 449882994552866853104023)
                  ·
                    rfl

theorem cell21_1971324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_1971324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971324 prefixEnd_1971324 := by exact prefixLift 1971324
  have htrace : WordTrace (prefixWord ++ tailWord_1971324) baseStart_1971324 baseEnd_1971324 := by
    simpa [prefixWord, tailWord_1971324, baseEnd_1971324] using wordTrace_append hprefix tailTrace_1971324
  have hstable : (prefixWord ++ tailWord_1971324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971324).length < 2 ^ (prefixWord ++ tailWord_1971324).sum := by decide
  have hdescent : baseEnd_1971324 < baseStart_1971324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971400 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_1971400 : Nat := 118140960795 + 1971400 * 2 ^ 59
def prefixEnd_1971400 : Nat := 4983230072969 + 3 ^ 40 * 1971400 * 2
def baseEnd_1971400 : Nat := 449900338788307609837201

theorem tailTrace_1971400 : CollatzResearch.WordTrace tailWord_1971400 prefixEnd_1971400 449900338788307609837201 := by
  unfold tailWord_1971400
  simp only [CollatzResearch.WordTrace]
  refine ⟨35951432528980981579991827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47935243371974642106655769 35951432528980981579991827)
  ·
    refine ⟨53927148793471472369987741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35951432528980981579991827 53927148793471472369987741)
    ·
      refine ⟨20222680797551802138745403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53927148793471472369987741 20222680797551802138745403)
      ·
        refine ⟨30334021196327703208118105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20222680797551802138745403 30334021196327703208118105)
        ·
          refine ⟨22750515897245777406088579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30334021196327703208118105 22750515897245777406088579)
          ·
            refine ⟨34125773845868666109132869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22750515897245777406088579 34125773845868666109132869)
            ·
              refine ⟨6398582596100374895462413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34125773845868666109132869 6398582596100374895462413)
              ·
                refine ⟨2399468473537640585798405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6398582596100374895462413 2399468473537640585798405)
                ·
                  refine ⟨449900338788307609837201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399468473537640585798405 449900338788307609837201)
                  ·
                    rfl

theorem cell21_1971400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_1971400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971400 prefixEnd_1971400 := by exact prefixLift 1971400
  have htrace : WordTrace (prefixWord ++ tailWord_1971400) baseStart_1971400 baseEnd_1971400 := by
    simpa [prefixWord, tailWord_1971400, baseEnd_1971400] using wordTrace_append hprefix tailTrace_1971400
  have hstable : (prefixWord ++ tailWord_1971400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971400).length < 2 ^ (prefixWord ++ tailWord_1971400).sum := by decide
  have hdescent : baseEnd_1971400 < baseStart_1971400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971431 : List Nat := [1, 1, 5, 3, 2, 1, 8]
def baseStart_1971431 : Nat := 118140960795 + 1971431 * 2 ^ 59
def prefixEnd_1971431 : Nat := 4983230072969 + 3 ^ 40 * 1971431 * 2
def baseEnd_1971431 : Nat := 49989712601184271646719

theorem tailTrace_1971431 : CollatzResearch.WordTrace tailWord_1971431 prefixEnd_1971431 49989712601184271646719 := by
  unfold tailWord_1971431
  simp only [CollatzResearch.WordTrace]
  refine ⟨71903995720849655454362147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47935997147233103636241431 71903995720849655454362147)
  ·
    refine ⟨107855993581274483181543221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71903995720849655454362147 107855993581274483181543221)
    ·
      refine ⟨10111499398244482798269677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107855993581274483181543221 10111499398244482798269677)
      ·
        refine ⟨3791812274341681049351129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10111499398244482798269677 3791812274341681049351129)
        ·
          refine ⟨2843859205756260787013347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3791812274341681049351129 2843859205756260787013347)
          ·
            refine ⟨4265788808634391180520021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843859205756260787013347 4265788808634391180520021)
            ·
              refine ⟨49989712601184271646719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4265788808634391180520021 49989712601184271646719)
              ·
                rfl

theorem cell21_1971431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 8].length) (baseStart_1971431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971431 prefixEnd_1971431 := by exact prefixLift 1971431
  have htrace : WordTrace (prefixWord ++ tailWord_1971431) baseStart_1971431 baseEnd_1971431 := by
    simpa [prefixWord, tailWord_1971431, baseEnd_1971431] using wordTrace_append hprefix tailTrace_1971431
  have hstable : (prefixWord ++ tailWord_1971431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971431).length < 2 ^ (prefixWord ++ tailWord_1971431).sum := by decide
  have hdescent : baseEnd_1971431 < baseStart_1971431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971496 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 3]
def baseStart_1971496 : Nat := 118140960795 + 1971496 * 2 ^ 59
def prefixEnd_1971496 : Nat := 4983230072969 + 3 ^ 40 * 1971496 * 2
def baseEnd_1971496 : Nat := 449922247296232776237005

theorem tailTrace_1971496 : CollatzResearch.WordTrace tailWord_1971496 prefixEnd_1971496 449922247296232776237005 := by
  unfold tailWord_1971496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35953183232807085777739171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47937577643742781036985561 35953183232807085777739171)
  ·
    refine ⟨53929774849210628666608757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35953183232807085777739171 53929774849210628666608757)
    ·
      refine ⟨5055916392113496437494571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53929774849210628666608757 5055916392113496437494571)
      ·
        refine ⟨7583874588170244656241857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5055916392113496437494571 7583874588170244656241857)
        ·
          refine ⟨5687905941127683492181393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7583874588170244656241857 5687905941127683492181393)
          ·
            refine ⟨4265929455845762619136045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5687905941127683492181393 4265929455845762619136045)
            ·
              refine ⟨1599723545942160982176017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4265929455845762619136045 1599723545942160982176017)
              ·
                refine ⟨1199792659456620736632013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599723545942160982176017 1199792659456620736632013)
                ·
                  refine ⟨449922247296232776237005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199792659456620736632013 449922247296232776237005)
                  ·
                    rfl

theorem cell21_1971496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_1971496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971496 prefixEnd_1971496 := by exact prefixLift 1971496
  have htrace : WordTrace (prefixWord ++ tailWord_1971496) baseStart_1971496 baseEnd_1971496 := by
    simpa [prefixWord, tailWord_1971496, baseEnd_1971496] using wordTrace_append hprefix tailTrace_1971496
  have hstable : (prefixWord ++ tailWord_1971496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971496).length < 2 ^ (prefixWord ++ tailWord_1971496).sum := by decide
  have hdescent : baseEnd_1971496 < baseStart_1971496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971538 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_1971538 : Nat := 118140960795 + 1971538 * 2 ^ 59
def prefixEnd_1971538 : Nat := 4983230072969 + 3 ^ 40 * 1971538 * 2
def baseEnd_1971538 : Nat := 449931832268450036536919

theorem tailTrace_1971538 : CollatzResearch.WordTrace tailWord_1971538 prefixEnd_1971538 449931832268450036536919 := by
  unfold tailWord_1971538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976974582865503182126817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47938598887641341819004845 17976974582865503182126817)
  ·
    refine ⟨13482730937149127386595113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17976974582865503182126817 13482730937149127386595113)
    ·
      refine ⟨10112048202861845539946335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13482730937149127386595113 10112048202861845539946335)
      ·
        refine ⟨15168072304292768309919503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112048202861845539946335 15168072304292768309919503)
        ·
          refine ⟨22752108456439152464879255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15168072304292768309919503 22752108456439152464879255)
          ·
            refine ⟨34128162684658728697318883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22752108456439152464879255 34128162684658728697318883)
            ·
              refine ⟨51192244026988093045978325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34128162684658728697318883 51192244026988093045978325)
              ·
                refine ⟨1199818219382533430765117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51192244026988093045978325 1199818219382533430765117)
                ·
                  refine ⟨449931832268450036536919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199818219382533430765117 449931832268450036536919)
                  ·
                    rfl

theorem cell21_1971538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_1971538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971538 prefixEnd_1971538 := by exact prefixLift 1971538
  have htrace : WordTrace (prefixWord ++ tailWord_1971538) baseStart_1971538 baseEnd_1971538 := by
    simpa [prefixWord, tailWord_1971538, baseEnd_1971538] using wordTrace_append hprefix tailTrace_1971538
  have hstable : (prefixWord ++ tailWord_1971538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971538).length < 2 ^ (prefixWord ++ tailWord_1971538).sum := by decide
  have hdescent : baseEnd_1971538 < baseStart_1971538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971552 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_1971552 : Nat := 118140960795 + 1971552 * 2 ^ 59
def prefixEnd_1971552 : Nat := 4983230072969 + 3 ^ 40 * 1971552 * 2
def baseEnd_1971552 : Nat := 449935027259189123303557

theorem tailTrace_1971552 : CollatzResearch.WordTrace tailWord_1971552 prefixEnd_1971552 449935027259189123303557 := by
  unfold tailWord_1971552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954204476705646559758455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47938939302274195413011273 35954204476705646559758455)
  ·
    refine ⟨53931306715058469839637683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35954204476705646559758455 53931306715058469839637683)
    ·
      refine ⟨80896960072587704759456525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53931306715058469839637683 80896960072587704759456525)
      ·
        refine ⟨30336360027220389284796197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80896960072587704759456525 30336360027220389284796197)
        ·
          refine ⟨5688067505103822990899287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30336360027220389284796197 5688067505103822990899287)
          ·
            refine ⟨8532101257655734486348931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688067505103822990899287 8532101257655734486348931)
            ·
              refine ⟨12798151886483601729523397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532101257655734486348931 12798151886483601729523397)
              ·
                refine ⟨2399653478715675324285637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12798151886483601729523397 2399653478715675324285637)
                ·
                  refine ⟨449935027259189123303557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399653478715675324285637 449935027259189123303557)
                  ·
                    rfl

theorem cell21_1971552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_1971552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971552 prefixEnd_1971552 := by exact prefixLift 1971552
  have htrace : WordTrace (prefixWord ++ tailWord_1971552) baseStart_1971552 baseEnd_1971552 := by
    simpa [prefixWord, tailWord_1971552, baseEnd_1971552] using wordTrace_append hprefix tailTrace_1971552
  have hstable : (prefixWord ++ tailWord_1971552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971552).length < 2 ^ (prefixWord ++ tailWord_1971552).sum := by decide
  have hdescent : baseEnd_1971552 < baseStart_1971552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971555 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 3]
def baseStart_1971555 : Nat := 118140960795 + 1971555 * 2 ^ 59
def prefixEnd_1971555 : Nat := 4983230072969 + 3 ^ 40 * 1971555 * 2
def baseEnd_1971555 : Nat := 449935711900061784753551

theorem tailTrace_1971555 : CollatzResearch.WordTrace tailWord_1971555 prefixEnd_1971555 449935711900061784753551 := by
  unfold tailWord_1971555
  simp only [CollatzResearch.WordTrace]
  refine ⟨71908518372400424631876119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47939012248266949754584079 71908518372400424631876119)
  ·
    refine ⟨107862777558600636947814179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71908518372400424631876119 107862777558600636947814179)
    ·
      refine ⟨161794166337900955421721269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107862777558600636947814179 161794166337900955421721269)
      ·
        refine ⟨15168203094178214570786369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161794166337900955421721269 15168203094178214570786369)
        ·
          refine ⟨11376152320633660928089777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15168203094178214570786369 11376152320633660928089777)
          ·
            refine ⟨8532114240475245696067333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376152320633660928089777 8532114240475245696067333)
            ·
              refine ⟨1599771420089108568012625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8532114240475245696067333 1599771420089108568012625)
              ·
                refine ⟨1199828565066831426009469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599771420089108568012625 1199828565066831426009469)
                ·
                  refine ⟨449935711900061784753551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199828565066831426009469 449935711900061784753551)
                  ·
                    rfl

theorem cell21_1971555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3].length) (baseStart_1971555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971555 prefixEnd_1971555 := by exact prefixLift 1971555
  have htrace : WordTrace (prefixWord ++ tailWord_1971555) baseStart_1971555 baseEnd_1971555 := by
    simpa [prefixWord, tailWord_1971555, baseEnd_1971555] using wordTrace_append hprefix tailTrace_1971555
  have hstable : (prefixWord ++ tailWord_1971555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971555).length < 2 ^ (prefixWord ++ tailWord_1971555).sum := by decide
  have hdescent : baseEnd_1971555 < baseStart_1971555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971673 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_1971673 : Nat := 118140960795 + 1971673 * 2 ^ 59
def prefixEnd_1971673 : Nat := 4983230072969 + 3 ^ 40 * 1971673 * 2
def baseEnd_1971673 : Nat := 449962641107719801786643

theorem tailTrace_1971673 : CollatzResearch.WordTrace tailWord_1971673 prefixEnd_1971673 449962641107719801786643 := by
  unfold tailWord_1971673
  simp only [CollatzResearch.WordTrace]
  refine ⟨71912822185972930784671673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47941881457315287189781115 71912822185972930784671673)
  ·
    refine ⟨53934616639479698088503755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71912822185972930784671673 53934616639479698088503755)
    ·
      refine ⟨80901924959219547132755633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53934616639479698088503755 80901924959219547132755633)
      ·
        refine ⟨60676443719414660349566725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80901924959219547132755633 60676443719414660349566725)
        ·
          refine ⟨11376833197390248815543761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60676443719414660349566725 11376833197390248815543761)
          ·
            refine ⟨8532624898042686611657821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11376833197390248815543761 8532624898042686611657821)
            ·
              refine ⟨3199734336766007479371683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8532624898042686611657821 3199734336766007479371683)
              ·
                refine ⟨4799601505149011219057525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199734336766007479371683 4799601505149011219057525)
                ·
                  refine ⟨449962641107719801786643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4799601505149011219057525 449962641107719801786643)
                  ·
                    rfl

theorem cell21_1971673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_1971673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971673 prefixEnd_1971673 := by exact prefixLift 1971673
  have htrace : WordTrace (prefixWord ++ tailWord_1971673) baseStart_1971673 baseEnd_1971673 := by
    simpa [prefixWord, tailWord_1971673, baseEnd_1971673] using wordTrace_append hprefix tailTrace_1971673
  have hstable : (prefixWord ++ tailWord_1971673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971673).length < 2 ^ (prefixWord ++ tailWord_1971673).sum := by decide
  have hdescent : baseEnd_1971673 < baseStart_1971673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971724 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 3]
def baseStart_1971724 : Nat := 118140960795 + 1971724 * 2 ^ 59
def prefixEnd_1971724 : Nat := 4983230072969 + 3 ^ 40 * 1971724 * 2
def baseEnd_1971724 : Nat := 449974280002555046436539

theorem tailTrace_1971724 : CollatzResearch.WordTrace tailWord_1971724 prefixEnd_1971724 449974280002555046436539 := by
  unfold tailWord_1971724
  simp only [CollatzResearch.WordTrace]
  refine ⟨35957341154394083247389113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47943121539192110996518817 35957341154394083247389113)
  ·
    refine ⟨26968005865795562435541835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35957341154394083247389113 26968005865795562435541835)
    ·
      refine ⟨40452008798693343653312753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26968005865795562435541835 40452008798693343653312753)
      ·
        refine ⟨30339006599020007739984565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40452008798693343653312753 30339006599020007739984565)
        ·
          refine ⟨2844281868658125725623553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30339006599020007739984565 2844281868658125725623553)
          ·
            refine ⟨2133211401493594294217665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844281868658125725623553 2133211401493594294217665)
            ·
              refine ⟨1599908551120195720663249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133211401493594294217665 1599908551120195720663249)
              ·
                refine ⟨1199931413340146790497437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599908551120195720663249 1199931413340146790497437)
                ·
                  refine ⟨449974280002555046436539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199931413340146790497437 449974280002555046436539)
                  ·
                    rfl

theorem cell21_1971724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_1971724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971724 prefixEnd_1971724 := by exact prefixLift 1971724
  have htrace : WordTrace (prefixWord ++ tailWord_1971724) baseStart_1971724 baseEnd_1971724 := by
    simpa [prefixWord, tailWord_1971724, baseEnd_1971724] using wordTrace_append hprefix tailTrace_1971724
  have hstable : (prefixWord ++ tailWord_1971724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971724).length < 2 ^ (prefixWord ++ tailWord_1971724).sum := by decide
  have hdescent : baseEnd_1971724 < baseStart_1971724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971752 : List Nat := [2, 1, 5, 2, 2, 1, 3, 5]
def baseStart_1971752 : Nat := 118140960795 + 1971752 * 2 ^ 59
def prefixEnd_1971752 : Nat := 4983230072969 + 3 ^ 40 * 1971752 * 2
def baseEnd_1971752 : Nat := 149993556661344406656605

theorem tailTrace_1971752 : CollatzResearch.WordTrace tailWord_1971752 prefixEnd_1971752 149993556661344406656605 := by
  unfold tailWord_1971752
  simp only [CollatzResearch.WordTrace]
  refine ⟨35957851776343363638398755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47943802368457818184531673 35957851776343363638398755)
  ·
    refine ⟨53936777664515045457598133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35957851776343363638398755 53936777664515045457598133)
    ·
      refine ⟨5056572906048285511649825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53936777664515045457598133 5056572906048285511649825)
      ·
        refine ⟨3792429679536214133737369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5056572906048285511649825 3792429679536214133737369)
        ·
          refine ⟨2844322259652160600303027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792429679536214133737369 2844322259652160600303027)
          ·
            refine ⟨4266483389478240900454541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844322259652160600303027 4266483389478240900454541)
            ·
              refine ⟨1599931271054340337670453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4266483389478240900454541 1599931271054340337670453)
              ·
                refine ⟨149993556661344406656605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1599931271054340337670453 149993556661344406656605)
                ·
                  rfl

theorem cell21_1971752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_1971752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971752 prefixEnd_1971752 := by exact prefixLift 1971752
  have htrace : WordTrace (prefixWord ++ tailWord_1971752) baseStart_1971752 baseEnd_1971752 := by
    simpa [prefixWord, tailWord_1971752, baseEnd_1971752] using wordTrace_append hprefix tailTrace_1971752
  have hstable : (prefixWord ++ tailWord_1971752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971752).length < 2 ^ (prefixWord ++ tailWord_1971752).sum := by decide
  have hdescent : baseEnd_1971752 < baseStart_1971752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971811 : List Nat := [1, 1, 1, 5, 1, 5, 2, 5]
def baseStart_1971811 : Nat := 118140960795 + 1971811 * 2 ^ 59
def prefixEnd_1971811 : Nat := 4983230072969 + 3 ^ 40 * 1971811 * 2
def baseEnd_1971811 : Nat := 149998044862620742828787

theorem tailTrace_1971811 : CollatzResearch.WordTrace tailWord_1971811 prefixEnd_1971811 149998044862620742828787 := by
  unfold tailWord_1971811
  simp only [CollatzResearch.WordTrace]
  refine ⟨71917855459472980353195287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47945236972981986902130191 71917855459472980353195287)
  ·
    refine ⟨107876783189209470529792931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71917855459472980353195287 107876783189209470529792931)
    ·
      refine ⟨161815174783814205794689397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107876783189209470529792931 161815174783814205794689397)
      ·
        refine ⟨15170172635982581793252131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161815174783814205794689397 15170172635982581793252131)
        ·
          refine ⟨22755258953973872689878197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15170172635982581793252131 22755258953973872689878197)
          ·
            refine ⟨2133305526935050564676081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22755258953973872689878197 2133305526935050564676081)
            ·
              refine ⟨1599979145201287923507061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133305526935050564676081 1599979145201287923507061)
              ·
                refine ⟨149998044862620742828787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1599979145201287923507061 149998044862620742828787)
                ·
                  rfl

theorem cell21_1971811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 5].length) (baseStart_1971811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971811 prefixEnd_1971811 := by exact prefixLift 1971811
  have htrace : WordTrace (prefixWord ++ tailWord_1971811) baseStart_1971811 baseEnd_1971811 := by
    simpa [prefixWord, tailWord_1971811, baseEnd_1971811] using wordTrace_append hprefix tailTrace_1971811
  have hstable : (prefixWord ++ tailWord_1971811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971811).length < 2 ^ (prefixWord ++ tailWord_1971811).sum := by decide
  have hdescent : baseEnd_1971811 < baseStart_1971811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971893 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 3]
def baseStart_1971893 : Nat := 118140960795 + 1971893 * 2 ^ 59
def prefixEnd_1971893 : Nat := 4983230072969 + 3 ^ 40 * 1971893 * 2
def baseEnd_1971893 : Nat := 450012848105048308119527

theorem tailTrace_1971893 : CollatzResearch.WordTrace tailWord_1971893 prefixEnd_1971893 450012848105048308119527 := by
  unfold tailWord_1971893
  simp only [CollatzResearch.WordTrace]
  refine ⟨71920846245175908357680333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47947230830117272238453555 71920846245175908357680333)
  ·
    refine ⟨26970317341940965634130125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71920846245175908357680333 26970317341940965634130125)
    ·
      refine ⟨10113869003227862112798797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26970317341940965634130125 10113869003227862112798797)
      ·
        refine ⟨3792700876210448292299549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10113869003227862112798797 3792700876210448292299549)
        ·
          refine ⟨1422262828578918109612331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3792700876210448292299549 1422262828578918109612331)
          ·
            refine ⟨2133394242868377164418497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422262828578918109612331 2133394242868377164418497)
            ·
              refine ⟨1600045682151282873313873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133394242868377164418497 1600045682151282873313873)
              ·
                refine ⟨1200034261613462154985405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600045682151282873313873 1200034261613462154985405)
                ·
                  refine ⟨450012848105048308119527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200034261613462154985405 450012848105048308119527)
                  ·
                    rfl

theorem cell21_1971893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_1971893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971893 prefixEnd_1971893 := by exact prefixLift 1971893
  have htrace : WordTrace (prefixWord ++ tailWord_1971893) baseStart_1971893 baseEnd_1971893 := by
    simpa [prefixWord, tailWord_1971893, baseEnd_1971893] using wordTrace_append hprefix tailTrace_1971893
  have hstable : (prefixWord ++ tailWord_1971893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971893).length < 2 ^ (prefixWord ++ tailWord_1971893).sum := by decide
  have hdescent : baseEnd_1971893 < baseStart_1971893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971949 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1971949 : Nat := 118140960795 + 1971949 * 2 ^ 59
def prefixEnd_1971949 : Nat := 4983230072969 + 3 ^ 40 * 1971949 * 2
def baseEnd_1971949 : Nat := 450025628068004655186079

theorem tailTrace_1971949 : CollatzResearch.WordTrace tailWord_1971949 prefixEnd_1971949 450025628068004655186079 := by
  unfold tailWord_1971949
  simp only [CollatzResearch.WordTrace]
  refine ⟨71922888732973029921718901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47948592488648686614479267 71922888732973029921718901)
  ·
    refine ⟨6742770818716221555161147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71922888732973029921718901 6742770818716221555161147)
    ·
      refine ⟨10114156228074332332741721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742770818716221555161147 10114156228074332332741721)
      ·
        refine ⟨7585617171055749249556291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10114156228074332332741721 7585617171055749249556291)
        ·
          refine ⟨11378425756583623874334437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585617171055749249556291 11378425756583623874334437)
          ·
            refine ⟨2133454829359429476437707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11378425756583623874334437 2133454829359429476437707)
            ·
              refine ⟨3200182244039144214656561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133454829359429476437707 3200182244039144214656561)
              ·
                refine ⟨2400136683029358160992421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3200182244039144214656561 2400136683029358160992421)
                ·
                  refine ⟨450025628068004655186079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400136683029358160992421 450025628068004655186079)
                  ·
                    rfl

theorem cell21_1971949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1971949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971949 prefixEnd_1971949 := by exact prefixLift 1971949
  have htrace : WordTrace (prefixWord ++ tailWord_1971949) baseStart_1971949 baseEnd_1971949 := by
    simpa [prefixWord, tailWord_1971949, baseEnd_1971949] using wordTrace_append hprefix tailTrace_1971949
  have hstable : (prefixWord ++ tailWord_1971949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971949).length < 2 ^ (prefixWord ++ tailWord_1971949).sum := by decide
  have hdescent : baseEnd_1971949 < baseStart_1971949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971966 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1971966 : Nat := 118140960795 + 1971966 * 2 ^ 59
def prefixEnd_1971966 : Nat := 4983230072969 + 3 ^ 40 * 1971966 * 2
def baseEnd_1971966 : Nat := 450029507699616403402711

theorem tailTrace_1971966 : CollatzResearch.WordTrace tailWord_1971966 prefixEnd_1971966 450029507699616403402711 := by
  unfold tailWord_1971966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990438596738930228135969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47949005849274294550058501 8990438596738930228135969)
  ·
    refine ⟨6742828947554197671101977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8990438596738930228135969 6742828947554197671101977)
    ·
      refine ⟨5057121710665648253326483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6742828947554197671101977 5057121710665648253326483)
      ·
        refine ⟨7585682565998472379989725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057121710665648253326483 7585682565998472379989725)
        ·
          refine ⟨2844630962249427142496147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7585682565998472379989725 2844630962249427142496147)
          ·
            refine ⟨4266946443374140713744221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844630962249427142496147 4266946443374140713744221)
            ·
              refine ⟨1600104916265302767654083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4266946443374140713744221 1600104916265302767654083)
              ·
                refine ⟨2400157374397954151481125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600104916265302767654083 2400157374397954151481125)
                ·
                  refine ⟨450029507699616403402711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400157374397954151481125 450029507699616403402711)
                  ·
                    rfl

theorem cell21_1971966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1971966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971966 prefixEnd_1971966 := by exact prefixLift 1971966
  have htrace : WordTrace (prefixWord ++ tailWord_1971966) baseStart_1971966 baseEnd_1971966 := by
    simpa [prefixWord, tailWord_1971966, baseEnd_1971966] using wordTrace_append hprefix tailTrace_1971966
  have hstable : (prefixWord ++ tailWord_1971966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971966).length < 2 ^ (prefixWord ++ tailWord_1971966).sum := by decide
  have hdescent : baseEnd_1971966 < baseStart_1971966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971991 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_1971991 : Nat := 118140960795 + 1971991 * 2 ^ 59
def prefixEnd_1971991 : Nat := 4983230072969 + 3 ^ 40 * 1971991 * 2
def baseEnd_1971991 : Nat := 450035213040221915485993

theorem tailTrace_1971991 : CollatzResearch.WordTrace tailWord_1971991 prefixEnd_1971991 450035213040221915485993 := by
  unfold tailWord_1971991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71924420598820871094747827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47949613732547247396498551 71924420598820871094747827)
  ·
    refine ⟨107886630898231306642121741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71924420598820871094747827 107886630898231306642121741)
    ·
      refine ⟨40457486586836739990795653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107886630898231306642121741 40457486586836739990795653)
      ·
        refine ⟨7585778735031888748274185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40457486586836739990795653 7585778735031888748274185)
        ·
          refine ⟨5689334051273916561205639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7585778735031888748274185 5689334051273916561205639)
          ·
            refine ⟨8534001076910874841808459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689334051273916561205639 8534001076910874841808459)
            ·
              refine ⟨12801001615366312262712689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534001076910874841808459 12801001615366312262712689)
              ·
                refine ⟨9600751211524734197034517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801001615366312262712689 9600751211524734197034517)
                ·
                  refine ⟨450035213040221915485993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9600751211524734197034517 450035213040221915485993)
                  ·
                    rfl

theorem cell21_1971991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_1971991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971991 prefixEnd_1971991 := by exact prefixLift 1971991
  have htrace : WordTrace (prefixWord ++ tailWord_1971991) baseStart_1971991 baseEnd_1971991 := by
    simpa [prefixWord, tailWord_1971991, baseEnd_1971991] using wordTrace_append hprefix tailTrace_1971991
  have hstable : (prefixWord ++ tailWord_1971991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971991).length < 2 ^ (prefixWord ++ tailWord_1971991).sum := by decide
  have hdescent : baseEnd_1971991 < baseStart_1971991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971994 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1971994 : Nat := 118140960795 + 1971994 * 2 ^ 59
def prefixEnd_1971994 : Nat := 4983230072969 + 3 ^ 40 * 1971994 * 2
def baseEnd_1971994 : Nat := 450035897681094576935987

theorem tailTrace_1971994 : CollatzResearch.WordTrace tailWord_1971994 prefixEnd_1971994 450035897681094576935987 := by
  unfold tailWord_1971994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17981132504452500651776759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47949686678540001738071357 17981132504452500651776759)
  ·
    refine ⟨26971698756678750977665139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17981132504452500651776759 26971698756678750977665139)
    ·
      refine ⟨40457548135018126466497709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26971698756678750977665139 40457548135018126466497709)
      ·
        refine ⟨15171580550631797424936641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40457548135018126466497709 15171580550631797424936641)
        ·
          refine ⟨11378685412973848068702481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15171580550631797424936641 11378685412973848068702481)
          ·
            refine ⟨8534014059730386051526861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11378685412973848068702481 8534014059730386051526861)
            ·
              refine ⟨3200255272398894769322573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8534014059730386051526861 3200255272398894769322573)
              ·
                refine ⟨1200095727149585538495965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3200255272398894769322573 1200095727149585538495965)
                ·
                  refine ⟨450035897681094576935987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200095727149585538495965 450035897681094576935987)
                  ·
                    rfl

theorem cell21_1971994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1971994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1971994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1971994 prefixEnd_1971994 := by exact prefixLift 1971994
  have htrace : WordTrace (prefixWord ++ tailWord_1971994) baseStart_1971994 baseEnd_1971994 := by
    simpa [prefixWord, tailWord_1971994, baseEnd_1971994] using wordTrace_append hprefix tailTrace_1971994
  have hstable : (prefixWord ++ tailWord_1971994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971994).length < 2 ^ (prefixWord ++ tailWord_1971994).sum := by decide
  have hdescent : baseEnd_1971994 < baseStart_1971994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972005 : List Nat := [1, 3, 1, 2, 3, 2, 9]
def baseStart_1972005 : Nat := 118140960795 + 1972005 * 2 ^ 59
def prefixEnd_1972005 : Nat := 4983230072969 + 3 ^ 40 * 1972005 * 2
def baseEnd_1972005 : Nat := 50004267558995666916959

theorem tailTrace_1972005 : CollatzResearch.WordTrace tailWord_1972005 prefixEnd_1972005 50004267558995666916959 := by
  unfold tailWord_1972005
  simp only [CollatzResearch.WordTrace]
  refine ⟨71924931220770151485757469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47949954147180100990504979 71924931220770151485757469)
  ·
    refine ⟨26971849207788806807159051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71924931220770151485757469 26971849207788806807159051)
    ·
      refine ⟨40457773811683210210738577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26971849207788806807159051 40457773811683210210738577)
      ·
        refine ⟨30343330358762407658053933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40457773811683210210738577 30343330358762407658053933)
        ·
          refine ⟨11378748884535902871770225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30343330358762407658053933 11378748884535902871770225)
          ·
            refine ⟨8534061663401927153827669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11378748884535902871770225 8534061663401927153827669)
            ·
              refine ⟨50004267558995666916959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8534061663401927153827669 50004267558995666916959)
              ·
                rfl

theorem cell21_1972005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 9].length) (baseStart_1972005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972005 prefixEnd_1972005 := by exact prefixLift 1972005
  have htrace : WordTrace (prefixWord ++ tailWord_1972005) baseStart_1972005 baseEnd_1972005 := by
    simpa [prefixWord, tailWord_1972005, baseEnd_1972005] using wordTrace_append hprefix tailTrace_1972005
  have hstable : (prefixWord ++ tailWord_1972005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972005).length < 2 ^ (prefixWord ++ tailWord_1972005).sum := by decide
  have hdescent : baseEnd_1972005 < baseStart_1972005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972025 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 4]
def baseStart_1972025 : Nat := 118140960795 + 1972025 * 2 ^ 59
def prefixEnd_1972025 : Nat := 4983230072969 + 3 ^ 40 * 1972025 * 2
def baseEnd_1972025 : Nat := 450042972303445411919257

theorem tailTrace_1972025 : CollatzResearch.WordTrace tailWord_1972025 prefixEnd_1972025 450042972303445411919257 := by
  unfold tailWord_1972025
  simp only [CollatzResearch.WordTrace]
  refine ⟨71925660680697694901485529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47950440453798463267657019 71925660680697694901485529)
  ·
    refine ⟨53944245510523271176114147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71925660680697694901485529 53944245510523271176114147)
    ·
      refine ⟨80916368265784906764171221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53944245510523271176114147 80916368265784906764171221)
      ·
        refine ⟨1896477381229333752285263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80916368265784906764171221 1896477381229333752285263)
        ·
          refine ⟨2844716071844000628427895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896477381229333752285263 2844716071844000628427895)
          ·
            refine ⟨4267074107766000942641843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844716071844000628427895 4267074107766000942641843)
            ·
              refine ⟨6400611161649001413962765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267074107766000942641843 6400611161649001413962765)
              ·
                refine ⟨2400229185618375530236037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400611161649001413962765 2400229185618375530236037)
                ·
                  refine ⟨450042972303445411919257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400229185618375530236037 450042972303445411919257)
                  ·
                    rfl

theorem cell21_1972025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_1972025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972025 prefixEnd_1972025 := by exact prefixLift 1972025
  have htrace : WordTrace (prefixWord ++ tailWord_1972025) baseStart_1972025 baseEnd_1972025 := by
    simpa [prefixWord, tailWord_1972025, baseEnd_1972025] using wordTrace_append hprefix tailTrace_1972025
  have hstable : (prefixWord ++ tailWord_1972025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972025).length < 2 ^ (prefixWord ++ tailWord_1972025).sum := by decide
  have hdescent : baseEnd_1972025 < baseStart_1972025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972118 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1972118 : Nat := 118140960795 + 1972118 * 2 ^ 59
def prefixEnd_1972118 : Nat := 4983230072969 + 3 ^ 40 * 1972118 * 2
def baseEnd_1972118 : Nat := 450064196170497916869067

theorem tailTrace_1972118 : CollatzResearch.WordTrace tailWord_1972118 prefixEnd_1972118 450064196170497916869067 := by
  unfold tailWord_1972118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495565791835048236538813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47952701779573847856414005 4495565791835048236538813)
  ·
    refine ⟨1685837171938143088702055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4495565791835048236538813 1685837171938143088702055)
    ·
      refine ⟨2528755757907214633053083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685837171938143088702055 2528755757907214633053083)
      ·
        refine ⟨3793133636860821949579625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528755757907214633053083 3793133636860821949579625)
        ·
          refine ⟨2844850227645616462184719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793133636860821949579625 2844850227645616462184719)
          ·
            refine ⟨4267275341468424693277079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844850227645616462184719 4267275341468424693277079)
            ·
              refine ⟨6400913012202637039915619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267275341468424693277079 6400913012202637039915619)
              ·
                refine ⟨9601369518303955559873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400913012202637039915619 9601369518303955559873429)
                ·
                  refine ⟨450064196170497916869067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9601369518303955559873429 450064196170497916869067)
                  ·
                    rfl

theorem cell21_1972118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1972118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972118 prefixEnd_1972118 := by exact prefixLift 1972118
  have htrace : WordTrace (prefixWord ++ tailWord_1972118) baseStart_1972118 baseEnd_1972118 := by
    simpa [prefixWord, tailWord_1972118, baseEnd_1972118] using wordTrace_append hprefix tailTrace_1972118
  have hstable : (prefixWord ++ tailWord_1972118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972118).length < 2 ^ (prefixWord ++ tailWord_1972118).sum := by decide
  have hdescent : baseEnd_1972118 < baseStart_1972118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972250 : List Nat := [3, 1, 1, 3, 1, 5, 1, 6]
def baseStart_1972250 : Nat := 118140960795 + 1972250 * 2 ^ 59
def prefixEnd_1972250 : Nat := 4983230072969 + 3 ^ 40 * 1972250 * 2
def baseEnd_1972250 : Nat := 150031440122965006889599

theorem tailTrace_1972250 : CollatzResearch.WordTrace tailWord_1972250 prefixEnd_1972250 150031440122965006889599 := by
  unfold tailWord_1972250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983466776220639582106551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47955911403255038885617469 17983466776220639582106551)
  ·
    refine ⟨26975200164330959373159827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17983466776220639582106551 26975200164330959373159827)
    ·
      refine ⟨40462800246496439059739741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26975200164330959373159827 40462800246496439059739741)
      ·
        refine ⟨15173550092436164647402403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40462800246496439059739741 15173550092436164647402403)
        ·
          refine ⟨22760325138654246971103605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173550092436164647402403 22760325138654246971103605)
          ·
            refine ⟨2133780481748835653540963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22760325138654246971103605 2133780481748835653540963)
            ·
              refine ⟨3200670722623253480311445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133780481748835653540963 3200670722623253480311445)
              ·
                refine ⟨150031440122965006889599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3200670722623253480311445 150031440122965006889599)
                ·
                  rfl

theorem cell21_1972250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_1972250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972250 prefixEnd_1972250 := by exact prefixLift 1972250
  have htrace : WordTrace (prefixWord ++ tailWord_1972250) baseStart_1972250 baseEnd_1972250 := by
    simpa [prefixWord, tailWord_1972250, baseEnd_1972250] using wordTrace_append hprefix tailTrace_1972250
  have hstable : (prefixWord ++ tailWord_1972250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972250).length < 2 ^ (prefixWord ++ tailWord_1972250).sum := by decide
  have hdescent : baseEnd_1972250 < baseStart_1972250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972312 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_1972312 : Nat := 118140960795 + 1972312 * 2 ^ 59
def prefixEnd_1972312 : Nat := 4983230072969 + 3 ^ 40 * 1972312 * 2
def baseEnd_1972312 : Nat := 450108469613596690635337

theorem tailTrace_1972312 : CollatzResearch.WordTrace tailWord_1972312 prefixEnd_1972312 450108469613596690635337 := by
  unfold tailWord_1972312
  simp only [CollatzResearch.WordTrace]
  refine ⟨35968064215328971458591595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47957418953771961944788793 35968064215328971458591595)
  ·
    refine ⟨53952096322993457187887393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35968064215328971458591595 53952096322993457187887393)
    ·
      refine ⟨40464072242245092890915545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53952096322993457187887393 40464072242245092890915545)
      ·
        refine ⟨30348054181683819668186659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40464072242245092890915545 30348054181683819668186659)
        ·
          refine ⟨45522081272525729502279989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30348054181683819668186659 45522081272525729502279989)
          ·
            refine ⟨4267695119299287140838749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45522081272525729502279989 4267695119299287140838749)
            ·
              refine ⟨1600385669737232677814531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4267695119299287140838749 1600385669737232677814531)
              ·
                refine ⟨2400578504605849016721797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600385669737232677814531 2400578504605849016721797)
                ·
                  refine ⟨450108469613596690635337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400578504605849016721797 450108469613596690635337)
                  ·
                    rfl

theorem cell21_1972312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_1972312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972312 prefixEnd_1972312 := by exact prefixLift 1972312
  have htrace : WordTrace (prefixWord ++ tailWord_1972312) baseStart_1972312 baseEnd_1972312 := by
    simpa [prefixWord, tailWord_1972312, baseEnd_1972312] using wordTrace_append hprefix tailTrace_1972312
  have hstable : (prefixWord ++ tailWord_1972312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972312).length < 2 ^ (prefixWord ++ tailWord_1972312).sum := by decide
  have hdescent : baseEnd_1972312 < baseStart_1972312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972318 : List Nat := [4, 4, 1, 1, 3, 1, 2, 5]
def baseStart_1972318 : Nat := 118140960795 + 1972318 * 2 ^ 59
def prefixEnd_1972318 : Nat := 4983230072969 + 3 ^ 40 * 1972318 * 2
def baseEnd_1972318 : Nat := 150036612965114004511775

theorem tailTrace_1972318 : CollatzResearch.WordTrace tailWord_1972318 prefixEnd_1972318 150036612965114004511775 := by
  unfold tailWord_1972318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992043408579525742737701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47957564845757470627934405 8992043408579525742737701)
  ·
    refine ⟨1686008139108661076763319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8992043408579525742737701 1686008139108661076763319)
    ·
      refine ⟨2529012208662991615144979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686008139108661076763319 2529012208662991615144979)
      ·
        refine ⟨3793518312994487422717469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529012208662991615144979 3793518312994487422717469)
        ·
          refine ⟨1422569367372932783519051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3793518312994487422717469 1422569367372932783519051)
          ·
            refine ⟨2133854051059399175278577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422569367372932783519051 2133854051059399175278577)
            ·
              refine ⟨1600390538294549381458933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133854051059399175278577 1600390538294549381458933)
              ·
                refine ⟨150036612965114004511775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1600390538294549381458933 150036612965114004511775)
                ·
                  rfl

theorem cell21_1972318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_1972318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972318 prefixEnd_1972318 := by exact prefixLift 1972318
  have htrace : WordTrace (prefixWord ++ tailWord_1972318) baseStart_1972318 baseEnd_1972318 := by
    simpa [prefixWord, tailWord_1972318, baseEnd_1972318] using wordTrace_append hprefix tailTrace_1972318
  have hstable : (prefixWord ++ tailWord_1972318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972318).length < 2 ^ (prefixWord ++ tailWord_1972318).sum := by decide
  have hdescent : baseEnd_1972318 < baseStart_1972318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972357 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 5]
def baseStart_1972357 : Nat := 118140960795 + 1972357 * 2 ^ 59
def prefixEnd_1972357 : Nat := 4983230072969 + 3 ^ 40 * 1972357 * 2
def baseEnd_1972357 : Nat := 450118739226686612385245

theorem tailTrace_1972357 : CollatzResearch.WordTrace tailWord_1972357 prefixEnd_1972357 450118739226686612385245 := by
  unfold tailWord_1972357
  simp only [CollatzResearch.WordTrace]
  refine ⟨71937769715494915602571325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47958513143663277068380883 71937769715494915602571325)
  ·
    refine ⟨26976663643310593350964247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71937769715494915602571325 26976663643310593350964247)
    ·
      refine ⟨40464995464965890026446371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26976663643310593350964247 40464995464965890026446371)
      ·
        refine ⟨60697493197448835039669557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40464995464965890026446371 60697493197448835039669557)
        ·
          refine ⟨5690389987260828284969021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60697493197448835039669557 5690389987260828284969021)
          ·
            refine ⟨2133896245222810606863383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5690389987260828284969021 2133896245222810606863383)
            ·
              refine ⟨3200844367834215910295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133896245222810606863383 3200844367834215910295075)
              ·
                refine ⟨4801266551751323865442613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200844367834215910295075 4801266551751323865442613)
                ·
                  refine ⟨450118739226686612385245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4801266551751323865442613 450118739226686612385245)
                  ·
                    rfl

theorem cell21_1972357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_1972357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972357 prefixEnd_1972357 := by exact prefixLift 1972357
  have htrace : WordTrace (prefixWord ++ tailWord_1972357) baseStart_1972357 baseEnd_1972357 := by
    simpa [prefixWord, tailWord_1972357, baseEnd_1972357] using wordTrace_append hprefix tailTrace_1972357
  have hstable : (prefixWord ++ tailWord_1972357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972357).length < 2 ^ (prefixWord ++ tailWord_1972357).sum := by decide
  have hdescent : baseEnd_1972357 < baseStart_1972357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972385 : List Nat := [1, 2, 3, 3, 1, 2, 2, 7]
def baseStart_1972385 : Nat := 118140960795 + 1972385 * 2 ^ 59
def prefixEnd_1972385 : Nat := 4983230072969 + 3 ^ 40 * 1972385 * 2
def baseEnd_1972385 : Nat := 150041709736054928639507

theorem tailTrace_1972385 : CollatzResearch.WordTrace tailWord_1972385 prefixEnd_1972385 150041709736054928639507 := by
  unfold tailWord_1972385
  simp only [CollatzResearch.WordTrace]
  refine ⟨71938790959393476384590609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47959193972928984256393739 71938790959393476384590609)
  ·
    refine ⟨53954093219545107288442957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71938790959393476384590609 53954093219545107288442957)
    ·
      refine ⟨20232784957329415233166109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53954093219545107288442957 20232784957329415233166109)
      ·
        refine ⟨7587294358998530712437291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20232784957329415233166109 7587294358998530712437291)
        ·
          refine ⟨11380941538497796068655937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7587294358998530712437291 11380941538497796068655937)
          ·
            refine ⟨8535706153873347051491953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11380941538497796068655937 8535706153873347051491953)
            ·
              refine ⟨6401779615405010288618965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8535706153873347051491953 6401779615405010288618965)
              ·
                refine ⟨150041709736054928639507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6401779615405010288618965 150041709736054928639507)
                ·
                  rfl

theorem cell21_1972385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 7].length) (baseStart_1972385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972385 prefixEnd_1972385 := by exact prefixLift 1972385
  have htrace : WordTrace (prefixWord ++ tailWord_1972385) baseStart_1972385 baseEnd_1972385 := by
    simpa [prefixWord, tailWord_1972385, baseEnd_1972385] using wordTrace_append hprefix tailTrace_1972385
  have hstable : (prefixWord ++ tailWord_1972385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972385).length < 2 ^ (prefixWord ++ tailWord_1972385).sum := by decide
  have hdescent : baseEnd_1972385 < baseStart_1972385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972405 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 4]
def baseStart_1972405 : Nat := 118140960795 + 1972405 * 2 ^ 59
def prefixEnd_1972405 : Nat := 4983230072969 + 3 ^ 40 * 1972405 * 2
def baseEnd_1972405 : Nat := 450129693480649195585147

theorem tailTrace_1972405 : CollatzResearch.WordTrace tailWord_1972405 prefixEnd_1972405 450129693480649195585147 := by
  unfold tailWord_1972405
  simp only [CollatzResearch.WordTrace]
  refine ⟨71939520419321019800318669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47959680279547346533545779 71939520419321019800318669)
  ·
    refine ⟨26977320157245382425119501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71939520419321019800318669 26977320157245382425119501)
    ·
      refine ⟨10116495058967018409419813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26977320157245382425119501 10116495058967018409419813)
      ·
        refine ⟨1896842823556315951766215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10116495058967018409419813 1896842823556315951766215)
        ·
          refine ⟨2845264235334473927649323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896842823556315951766215 2845264235334473927649323)
          ·
            refine ⟨4267896353001710891473985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845264235334473927649323 4267896353001710891473985)
            ·
              refine ⟨3200922264751283168605489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267896353001710891473985 3200922264751283168605489)
              ·
                refine ⟨2400691698563462376454117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3200922264751283168605489 2400691698563462376454117)
                ·
                  refine ⟨450129693480649195585147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2400691698563462376454117 450129693480649195585147)
                  ·
                    rfl

theorem cell21_1972405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_1972405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972405 prefixEnd_1972405 := by exact prefixLift 1972405
  have htrace : WordTrace (prefixWord ++ tailWord_1972405) baseStart_1972405 baseEnd_1972405 := by
    simpa [prefixWord, tailWord_1972405, baseEnd_1972405] using wordTrace_append hprefix tailTrace_1972405
  have hstable : (prefixWord ++ tailWord_1972405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972405).length < 2 ^ (prefixWord ++ tailWord_1972405).sum := by decide
  have hdescent : baseEnd_1972405 < baseStart_1972405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972537 : List Nat := [1, 2, 1, 6, 1, 1, 1, 8]
def baseStart_1972537 : Nat := 118140960795 + 1972537 * 2 ^ 59
def prefixEnd_1972537 : Nat := 4983230072969 + 3 ^ 40 * 1972537 * 2
def baseEnd_1972537 : Nat := 150053272559682099794959

theorem tailTrace_1972537 : CollatzResearch.WordTrace tailWord_1972537 prefixEnd_1972537 150053272559682099794959 := by
  unfold tailWord_1972537
  simp only [CollatzResearch.WordTrace]
  refine ⟨71944334854842806344123865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47962889903228537562749243 71944334854842806344123865)
  ·
    refine ⟨53958251141132104758092899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71944334854842806344123865 53958251141132104758092899)
    ·
      refine ⟨80937376711698157137139349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53958251141132104758092899 80937376711698157137139349)
      ·
        refine ⟨3793939533360851115803407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80937376711698157137139349 3793939533360851115803407)
        ·
          refine ⟨5690909300041276673705111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793939533360851115803407 5690909300041276673705111)
          ·
            refine ⟨8536363950061915010557667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5690909300041276673705111 8536363950061915010557667)
            ·
              refine ⟨12804545925092872515836501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536363950061915010557667 12804545925092872515836501)
              ·
                refine ⟨150053272559682099794959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12804545925092872515836501 150053272559682099794959)
                ·
                  rfl

theorem cell21_1972537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_1972537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972537 prefixEnd_1972537 := by exact prefixLift 1972537
  have htrace : WordTrace (prefixWord ++ tailWord_1972537) baseStart_1972537 baseEnd_1972537 := by
    simpa [prefixWord, tailWord_1972537, baseEnd_1972537] using wordTrace_append hprefix tailTrace_1972537
  have hstable : (prefixWord ++ tailWord_1972537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972537).length < 2 ^ (prefixWord ++ tailWord_1972537).sum := by decide
  have hdescent : baseEnd_1972537 < baseStart_1972537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972551 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_1972551 : Nat := 118140960795 + 1972551 * 2 ^ 59
def prefixEnd_1972551 : Nat := 4983230072969 + 3 ^ 40 * 1972551 * 2
def baseEnd_1972551 : Nat := 450163012669785386151515

theorem tailTrace_1972551 : CollatzResearch.WordTrace tailWord_1972551 prefixEnd_1972551 450163012669785386151515 := by
  unfold tailWord_1972551
  simp only [CollatzResearch.WordTrace]
  refine ⟨71944845476792086735133507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47963230317861391156755671 71944845476792086735133507)
  ·
    refine ⟨107917268215188130102700261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71944845476792086735133507 107917268215188130102700261)
    ·
      refine ⟨20234487790347774394256299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107917268215188130102700261 20234487790347774394256299)
      ·
        refine ⟨30351731685521661591384449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20234487790347774394256299 30351731685521661591384449)
        ·
          refine ⟨22763798764141246193538337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30351731685521661591384449 22763798764141246193538337)
          ·
            refine ⟨17072849073105934645153753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22763798764141246193538337 17072849073105934645153753)
            ·
              refine ⟨12804636804829450983865315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17072849073105934645153753 12804636804829450983865315)
              ·
                refine ⟨19206955207244176475797973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12804636804829450983865315 19206955207244176475797973)
                ·
                  refine ⟨450163012669785386151515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19206955207244176475797973 450163012669785386151515)
                  ·
                    rfl

theorem cell21_1972551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_1972551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972551 prefixEnd_1972551 := by exact prefixLift 1972551
  have htrace : WordTrace (prefixWord ++ tailWord_1972551) baseStart_1972551 baseEnd_1972551 := by
    simpa [prefixWord, tailWord_1972551, baseEnd_1972551] using wordTrace_append hprefix tailTrace_1972551
  have hstable : (prefixWord ++ tailWord_1972551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972551).length < 2 ^ (prefixWord ++ tailWord_1972551).sum := by decide
  have hdescent : baseEnd_1972551 < baseStart_1972551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972709 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 4]
def baseStart_1972709 : Nat := 118140960795 + 1972709 * 2 ^ 59
def prefixEnd_1972709 : Nat := 4983230072969 + 3 ^ 40 * 1972709 * 2
def baseEnd_1972709 : Nat := 450199070422412222517859

theorem tailTrace_1972709 : CollatzResearch.WordTrace tailWord_1972709 prefixEnd_1972709 450199070422412222517859 := by
  unfold tailWord_1972709
  simp only [CollatzResearch.WordTrace]
  refine ⟨71950608210219679719385181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47967072140146453146256787 71950608210219679719385181)
  ·
    refine ⟨26981478078832379894769443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71950608210219679719385181 26981478078832379894769443)
    ·
      refine ⟨40472217118248569842154165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26981478078832379894769443 40472217118248569842154165)
      ·
        refine ⟨3794270354835803422701953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40472217118248569842154165 3794270354835803422701953)
        ·
          refine ⟨2845702766126852567026465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3794270354835803422701953 2845702766126852567026465)
          ·
            refine ⟨2134277074595139425269849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845702766126852567026465 2134277074595139425269849)
            ·
              refine ⟨1600707805946354568952387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134277074595139425269849 1600707805946354568952387)
              ·
                refine ⟨2401061708919531853428581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600707805946354568952387 2401061708919531853428581)
                ·
                  refine ⟨450199070422412222517859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401061708919531853428581 450199070422412222517859)
                  ·
                    rfl

theorem cell21_1972709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_1972709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972709 prefixEnd_1972709 := by exact prefixLift 1972709
  have htrace : WordTrace (prefixWord ++ tailWord_1972709) baseStart_1972709 baseEnd_1972709 := by
    simpa [prefixWord, tailWord_1972709, baseEnd_1972709] using wordTrace_append hprefix tailTrace_1972709
  have hstable : (prefixWord ++ tailWord_1972709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972709).length < 2 ^ (prefixWord ++ tailWord_1972709).sum := by decide
  have hdescent : baseEnd_1972709 < baseStart_1972709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972748 : List Nat := [2, 2, 1, 2, 4, 10]
def baseStart_1972748 : Nat := 118140960795 + 1972748 * 2 ^ 59
def prefixEnd_1972748 : Nat := 4983230072969 + 3 ^ 40 * 1972748 * 2
def baseEnd_1972748 : Nat := 16674369287176178569177

theorem tailTrace_1972748 : CollatzResearch.WordTrace tailWord_1972748 prefixEnd_1972748 16674369287176178569177 := by
  unfold tailWord_1972748
  simp only [CollatzResearch.WordTrace]
  refine ⟨35976015328539194690027449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47968020438052259586703265 35976015328539194690027449)
  ·
    refine ⟨26982011496404396017520587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35976015328539194690027449 26982011496404396017520587)
    ·
      refine ⟨40473017244606594026280881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26982011496404396017520587 40473017244606594026280881)
      ·
        refine ⟨30354762933454945519710661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40473017244606594026280881 30354762933454945519710661)
        ·
          refine ⟨5691518050022802284945749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30354762933454945519710661 5691518050022802284945749)
          ·
            refine ⟨16674369287176178569177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5691518050022802284945749 16674369287176178569177)
            ·
              rfl

theorem cell21_1972748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 10].length) (baseStart_1972748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972748 prefixEnd_1972748 := by exact prefixLift 1972748
  have htrace : WordTrace (prefixWord ++ tailWord_1972748) baseStart_1972748 baseEnd_1972748 := by
    simpa [prefixWord, tailWord_1972748, baseEnd_1972748] using wordTrace_append hprefix tailTrace_1972748
  have hstable : (prefixWord ++ tailWord_1972748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972748).length < 2 ^ (prefixWord ++ tailWord_1972748).sum := by decide
  have hdescent : baseEnd_1972748 < baseStart_1972748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972765 : List Nat := [1, 4, 2, 2, 1, 2, 3, 6]
def baseStart_1972765 : Nat := 118140960795 + 1972765 * 2 ^ 59
def prefixEnd_1972765 : Nat := 4983230072969 + 3 ^ 40 * 1972765 * 2
def baseEnd_1972765 : Nat := 150070616795122856528137

theorem tailTrace_1972765 : CollatzResearch.WordTrace tailWord_1972765 prefixEnd_1972765 150070616795122856528137 := by
  unfold tailWord_1972765
  simp only [CollatzResearch.WordTrace]
  refine ⟨71952650698016801283423749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47968433798677867522282499 71952650698016801283423749)
  ·
    refine ⟨13491122005878150240641953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71952650698016801283423749 13491122005878150240641953)
    ·
      refine ⟨10118341504408612680481465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13491122005878150240641953 10118341504408612680481465)
      ·
        refine ⟨7588756128306459510361099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10118341504408612680481465 7588756128306459510361099)
        ·
          refine ⟨11383134192459689265541649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588756128306459510361099 11383134192459689265541649)
          ·
            refine ⟨8537350644344766949156237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383134192459689265541649 8537350644344766949156237)
            ·
              refine ⟨3201506491629287605933589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8537350644344766949156237 3201506491629287605933589)
              ·
                refine ⟨150070616795122856528137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3201506491629287605933589 150070616795122856528137)
                ·
                  rfl

theorem cell21_1972765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_1972765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972765 prefixEnd_1972765 := by exact prefixLift 1972765
  have htrace : WordTrace (prefixWord ++ tailWord_1972765) baseStart_1972765 baseEnd_1972765 := by
    simpa [prefixWord, tailWord_1972765, baseEnd_1972765] using wordTrace_append hprefix tailTrace_1972765
  have hstable : (prefixWord ++ tailWord_1972765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972765).length < 2 ^ (prefixWord ++ tailWord_1972765).sum := by decide
  have hdescent : baseEnd_1972765 < baseStart_1972765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972810 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1972810 : Nat := 118140960795 + 1972810 * 2 ^ 59
def prefixEnd_1972810 : Nat := 4983230072969 + 3 ^ 40 * 1972810 * 2
def baseEnd_1972810 : Nat := 450222119998458491334319

theorem tailTrace_1972810 : CollatzResearch.WordTrace tailWord_1972810 prefixEnd_1972810 450222119998458491334319 := by
  unfold tailWord_1972810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17988572995713443492202971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47969527988569182645874589 17988572995713443492202971)
  ·
    refine ⟨26982859493570165238304457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17988572995713443492202971 26982859493570165238304457)
    ·
      refine ⟨20237144620177623928728343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26982859493570165238304457 20237144620177623928728343)
      ·
        refine ⟨30355716930266435893092515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20237144620177623928728343 30355716930266435893092515)
        ·
          refine ⟨45533575395399653839638773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30355716930266435893092515 45533575395399653839638773)
          ·
            refine ⟨4268772693318717547466135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45533575395399653839638773 4268772693318717547466135)
            ·
              refine ⟨6403159039978076321199203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268772693318717547466135 6403159039978076321199203)
              ·
                refine ⟨9604738559967114481798805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403159039978076321199203 9604738559967114481798805)
                ·
                  refine ⟨450222119998458491334319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9604738559967114481798805 450222119998458491334319)
                  ·
                    rfl

theorem cell21_1972810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1972810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972810 prefixEnd_1972810 := by exact prefixLift 1972810
  have htrace : WordTrace (prefixWord ++ tailWord_1972810) baseStart_1972810 baseEnd_1972810 := by
    simpa [prefixWord, tailWord_1972810, baseEnd_1972810] using wordTrace_append hprefix tailTrace_1972810
  have hstable : (prefixWord ++ tailWord_1972810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972810).length < 2 ^ (prefixWord ++ tailWord_1972810).sum := by decide
  have hdescent : baseEnd_1972810 < baseStart_1972810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972813 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1972813 : Nat := 118140960795 + 1972813 * 2 ^ 59
def prefixEnd_1972813 : Nat := 4983230072969 + 3 ^ 40 * 1972813 * 2
def baseEnd_1972813 : Nat := 450222804639331152784313

theorem tailTrace_1972813 : CollatzResearch.WordTrace tailWord_1972813 prefixEnd_1972813 450222804639331152784313 := by
  unfold tailWord_1972813
  simp only [CollatzResearch.WordTrace]
  refine ⟨71954401401842905481171093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47969600934561936987447395 71954401401842905481171093)
  ·
    refine ⟨3372862565711386194429895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71954401401842905481171093 3372862565711386194429895)
    ·
      refine ⟨5059293848567079291644843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372862565711386194429895 5059293848567079291644843)
      ·
        refine ⟨7588940772850618937467265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059293848567079291644843 7588940772850618937467265)
        ·
          refine ⟨5691705579637964203100449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7588940772850618937467265 5691705579637964203100449)
          ·
            refine ⟨4268779184728473152325337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691705579637964203100449 4268779184728473152325337)
            ·
              refine ⟨3201584388546354864244003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268779184728473152325337 3201584388546354864244003)
              ·
                refine ⟨4802376582819532296366005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201584388546354864244003 4802376582819532296366005)
                ·
                  refine ⟨450222804639331152784313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4802376582819532296366005 450222804639331152784313)
                  ·
                    rfl

theorem cell21_1972813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1972813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972813 prefixEnd_1972813 := by exact prefixLift 1972813
  have htrace : WordTrace (prefixWord ++ tailWord_1972813) baseStart_1972813 baseEnd_1972813 := by
    simpa [prefixWord, tailWord_1972813, baseEnd_1972813] using wordTrace_append hprefix tailTrace_1972813
  have hstable : (prefixWord ++ tailWord_1972813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972813).length < 2 ^ (prefixWord ++ tailWord_1972813).sum := by decide
  have hdescent : baseEnd_1972813 < baseStart_1972813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972900 : List Nat := [2, 3, 1, 2, 2, 1, 1, 9]
def baseStart_1972900 : Nat := 118140960795 + 1972900 * 2 ^ 59
def prefixEnd_1972900 : Nat := 4983230072969 + 3 ^ 40 * 1972900 * 2
def baseEnd_1972900 : Nat := 150080886408212778278045

theorem tailTrace_1972900 : CollatzResearch.WordTrace tailWord_1972900 prefixEnd_1972900 150080886408212778278045 := by
  unfold tailWord_1972900
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978787276263859669794077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47971716368351812893058769 35978787276263859669794077)
  ·
    refine ⟨13492045228598947376172779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35978787276263859669794077 13492045228598947376172779)
    ·
      refine ⟨20238067842898421064259169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13492045228598947376172779 20238067842898421064259169)
      ·
        refine ⟨15178550882173815798194377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20238067842898421064259169 15178550882173815798194377)
        ·
          refine ⟨11383913161630361848645783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15178550882173815798194377 11383913161630361848645783)
          ·
            refine ⟨17075869742445542772968675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383913161630361848645783 17075869742445542772968675)
            ·
              refine ⟨25613804613668314159453013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17075869742445542772968675 25613804613668314159453013)
              ·
                refine ⟨150080886408212778278045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25613804613668314159453013 150080886408212778278045)
                ·
                  rfl

theorem cell21_1972900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_1972900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972900 prefixEnd_1972900 := by exact prefixLift 1972900
  have htrace : WordTrace (prefixWord ++ tailWord_1972900) baseStart_1972900 baseEnd_1972900 := by
    simpa [prefixWord, tailWord_1972900, baseEnd_1972900] using wordTrace_append hprefix tailTrace_1972900
  have hstable : (prefixWord ++ tailWord_1972900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972900).length < 2 ^ (prefixWord ++ tailWord_1972900).sum := by decide
  have hdescent : baseEnd_1972900 < baseStart_1972900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972965 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 3]
def baseStart_1972965 : Nat := 118140960795 + 1972965 * 2 ^ 59
def prefixEnd_1972965 : Nat := 4983230072969 + 3 ^ 40 * 1972965 * 2
def baseEnd_1972965 : Nat := 450257493110212666250669

theorem tailTrace_1972965 : CollatzResearch.WordTrace tailWord_1972965 prefixEnd_1972965 450257493110212666250669 := by
  unfold tailWord_1972965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71959945297292235440704349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47973296864861490293802899 71959945297292235440704349)
  ·
    refine ⟨26984979486484588290264131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71959945297292235440704349 26984979486484588290264131)
    ·
      refine ⟨40477469229726882435396197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26984979486484588290264131 40477469229726882435396197)
      ·
        refine ⟨7589525480573790456636787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40477469229726882435396197 7589525480573790456636787)
        ·
          refine ⟨11384288220860685684955181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589525480573790456636787 11384288220860685684955181)
          ·
            refine ⟨4269108082822757131858193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11384288220860685684955181 4269108082822757131858193)
            ·
              refine ⟨3201831062117067848893645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269108082822757131858193 3201831062117067848893645)
              ·
                refine ⟨1200686648293900443335117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201831062117067848893645 1200686648293900443335117)
                ·
                  refine ⟨450257493110212666250669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200686648293900443335117 450257493110212666250669)
                  ·
                    rfl

theorem cell21_1972965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_1972965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1972965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1972965 prefixEnd_1972965 := by exact prefixLift 1972965
  have htrace : WordTrace (prefixWord ++ tailWord_1972965) baseStart_1972965 baseEnd_1972965 := by
    simpa [prefixWord, tailWord_1972965, baseEnd_1972965] using wordTrace_append hprefix tailTrace_1972965
  have hstable : (prefixWord ++ tailWord_1972965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972965).length < 2 ^ (prefixWord ++ tailWord_1972965).sum := by decide
  have hdescent : baseEnd_1972965 < baseStart_1972965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973010 : List Nat := [3, 2, 4, 1, 2, 1, 1, 7]
def baseStart_1973010 : Nat := 118140960795 + 1973010 * 2 ^ 59
def prefixEnd_1973010 : Nat := 4983230072969 + 3 ^ 40 * 1973010 * 2
def baseEnd_1973010 : Nat := 150089254241100862666859

theorem tailTrace_1973010 : CollatzResearch.WordTrace tailWord_1973010 prefixEnd_1973010 150089254241100862666859 := by
  unfold tailWord_1973010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990396645532302031523121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47974391054752805417394989 17990396645532302031523121)
  ·
    refine ⟨13492797484149226523642341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17990396645532302031523121 13492797484149226523642341)
    ·
      refine ⟨2529899528277979973182939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13492797484149226523642341 2529899528277979973182939)
      ·
        refine ⟨3794849292416969959774409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529899528277979973182939 3794849292416969959774409)
        ·
          refine ⟨2846136969312727469830807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3794849292416969959774409 2846136969312727469830807)
          ·
            refine ⟨4269205453969091204746211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846136969312727469830807 4269205453969091204746211)
            ·
              refine ⟨6403808180953636807119317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269205453969091204746211 6403808180953636807119317)
              ·
                refine ⟨150089254241100862666859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6403808180953636807119317 150089254241100862666859)
                ·
                  rfl

theorem cell21_1973010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_1973010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973010 prefixEnd_1973010 := by exact prefixLift 1973010
  have htrace : WordTrace (prefixWord ++ tailWord_1973010) baseStart_1973010 baseEnd_1973010 := by
    simpa [prefixWord, tailWord_1973010, baseEnd_1973010] using wordTrace_append hprefix tailTrace_1973010
  have hstable : (prefixWord ++ tailWord_1973010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973010).length < 2 ^ (prefixWord ++ tailWord_1973010).sum := by decide
  have hdescent : baseEnd_1973010 < baseStart_1973010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973041 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 3]
def baseStart_1973041 : Nat := 118140960795 + 1973041 * 2 ^ 59
def prefixEnd_1973041 : Nat := 4983230072969 + 3 ^ 40 * 1973041 * 2
def baseEnd_1973041 : Nat := 450274837345653422983847

theorem tailTrace_1973041 : CollatzResearch.WordTrace tailWord_1973041 prefixEnd_1973041 450274837345653422983847 := by
  unfold tailWord_1973041
  simp only [CollatzResearch.WordTrace]
  refine ⟨71962717245016900420470977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47975144830011266946980651 71962717245016900420470977)
  ·
    refine ⟨53972037933762675315353233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71962717245016900420470977 53972037933762675315353233)
    ·
      refine ⟨40479028450322006486514925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53972037933762675315353233 40479028450322006486514925)
      ·
        refine ⟨15179635668870752432443097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40479028450322006486514925 15179635668870752432443097)
        ·
          refine ⟨11384726751653064324332323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15179635668870752432443097 11384726751653064324332323)
          ·
            refine ⟨17077090127479596486498485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11384726751653064324332323 17077090127479596486498485)
            ·
              refine ⟨1600977199451212170609233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17077090127479596486498485 1600977199451212170609233)
              ·
                refine ⟨1200732899588409127956925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600977199451212170609233 1200732899588409127956925)
                ·
                  refine ⟨450274837345653422983847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200732899588409127956925 450274837345653422983847)
                  ·
                    rfl

theorem cell21_1973041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_1973041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973041 prefixEnd_1973041 := by exact prefixLift 1973041
  have htrace : WordTrace (prefixWord ++ tailWord_1973041) baseStart_1973041 baseEnd_1973041 := by
    simpa [prefixWord, tailWord_1973041, baseEnd_1973041] using wordTrace_append hprefix tailTrace_1973041
  have hstable : (prefixWord ++ tailWord_1973041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973041).length < 2 ^ (prefixWord ++ tailWord_1973041).sum := by decide
  have hdescent : baseEnd_1973041 < baseStart_1973041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973055 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 4]
def baseStart_1973055 : Nat := 118140960795 + 1973055 * 2 ^ 59
def prefixEnd_1973055 : Nat := 4983230072969 + 3 ^ 40 * 1973055 * 2
def baseEnd_1973055 : Nat := 450278032336392509750485

theorem tailTrace_1973055 : CollatzResearch.WordTrace tailWord_1973055 prefixEnd_1973055 450278032336392509750485 := by
  unfold tailWord_1973055
  simp only [CollatzResearch.WordTrace]
  refine ⟨71963227866966180811480619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47975485244644120540987079 71963227866966180811480619)
  ·
    refine ⟨107944841800449271217220929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71963227866966180811480619 107944841800449271217220929)
    ·
      refine ⟨80958631350336953412915697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107944841800449271217220929 80958631350336953412915697)
      ·
        refine ⟨60718973512752715059686773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80958631350336953412915697 60718973512752715059686773)
        ·
          refine ⟨5692403766820567036845635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60718973512752715059686773 5692403766820567036845635)
          ·
            refine ⟨8538605650230850555268453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5692403766820567036845635 8538605650230850555268453)
            ·
              refine ⟨1600988559418284479112835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8538605650230850555268453 1600988559418284479112835)
              ·
                refine ⟨2401482839127426718669253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600988559418284479112835 2401482839127426718669253)
                ·
                  refine ⟨450278032336392509750485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401482839127426718669253 450278032336392509750485)
                  ·
                    rfl

theorem cell21_1973055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 4].length) (baseStart_1973055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973055 prefixEnd_1973055 := by exact prefixLift 1973055
  have htrace : WordTrace (prefixWord ++ tailWord_1973055) baseStart_1973055 baseEnd_1973055 := by
    simpa [prefixWord, tailWord_1973055, baseEnd_1973055] using wordTrace_append hprefix tailTrace_1973055
  have hstable : (prefixWord ++ tailWord_1973055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973055).length < 2 ^ (prefixWord ++ tailWord_1973055).sum := by decide
  have hdescent : baseEnd_1973055 < baseStart_1973055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973100 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_1973100 : Nat := 118140960795 + 1973100 * 2 ^ 59
def prefixEnd_1973100 : Nat := 4983230072969 + 3 ^ 40 * 1973100 * 2
def baseEnd_1973100 : Nat := 450288301949482431500393

theorem tailTrace_1973100 : CollatzResearch.WordTrace tailWord_1973100 prefixEnd_1973100 450288301949482431500393 := by
  unfold tailWord_1973100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35982434575901576748434377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47976579434535435664579169 35982434575901576748434377)
  ·
    refine ⟨26986825931926182561325783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35982434575901576748434377 26986825931926182561325783)
    ·
      refine ⟨40480238897889273841988675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26986825931926182561325783 40480238897889273841988675)
      ·
        refine ⟨60720358346833910762983013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40480238897889273841988675 60720358346833910762983013)
        ·
          refine ⟨11385067190031358268059315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60720358346833910762983013 11385067190031358268059315)
          ·
            refine ⟨17077600785047037402088973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11385067190031358268059315 17077600785047037402088973)
            ·
              refine ⟨6404100294392639025783365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17077600785047037402088973 6404100294392639025783365)
              ·
                refine ⟨1200768805198619817334381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6404100294392639025783365 1200768805198619817334381)
                ·
                  refine ⟨450288301949482431500393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200768805198619817334381 450288301949482431500393)
                  ·
                    rfl

theorem cell21_1973100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_1973100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973100 prefixEnd_1973100 := by exact prefixLift 1973100
  have htrace : WordTrace (prefixWord ++ tailWord_1973100) baseStart_1973100 baseEnd_1973100 := by
    simpa [prefixWord, tailWord_1973100, baseEnd_1973100] using wordTrace_append hprefix tailTrace_1973100
  have hstable : (prefixWord ++ tailWord_1973100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973100).length < 2 ^ (prefixWord ++ tailWord_1973100).sum := by decide
  have hdescent : baseEnd_1973100 < baseStart_1973100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973148 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1973148 : Nat := 118140960795 + 1973148 * 2 ^ 59
def prefixEnd_1973148 : Nat := 4983230072969 + 3 ^ 40 * 1973148 * 2
def baseEnd_1973148 : Nat := 450299256203445014700295

theorem tailTrace_1973148 : CollatzResearch.WordTrace tailWord_1973148 prefixEnd_1973148 450299256203445014700295 := by
  unfold tailWord_1973148
  simp only [CollatzResearch.WordTrace]
  refine ⟨35983309927814628847308049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47977746570419505129744065 35983309927814628847308049)
  ·
    refine ⟨26987482445860971635481037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35983309927814628847308049 26987482445860971635481037)
    ·
      refine ⟨10120305917197864363305389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26987482445860971635481037 10120305917197864363305389)
      ·
        refine ⟨3795114718949199136239521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10120305917197864363305389 3795114718949199136239521)
        ·
          refine ⟨2846336039211899352179641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795114718949199136239521 2846336039211899352179641)
          ·
            refine ⟨2134752029408924514134731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846336039211899352179641 2134752029408924514134731)
            ·
              refine ⟨3202128044113386771202097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134752029408924514134731 3202128044113386771202097)
              ·
                refine ⟨2401596033085040078401573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202128044113386771202097 2401596033085040078401573)
                ·
                  refine ⟨450299256203445014700295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401596033085040078401573 450299256203445014700295)
                  ·
                    rfl

theorem cell21_1973148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1973148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973148 prefixEnd_1973148 := by exact prefixLift 1973148
  have htrace : WordTrace (prefixWord ++ tailWord_1973148) baseStart_1973148 baseEnd_1973148 := by
    simpa [prefixWord, tailWord_1973148, baseEnd_1973148] using wordTrace_append hprefix tailTrace_1973148
  have hstable : (prefixWord ++ tailWord_1973148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973148).length < 2 ^ (prefixWord ++ tailWord_1973148).sum := by decide
  have hdescent : baseEnd_1973148 < baseStart_1973148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973165 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1973165 : Nat := 118140960795 + 1973165 * 2 ^ 59
def prefixEnd_1973165 : Nat := 4983230072969 + 3 ^ 40 * 1973165 * 2
def baseEnd_1973165 : Nat := 450303135835056762916927

theorem tailTrace_1973165 : CollatzResearch.WordTrace tailWord_1973165 prefixEnd_1973165 450303135835056762916927 := by
  unfold tailWord_1973165
  simp only [CollatzResearch.WordTrace]
  refine ⟨71967239896567669597984949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47978159931045113065323299 71967239896567669597984949)
  ·
    refine ⟨6746928740303219024811089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71967239896567669597984949 6746928740303219024811089)
    ·
      refine ⟨5060196555227414268608317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6746928740303219024811089 5060196555227414268608317)
      ·
        refine ⟨1897573708210280350728119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5060196555227414268608317 1897573708210280350728119)
        ·
          refine ⟨2846360562315420526092179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897573708210280350728119 2846360562315420526092179)
          ·
            refine ⟨4269540843473130789138269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846360562315420526092179 4269540843473130789138269)
            ·
              refine ⟨1601077816302424045926851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4269540843473130789138269 1601077816302424045926851)
              ·
                refine ⟨2401616724453636068890277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601077816302424045926851 2401616724453636068890277)
                ·
                  refine ⟨450303135835056762916927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401616724453636068890277 450303135835056762916927)
                  ·
                    rfl

theorem cell21_1973165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1973165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973165 prefixEnd_1973165 := by exact prefixLift 1973165
  have htrace : WordTrace (prefixWord ++ tailWord_1973165) baseStart_1973165 baseEnd_1973165 := by
    simpa [prefixWord, tailWord_1973165, baseEnd_1973165] using wordTrace_append hprefix tailTrace_1973165
  have hstable : (prefixWord ++ tailWord_1973165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973165).length < 2 ^ (prefixWord ++ tailWord_1973165).sum := by decide
  have hdescent : baseEnd_1973165 < baseStart_1973165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973187 : List Nat := [1, 1, 1, 3, 1, 1, 2, 11]
def baseStart_1973187 : Nat := 118140960795 + 1973187 * 2 ^ 59
def prefixEnd_1973187 : Nat := 4983230072969 + 3 ^ 40 * 1973187 * 2
def baseEnd_1973187 : Nat := 150102718844929871183405

theorem tailTrace_1973187 : CollatzResearch.WordTrace tailWord_1973187 prefixEnd_1973187 150102718844929871183405 := by
  unfold tailWord_1973187
  simp only [CollatzResearch.WordTrace]
  refine ⟨71968042302487967355285815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47978694868325311570190543 71968042302487967355285815)
  ·
    refine ⟨107952063453731951032928723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71968042302487967355285815 107952063453731951032928723)
    ·
      refine ⟨161928095180597926549393085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107952063453731951032928723 161928095180597926549393085)
      ·
        refine ⟨60723035692724222456022407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161928095180597926549393085 60723035692724222456022407)
        ·
          refine ⟨91084553539086333684033611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60723035692724222456022407 91084553539086333684033611)
          ·
            refine ⟨136626830308629500526050417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91084553539086333684033611 136626830308629500526050417)
            ·
              refine ⟨102470122731472125394537813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136626830308629500526050417 102470122731472125394537813)
              ·
                refine ⟨150102718844929871183405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 102470122731472125394537813 150102718844929871183405)
                ·
                  rfl

theorem cell21_1973187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_1973187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973187 prefixEnd_1973187 := by exact prefixLift 1973187
  have htrace : WordTrace (prefixWord ++ tailWord_1973187) baseStart_1973187 baseEnd_1973187 := by
    simpa [prefixWord, tailWord_1973187, baseEnd_1973187] using wordTrace_append hprefix tailTrace_1973187
  have hstable : (prefixWord ++ tailWord_1973187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973187).length < 2 ^ (prefixWord ++ tailWord_1973187).sum := by decide
  have hdescent : baseEnd_1973187 < baseStart_1973187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973204 : List Nat := [2, 4, 1, 2, 1, 2, 9]
def baseStart_1973204 : Nat := 118140960795 + 1973204 * 2 ^ 59
def prefixEnd_1973204 : Nat := 4983230072969 + 3 ^ 40 * 1973204 * 2
def baseEnd_1973204 : Nat := 50034670685155706862983

theorem tailTrace_1973204 : CollatzResearch.WordTrace tailWord_1973204 prefixEnd_1973204 50034670685155706862983 := by
  unfold tailWord_1973204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984331171713189629327333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47979108228950919505769777 35984331171713189629327333)
  ·
    refine ⟨6747062094696223055498875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35984331171713189629327333 6747062094696223055498875)
    ·
      refine ⟨10120593142044334583248313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6747062094696223055498875 10120593142044334583248313)
      ·
        refine ⟨7590444856533250937436235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10120593142044334583248313 7590444856533250937436235)
        ·
          refine ⟨11385667284799876406154353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7590444856533250937436235 11385667284799876406154353)
          ·
            refine ⟨8539250463599907304615765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11385667284799876406154353 8539250463599907304615765)
            ·
              refine ⟨50034670685155706862983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8539250463599907304615765 50034670685155706862983)
              ·
                rfl

theorem cell21_1973204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 9].length) (baseStart_1973204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973204 prefixEnd_1973204 := by exact prefixLift 1973204
  have htrace : WordTrace (prefixWord ++ tailWord_1973204) baseStart_1973204 baseEnd_1973204 := by
    simpa [prefixWord, tailWord_1973204, baseEnd_1973204] using wordTrace_append hprefix tailTrace_1973204
  have hstable : (prefixWord ++ tailWord_1973204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973204).length < 2 ^ (prefixWord ++ tailWord_1973204).sum := by decide
  have hdescent : baseEnd_1973204 < baseStart_1973204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973269 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 3]
def baseStart_1973269 : Nat := 118140960795 + 1973269 * 2 ^ 59
def prefixEnd_1973269 : Nat := 4983230072969 + 3 ^ 40 * 1973269 * 2
def baseEnd_1973269 : Nat := 450326870051975693183381

theorem tailTrace_1973269 : CollatzResearch.WordTrace tailWord_1973269 prefixEnd_1973269 450326870051975693183381 := by
  unfold tailWord_1973269
  simp only [CollatzResearch.WordTrace]
  refine ⟨71971033088190895359770861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47980688725460596906513907 71971033088190895359770861)
  ·
    refine ⟨26989137408071585759914073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71971033088190895359770861 26989137408071585759914073)
    ·
      refine ⟨20241853056053689319935555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26989137408071585759914073 20241853056053689319935555)
      ·
        refine ⟨30362779584080533979903333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20241853056053689319935555 30362779584080533979903333)
        ·
          refine ⟨5693021172015100121231875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30362779584080533979903333 5693021172015100121231875)
          ·
            refine ⟨8539531758022650181847813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693021172015100121231875 8539531758022650181847813)
            ·
              refine ⟨1601162204629246909096465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8539531758022650181847813 1601162204629246909096465)
              ·
                refine ⟨1200871653471935181822349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601162204629246909096465 1200871653471935181822349)
                ·
                  refine ⟨450326870051975693183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200871653471935181822349 450326870051975693183381)
                  ·
                    rfl

theorem cell21_1973269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_1973269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973269 prefixEnd_1973269 := by exact prefixLift 1973269
  have htrace : WordTrace (prefixWord ++ tailWord_1973269) baseStart_1973269 baseEnd_1973269 := by
    simpa [prefixWord, tailWord_1973269, baseEnd_1973269] using wordTrace_append hprefix tailTrace_1973269
  have hstable : (prefixWord ++ tailWord_1973269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973269).length < 2 ^ (prefixWord ++ tailWord_1973269).sum := by decide
  have hdescent : baseEnd_1973269 < baseStart_1973269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973387 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 3]
def baseStart_1973387 : Nat := 118140960795 + 1973387 * 2 ^ 59
def prefixEnd_1973387 : Nat := 4983230072969 + 3 ^ 40 * 1973387 * 2
def baseEnd_1973387 : Nat := 450353799259633710216473

theorem tailTrace_1973387 : CollatzResearch.WordTrace tailWord_1973387 prefixEnd_1973387 450353799259633710216473 := by
  unfold tailWord_1973387
  simp only [CollatzResearch.WordTrace]
  refine ⟨71975336901763401512566415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47983557934508934341710943 71975336901763401512566415)
  ·
    refine ⟨107963005352645102268849623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71975336901763401512566415 107963005352645102268849623)
    ·
      refine ⟨161944508028967653403274435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107963005352645102268849623 161944508028967653403274435)
      ·
        refine ⟨242916762043451480104911653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161944508028967653403274435 242916762043451480104911653)
        ·
          refine ⟨45546892883147152519670935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 242916762043451480104911653 45546892883147152519670935)
          ·
            refine ⟨68320339324720728779506403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45546892883147152519670935 68320339324720728779506403)
            ·
              refine ⟨102480508987081093169259605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68320339324720728779506403 102480508987081093169259605)
              ·
                refine ⟨1200943464692356560577261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 102480508987081093169259605 1200943464692356560577261)
                ·
                  refine ⟨450353799259633710216473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200943464692356560577261 450353799259633710216473)
                  ·
                    rfl

theorem cell21_1973387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3].length) (baseStart_1973387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973387 prefixEnd_1973387 := by exact prefixLift 1973387
  have htrace : WordTrace (prefixWord ++ tailWord_1973387) baseStart_1973387 baseEnd_1973387 := by
    simpa [prefixWord, tailWord_1973387, baseEnd_1973387] using wordTrace_append hprefix tailTrace_1973387
  have hstable : (prefixWord ++ tailWord_1973387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973387).length < 2 ^ (prefixWord ++ tailWord_1973387).sum := by decide
  have hdescent : baseEnd_1973387 < baseStart_1973387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973438 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1973438 : Nat := 118140960795 + 1973438 * 2 ^ 59
def prefixEnd_1973438 : Nat := 4983230072969 + 3 ^ 40 * 1973438 * 2
def baseEnd_1973438 : Nat := 450365438154468954866369

theorem tailTrace_1973438 : CollatzResearch.WordTrace tailWord_1973438 prefixEnd_1973438 450365438154468954866369 := by
  unfold tailWord_1973438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997149628072329652834121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47984798016385758148448645 8997149628072329652834121)
  ·
    refine ⟨6747862221054247239625591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8997149628072329652834121 6747862221054247239625591)
    ·
      refine ⟨10121793331581370859438387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6747862221054247239625591 10121793331581370859438387)
      ·
        refine ⟨15182689997372056289157581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10121793331581370859438387 15182689997372056289157581)
        ·
          refine ⟨5693508749014521108434093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15182689997372056289157581 5693508749014521108434093)
          ·
            refine ⟨2135065780880445415662785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5693508749014521108434093 2135065780880445415662785)
            ·
              refine ⟨1601299335660334061747089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135065780880445415662785 1601299335660334061747089)
              ·
                refine ⟨1200974501745250546310317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601299335660334061747089 1200974501745250546310317)
                ·
                  refine ⟨450365438154468954866369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200974501745250546310317 450365438154468954866369)
                  ·
                    rfl

theorem cell21_1973438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1973438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973438 prefixEnd_1973438 := by exact prefixLift 1973438
  have htrace : WordTrace (prefixWord ++ tailWord_1973438) baseStart_1973438 baseEnd_1973438 := by
    simpa [prefixWord, tailWord_1973438, baseEnd_1973438] using wordTrace_append hprefix tailTrace_1973438
  have hstable : (prefixWord ++ tailWord_1973438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973438).length < 2 ^ (prefixWord ++ tailWord_1973438).sum := by decide
  have hdescent : baseEnd_1973438 < baseStart_1973438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973480 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 3]
def baseStart_1973480 : Nat := 118140960795 + 1973480 * 2 ^ 59
def prefixEnd_1973480 : Nat := 4983230072969 + 3 ^ 40 * 1973480 * 2
def baseEnd_1973480 : Nat := 450375023126686215166283

theorem tailTrace_1973480 : CollatzResearch.WordTrace tailWord_1973480 prefixEnd_1973480 450375023126686215166283 := by
  unfold tailWord_1973480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35989364445213239197850947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47985819260284318930467929 35989364445213239197850947)
  ·
    refine ⟨53984046667819858796776421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35989364445213239197850947 53984046667819858796776421)
    ·
      refine ⟨10122008750216223524395579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53984046667819858796776421 10122008750216223524395579)
      ·
        refine ⟨15183013125324335286593369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122008750216223524395579 15183013125324335286593369)
        ·
          refine ⟨11387259843993251464945027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15183013125324335286593369 11387259843993251464945027)
          ·
            refine ⟨17080889765989877197417541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387259843993251464945027 17080889765989877197417541)
            ·
              refine ⟨3202666831123101974515789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17080889765989877197417541 3202666831123101974515789)
              ·
                refine ⟨1201000061671163240443421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3202666831123101974515789 1201000061671163240443421)
                ·
                  refine ⟨450375023126686215166283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201000061671163240443421 450375023126686215166283)
                  ·
                    rfl

theorem cell21_1973480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_1973480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973480 prefixEnd_1973480 := by exact prefixLift 1973480
  have htrace : WordTrace (prefixWord ++ tailWord_1973480) baseStart_1973480 baseEnd_1973480 := by
    simpa [prefixWord, tailWord_1973480, baseEnd_1973480] using wordTrace_append hprefix tailTrace_1973480
  have hstable : (prefixWord ++ tailWord_1973480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973480).length < 2 ^ (prefixWord ++ tailWord_1973480).sum := by decide
  have hdescent : baseEnd_1973480 < baseStart_1973480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973491 : List Nat := [1, 1, 1, 2, 2, 6, 8]
def baseStart_1973491 : Nat := 118140960795 + 1973491 * 2 ^ 59
def prefixEnd_1973491 : Nat := 4983230072969 + 3 ^ 40 * 1973491 * 2
def baseEnd_1973491 : Nat := 50041948164061404498103

theorem tailTrace_1973491 : CollatzResearch.WordTrace tailWord_1973491 prefixEnd_1973491 50041948164061404498103 := by
  unfold tailWord_1973491
  simp only [CollatzResearch.WordTrace]
  refine ⟨71979130093386627274352327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47986086728924418182901551 71979130093386627274352327)
  ·
    refine ⟨107968695140079940911528491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71979130093386627274352327 107968695140079940911528491)
    ·
      refine ⟨161953042710119911367292737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107968695140079940911528491 161953042710119911367292737)
      ·
        refine ⟨121464782032589933525469553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161953042710119911367292737 121464782032589933525469553)
        ·
          refine ⟨91098586524442450144102165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121464782032589933525469553 91098586524442450144102165)
          ·
            refine ⟨4270246243333239850504789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91098586524442450144102165 4270246243333239850504789)
            ·
              refine ⟨50041948164061404498103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4270246243333239850504789 50041948164061404498103)
              ·
                rfl

theorem cell21_1973491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 8].length) (baseStart_1973491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973491 prefixEnd_1973491 := by exact prefixLift 1973491
  have htrace : WordTrace (prefixWord ++ tailWord_1973491) baseStart_1973491 baseEnd_1973491 := by
    simpa [prefixWord, tailWord_1973491, baseEnd_1973491] using wordTrace_append hprefix tailTrace_1973491
  have hstable : (prefixWord ++ tailWord_1973491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973491).length < 2 ^ (prefixWord ++ tailWord_1973491).sum := by decide
  have hdescent : baseEnd_1973491 < baseStart_1973491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973553 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_1973553 : Nat := 118140960795 + 1973553 * 2 ^ 59
def prefixEnd_1973553 : Nat := 4983230072969 + 3 ^ 40 * 1973553 * 2
def baseEnd_1973553 : Nat := 450391682721254310449467

theorem tailTrace_1973553 : CollatzResearch.WordTrace tailWord_1973553 prefixEnd_1973553 450391682721254310449467 := by
  unfold tailWord_1973553
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981391419162011863109313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47987594279441341242072875 71981391419162011863109313)
  ·
    refine ⟨53986043564371508897331985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71981391419162011863109313 53986043564371508897331985)
    ·
      refine ⟨40489532673278631672998989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53986043564371508897331985 40489532673278631672998989)
      ·
        refine ⟨15183574752479486877374621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40489532673278631672998989 15183574752479486877374621)
        ·
          refine ⟨5693840532179807579015483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15183574752479486877374621 5693840532179807579015483)
          ·
            refine ⟨8540760798269711368523225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5693840532179807579015483 8540760798269711368523225)
            ·
              refine ⟨6405570598702283526392419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8540760798269711368523225 6405570598702283526392419)
              ·
                refine ⟨9608355898053425289588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405570598702283526392419 9608355898053425289588629)
                ·
                  refine ⟨450391682721254310449467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9608355898053425289588629 450391682721254310449467)
                  ·
                    rfl

theorem cell21_1973553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_1973553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973553 prefixEnd_1973553 := by exact prefixLift 1973553
  have htrace : WordTrace (prefixWord ++ tailWord_1973553) baseStart_1973553 baseEnd_1973553 := by
    simpa [prefixWord, tailWord_1973553, baseEnd_1973553] using wordTrace_append hprefix tailTrace_1973553
  have hstable : (prefixWord ++ tailWord_1973553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973553).length < 2 ^ (prefixWord ++ tailWord_1973553).sum := by decide
  have hdescent : baseEnd_1973553 < baseStart_1973553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973567 : List Nat := [1, 1, 2, 2, 4, 2, 1, 8]
def baseStart_1973567 : Nat := 118140960795 + 1973567 * 2 ^ 59
def prefixEnd_1973567 : Nat := 4983230072969 + 3 ^ 40 * 1973567 * 2
def baseEnd_1973567 : Nat := 150131625903997799072035

theorem tailTrace_1973567 : CollatzResearch.WordTrace tailWord_1973567 prefixEnd_1973567 150131625903997799072035 := by
  unfold tailWord_1973567
  simp only [CollatzResearch.WordTrace]
  refine ⟨71981902041111292254118955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47987934694074194836079303 71981902041111292254118955)
  ·
    refine ⟨107972853061666938381178433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71981902041111292254118955 107972853061666938381178433)
    ·
      refine ⟨80979639796250203785883825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107972853061666938381178433 80979639796250203785883825)
      ·
        refine ⟨60734729847187652839412869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80979639796250203785883825 60734729847187652839412869)
        ·
          refine ⟨11387761846347684907389913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60734729847187652839412869 11387761846347684907389913)
          ·
            refine ⟨8540821384760763680542435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11387761846347684907389913 8540821384760763680542435)
            ·
              refine ⟨12811232077141145520813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8540821384760763680542435 12811232077141145520813653)
              ·
                refine ⟨150131625903997799072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12811232077141145520813653 150131625903997799072035)
                ·
                  rfl

theorem cell21_1973567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_1973567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973567 prefixEnd_1973567 := by exact prefixLift 1973567
  have htrace : WordTrace (prefixWord ++ tailWord_1973567) baseStart_1973567 baseEnd_1973567 := by
    simpa [prefixWord, tailWord_1973567, baseEnd_1973567] using wordTrace_append hprefix tailTrace_1973567
  have hstable : (prefixWord ++ tailWord_1973567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973567).length < 2 ^ (prefixWord ++ tailWord_1973567).sum := by decide
  have hdescent : baseEnd_1973567 < baseStart_1973567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973615 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 3]
def baseStart_1973615 : Nat := 118140960795 + 1973615 * 2 ^ 59
def prefixEnd_1973615 : Nat := 4983230072969 + 3 ^ 40 * 1973615 * 2
def baseEnd_1973615 : Nat := 450405831965955980416007

theorem tailTrace_1973615 : CollatzResearch.WordTrace tailWord_1973615 prefixEnd_1973615 450405831965955980416007 := by
  unfold tailWord_1973615
  simp only [CollatzResearch.WordTrace]
  refine ⟨71983652744937396451866299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47989101829958264301244199 71983652744937396451866299)
  ·
    refine ⟨107975479117406094677799449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71983652744937396451866299 107975479117406094677799449)
    ·
      refine ⟨80981609338054571008349587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107975479117406094677799449 80981609338054571008349587)
      ·
        refine ⟨121472414007081856512524381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80981609338054571008349587 121472414007081856512524381)
        ·
          refine ⟨45552155252655696192196643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121472414007081856512524381 45552155252655696192196643)
          ·
            refine ⟨68328232878983544288294965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45552155252655696192196643 68328232878983544288294965)
            ·
              refine ⟨6405771832404707277027653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68328232878983544288294965 6405771832404707277027653)
              ·
                refine ⟨1201082218575882614442685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6405771832404707277027653 1201082218575882614442685)
                ·
                  refine ⟨450405831965955980416007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201082218575882614442685 450405831965955980416007)
                  ·
                    rfl

theorem cell21_1973615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 3].length) (baseStart_1973615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973615 prefixEnd_1973615 := by exact prefixLift 1973615
  have htrace : WordTrace (prefixWord ++ tailWord_1973615) baseStart_1973615 baseEnd_1973615 := by
    simpa [prefixWord, tailWord_1973615, baseEnd_1973615] using wordTrace_append hprefix tailTrace_1973615
  have hstable : (prefixWord ++ tailWord_1973615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973615).length < 2 ^ (prefixWord ++ tailWord_1973615).sum := by decide
  have hdescent : baseEnd_1973615 < baseStart_1973615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973629 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_1973629 : Nat := 118140960795 + 1973629 * 2 ^ 59
def prefixEnd_1973629 : Nat := 4983230072969 + 3 ^ 40 * 1973629 * 2
def baseEnd_1973629 : Nat := 450409026956695067182645

theorem tailTrace_1973629 : CollatzResearch.WordTrace tailWord_1973629 prefixEnd_1973629 450409026956695067182645 := by
  unfold tailWord_1973629
  simp only [CollatzResearch.WordTrace]
  refine ⟨71984163366886676842875941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47989442244591117895250627 71984163366886676842875941)
  ·
    refine ⟨13497030631291251908039239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71984163366886676842875941 13497030631291251908039239)
    ·
      refine ⟨20245545946936877862058859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13497030631291251908039239 20245545946936877862058859)
      ·
        refine ⟨30368318920405316793088289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20245545946936877862058859 30368318920405316793088289)
        ·
          refine ⟨22776239190303987594816217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30368318920405316793088289 22776239190303987594816217)
          ·
            refine ⟨17082179392727990696112163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22776239190303987594816217 17082179392727990696112163)
            ·
              refine ⟨25623269089091986044168245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17082179392727990696112163 25623269089091986044168245)
              ·
                refine ⟨2402181477102373691640773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25623269089091986044168245 2402181477102373691640773)
                ·
                  refine ⟨450409026956695067182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402181477102373691640773 450409026956695067182645)
                  ·
                    rfl

theorem cell21_1973629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_1973629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973629 prefixEnd_1973629 := by exact prefixLift 1973629
  have htrace : WordTrace (prefixWord ++ tailWord_1973629) baseStart_1973629 baseEnd_1973629 := by
    simpa [prefixWord, tailWord_1973629, baseEnd_1973629] using wordTrace_append hprefix tailTrace_1973629
  have hstable : (prefixWord ++ tailWord_1973629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973629).length < 2 ^ (prefixWord ++ tailWord_1973629).sum := by decide
  have hdescent : baseEnd_1973629 < baseStart_1973629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973708 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 3]
def baseStart_1973708 : Nat := 118140960795 + 1973708 * 2 ^ 59
def prefixEnd_1973708 : Nat := 4983230072969 + 3 ^ 40 * 1973708 * 2
def baseEnd_1973708 : Nat := 450427055833008485365817

theorem tailTrace_1973708 : CollatzResearch.WordTrace tailWord_1973708 prefixEnd_1973708 450427055833008485365817 := by
  unfold tailWord_1973708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993522366800236667500889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47991363155733648890001185 35993522366800236667500889)
  ·
    refine ⟨26995141775100177500625667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35993522366800236667500889 26995141775100177500625667)
    ·
      refine ⟨40492712662650266250938501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26995141775100177500625667 40492712662650266250938501)
      ·
        refine ⟨7592383624246924922050969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40492712662650266250938501 7592383624246924922050969)
        ·
          refine ⟨5694287718185193691538227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592383624246924922050969 5694287718185193691538227)
          ·
            refine ⟨8541431577277790537307341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694287718185193691538227 8541431577277790537307341)
            ·
              refine ⟨3203036841479171451490253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8541431577277790537307341 3203036841479171451490253)
              ·
                refine ⟨1201138815554689294308845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203036841479171451490253 1201138815554689294308845)
                ·
                  refine ⟨450427055833008485365817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201138815554689294308845 450427055833008485365817)
                  ·
                    rfl

theorem cell21_1973708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_1973708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973708 prefixEnd_1973708 := by exact prefixLift 1973708
  have htrace : WordTrace (prefixWord ++ tailWord_1973708) baseStart_1973708 baseEnd_1973708 := by
    simpa [prefixWord, tailWord_1973708, baseEnd_1973708] using wordTrace_append hprefix tailTrace_1973708
  have hstable : (prefixWord ++ tailWord_1973708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973708).length < 2 ^ (prefixWord ++ tailWord_1973708).sum := by decide
  have hdescent : baseEnd_1973708 < baseStart_1973708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973725 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 3]
def baseStart_1973725 : Nat := 118140960795 + 1973725 * 2 ^ 59
def prefixEnd_1973725 : Nat := 4983230072969 + 3 ^ 40 * 1973725 * 2
def baseEnd_1973725 : Nat := 450430935464620233582449

theorem tailTrace_1973725 : CollatzResearch.WordTrace tailWord_1973725 prefixEnd_1973725 450430935464620233582449 := by
  unfold tailWord_1973725
  simp only [CollatzResearch.WordTrace]
  refine ⟨71987664774538885238370629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47991776516359256825580419 71987664774538885238370629)
  ·
    refine ⟨13497687145226040982194493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71987664774538885238370629 13497687145226040982194493)
    ·
      refine ⟨5061632679459765368322935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13497687145226040982194493 5061632679459765368322935)
      ·
        refine ⟨7592449019189648052484403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061632679459765368322935 7592449019189648052484403)
        ·
          refine ⟨11388673528784472078726605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592449019189648052484403 11388673528784472078726605)
          ·
            refine ⟨4270752573294177029522477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11388673528784472078726605 4270752573294177029522477)
            ·
              refine ⟨1601532214985316386070929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4270752573294177029522477 1601532214985316386070929)
              ·
                refine ⟨1201149161238987289553197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601532214985316386070929 1201149161238987289553197)
                ·
                  refine ⟨450430935464620233582449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201149161238987289553197 450430935464620233582449)
                  ·
                    rfl

theorem cell21_1973725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_1973725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973725 prefixEnd_1973725 := by exact prefixLift 1973725
  have htrace : WordTrace (prefixWord ++ tailWord_1973725) baseStart_1973725 baseEnd_1973725 := by
    simpa [prefixWord, tailWord_1973725, baseEnd_1973725] using wordTrace_append hprefix tailTrace_1973725
  have hstable : (prefixWord ++ tailWord_1973725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973725).length < 2 ^ (prefixWord ++ tailWord_1973725).sum := by decide
  have hdescent : baseEnd_1973725 < baseStart_1973725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973781 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1973781 : Nat := 118140960795 + 1973781 * 2 ^ 59
def prefixEnd_1973781 : Nat := 4983230072969 + 3 ^ 40 * 1973781 * 2
def baseEnd_1973781 : Nat := 450443715427576580649001

theorem tailTrace_1973781 : CollatzResearch.WordTrace tailWord_1973781 prefixEnd_1973781 450443715427576580649001 := by
  unfold tailWord_1973781
  simp only [CollatzResearch.WordTrace]
  refine ⟨71989707262336006802409197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47993138174890671201606131 71989707262336006802409197)
  ·
    refine ⟨26996140223376002550903449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71989707262336006802409197 26996140223376002550903449)
    ·
      refine ⟨20247105167532001913177587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26996140223376002550903449 20247105167532001913177587)
      ·
        refine ⟨30370657751298002869766381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20247105167532001913177587 30370657751298002869766381)
        ·
          refine ⟨11388996656736751076162393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30370657751298002869766381 11388996656736751076162393)
          ·
            refine ⟨8541747492552563307121795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11388996656736751076162393 8541747492552563307121795)
            ·
              refine ⟨12812621238828844960682693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541747492552563307121795 12812621238828844960682693)
              ·
                refine ⟨2402366482280408430128005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12812621238828844960682693 2402366482280408430128005)
                ·
                  refine ⟨450443715427576580649001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402366482280408430128005 450443715427576580649001)
                  ·
                    rfl

theorem cell21_1973781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1973781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973781 prefixEnd_1973781 := by exact prefixLift 1973781
  have htrace : WordTrace (prefixWord ++ tailWord_1973781) baseStart_1973781 baseEnd_1973781 := by
    simpa [prefixWord, tailWord_1973781, baseEnd_1973781] using wordTrace_append hprefix tailTrace_1973781
  have hstable : (prefixWord ++ tailWord_1973781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973781).length < 2 ^ (prefixWord ++ tailWord_1973781).sum := by decide
  have hdescent : baseEnd_1973781 < baseStart_1973781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973784 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_1973784 : Nat := 118140960795 + 1973784 * 2 ^ 59
def prefixEnd_1973784 : Nat := 4983230072969 + 3 ^ 40 * 1973784 * 2
def baseEnd_1973784 : Nat := 450444400068449242098995

theorem tailTrace_1973784 : CollatzResearch.WordTrace tailWord_1973784 prefixEnd_1973784 450444400068449242098995 := by
  unfold tailWord_1973784
  simp only [CollatzResearch.WordTrace]
  refine ⟨35994908340662569157384203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47993211120883425543178937 35994908340662569157384203)
  ·
    refine ⟨53992362510993853736076305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35994908340662569157384203 53992362510993853736076305)
    ·
      refine ⟨40494271883245390302057229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53992362510993853736076305 40494271883245390302057229)
      ·
        refine ⟨15185351956217021363271461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40494271883245390302057229 15185351956217021363271461)
        ·
          refine ⟨2847253491790691505613399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15185351956217021363271461 2847253491790691505613399)
          ·
            refine ⟨4270880237686037258420099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847253491790691505613399 4270880237686037258420099)
            ·
              refine ⟨6406320356529055887630149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270880237686037258420099 6406320356529055887630149)
              ·
                refine ⟨1201185066849197978930653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6406320356529055887630149 1201185066849197978930653)
                ·
                  refine ⟨450444400068449242098995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201185066849197978930653 450444400068449242098995)
                  ·
                    rfl

theorem cell21_1973784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_1973784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973784 prefixEnd_1973784 := by exact prefixLift 1973784
  have htrace : WordTrace (prefixWord ++ tailWord_1973784) baseStart_1973784 baseEnd_1973784 := by
    simpa [prefixWord, tailWord_1973784, baseEnd_1973784] using wordTrace_append hprefix tailTrace_1973784
  have hstable : (prefixWord ++ tailWord_1973784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973784).length < 2 ^ (prefixWord ++ tailWord_1973784).sum := by decide
  have hdescent : baseEnd_1973784 < baseStart_1973784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973840 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_1973840 : Nat := 118140960795 + 1973840 * 2 ^ 59
def prefixEnd_1973840 : Nat := 4983230072969 + 3 ^ 40 * 1973840 * 2
def baseEnd_1973840 : Nat := 450457180031405589165547

theorem tailTrace_1973840 : CollatzResearch.WordTrace tailWord_1973840 prefixEnd_1973840 450457180031405589165547 := by
  unfold tailWord_1973840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35995929584561129939403487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47994572779414839919204649 35995929584561129939403487)
  ·
    refine ⟨53993894376841694909105231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35995929584561129939403487 53993894376841694909105231)
    ·
      refine ⟨80990841565262542363657847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53993894376841694909105231 80990841565262542363657847)
      ·
        refine ⟨121486262347893813545486771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80990841565262542363657847 121486262347893813545486771)
        ·
          refine ⟨182229393521840720318230157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121486262347893813545486771 182229393521840720318230157)
          ·
            refine ⟨68336022570690270119336309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182229393521840720318230157 68336022570690270119336309)
            ·
              refine ⟨6406502116002212823687779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68336022570690270119336309 6406502116002212823687779)
              ·
                refine ⟨9609753174003319235531669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406502116002212823687779 9609753174003319235531669)
                ·
                  refine ⟨450457180031405589165547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9609753174003319235531669 450457180031405589165547)
                  ·
                    rfl

theorem cell21_1973840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_1973840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973840 prefixEnd_1973840 := by exact prefixLift 1973840
  have htrace : WordTrace (prefixWord ++ tailWord_1973840) baseStart_1973840 baseEnd_1973840 := by
    simpa [prefixWord, tailWord_1973840, baseEnd_1973840] using wordTrace_append hprefix tailTrace_1973840
  have hstable : (prefixWord ++ tailWord_1973840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973840).length < 2 ^ (prefixWord ++ tailWord_1973840).sum := by decide
  have hdescent : baseEnd_1973840 < baseStart_1973840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973877 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 3]
def baseStart_1973877 : Nat := 118140960795 + 1973877 * 2 ^ 59
def prefixEnd_1973877 : Nat := 4983230072969 + 3 ^ 40 * 1973877 * 2
def baseEnd_1973877 : Nat := 450465623935501747048805

theorem tailTrace_1973877 : CollatzResearch.WordTrace tailWord_1973877 prefixEnd_1973877 450465623935501747048805 := by
  unfold tailWord_1973877
  simp only [CollatzResearch.WordTrace]
  refine ⟨71993208669988215197903885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47995472446658810131935923 71993208669988215197903885)
  ·
    refine ⟨26997453251245580699213957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71993208669988215197903885 26997453251245580699213957)
    ·
      refine ⟨5062022484608546381102617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26997453251245580699213957 5062022484608546381102617)
      ·
        refine ⟨3796516863456409785826963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062022484608546381102617 3796516863456409785826963)
        ·
          refine ⟨5694775295184614678740445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796516863456409785826963 5694775295184614678740445)
          ·
            refine ⟨2135540735694230504527667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5694775295184614678740445 2135540735694230504527667)
            ·
              refine ⟨3203311103541345756791501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135540735694230504527667 3203311103541345756791501)
              ·
                refine ⟨1201241663828004658796813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203311103541345756791501 1201241663828004658796813)
                ·
                  refine ⟨450465623935501747048805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201241663828004658796813 450465623935501747048805)
                  ·
                    rfl

theorem cell21_1973877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_1973877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973877 prefixEnd_1973877 := by exact prefixLift 1973877
  have htrace : WordTrace (prefixWord ++ tailWord_1973877) baseStart_1973877 baseEnd_1973877 := by
    simpa [prefixWord, tailWord_1973877, baseEnd_1973877] using wordTrace_append hprefix tailTrace_1973877
  have hstable : (prefixWord ++ tailWord_1973877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973877).length < 2 ^ (prefixWord ++ tailWord_1973877).sum := by decide
  have hdescent : baseEnd_1973877 < baseStart_1973877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973908 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1973908 : Nat := 118140960795 + 1973908 * 2 ^ 59
def prefixEnd_1973908 : Nat := 4983230072969 + 3 ^ 40 * 1973908 * 2
def baseEnd_1973908 : Nat := 450472698557852582032075

theorem tailTrace_1973908 : CollatzResearch.WordTrace tailWord_1973908 prefixEnd_1973908 450472698557852582032075 := by
  unfold tailWord_1973908
  simp only [CollatzResearch.WordTrace]
  refine ⟨35997169666437953746141189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47996226221917271661521585 35997169666437953746141189)
  ·
    refine ⟨6749469312457116327401473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35997169666437953746141189 6749469312457116327401473)
    ·
      refine ⟨5062101984342837245551105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6749469312457116327401473 5062101984342837245551105)
      ·
        refine ⟨3796576488257127934163329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062101984342837245551105 3796576488257127934163329)
        ·
          refine ⟨2847432366192845950622497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796576488257127934163329 2847432366192845950622497)
          ·
            refine ⟨2135574274644634462966873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2847432366192845950622497 2135574274644634462966873)
            ·
              refine ⟨1601680705983475847225155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135574274644634462966873 1601680705983475847225155)
              ·
                refine ⟨2402521058975213770837733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601680705983475847225155 2402521058975213770837733)
                ·
                  refine ⟨450472698557852582032075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402521058975213770837733 450472698557852582032075)
                  ·
                    rfl

theorem cell21_1973908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1973908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973908 prefixEnd_1973908 := by exact prefixLift 1973908
  have htrace : WordTrace (prefixWord ++ tailWord_1973908) baseStart_1973908 baseEnd_1973908 := by
    simpa [prefixWord, tailWord_1973908, baseEnd_1973908] using wordTrace_append hprefix tailTrace_1973908
  have hstable : (prefixWord ++ tailWord_1973908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973908).length < 2 ^ (prefixWord ++ tailWord_1973908).sum := by decide
  have hdescent : baseEnd_1973908 < baseStart_1973908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973950 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1973950 : Nat := 118140960795 + 1973950 * 2 ^ 59
def prefixEnd_1973950 : Nat := 4983230072969 + 3 ^ 40 * 1973950 * 2
def baseEnd_1973950 : Nat := 450482283530069842331989

theorem tailTrace_1973950 : CollatzResearch.WordTrace tailWord_1973950 prefixEnd_1973950 450482283530069842331989 := by
  unfold tailWord_1973950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999483899840468583163913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47997247465815832443540869 8999483899840468583163913)
  ·
    refine ⟨6749612924880351437372935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8999483899840468583163913 6749612924880351437372935)
    ·
      refine ⟨10124419387320527156059403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749612924880351437372935 10124419387320527156059403)
      ·
        refine ⟨15186629080980790734089105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10124419387320527156059403 15186629080980790734089105)
        ·
          refine ⟨11389971810735593050566829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15186629080980790734089105 11389971810735593050566829)
          ·
            refine ⟨4271239429025847393962561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11389971810735593050566829 4271239429025847393962561)
            ·
              refine ⟨3203429571769385545471921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271239429025847393962561 3203429571769385545471921)
              ·
                refine ⟨2402572178827039159103941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203429571769385545471921 2402572178827039159103941)
                ·
                  refine ⟨450482283530069842331989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402572178827039159103941 450482283530069842331989)
                  ·
                    rfl

theorem cell21_1973950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1973950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973950 prefixEnd_1973950 := by exact prefixLift 1973950
  have htrace : WordTrace (prefixWord ++ tailWord_1973950) baseStart_1973950 baseEnd_1973950 := by
    simpa [prefixWord, tailWord_1973950, baseEnd_1973950] using wordTrace_append hprefix tailTrace_1973950
  have hstable : (prefixWord ++ tailWord_1973950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973950).length < 2 ^ (prefixWord ++ tailWord_1973950).sum := by decide
  have hdescent : baseEnd_1973950 < baseStart_1973950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973978 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1973978 : Nat := 118140960795 + 1973978 * 2 ^ 59
def prefixEnd_1973978 : Nat := 4983230072969 + 3 ^ 40 * 1973978 * 2
def baseEnd_1973978 : Nat := 450488673511548015865265

theorem tailTrace_1973978 : CollatzResearch.WordTrace tailWord_1973978 prefixEnd_1973978 450488673511548015865265 := by
  unfold tailWord_1973978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999223110655577361832647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47997928295081539631553725 17999223110655577361832647)
  ·
    refine ⟨26998834665983366042748971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17999223110655577361832647 26998834665983366042748971)
    ·
      refine ⟨40498251998975049064123457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26998834665983366042748971 40498251998975049064123457)
      ·
        refine ⟨30373688999231286798092593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40498251998975049064123457 30373688999231286798092593)
        ·
          refine ⟨22780266749423465098569445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30373688999231286798092593 22780266749423465098569445)
          ·
            refine ⟨4271300015516899705981771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22780266749423465098569445 4271300015516899705981771)
            ·
              refine ⟨6406950023275349558972657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271300015516899705981771 6406950023275349558972657)
              ·
                refine ⟨4805212517456512169229493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6406950023275349558972657 4805212517456512169229493)
                ·
                  refine ⟨450488673511548015865265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4805212517456512169229493 450488673511548015865265)
                  ·
                    rfl

theorem cell21_1973978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1973978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1973978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1973978 prefixEnd_1973978 := by exact prefixLift 1973978
  have htrace : WordTrace (prefixWord ++ tailWord_1973978) baseStart_1973978 baseEnd_1973978 := by
    simpa [prefixWord, tailWord_1973978, baseEnd_1973978] using wordTrace_append hprefix tailTrace_1973978
  have hstable : (prefixWord ++ tailWord_1973978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973978).length < 2 ^ (prefixWord ++ tailWord_1973978).sum := by decide
  have hdescent : baseEnd_1973978 < baseStart_1973978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974026 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_1974026 : Nat := 118140960795 + 1974026 * 2 ^ 59
def prefixEnd_1974026 : Nat := 4983230072969 + 3 ^ 40 * 1974026 * 2
def baseEnd_1974026 : Nat := 450499627765510599065167

theorem tailTrace_1974026 : CollatzResearch.WordTrace tailWord_1974026 prefixEnd_1974026 450499627765510599065167 := by
  unfold tailWord_1974026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999660786612103411269483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47999095430965609096718621 17999660786612103411269483)
  ·
    refine ⟨26999491179918155116904225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17999660786612103411269483 26999491179918155116904225)
    ·
      refine ⟨20249618384938616337678169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26999491179918155116904225 20249618384938616337678169)
      ·
        refine ⟨15187213788703962253258627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20249618384938616337678169 15187213788703962253258627)
        ·
          refine ⟨22780820683055943379887941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15187213788703962253258627 22780820683055943379887941)
          ·
            refine ⟨4271403878072989383728989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22780820683055943379887941 4271403878072989383728989)
            ·
              refine ⟨1601776454277371018898371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4271403878072989383728989 1601776454277371018898371)
              ·
                refine ⟨2402664681416056528347557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601776454277371018898371 2402664681416056528347557)
                ·
                  refine ⟨450499627765510599065167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402664681416056528347557 450499627765510599065167)
                  ·
                    rfl

theorem cell21_1974026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_1974026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974026 prefixEnd_1974026 := by exact prefixLift 1974026
  have htrace : WordTrace (prefixWord ++ tailWord_1974026) baseStart_1974026 baseEnd_1974026 := by
    simpa [prefixWord, tailWord_1974026, baseEnd_1974026] using wordTrace_append hprefix tailTrace_1974026
  have hstable : (prefixWord ++ tailWord_1974026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974026).length < 2 ^ (prefixWord ++ tailWord_1974026).sum := by decide
  have hdescent : baseEnd_1974026 < baseStart_1974026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974122 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_1974122 : Nat := 118140960795 + 1974122 * 2 ^ 59
def prefixEnd_1974122 : Nat := 4983230072969 + 3 ^ 40 * 1974122 * 2
def baseEnd_1974122 : Nat := 450521536273435765464971

theorem tailTrace_1974122 : CollatzResearch.WordTrace tailWord_1974122 prefixEnd_1974122 450521536273435765464971 := by
  unfold tailWord_1974122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000536138525155510143155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48001429702733748027048413 18000536138525155510143155)
  ·
    refine ⟨27000804207787733265214733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18000536138525155510143155 27000804207787733265214733)
    ·
      refine ⟨10125301577920399974455525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27000804207787733265214733 10125301577920399974455525)
      ·
        refine ⟨1898494045860074995210411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10125301577920399974455525 1898494045860074995210411)
        ·
          refine ⟨2847741068790112492815617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898494045860074995210411 2847741068790112492815617)
          ·
            refine ⟨2135805801592584369611713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2847741068790112492815617 2135805801592584369611713)
            ·
              refine ⟨1601854351194438277208785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135805801592584369611713 1601854351194438277208785)
              ·
                refine ⟨1201390763395828707906589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601854351194438277208785 1201390763395828707906589)
                ·
                  refine ⟨450521536273435765464971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201390763395828707906589 450521536273435765464971)
                  ·
                    rfl

theorem cell21_1974122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_1974122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974122 prefixEnd_1974122 := by exact prefixLift 1974122
  have htrace : WordTrace (prefixWord ++ tailWord_1974122) baseStart_1974122 baseEnd_1974122 := by
    simpa [prefixWord, tailWord_1974122, baseEnd_1974122] using wordTrace_append hprefix tailTrace_1974122
  have hstable : (prefixWord ++ tailWord_1974122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974122).length < 2 ^ (prefixWord ++ tailWord_1974122).sum := by decide
  have hdescent : baseEnd_1974122 < baseStart_1974122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974144 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_1974144 : Nat := 118140960795 + 1974144 * 2 ^ 59
def prefixEnd_1974144 : Nat := 4983230072969 + 3 ^ 40 * 1974144 * 2
def baseEnd_1974144 : Nat := 450526556973168616098259

theorem tailTrace_1974144 : CollatzResearch.WordTrace tailWord_1974144 prefixEnd_1974144 450526556973168616098259 := by
  unfold tailWord_1974144
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001473480010459898936743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48001964640013946531915657 36001473480010459898936743)
  ·
    refine ⟨54002210220015689848405115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36001473480010459898936743 54002210220015689848405115)
    ·
      refine ⟨81003315330023534772607673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54002210220015689848405115 81003315330023534772607673)
      ·
        refine ⟨60752486497517651079455755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81003315330023534772607673 60752486497517651079455755)
        ·
          refine ⟨91128729746276476619183633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60752486497517651079455755 91128729746276476619183633)
          ·
            refine ⟨68346547309707357464387725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91128729746276476619183633 68346547309707357464387725)
            ·
              refine ⟨25629955241140259049145397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68346547309707357464387725 25629955241140259049145397)
              ·
                refine ⟨2402808303856899285857381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25629955241140259049145397 2402808303856899285857381)
                ·
                  refine ⟨450526556973168616098259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402808303856899285857381 450526556973168616098259)
                  ·
                    rfl

theorem cell21_1974144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_1974144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974144 prefixEnd_1974144 := by exact prefixLift 1974144
  have htrace : WordTrace (prefixWord ++ tailWord_1974144) baseStart_1974144 baseEnd_1974144 := by
    simpa [prefixWord, tailWord_1974144, baseEnd_1974144] using wordTrace_append hprefix tailTrace_1974144
  have hstable : (prefixWord ++ tailWord_1974144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974144).length < 2 ^ (prefixWord ++ tailWord_1974144).sum := by decide
  have hdescent : baseEnd_1974144 < baseStart_1974144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974164 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1974164 : Nat := 118140960795 + 1974164 * 2 ^ 59
def prefixEnd_1974164 : Nat := 4983230072969 + 3 ^ 40 * 1974164 * 2
def baseEnd_1974164 : Nat := 450531121245653025764885

theorem tailTrace_1974164 : CollatzResearch.WordTrace tailWord_1974164 prefixEnd_1974164 450531121245653025764885 := by
  unfold tailWord_1974164
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001838209974231606800773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48002450946632308809067697 36001838209974231606800773)
  ·
    refine ⟨6750344664370168426275145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36001838209974231606800773 6750344664370168426275145)
    ·
      refine ⟨5062758498277626319706359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6750344664370168426275145 5062758498277626319706359)
      ·
        refine ⟨7594137747416439479559539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062758498277626319706359 7594137747416439479559539)
        ·
          refine ⟨11391206621124659219339309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594137747416439479559539 11391206621124659219339309)
          ·
            refine ⟨4271702482921747207252241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11391206621124659219339309 4271702482921747207252241)
            ·
              refine ⟨3203776862191310405439181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271702482921747207252241 3203776862191310405439181)
              ·
                refine ⟨1201416323321741402039693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203776862191310405439181 1201416323321741402039693)
                ·
                  refine ⟨450531121245653025764885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201416323321741402039693 450531121245653025764885)
                  ·
                    rfl

theorem cell21_1974164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1974164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974164 prefixEnd_1974164 := by exact prefixLift 1974164
  have htrace : WordTrace (prefixWord ++ tailWord_1974164) baseStart_1974164 baseEnd_1974164 := by
    simpa [prefixWord, tailWord_1974164, baseEnd_1974164] using wordTrace_append hprefix tailTrace_1974164
  have hstable : (prefixWord ++ tailWord_1974164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974164).length < 2 ^ (prefixWord ++ tailWord_1974164).sum := by decide
  have hdescent : baseEnd_1974164 < baseStart_1974164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974175 : List Nat := [1, 1, 2, 5, 3, 1, 8]
def baseStart_1974175 : Nat := 118140960795 + 1974175 * 2 ^ 59
def prefixEnd_1974175 : Nat := 4983230072969 + 3 ^ 40 * 1974175 * 2
def baseEnd_1974175 : Nat := 50059292399502161231281

theorem tailTrace_1974175 : CollatzResearch.WordTrace tailWord_1974175 prefixEnd_1974175 50059292399502161231281 := by
  unfold tailWord_1974175
  simp only [CollatzResearch.WordTrace]
  refine ⟨72004077622908612092251979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48002718415272408061501319 72004077622908612092251979)
  ·
    refine ⟨108006116434362918138377969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72004077622908612092251979 108006116434362918138377969)
    ·
      refine ⟨81004587325772188603783477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108006116434362918138377969 81004587325772188603783477)
      ·
        refine ⟨7594180061791142681604701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81004587325772188603783477 7594180061791142681604701)
        ·
          refine ⟨2847817523171678505601763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7594180061791142681604701 2847817523171678505601763)
          ·
            refine ⟨4271726284757517758402645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847817523171678505601763 4271726284757517758402645)
            ·
              refine ⟨50059292399502161231281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4271726284757517758402645 50059292399502161231281)
              ·
                rfl

theorem cell21_1974175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 8].length) (baseStart_1974175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974175 prefixEnd_1974175 := by exact prefixLift 1974175
  have htrace : WordTrace (prefixWord ++ tailWord_1974175) baseStart_1974175 baseEnd_1974175 := by
    simpa [prefixWord, tailWord_1974175, baseEnd_1974175] using wordTrace_append hprefix tailTrace_1974175
  have hstable : (prefixWord ++ tailWord_1974175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974175).length < 2 ^ (prefixWord ++ tailWord_1974175).sum := by decide
  have hdescent : baseEnd_1974175 < baseStart_1974175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974203 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 8]
def baseStart_1974203 : Nat := 118140960795 + 1974203 * 2 ^ 59
def prefixEnd_1974203 : Nat := 4983230072969 + 3 ^ 40 * 1974203 * 2
def baseEnd_1974203 : Nat := 450540021576997624614805

theorem tailTrace_1974203 : CollatzResearch.WordTrace tailWord_1974203 prefixEnd_1974203 450540021576997624614805 := by
  unfold tailWord_1974203
  simp only [CollatzResearch.WordTrace]
  refine ⟨72005098866807172874271263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48003399244538115249514175 72005098866807172874271263)
  ·
    refine ⟨108007648300210759311406895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72005098866807172874271263 108007648300210759311406895)
    ·
      refine ⟨162011472450316138967110343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108007648300210759311406895 162011472450316138967110343)
      ·
        refine ⟨243017208675474208450665515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162011472450316138967110343 243017208675474208450665515)
        ·
          refine ⟨364525813013211312675998273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243017208675474208450665515 364525813013211312675998273)
          ·
            refine ⟨273394359759908484506998705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364525813013211312675998273 273394359759908484506998705)
            ·
              refine ⟨205045769819931363380249029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273394359759908484506998705 205045769819931363380249029)
              ·
                refine ⟨38446081841237130633796693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205045769819931363380249029 38446081841237130633796693)
                ·
                  refine ⟨450540021576997624614805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38446081841237130633796693 450540021576997624614805)
                  ·
                    rfl

theorem cell21_1974203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_1974203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974203 prefixEnd_1974203 := by exact prefixLift 1974203
  have htrace : WordTrace (prefixWord ++ tailWord_1974203) baseStart_1974203 baseEnd_1974203 := by
    simpa [prefixWord, tailWord_1974203, baseEnd_1974203] using wordTrace_append hprefix tailTrace_1974203
  have hstable : (prefixWord ++ tailWord_1974203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974203).length < 2 ^ (prefixWord ++ tailWord_1974203).sum := by decide
  have hdescent : baseEnd_1974203 < baseStart_1974203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974206 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1974206 : Nat := 118140960795 + 1974206 * 2 ^ 59
def prefixEnd_1974206 : Nat := 4983230072969 + 3 ^ 40 * 1974206 * 2
def baseEnd_1974206 : Nat := 450540706217870286064799

theorem tailTrace_1974206 : CollatzResearch.WordTrace tailWord_1974206 prefixEnd_1974206 450540706217870286064799 := by
  unfold tailWord_1974206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000651035724538048328809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48003472190530869591086981 9000651035724538048328809)
  ·
    refine ⟨6750488276793403536246607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9000651035724538048328809 6750488276793403536246607)
    ·
      refine ⟨10125732415190105304369911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6750488276793403536246607 10125732415190105304369911)
      ·
        refine ⟨15188598622785157956554867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10125732415190105304369911 15188598622785157956554867)
        ·
          refine ⟨22782897934177736934832301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15188598622785157956554867 22782897934177736934832301)
          ·
            refine ⟨8543586725316651350562113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22782897934177736934832301 8543586725316651350562113)
            ·
              refine ⟨6407690043987488512921585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8543586725316651350562113 6407690043987488512921585)
              ·
                refine ⟨4805767532990616384691189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6407690043987488512921585 4805767532990616384691189)
                ·
                  refine ⟨450540706217870286064799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4805767532990616384691189 450540706217870286064799)
                  ·
                    rfl

theorem cell21_1974206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1974206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974206 prefixEnd_1974206 := by exact prefixLift 1974206
  have htrace : WordTrace (prefixWord ++ tailWord_1974206) baseStart_1974206 baseEnd_1974206 := by
    simpa [prefixWord, tailWord_1974206, baseEnd_1974206] using wordTrace_append hprefix tailTrace_1974206
  have hstable : (prefixWord ++ tailWord_1974206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974206).length < 2 ^ (prefixWord ++ tailWord_1974206).sum := by decide
  have hdescent : baseEnd_1974206 < baseStart_1974206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974220 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_1974220 : Nat := 118140960795 + 1974220 * 2 ^ 59
def prefixEnd_1974220 : Nat := 4983230072969 + 3 ^ 40 * 1974220 * 2
def baseEnd_1974220 : Nat := 450543901208609372831437

theorem tailTrace_1974220 : CollatzResearch.WordTrace tailWord_1974220 prefixEnd_1974220 450543901208609372831437 := by
  unfold tailWord_1974220
  simp only [CollatzResearch.WordTrace]
  refine ⟨36002859453872792388820057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48003812605163723185093409 36002859453872792388820057)
  ·
    refine ⟨27002144590404594291615043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36002859453872792388820057 27002144590404594291615043)
    ·
      refine ⟨40503216885606891437422565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27002144590404594291615043 40503216885606891437422565)
      ·
        refine ⟨7594353166051292144516731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40503216885606891437422565 7594353166051292144516731)
        ·
          refine ⟨11391529749076938216775097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594353166051292144516731 11391529749076938216775097)
          ·
            refine ⟨8543647311807703662581323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11391529749076938216775097 8543647311807703662581323)
            ·
              refine ⟨12815470967711555493871985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8543647311807703662581323 12815470967711555493871985)
              ·
                refine ⟨9611603225783666620403989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12815470967711555493871985 9611603225783666620403989)
                ·
                  refine ⟨450543901208609372831437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9611603225783666620403989 450543901208609372831437)
                  ·
                    rfl

theorem cell21_1974220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_1974220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974220 prefixEnd_1974220 := by exact prefixLift 1974220
  have htrace : WordTrace (prefixWord ++ tailWord_1974220) baseStart_1974220 baseEnd_1974220 := by
    simpa [prefixWord, tailWord_1974220, baseEnd_1974220] using wordTrace_append hprefix tailTrace_1974220
  have hstable : (prefixWord ++ tailWord_1974220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974220).length < 2 ^ (prefixWord ++ tailWord_1974220).sum := by decide
  have hdescent : baseEnd_1974220 < baseStart_1974220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974254 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_1974254 : Nat := 118140960795 + 1974254 * 2 ^ 59
def prefixEnd_1974254 : Nat := 4983230072969 + 3 ^ 40 * 1974254 * 2
def baseEnd_1974254 : Nat := 450551660471832869264701

theorem tailTrace_1974254 : CollatzResearch.WordTrace tailWord_1974254 prefixEnd_1974254 450551660471832869264701 := by
  unfold tailWord_1974254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000869873702801073047227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48004639326414939056251877 9000869873702801073047227)
  ·
    refine ⟨13501304810554201609570841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9000869873702801073047227 13501304810554201609570841)
    ·
      refine ⟨10125978607915651207178131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13501304810554201609570841 10125978607915651207178131)
      ·
        refine ⟨15188967911873476810767197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10125978607915651207178131 15188967911873476810767197)
        ·
          refine ⟨5695862966952553804037699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15188967911873476810767197 5695862966952553804037699)
          ·
            refine ⟨8543794450428830706056549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695862966952553804037699 8543794450428830706056549)
            ·
              refine ⟨1601961459455405757385603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8543794450428830706056549 1601961459455405757385603)
              ·
                refine ⟨2402942189183108636078405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601961459455405757385603 2402942189183108636078405)
                ·
                  refine ⟨450551660471832869264701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402942189183108636078405 450551660471832869264701)
                  ·
                    rfl

theorem cell21_1974254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_1974254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974254 prefixEnd_1974254 := by exact prefixLift 1974254
  have htrace : WordTrace (prefixWord ++ tailWord_1974254) baseStart_1974254 baseEnd_1974254 := by
    simpa [prefixWord, tailWord_1974254, baseEnd_1974254] using wordTrace_append hprefix tailTrace_1974254
  have hstable : (prefixWord ++ tailWord_1974254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974254).length < 2 ^ (prefixWord ++ tailWord_1974254).sum := by decide
  have hdescent : baseEnd_1974254 < baseStart_1974254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974285 : List Nat := [1, 7, 1, 2, 1, 9]
def baseStart_1974285 : Nat := 118140960795 + 1974285 * 2 ^ 59
def prefixEnd_1974285 : Nat := 4983230072969 + 3 ^ 40 * 1974285 * 2
def baseEnd_1974285 : Nat := 16687360559043840898073

theorem tailTrace_1974285 : CollatzResearch.WordTrace tailWord_1974285 prefixEnd_1974285 16687360559043840898073 := by
  unfold tailWord_1974285
  simp only [CollatzResearch.WordTrace]
  refine ⟨72008089652510100878756309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48005393101673400585837539 72008089652510100878756309)
  ·
    refine ⟨1687689601230705489345851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 72008089652510100878756309 1687689601230705489345851)
    ·
      refine ⟨2531534401846058234018777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687689601230705489345851 2531534401846058234018777)
      ·
        refine ⟨1898650801384543675514083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2531534401846058234018777 1898650801384543675514083)
        ·
          refine ⟨2847976202076815513271125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898650801384543675514083 2847976202076815513271125)
          ·
            refine ⟨16687360559043840898073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2847976202076815513271125 16687360559043840898073)
            ·
              rfl

theorem cell21_1974285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 9].length) (baseStart_1974285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974285 prefixEnd_1974285 := by exact prefixLift 1974285
  have htrace : WordTrace (prefixWord ++ tailWord_1974285) baseStart_1974285 baseEnd_1974285 := by
    simpa [prefixWord, tailWord_1974285, baseEnd_1974285] using wordTrace_append hprefix tailTrace_1974285
  have hstable : (prefixWord ++ tailWord_1974285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974285).length < 2 ^ (prefixWord ++ tailWord_1974285).sum := by decide
  have hdescent : baseEnd_1974285 < baseStart_1974285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974372 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1974372 : Nat := 118140960795 + 1974372 * 2 ^ 59
def prefixEnd_1974372 : Nat := 4983230072969 + 3 ^ 40 * 1974372 * 2
def baseEnd_1974372 : Nat := 450578589679490886297793

theorem tailTrace_1974372 : CollatzResearch.WordTrace tailWord_1974372 prefixEnd_1974372 450578589679490886297793 := by
  unfold tailWord_1974372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005631401597457368586685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48007508535463276491448913 36005631401597457368586685)
  ·
    refine ⟨13502111775599046513220007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36005631401597457368586685 13502111775599046513220007)
    ·
      refine ⟨20253167663398569769830011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13502111775599046513220007 20253167663398569769830011)
      ·
        refine ⟨30379751495097854654745017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20253167663398569769830011 30379751495097854654745017)
        ·
          refine ⟨22784813621323390991058763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30379751495097854654745017 22784813621323390991058763)
          ·
            refine ⟨34177220431985086486588145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784813621323390991058763 34177220431985086486588145)
            ·
              refine ⟨25632915323988814864941109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34177220431985086486588145 25632915323988814864941109)
              ·
                refine ⟨2403085811623951393588229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25632915323988814864941109 2403085811623951393588229)
                ·
                  refine ⟨450578589679490886297793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403085811623951393588229 450578589679490886297793)
                  ·
                    rfl

theorem cell21_1974372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1974372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974372 prefixEnd_1974372 := by exact prefixLift 1974372
  have htrace : WordTrace (prefixWord ++ tailWord_1974372) baseStart_1974372 baseEnd_1974372 := by
    simpa [prefixWord, tailWord_1974372, baseEnd_1974372] using wordTrace_append hprefix tailTrace_1974372
  have hstable : (prefixWord ++ tailWord_1974372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974372).length < 2 ^ (prefixWord ++ tailWord_1974372).sum := by decide
  have hdescent : baseEnd_1974372 < baseStart_1974372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974423 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 4]
def baseStart_1974423 : Nat := 118140960795 + 1974423 * 2 ^ 59
def prefixEnd_1974423 : Nat := 4983230072969 + 3 ^ 40 * 1974423 * 2
def baseEnd_1974423 : Nat := 450590228574326130947689

theorem tailTrace_1974423 : CollatzResearch.WordTrace tailWord_1974423 prefixEnd_1974423 450590228574326130947689 := by
  unfold tailWord_1974423
  simp only [CollatzResearch.WordTrace]
  refine ⟨72013122926010150447279923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48008748617340100298186615 72013122926010150447279923)
  ·
    refine ⟨108019684389015225670919885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72013122926010150447279923 108019684389015225670919885)
    ·
      refine ⟨40507381645880709626594957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108019684389015225670919885 40507381645880709626594957)
      ·
        refine ⟨15190268117205266109973109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40507381645880709626594957 15190268117205266109973109)
        ·
          refine ⟨1424087635987993697809979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15190268117205266109973109 1424087635987993697809979)
          ·
            refine ⟨2136131453981990546714969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424087635987993697809979 2136131453981990546714969)
            ·
              refine ⟨1602098590486492910036227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136131453981990546714969 1602098590486492910036227)
              ·
                refine ⟨2403147885729739365054341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602098590486492910036227 2403147885729739365054341)
                ·
                  refine ⟨450590228574326130947689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403147885729739365054341 450590228574326130947689)
                  ·
                    rfl

theorem cell21_1974423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 4].length) (baseStart_1974423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974423 prefixEnd_1974423 := by exact prefixLift 1974423
  have htrace : WordTrace (prefixWord ++ tailWord_1974423) baseStart_1974423 baseEnd_1974423 := by
    simpa [prefixWord, tailWord_1974423, baseEnd_1974423] using wordTrace_append hprefix tailTrace_1974423
  have hstable : (prefixWord ++ tailWord_1974423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974423).length < 2 ^ (prefixWord ++ tailWord_1974423).sum := by decide
  have hdescent : baseEnd_1974423 < baseStart_1974423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974462 : List Nat := [4, 2, 1, 1, 13]
def baseStart_1974462 : Nat := 118140960795 + 1974462 * 2 ^ 59
def prefixEnd_1974462 : Nat := 4983230072969 + 3 ^ 40 * 1974462 * 2
def baseEnd_1974462 : Nat := 5562952208711984318489

theorem tailTrace_1974462 : CollatzResearch.WordTrace tailWord_1974462 prefixEnd_1974462 5562952208711984318489 := by
  unfold tailWord_1974462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001818171608607513493705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48009696915245906738633093 9001818171608607513493705)
  ·
    refine ⟨6751363628706455635120279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9001818171608607513493705 6751363628706455635120279)
    ·
      refine ⟨10127045443059683452680419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6751363628706455635120279 10127045443059683452680419)
      ·
        refine ⟨15190568164589525179020629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10127045443059683452680419 15190568164589525179020629)
        ·
          refine ⟨5562952208711984318489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15190568164589525179020629 5562952208711984318489)
          ·
            rfl

theorem cell21_1974462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 13].length) (baseStart_1974462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974462 prefixEnd_1974462 := by exact prefixLift 1974462
  have htrace : WordTrace (prefixWord ++ tailWord_1974462) baseStart_1974462 baseEnd_1974462 := by
    simpa [prefixWord, tailWord_1974462, baseEnd_1974462] using wordTrace_append hprefix tailTrace_1974462
  have hstable : (prefixWord ++ tailWord_1974462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974462).length < 2 ^ (prefixWord ++ tailWord_1974462).sum := by decide
  have hdescent : baseEnd_1974462 < baseStart_1974462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974468 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_1974468 : Nat := 118140960795 + 1974468 * 2 ^ 59
def prefixEnd_1974468 : Nat := 4983230072969 + 3 ^ 40 * 1974468 * 2
def baseEnd_1974468 : Nat := 450600498187416052697597

theorem tailTrace_1974468 : CollatzResearch.WordTrace tailWord_1974468 prefixEnd_1974468 450600498187416052697597 := by
  unfold tailWord_1974468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36007382105423561566334029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48009842807231415421778705 36007382105423561566334029)
  ·
    refine ⟨13502768289533835587375261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36007382105423561566334029 13502768289533835587375261)
    ·
      refine ⟨5063538108575188345265723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13502768289533835587375261 5063538108575188345265723)
      ·
        refine ⟨7595307162862782517898585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063538108575188345265723 7595307162862782517898585)
        ·
          refine ⟨5696480372147086888423939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7595307162862782517898585 5696480372147086888423939)
          ·
            refine ⟨8544720558220630332635909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696480372147086888423939 8544720558220630332635909)
            ·
              refine ⟨1602135104666368187369233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8544720558220630332635909 1602135104666368187369233)
              ·
                refine ⟨1201601328499776140526925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602135104666368187369233 1201601328499776140526925)
                ·
                  refine ⟨450600498187416052697597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201601328499776140526925 450600498187416052697597)
                  ·
                    rfl

theorem cell21_1974468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_1974468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974468 prefixEnd_1974468 := by exact prefixLift 1974468
  have htrace : WordTrace (prefixWord ++ tailWord_1974468) baseStart_1974468 baseEnd_1974468 := by
    simpa [prefixWord, tailWord_1974468, baseEnd_1974468] using wordTrace_append hprefix tailTrace_1974468
  have hstable : (prefixWord ++ tailWord_1974468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974468).length < 2 ^ (prefixWord ++ tailWord_1974468).sum := by decide
  have hdescent : baseEnd_1974468 < baseStart_1974468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974507 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_1974507 : Nat := 118140960795 + 1974507 * 2 ^ 59
def prefixEnd_1974507 : Nat := 4983230072969 + 3 ^ 40 * 1974507 * 2
def baseEnd_1974507 : Nat := 450609398518760651547517

theorem tailTrace_1974507 : CollatzResearch.WordTrace tailWord_1974507 prefixEnd_1974507 450609398518760651547517 := by
  unfold tailWord_1974507
  simp only [CollatzResearch.WordTrace]
  refine ⟨72016186657705832793337775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48010791105137221862225183 72016186657705832793337775)
  ·
    refine ⟨108024279986558749190006663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72016186657705832793337775 108024279986558749190006663)
    ·
      refine ⟨162036419979838123785009995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108024279986558749190006663 162036419979838123785009995)
      ·
        refine ⟨243054629969757185677514993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162036419979838123785009995 243054629969757185677514993)
        ·
          refine ⟨182290972477317889258136245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243054629969757185677514993 182290972477317889258136245)
          ·
            refine ⟨17089778669748552117950273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182290972477317889258136245 17089778669748552117950273)
            ·
              refine ⟨12817334002311414088462705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17089778669748552117950273 12817334002311414088462705)
              ·
                refine ⟨9613000501733560566347029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12817334002311414088462705 9613000501733560566347029)
                ·
                  refine ⟨450609398518760651547517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9613000501733560566347029 450609398518760651547517)
                  ·
                    rfl

theorem cell21_1974507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_1974507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974507 prefixEnd_1974507 := by exact prefixLift 1974507
  have htrace : WordTrace (prefixWord ++ tailWord_1974507) baseStart_1974507 baseEnd_1974507 := by
    simpa [prefixWord, tailWord_1974507, baseEnd_1974507] using wordTrace_append hprefix tailTrace_1974507
  have hstable : (prefixWord ++ tailWord_1974507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974507).length < 2 ^ (prefixWord ++ tailWord_1974507).sum := by decide
  have hdescent : baseEnd_1974507 < baseStart_1974507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974524 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1974524 : Nat := 118140960795 + 1974524 * 2 ^ 59
def prefixEnd_1974524 : Nat := 4983230072969 + 3 ^ 40 * 1974524 * 2
def baseEnd_1974524 : Nat := 450613278150372399764149

theorem tailTrace_1974524 : CollatzResearch.WordTrace tailWord_1974524 prefixEnd_1974524 450613278150372399764149 := by
  unfold tailWord_1974524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36008403349322122348353313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48011204465762829797804417 36008403349322122348353313)
  ·
    refine ⟨27006302511991591761264985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36008403349322122348353313 27006302511991591761264985)
    ·
      refine ⟨20254726883993693820948739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27006302511991591761264985 20254726883993693820948739)
      ·
        refine ⟨30382090325990540731423109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20254726883993693820948739 30382090325990540731423109)
        ·
          refine ⟨5696641936123226387141833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30382090325990540731423109 5696641936123226387141833)
          ·
            refine ⟨4272481452092419790356375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5696641936123226387141833 4272481452092419790356375)
            ·
              refine ⟨6408722178138629685534563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272481452092419790356375 6408722178138629685534563)
              ·
                refine ⟨9613083267207944528301845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408722178138629685534563 9613083267207944528301845)
                ·
                  refine ⟨450613278150372399764149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9613083267207944528301845 450613278150372399764149)
                  ·
                    rfl

theorem cell21_1974524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1974524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974524 prefixEnd_1974524 := by exact prefixLift 1974524
  have htrace : WordTrace (prefixWord ++ tailWord_1974524) baseStart_1974524 baseEnd_1974524 := by
    simpa [prefixWord, tailWord_1974524, baseEnd_1974524] using wordTrace_append hprefix tailTrace_1974524
  have hstable : (prefixWord ++ tailWord_1974524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974524).length < 2 ^ (prefixWord ++ tailWord_1974524).sum := by decide
  have hdescent : baseEnd_1974524 < baseStart_1974524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974586 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1974586 : Nat := 118140960795 + 1974586 * 2 ^ 59
def prefixEnd_1974586 : Nat := 4983230072969 + 3 ^ 40 * 1974586 * 2
def baseEnd_1974586 : Nat := 450627427395074069730689

theorem tailTrace_1974586 : CollatzResearch.WordTrace tailWord_1974586 prefixEnd_1974586 450627427395074069730689 := by
  unfold tailWord_1974586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18004767006104907321365903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48012712016279752856975741 18004767006104907321365903)
  ·
    refine ⟨27007150509157360982048855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18004767006104907321365903 27007150509157360982048855)
    ·
      refine ⟨40510725763736041473073283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27007150509157360982048855 40510725763736041473073283)
      ·
        refine ⟨60766088645604062209609925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40510725763736041473073283 60766088645604062209609925)
        ·
          refine ⟨11393641621050761664301861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60766088645604062209609925 11393641621050761664301861)
          ·
            refine ⟨2136307803947017812056599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11393641621050761664301861 2136307803947017812056599)
            ·
              refine ⟨3204461705920526718084899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136307803947017812056599 3204461705920526718084899)
              ·
                refine ⟨4806692558880790077127349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204461705920526718084899 4806692558880790077127349)
                ·
                  refine ⟨450627427395074069730689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4806692558880790077127349 450627427395074069730689)
                  ·
                    rfl

theorem cell21_1974586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1974586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974586 prefixEnd_1974586 := by exact prefixLift 1974586
  have htrace : WordTrace (prefixWord ++ tailWord_1974586) baseStart_1974586 baseEnd_1974586 := by
    simpa [prefixWord, tailWord_1974586, baseEnd_1974586] using wordTrace_append hprefix tailTrace_1974586
  have hstable : (prefixWord ++ tailWord_1974586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974586).length < 2 ^ (prefixWord ++ tailWord_1974586).sum := by decide
  have hdescent : baseEnd_1974586 < baseStart_1974586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974690 : List Nat := [3, 3, 1, 2, 1, 1, 10]
def baseStart_1974690 : Nat := 118140960795 + 1974690 * 2 ^ 59
def prefixEnd_1974690 : Nat := 4983230072969 + 3 ^ 40 * 1974690 * 2
def baseEnd_1974690 : Nat := 50072351290221444444127

theorem tailTrace_1974690 : CollatzResearch.WordTrace tailWord_1974690 prefixEnd_1974690 50072351290221444444127 := by
  unfold tailWord_1974690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005715304010713761812381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48015240810695236698166349 18005715304010713761812381)
  ·
    refine ⟨6752143239004017660679643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18005715304010713761812381 6752143239004017660679643)
    ·
      refine ⟨10128214858506026491019465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752143239004017660679643 10128214858506026491019465)
      ·
        refine ⟨7596161143879519868264599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10128214858506026491019465 7596161143879519868264599)
        ·
          refine ⟨11394241715819279802396899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596161143879519868264599 11394241715819279802396899)
          ·
            refine ⟨17091362573728919703595349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11394241715819279802396899 17091362573728919703595349)
            ·
              refine ⟨50072351290221444444127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17091362573728919703595349 50072351290221444444127)
              ·
                rfl

theorem cell21_1974690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 10].length) (baseStart_1974690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974690 prefixEnd_1974690 := by exact prefixLift 1974690
  have htrace : WordTrace (prefixWord ++ tailWord_1974690) baseStart_1974690 baseEnd_1974690 := by
    simpa [prefixWord, tailWord_1974690, baseEnd_1974690] using wordTrace_append hprefix tailTrace_1974690
  have hstable : (prefixWord ++ tailWord_1974690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974690).length < 2 ^ (prefixWord ++ tailWord_1974690).sum := by decide
  have hdescent : baseEnd_1974690 < baseStart_1974690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974755 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 5]
def baseStart_1974755 : Nat := 118140960795 + 1974755 * 2 ^ 59
def prefixEnd_1974755 : Nat := 4983230072969 + 3 ^ 40 * 1974755 * 2
def baseEnd_1974755 : Nat := 450665995497567331413677

theorem tailTrace_1974755 : CollatzResearch.WordTrace tailWord_1974755 prefixEnd_1974755 450665995497567331413677 := by
  unfold tailWord_1974755
  simp only [CollatzResearch.WordTrace]
  refine ⟨72025231960807371148365719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48016821307204914098910479 72025231960807371148365719)
  ·
    refine ⟨108037847941211056722548579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72025231960807371148365719 108037847941211056722548579)
    ·
      refine ⟨162056771911816585083822869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108037847941211056722548579 162056771911816585083822869)
      ·
        refine ⟨7596411183366402425804197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162056771911816585083822869 7596411183366402425804197)
        ·
          refine ⟨1424327096881200454838287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7596411183366402425804197 1424327096881200454838287)
          ·
            refine ⟨2136490645321800682257431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424327096881200454838287 2136490645321800682257431)
            ·
              refine ⟨3204735967982701023386147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136490645321800682257431 3204735967982701023386147)
              ·
                refine ⟨4807103951974051535079221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204735967982701023386147 4807103951974051535079221)
                ·
                  refine ⟨450665995497567331413677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4807103951974051535079221 450665995497567331413677)
                  ·
                    rfl

theorem cell21_1974755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5].length) (baseStart_1974755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974755 prefixEnd_1974755 := by exact prefixLift 1974755
  have htrace : WordTrace (prefixWord ++ tailWord_1974755) baseStart_1974755 baseEnd_1974755 := by
    simpa [prefixWord, tailWord_1974755, baseEnd_1974755] using wordTrace_append hprefix tailTrace_1974755
  have hstable : (prefixWord ++ tailWord_1974755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974755).length < 2 ^ (prefixWord ++ tailWord_1974755).sum := by decide
  have hdescent : baseEnd_1974755 < baseStart_1974755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974766 : List Nat := [4, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1974766 : Nat := 118140960795 + 1974766 * 2 ^ 59
def prefixEnd_1974766 : Nat := 4983230072969 + 3 ^ 40 * 1974766 * 2
def baseEnd_1974766 : Nat := 150222835282477918910107

theorem tailTrace_1974766 : CollatzResearch.WordTrace tailWord_1974766 prefixEnd_1974766 150222835282477918910107 := by
  unfold tailWord_1974766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003204145470940003377019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48017088775845013351344101 9003204145470940003377019)
  ·
    refine ⟨13504806218206410005065529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9003204145470940003377019 13504806218206410005065529)
    ·
      refine ⟨10128604663654807503799147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13504806218206410005065529 10128604663654807503799147)
      ·
        refine ⟨15192906995482211255698721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128604663654807503799147 15192906995482211255698721)
        ·
          refine ⟨11394680246611658441774041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15192906995482211255698721 11394680246611658441774041)
          ·
            refine ⟨8546010184958743831330531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11394680246611658441774041 8546010184958743831330531)
            ·
              refine ⟨12819015277438115746995797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546010184958743831330531 12819015277438115746995797)
              ·
                refine ⟨150222835282477918910107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12819015277438115746995797 150222835282477918910107)
                ·
                  rfl

theorem cell21_1974766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1974766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974766 prefixEnd_1974766 := by exact prefixLift 1974766
  have htrace : WordTrace (prefixWord ++ tailWord_1974766) baseStart_1974766 baseEnd_1974766 := by
    simpa [prefixWord, tailWord_1974766, baseEnd_1974766] using wordTrace_append hprefix tailTrace_1974766
  have hstable : (prefixWord ++ tailWord_1974766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974766).length < 2 ^ (prefixWord ++ tailWord_1974766).sum := by decide
  have hdescent : baseEnd_1974766 < baseStart_1974766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974780 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_1974780 : Nat := 118140960795 + 1974780 * 2 ^ 59
def prefixEnd_1974780 : Nat := 4983230072969 + 3 ^ 40 * 1974780 * 2
def baseEnd_1974780 : Nat := 450671700838172843496959

theorem tailTrace_1974780 : CollatzResearch.WordTrace tailWord_1974780 prefixEnd_1974780 450671700838172843496959 := by
  unfold tailWord_1974780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013071892858400209012897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48017429190477866945350529 36013071892858400209012897)
  ·
    refine ⟨27009803919643800156759673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36013071892858400209012897 27009803919643800156759673)
    ·
      refine ⟨20257352939732850117569755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27009803919643800156759673 20257352939732850117569755)
      ·
        refine ⟨30386029409599275176354633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20257352939732850117569755 30386029409599275176354633)
        ·
          refine ⟨22789522057199456382265975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30386029409599275176354633 22789522057199456382265975)
          ·
            refine ⟨34184283085799184573398963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22789522057199456382265975 34184283085799184573398963)
            ·
              refine ⟨51276424628698776860098445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34184283085799184573398963 51276424628698776860098445)
              ·
                refine ⟨19228659235762041322536917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51276424628698776860098445 19228659235762041322536917)
                ·
                  refine ⟨450671700838172843496959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19228659235762041322536917 450671700838172843496959)
                  ·
                    rfl

theorem cell21_1974780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_1974780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974780 prefixEnd_1974780 := by exact prefixLift 1974780
  have htrace : WordTrace (prefixWord ++ tailWord_1974780) baseStart_1974780 baseEnd_1974780 := by
    simpa [prefixWord, tailWord_1974780, baseEnd_1974780] using wordTrace_append hprefix tailTrace_1974780
  have hstable : (prefixWord ++ tailWord_1974780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974780).length < 2 ^ (prefixWord ++ tailWord_1974780).sum := by decide
  have hdescent : baseEnd_1974780 < baseStart_1974780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974980 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1974980 : Nat := 118140960795 + 1974980 * 2 ^ 59
def prefixEnd_1974980 : Nat := 4983230072969 + 3 ^ 40 * 1974980 * 2
def baseEnd_1974980 : Nat := 450717343563016940163217

theorem tailTrace_1974980 : CollatzResearch.WordTrace tailWord_1974980 prefixEnd_1974980 450717343563016940163217 := by
  unfold tailWord_1974980
  simp only [CollatzResearch.WordTrace]
  refine ⟨36016719192496117287653197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48022292256661489716870929 36016719192496117287653197)
  ·
    refine ⟨13506269697186043982869949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36016719192496117287653197 13506269697186043982869949)
    ·
      refine ⟨5064851136444766493576231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13506269697186043982869949 5064851136444766493576231)
      ·
        refine ⟨7597276704667149740364347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064851136444766493576231 7597276704667149740364347)
        ·
          refine ⟨11395915057000724610546521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597276704667149740364347 11395915057000724610546521)
          ·
            refine ⟨8546936292750543457909891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11395915057000724610546521 8546936292750543457909891)
            ·
              refine ⟨12820404439125815186864837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546936292750543457909891 12820404439125815186864837)
              ·
                refine ⟨2403825832336090347537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12820404439125815186864837 2403825832336090347537157)
                ·
                  refine ⟨450717343563016940163217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403825832336090347537157 450717343563016940163217)
                  ·
                    rfl

theorem cell21_1974980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1974980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1974980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1974980 prefixEnd_1974980 := by exact prefixLift 1974980
  have htrace : WordTrace (prefixWord ++ tailWord_1974980) baseStart_1974980 baseEnd_1974980 := by
    simpa [prefixWord, tailWord_1974980, baseEnd_1974980] using wordTrace_append hprefix tailTrace_1974980
  have hstable : (prefixWord ++ tailWord_1974980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974980).length < 2 ^ (prefixWord ++ tailWord_1974980).sum := by decide
  have hdescent : baseEnd_1974980 < baseStart_1974980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975011 : List Nat := [1, 1, 1, 7, 1, 2, 3, 5]
def baseStart_1975011 : Nat := 118140960795 + 1975011 * 2 ^ 59
def prefixEnd_1975011 : Nat := 4983230072969 + 3 ^ 40 * 1975011 * 2
def baseEnd_1975011 : Nat := 150241472728455925048829

theorem tailTrace_1975011 : CollatzResearch.WordTrace tailWord_1975011 prefixEnd_1975011 150241472728455925048829 := by
  unfold tailWord_1975011
  simp only [CollatzResearch.WordTrace]
  refine ⟨72034569047879926869684887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48023046031919951246456591 72034569047879926869684887)
  ·
    refine ⟨108051853571819890304527331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72034569047879926869684887 108051853571819890304527331)
    ·
      refine ⟨162077780357729835456790997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108051853571819890304527331 162077780357729835456790997)
      ·
        refine ⟨3798697977134293018518539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 162077780357729835456790997 3798697977134293018518539)
        ·
          refine ⟨5698046965701439527777809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798697977134293018518539 5698046965701439527777809)
          ·
            refine ⟨4273535224276079645833357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5698046965701439527777809 4273535224276079645833357)
            ·
              refine ⟨1602575709103529867187509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4273535224276079645833357 1602575709103529867187509)
              ·
                refine ⟨150241472728455925048829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1602575709103529867187509 150241472728455925048829)
                ·
                  rfl

theorem cell21_1975011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 5].length) (baseStart_1975011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975011 prefixEnd_1975011 := by exact prefixLift 1975011
  have htrace : WordTrace (prefixWord ++ tailWord_1975011) baseStart_1975011 baseEnd_1975011 := by
    simpa [prefixWord, tailWord_1975011, baseEnd_1975011] using wordTrace_append hprefix tailTrace_1975011
  have hstable : (prefixWord ++ tailWord_1975011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975011).length < 2 ^ (prefixWord ++ tailWord_1975011).sum := by decide
  have hdescent : baseEnd_1975011 < baseStart_1975011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975028 : List Nat := [2, 6, 1, 1, 2, 1, 8]
def baseStart_1975028 : Nat := 118140960795 + 1975028 * 2 ^ 59
def prefixEnd_1975028 : Nat := 4983230072969 + 3 ^ 40 * 1975028 * 2
def baseEnd_1975028 : Nat := 50080921979664391484791

theorem tailTrace_1975028 : CollatzResearch.WordTrace tailWord_1975028 prefixEnd_1975028 50080921979664391484791 := by
  unfold tailWord_1975028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36017594544409169386526869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48023459392545559182035825 36017594544409169386526869)
  ·
    refine ⟨1688324744269179814993447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36017594544409169386526869 1688324744269179814993447)
    ·
      refine ⟨2532487116403769722490171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688324744269179814993447 2532487116403769722490171)
      ·
        refine ⟨3798730674605654583735257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532487116403769722490171 3798730674605654583735257)
        ·
          refine ⟨2849048005954240937801443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798730674605654583735257 2849048005954240937801443)
          ·
            refine ⟨4273572008931361406702165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849048005954240937801443 4273572008931361406702165)
            ·
              refine ⟨50080921979664391484791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4273572008931361406702165 50080921979664391484791)
              ·
                rfl

theorem cell21_1975028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 8].length) (baseStart_1975028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975028 prefixEnd_1975028 := by exact prefixLift 1975028
  have htrace : WordTrace (prefixWord ++ tailWord_1975028) baseStart_1975028 baseEnd_1975028 := by
    simpa [prefixWord, tailWord_1975028, baseEnd_1975028] using wordTrace_append hprefix tailTrace_1975028
  have hstable : (prefixWord ++ tailWord_1975028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975028).length < 2 ^ (prefixWord ++ tailWord_1975028).sum := by decide
  have hdescent : baseEnd_1975028 < baseStart_1975028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975042 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1975042 : Nat := 118140960795 + 1975042 * 2 ^ 59
def prefixEnd_1975042 : Nat := 4983230072969 + 3 ^ 40 * 1975042 * 2
def baseEnd_1975042 : Nat := 450731492807718610129757

theorem tailTrace_1975042 : CollatzResearch.WordTrace tailWord_1975042 prefixEnd_1975042 450731492807718610129757 := by
  unfold tailWord_1975042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008924927691904791015845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48023799807178412776042253 18008924927691904791015845)
  ·
    refine ⟨3376673423942232148315471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18008924927691904791015845 3376673423942232148315471)
    ·
      refine ⟨5065010135913348222473207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376673423942232148315471 5065010135913348222473207)
      ·
        refine ⟨7597515203870022333709811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065010135913348222473207 7597515203870022333709811)
        ·
          refine ⟨11396272805805033500564717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597515203870022333709811 11396272805805033500564717)
          ·
            refine ⟨4273602302176887562711769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11396272805805033500564717 4273602302176887562711769)
            ·
              refine ⟨3205201726632665672033827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4273602302176887562711769 3205201726632665672033827)
              ·
                refine ⟨4807802589948998508050741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205201726632665672033827 4807802589948998508050741)
                ·
                  refine ⟨450731492807718610129757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4807802589948998508050741 450731492807718610129757)
                  ·
                    rfl

theorem cell21_1975042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1975042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975042 prefixEnd_1975042 := by exact prefixLift 1975042
  have htrace : WordTrace (prefixWord ++ tailWord_1975042) baseStart_1975042 baseEnd_1975042 := by
    simpa [prefixWord, tailWord_1975042, baseEnd_1975042] using wordTrace_append hprefix tailTrace_1975042
  have hstable : (prefixWord ++ tailWord_1975042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975042).length < 2 ^ (prefixWord ++ tailWord_1975042).sum := by decide
  have hdescent : baseEnd_1975042 < baseStart_1975042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975076 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1975076 : Nat := 118140960795 + 1975076 * 2 ^ 59
def prefixEnd_1975076 : Nat := 4983230072969 + 3 ^ 40 * 1975076 * 2
def baseEnd_1975076 : Nat := 450739252070942106563021

theorem tailTrace_1975076 : CollatzResearch.WordTrace tailWord_1975076 prefixEnd_1975076 450739252070942106563021 := by
  unfold tailWord_1975076
  simp only [CollatzResearch.WordTrace]
  refine ⟨36018469896322221485400541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48024626528429628647200721 36018469896322221485400541)
  ·
    refine ⟨13506926211120833057025203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36018469896322221485400541 13506926211120833057025203)
    ·
      refine ⟨20260389316681249585537805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13506926211120833057025203 20260389316681249585537805)
      ·
        refine ⟨7597645993755468594576677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20260389316681249585537805 7597645993755468594576677)
        ·
          refine ⟨1424558623829150361483127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7597645993755468594576677 1424558623829150361483127)
          ·
            refine ⟨2136837935743725542224691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424558623829150361483127 2136837935743725542224691)
            ·
              refine ⟨3205256903615588313337037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136837935743725542224691 3205256903615588313337037)
              ·
                refine ⟨1201971338855845617501389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3205256903615588313337037 1201971338855845617501389)
                ·
                  refine ⟨450739252070942106563021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201971338855845617501389 450739252070942106563021)
                  ·
                    rfl

theorem cell21_1975076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1975076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975076 prefixEnd_1975076 := by exact prefixLift 1975076
  have htrace : WordTrace (prefixWord ++ tailWord_1975076) baseStart_1975076 baseEnd_1975076 := by
    simpa [prefixWord, tailWord_1975076, baseEnd_1975076] using wordTrace_append hprefix tailTrace_1975076
  have hstable : (prefixWord ++ tailWord_1975076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975076).length < 2 ^ (prefixWord ++ tailWord_1975076).sum := by decide
  have hdescent : baseEnd_1975076 < baseStart_1975076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975129 : List Nat := [1, 2, 1, 2, 2, 4, 2, 7]
def baseStart_1975129 : Nat := 118140960795 + 1975129 * 2 ^ 59
def prefixEnd_1975129 : Nat := 4983230072969 + 3 ^ 40 * 1975129 * 2
def baseEnd_1975129 : Nat := 150250449131008597393193

theorem tailTrace_1975129 : CollatzResearch.WordTrace tailWord_1975129 prefixEnd_1975129 150250449131008597393193 := by
  unfold tailWord_1975129
  simp only [CollatzResearch.WordTrace]
  refine ⟨72038872861452433022480441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48025915240968288681653627 72038872861452433022480441)
  ·
    refine ⟨54029154646089324766860331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72038872861452433022480441 54029154646089324766860331)
    ·
      refine ⟨81043731969133987150290497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54029154646089324766860331 81043731969133987150290497)
      ·
        refine ⟨60782798976850490362717873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81043731969133987150290497 60782798976850490362717873)
        ·
          refine ⟨45587099232637867772038405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60782798976850490362717873 45587099232637867772038405)
          ·
            refine ⟨8547581106119600207257201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45587099232637867772038405 8547581106119600207257201)
            ·
              refine ⟨6410685829589700155442901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8547581106119600207257201 6410685829589700155442901)
              ·
                refine ⟨150250449131008597393193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6410685829589700155442901 150250449131008597393193)
                ·
                  rfl

theorem cell21_1975129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_1975129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975129 prefixEnd_1975129 := by exact prefixLift 1975129
  have htrace : WordTrace (prefixWord ++ tailWord_1975129) baseStart_1975129 baseEnd_1975129 := by
    simpa [prefixWord, tailWord_1975129, baseEnd_1975129] using wordTrace_append hprefix tailTrace_1975129
  have hstable : (prefixWord ++ tailWord_1975129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975129).length < 2 ^ (prefixWord ++ tailWord_1975129).sum := by decide
  have hdescent : baseEnd_1975129 < baseStart_1975129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975267 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_1975267 : Nat := 118140960795 + 1975267 * 2 ^ 59
def prefixEnd_1975267 : Nat := 4983230072969 + 3 ^ 40 * 1975267 * 2
def baseEnd_1975267 : Nat := 450782840873168218879297

theorem tailTrace_1975267 : CollatzResearch.WordTrace tailWord_1975267 prefixEnd_1975267 450782840873168218879297 := by
  unfold tailWord_1975267
  simp only [CollatzResearch.WordTrace]
  refine ⟨72043906134952482591004055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48029270756634988394002703 72043906134952482591004055)
  ·
    refine ⟨108065859202428723886506083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72043906134952482591004055 108065859202428723886506083)
    ·
      refine ⟨162098788803643085829759125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108065859202428723886506083 162098788803643085829759125)
      ·
        refine ⟨7598380725170769648269959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162098788803643085829759125 7598380725170769648269959)
        ·
          refine ⟨11397571087756154472404939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7598380725170769648269959 11397571087756154472404939)
          ·
            refine ⟨17096356631634231708607409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11397571087756154472404939 17096356631634231708607409)
            ·
              refine ⟨12822267473725673781455557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17096356631634231708607409 12822267473725673781455557)
              ·
                refine ⟨2404175151323563834022917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12822267473725673781455557 2404175151323563834022917)
                ·
                  refine ⟨450782840873168218879297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2404175151323563834022917 450782840873168218879297)
                  ·
                    rfl

theorem cell21_1975267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_1975267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975267 prefixEnd_1975267 := by exact prefixLift 1975267
  have htrace : WordTrace (prefixWord ++ tailWord_1975267) baseStart_1975267 baseEnd_1975267 := by
    simpa [prefixWord, tailWord_1975267, baseEnd_1975267] using wordTrace_append hprefix tailTrace_1975267
  have hstable : (prefixWord ++ tailWord_1975267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975267).length < 2 ^ (prefixWord ++ tailWord_1975267).sum := by decide
  have hdescent : baseEnd_1975267 < baseStart_1975267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975281 : List Nat := [1, 2, 2, 2, 4, 1, 1, 8]
def baseStart_1975281 : Nat := 118140960795 + 1975281 * 2 ^ 59
def prefixEnd_1975281 : Nat := 4983230072969 + 3 ^ 40 * 1975281 * 2
def baseEnd_1975281 : Nat := 150262011954635768548645

theorem tailTrace_1975281 : CollatzResearch.WordTrace tailWord_1975281 prefixEnd_1975281 150262011954635768548645 := by
  unfold tailWord_1975281
  simp only [CollatzResearch.WordTrace]
  refine ⟨72044416756901762982013697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48029611171267841988009131 72044416756901762982013697)
  ·
    refine ⟨54033312567676322236510273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72044416756901762982013697 54033312567676322236510273)
    ·
      refine ⟨40524984425757241677382705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54033312567676322236510273 40524984425757241677382705)
      ·
        refine ⟨30393738319317931258037029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40524984425757241677382705 30393738319317931258037029)
        ·
          refine ⟨5698825934872112110881943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30393738319317931258037029 5698825934872112110881943)
          ·
            refine ⟨8548238902308168166322915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698825934872112110881943 8548238902308168166322915)
            ·
              refine ⟨12822358353462252249484373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548238902308168166322915 12822358353462252249484373)
              ·
                refine ⟨150262011954635768548645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12822358353462252249484373 150262011954635768548645)
                ·
                  rfl

theorem cell21_1975281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_1975281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975281 prefixEnd_1975281 := by exact prefixLift 1975281
  have htrace : WordTrace (prefixWord ++ tailWord_1975281) baseStart_1975281 baseEnd_1975281 := by
    simpa [prefixWord, tailWord_1975281, baseEnd_1975281] using wordTrace_append hprefix tailTrace_1975281
  have hstable : (prefixWord ++ tailWord_1975281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975281).length < 2 ^ (prefixWord ++ tailWord_1975281).sum := by decide
  have hdescent : baseEnd_1975281 < baseStart_1975281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975433 : List Nat := [1, 2, 1, 1, 4, 5, 7]
def baseStart_1975433 : Nat := 118140960795 + 1975433 * 2 ^ 59
def prefixEnd_1975433 : Nat := 4983230072969 + 3 ^ 40 * 1975433 * 2
def baseEnd_1975433 : Nat := 50091191592754313234699

theorem tailTrace_1975433 : CollatzResearch.WordTrace tailWord_1975433 prefixEnd_1975433 50091191592754313234699 := by
  unfold tailWord_1975433
  simp only [CollatzResearch.WordTrace]
  refine ⟨72049960652351092941546953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48033307101567395294364635 72049960652351092941546953)
  ·
    refine ⟨54037470489263319706160215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72049960652351092941546953 54037470489263319706160215)
    ·
      refine ⟨81056205733894979559240323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54037470489263319706160215 81056205733894979559240323)
      ·
        refine ⟨121584308600842469338860485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81056205733894979559240323 121584308600842469338860485)
        ·
          refine ⟨22797057862657963001036341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121584308600842469338860485 22797057862657963001036341)
          ·
            refine ⟨2137224174624184031347157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22797057862657963001036341 2137224174624184031347157)
            ·
              refine ⟨50091191592754313234699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2137224174624184031347157 50091191592754313234699)
              ·
                rfl

theorem cell21_1975433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 7].length) (baseStart_1975433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975433 prefixEnd_1975433 := by exact prefixLift 1975433
  have htrace : WordTrace (prefixWord ++ tailWord_1975433) baseStart_1975433 baseEnd_1975433 := by
    simpa [prefixWord, tailWord_1975433, baseEnd_1975433] using wordTrace_append hprefix tailTrace_1975433
  have hstable : (prefixWord ++ tailWord_1975433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975433).length < 2 ^ (prefixWord ++ tailWord_1975433).sum := by decide
  have hdescent : baseEnd_1975433 < baseStart_1975433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975450 : List Nat := [3, 1, 1, 5, 1, 2, 2, 6]
def baseStart_1975450 : Nat := 118140960795 + 1975450 * 2 ^ 59
def prefixEnd_1975450 : Nat := 4983230072969 + 3 ^ 40 * 1975450 * 2
def baseEnd_1975450 : Nat := 150274867988800189109641

theorem tailTrace_1975450 : CollatzResearch.WordTrace tailWord_1975450 prefixEnd_1975450 150274867988800189109641 := by
  unfold tailWord_1975450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012645173322376211228951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48033720462193003229943869 18012645173322376211228951)
  ·
    refine ⟨27018967759983564316843427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18012645173322376211228951 27018967759983564316843427)
    ·
      refine ⟨40528451639975346475265141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27018967759983564316843427 40528451639975346475265141)
      ·
        refine ⟨3799542341247688732056107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40528451639975346475265141 3799542341247688732056107)
        ·
          refine ⟨5699313511871533098084161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799542341247688732056107 5699313511871533098084161)
          ·
            refine ⟨4274485133903649823563121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699313511871533098084161 4274485133903649823563121)
            ·
              refine ⟨3205863850427737367672341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274485133903649823563121 3205863850427737367672341)
              ·
                refine ⟨150274867988800189109641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3205863850427737367672341 150274867988800189109641)
                ·
                  rfl

theorem cell21_1975450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_1975450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975450 prefixEnd_1975450 := by exact prefixLift 1975450
  have htrace : WordTrace (prefixWord ++ tailWord_1975450) baseStart_1975450 baseEnd_1975450 := by
    simpa [prefixWord, tailWord_1975450, baseEnd_1975450] using wordTrace_append hprefix tailTrace_1975450
  have hstable : (prefixWord ++ tailWord_1975450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975450).length < 2 ^ (prefixWord ++ tailWord_1975450).sum := by decide
  have hdescent : baseEnd_1975450 < baseStart_1975450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975490 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1975490 : Nat := 118140960795 + 1975490 * 2 ^ 59
def prefixEnd_1975490 : Nat := 4983230072969 + 3 ^ 40 * 1975490 * 2
def baseEnd_1975490 : Nat := 450833732511369386662175

theorem tailTrace_1975490 : CollatzResearch.WordTrace tailWord_1975490 prefixEnd_1975490 450833732511369386662175 := by
  unfold tailWord_1975490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013009903286147919092981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48034693075429727784247949 18013009903286147919092981)
  ·
    refine ⟨1688719678433076367414967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18013009903286147919092981 1688719678433076367414967)
    ·
      refine ⟨2533079517649614551122451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688719678433076367414967 2533079517649614551122451)
      ·
        refine ⟨3799619276474421826683677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533079517649614551122451 3799619276474421826683677)
        ·
          refine ⟨1424857228677908185006379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3799619276474421826683677 1424857228677908185006379)
          ·
            refine ⟨2137285843016862277509569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424857228677908185006379 2137285843016862277509569)
            ·
              refine ⟨1602964382262646708132177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137285843016862277509569 1602964382262646708132177)
              ·
                refine ⟨1202223286696985031099133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602964382262646708132177 1202223286696985031099133)
                ·
                  refine ⟨450833732511369386662175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202223286696985031099133 450833732511369386662175)
                  ·
                    rfl

theorem cell21_1975490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1975490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975490 prefixEnd_1975490 := by exact prefixLift 1975490
  have htrace : WordTrace (prefixWord ++ tailWord_1975490) baseStart_1975490 baseEnd_1975490 := by
    simpa [prefixWord, tailWord_1975490, baseEnd_1975490] using wordTrace_append hprefix tailTrace_1975490
  have hstable : (prefixWord ++ tailWord_1975490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975490).length < 2 ^ (prefixWord ++ tailWord_1975490).sum := by decide
  have hdescent : baseEnd_1975490 < baseStart_1975490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975498 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_1975498 : Nat := 118140960795 + 1975498 * 2 ^ 59
def prefixEnd_1975498 : Nat := 4983230072969 + 3 ^ 40 * 1975498 * 2
def baseEnd_1975498 : Nat := 450835558220363150528825

theorem tailTrace_1975498 : CollatzResearch.WordTrace tailWord_1975498 prefixEnd_1975498 450835558220363150528825 := by
  unfold tailWord_1975498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013082849278902260665787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48034887598077072695108765 18013082849278902260665787)
  ·
    refine ⟨27019624273918353390998681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18013082849278902260665787 27019624273918353390998681)
    ·
      refine ⟨20264718205438765043249011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27019624273918353390998681 20264718205438765043249011)
      ·
        refine ⟨30397077308158147564873517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20264718205438765043249011 30397077308158147564873517)
        ·
          refine ⟨11398903990559305336827569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30397077308158147564873517 11398903990559305336827569)
          ·
            refine ⟨8549177992919479002620677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11398903990559305336827569 8549177992919479002620677)
            ·
              refine ⟨1602970873672402312991377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8549177992919479002620677 1602970873672402312991377)
              ·
                refine ⟨1202228155254301734743533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602970873672402312991377 1202228155254301734743533)
                ·
                  refine ⟨450835558220363150528825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202228155254301734743533 450835558220363150528825)
                  ·
                    rfl

theorem cell21_1975498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_1975498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975498 prefixEnd_1975498 := by exact prefixLift 1975498
  have htrace : WordTrace (prefixWord ++ tailWord_1975498) baseStart_1975498 baseEnd_1975498 := by
    simpa [prefixWord, tailWord_1975498, baseEnd_1975498] using wordTrace_append hprefix tailTrace_1975498
  have hstable : (prefixWord ++ tailWord_1975498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975498).length < 2 ^ (prefixWord ++ tailWord_1975498).sum := by decide
  have hdescent : baseEnd_1975498 < baseStart_1975498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975501 : List Nat := [1, 6, 2, 2, 2, 1, 1, 6]
def baseStart_1975501 : Nat := 118140960795 + 1975501 * 2 ^ 59
def prefixEnd_1975501 : Nat := 4983230072969 + 3 ^ 40 * 1975501 * 2
def baseEnd_1975501 : Nat := 150278747620411937326273

theorem tailTrace_1975501 : CollatzResearch.WordTrace tailWord_1975501 prefixEnd_1975501 150278747620411937326273 := by
  unfold tailWord_1975501
  simp only [CollatzResearch.WordTrace]
  refine ⟨72052440816104740555022357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48034960544069827036681571 72052440816104740555022357)
  ·
    refine ⟨3377458163254909713516673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72052440816104740555022357 3377458163254909713516673)
    ·
      refine ⟨2533093622441182285137505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3377458163254909713516673 2533093622441182285137505)
      ·
        refine ⟨1899820216830886713853129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2533093622441182285137505 1899820216830886713853129)
        ·
          refine ⟨1424865162623165035389847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899820216830886713853129 1424865162623165035389847)
          ·
            refine ⟨2137297743934747553084771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424865162623165035389847 2137297743934747553084771)
            ·
              refine ⟨3205946615902121329627157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137297743934747553084771 3205946615902121329627157)
              ·
                refine ⟨150278747620411937326273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3205946615902121329627157 150278747620411937326273)
                ·
                  rfl

theorem cell21_1975501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 6].length) (baseStart_1975501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975501 prefixEnd_1975501 := by exact prefixLift 1975501
  have htrace : WordTrace (prefixWord ++ tailWord_1975501) baseStart_1975501 baseEnd_1975501 := by
    simpa [prefixWord, tailWord_1975501, baseEnd_1975501] using wordTrace_append hprefix tailTrace_1975501
  have hstable : (prefixWord ++ tailWord_1975501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975501).length < 2 ^ (prefixWord ++ tailWord_1975501).sum := by decide
  have hdescent : baseEnd_1975501 < baseStart_1975501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975622 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1975622 : Nat := 118140960795 + 1975622 * 2 ^ 59
def prefixEnd_1975622 : Nat := 4983230072969 + 3 ^ 40 * 1975622 * 2
def baseEnd_1975622 : Nat := 450863856709766490461905

theorem tailTrace_1975622 : CollatzResearch.WordTrace tailWord_1975622 prefixEnd_1975622 450863856709766490461905 := by
  unfold tailWord_1975622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251776689020824319380535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48037902699110918813451413 2251776689020824319380535)
  ·
    refine ⟨3377665033531236479070803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251776689020824319380535 3377665033531236479070803)
    ·
      refine ⟨5066497550296854718606205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377665033531236479070803 5066497550296854718606205)
      ·
        refine ⟨1899936581361320519477327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5066497550296854718606205 1899936581361320519477327)
        ·
          refine ⟨2849904872041980779215991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899936581361320519477327 2849904872041980779215991)
          ·
            refine ⟨4274857308062971168823987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849904872041980779215991 4274857308062971168823987)
            ·
              refine ⟨6412285962094456753235981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274857308062971168823987 6412285962094456753235981)
              ·
                refine ⟨2404607235785421282463493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6412285962094456753235981 2404607235785421282463493)
                ·
                  refine ⟨450863856709766490461905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2404607235785421282463493 450863856709766490461905)
                  ·
                    rfl

theorem cell21_1975622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1975622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975622 prefixEnd_1975622 := by exact prefixLift 1975622
  have htrace : WordTrace (prefixWord ++ tailWord_1975622) baseStart_1975622 baseEnd_1975622 := by
    simpa [prefixWord, tailWord_1975622, baseEnd_1975622] using wordTrace_append hprefix tailTrace_1975622
  have hstable : (prefixWord ++ tailWord_1975622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975622).length < 2 ^ (prefixWord ++ tailWord_1975622).sum := by decide
  have hdescent : baseEnd_1975622 < baseStart_1975622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975675 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_1975675 : Nat := 118140960795 + 1975675 * 2 ^ 59
def prefixEnd_1975675 : Nat := 4983230072969 + 3 ^ 40 * 1975675 * 2
def baseEnd_1975675 : Nat := 450875952031850176078463

theorem tailTrace_1975675 : CollatzResearch.WordTrace tailWord_1975675 prefixEnd_1975675 450875952031850176078463 := by
  unfold tailWord_1975675
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058787117474368271856479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48039191411649578847904319 72058787117474368271856479)
  ·
    refine ⟨108088180676211552407784719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72058787117474368271856479 108088180676211552407784719)
    ·
      refine ⟨162132271014317328611677079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108088180676211552407784719 162132271014317328611677079)
      ·
        refine ⟨243198406521475992917515619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162132271014317328611677079 243198406521475992917515619)
        ·
          refine ⟨364797609782213989376273429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243198406521475992917515619 364797609782213989376273429)
          ·
            refine ⟨17099887958541280752012817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 364797609782213989376273429 17099887958541280752012817)
            ·
              refine ⟨12824915968905960564009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17099887958541280752012817 12824915968905960564009613)
              ·
                refine ⟨4809343488339735211503605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12824915968905960564009613 4809343488339735211503605)
                ·
                  refine ⟨450875952031850176078463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4809343488339735211503605 450875952031850176078463)
                  ·
                    rfl

theorem cell21_1975675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_1975675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975675 prefixEnd_1975675 := by exact prefixLift 1975675
  have htrace : WordTrace (prefixWord ++ tailWord_1975675) baseStart_1975675 baseEnd_1975675 := by
    simpa [prefixWord, tailWord_1975675, baseEnd_1975675] using wordTrace_append hprefix tailTrace_1975675
  have hstable : (prefixWord ++ tailWord_1975675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975675).length < 2 ^ (prefixWord ++ tailWord_1975675).sum := by decide
  have hdescent : baseEnd_1975675 < baseStart_1975675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975706 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1975706 : Nat := 118140960795 + 1975706 * 2 ^ 59
def prefixEnd_1975706 : Nat := 4983230072969 + 3 ^ 40 * 1975706 * 2
def baseEnd_1975706 : Nat := 450883026654201011061733

theorem tailTrace_1975706 : CollatzResearch.WordTrace tailWord_1975706 prefixEnd_1975706 450883026654201011061733 := by
  unfold tailWord_1975706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014979445090515141558743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48039945186908040377489981 18014979445090515141558743)
  ·
    refine ⟨27022469167635772712338115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18014979445090515141558743 27022469167635772712338115)
    ·
      refine ⟨40533703751453659068507173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27022469167635772712338115 40533703751453659068507173)
      ·
        refine ⟨7600069453397561075345095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40533703751453659068507173 7600069453397561075345095)
        ·
          refine ⟨11400104180096341613017643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7600069453397561075345095 11400104180096341613017643)
          ·
            refine ⟨17100156270144512419526465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400104180096341613017643 17100156270144512419526465)
            ·
              refine ⟨12825117202608384314644849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17100156270144512419526465 12825117202608384314644849)
              ·
                refine ⟨9618837901956288235983637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12825117202608384314644849 9618837901956288235983637)
                ·
                  refine ⟨450883026654201011061733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9618837901956288235983637 450883026654201011061733)
                  ·
                    rfl

theorem cell21_1975706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1975706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975706 prefixEnd_1975706 := by exact prefixLift 1975706
  have htrace : WordTrace (prefixWord ++ tailWord_1975706) baseStart_1975706 baseEnd_1975706 := by
    simpa [prefixWord, tailWord_1975706, baseEnd_1975706] using wordTrace_append hprefix tailTrace_1975706
  have hstable : (prefixWord ++ tailWord_1975706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975706).length < 2 ^ (prefixWord ++ tailWord_1975706).sum := by decide
  have hdescent : baseEnd_1975706 < baseStart_1975706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975709 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1975709 : Nat := 118140960795 + 1975709 * 2 ^ 59
def prefixEnd_1975709 : Nat := 4983230072969 + 3 ^ 40 * 1975709 * 2
def baseEnd_1975709 : Nat := 450883711295073672511727

theorem tailTrace_1975709 : CollatzResearch.WordTrace tailWord_1975709 prefixEnd_1975709 450883711295073672511727 := by
  unfold tailWord_1975709
  simp only [CollatzResearch.WordTrace]
  refine ⟨72060027199351192078594181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48040018132900794719062787 72060027199351192078594181)
  ·
    refine ⟨13511255099878348514736409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72060027199351192078594181 13511255099878348514736409)
    ·
      refine ⟨10133441324908761386052307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13511255099878348514736409 10133441324908761386052307)
      ·
        refine ⟨15200161987363142079078461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133441324908761386052307 15200161987363142079078461)
        ·
          refine ⟨5700060745261178279654423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15200161987363142079078461 5700060745261178279654423)
          ·
            refine ⟨8550091117891767419481635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700060745261178279654423 8550091117891767419481635)
            ·
              refine ⟨12825136676837651129222453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550091117891767419481635 12825136676837651129222453)
              ·
                refine ⟨1202356563453529793364605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12825136676837651129222453 1202356563453529793364605)
                ·
                  refine ⟨450883711295073672511727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202356563453529793364605 450883711295073672511727)
                  ·
                    rfl

theorem cell21_1975709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1975709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975709 prefixEnd_1975709 := by exact prefixLift 1975709
  have htrace : WordTrace (prefixWord ++ tailWord_1975709) baseStart_1975709 baseEnd_1975709 := by
    simpa [prefixWord, tailWord_1975709, baseEnd_1975709] using wordTrace_append hprefix tailTrace_1975709
  have hstable : (prefixWord ++ tailWord_1975709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975709).length < 2 ^ (prefixWord ++ tailWord_1975709).sum := by decide
  have hdescent : baseEnd_1975709 < baseStart_1975709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975746 : List Nat := [3, 5, 2, 1, 1, 2, 2, 5]
def baseStart_1975746 : Nat := 118140960795 + 1975746 * 2 ^ 59
def prefixEnd_1975746 : Nat := 4983230072969 + 3 ^ 40 * 1975746 * 2
def baseEnd_1975746 : Nat := 150297385066389943464995

theorem tailTrace_1975746 : CollatzResearch.WordTrace tailWord_1975746 prefixEnd_1975746 150297385066389943464995 := by
  unfold tailWord_1975746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015344175054286849422773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48040917800144764931794061 18015344175054286849422773)
  ·
    refine ⟨1688938516411339392133385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18015344175054286849422773 1688938516411339392133385)
    ·
      refine ⟨1266703887308504544100039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1688938516411339392133385 1266703887308504544100039)
      ·
        refine ⟨1900055830962756816150059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266703887308504544100039 1900055830962756816150059)
        ·
          refine ⟨2850083746444135224225089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900055830962756816150059 2850083746444135224225089)
          ·
            refine ⟨2137562809833101418168817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850083746444135224225089 2137562809833101418168817)
            ·
              refine ⟨1603172107374826063626613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137562809833101418168817 1603172107374826063626613)
              ·
                refine ⟨150297385066389943464995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603172107374826063626613 150297385066389943464995)
                ·
                  rfl

theorem cell21_1975746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_1975746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975746 prefixEnd_1975746 := by exact prefixLift 1975746
  have htrace : WordTrace (prefixWord ++ tailWord_1975746) baseStart_1975746 baseEnd_1975746 := by
    simpa [prefixWord, tailWord_1975746, baseEnd_1975746] using wordTrace_append hprefix tailTrace_1975746
  have hstable : (prefixWord ++ tailWord_1975746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975746).length < 2 ^ (prefixWord ++ tailWord_1975746).sum := by decide
  have hdescent : baseEnd_1975746 < baseStart_1975746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975751 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_1975751 : Nat := 118140960795 + 1975751 * 2 ^ 59
def prefixEnd_1975751 : Nat := 4983230072969 + 3 ^ 40 * 1975751 * 2
def baseEnd_1975751 : Nat := 450893296267290932811641

theorem tailTrace_1975751 : CollatzResearch.WordTrace tailWord_1975751 prefixEnd_1975751 450893296267290932811641 := by
  unfold tailWord_1975751
  simp only [CollatzResearch.WordTrace]
  refine ⟨72061559065199033251623107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48041039376799355501082071 72061559065199033251623107)
  ·
    refine ⟨108092338597798549877434661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72061559065199033251623107 108092338597798549877434661)
    ·
      refine ⟨20267313487087228102018999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108092338597798549877434661 20267313487087228102018999)
      ·
        refine ⟨30400970230630842153028499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20267313487087228102018999 30400970230630842153028499)
        ·
          refine ⟨45601455345946263229542749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30400970230630842153028499 45601455345946263229542749)
          ·
            refine ⟨17100545754729848711078531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45601455345946263229542749 17100545754729848711078531)
            ·
              refine ⟨25650818632094773066617797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17100545754729848711078531 25650818632094773066617797)
              ·
                refine ⟨4809528493517769949990837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25650818632094773066617797 4809528493517769949990837)
                ·
                  refine ⟨450893296267290932811641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4809528493517769949990837 450893296267290932811641)
                  ·
                    rfl

theorem cell21_1975751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_1975751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975751 prefixEnd_1975751 := by exact prefixLift 1975751
  have htrace : WordTrace (prefixWord ++ tailWord_1975751) baseStart_1975751 baseEnd_1975751 := by
    simpa [prefixWord, tailWord_1975751, baseEnd_1975751] using wordTrace_append hprefix tailTrace_1975751
  have hstable : (prefixWord ++ tailWord_1975751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975751).length < 2 ^ (prefixWord ++ tailWord_1975751).sum := by decide
  have hdescent : baseEnd_1975751 < baseStart_1975751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975754 : List Nat := [3, 1, 2, 1, 2, 5, 2, 5]
def baseStart_1975754 : Nat := 118140960795 + 1975754 * 2 ^ 59
def prefixEnd_1975754 : Nat := 4983230072969 + 3 ^ 40 * 1975754 * 2
def baseEnd_1975754 : Nat := 150297993636054531420545

theorem tailTrace_1975754 : CollatzResearch.WordTrace tailWord_1975754 prefixEnd_1975754 150297993636054531420545 := by
  unfold tailWord_1975754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015417121047041190995579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48041112322792109842654877 18015417121047041190995579)
  ·
    refine ⟨27023125681570561786493369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015417121047041190995579 27023125681570561786493369)
    ·
      refine ⟨20267344261177921339870027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27023125681570561786493369 20267344261177921339870027)
      ·
        refine ⟨30401016391766882009805041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20267344261177921339870027 30401016391766882009805041)
        ·
          refine ⟨22800762293825161507353781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30401016391766882009805041 22800762293825161507353781)
          ·
            refine ⟨2137571465046108891314417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22800762293825161507353781 2137571465046108891314417)
            ·
              refine ⟨1603178598784581668485813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137571465046108891314417 1603178598784581668485813)
              ·
                refine ⟨150297993636054531420545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603178598784581668485813 150297993636054531420545)
                ·
                  rfl

theorem cell21_1975754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_1975754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975754 prefixEnd_1975754 := by exact prefixLift 1975754
  have htrace : WordTrace (prefixWord ++ tailWord_1975754) baseStart_1975754 baseEnd_1975754 := by
    simpa [prefixWord, tailWord_1975754, baseEnd_1975754] using wordTrace_append hprefix tailTrace_1975754
  have hstable : (prefixWord ++ tailWord_1975754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975754).length < 2 ^ (prefixWord ++ tailWord_1975754).sum := by decide
  have hdescent : baseEnd_1975754 < baseStart_1975754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975937 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 3]
def baseStart_1975937 : Nat := 118140960795 + 1975937 * 2 ^ 59
def prefixEnd_1975937 : Nat := 4983230072969 + 3 ^ 40 * 1975937 * 2
def baseEnd_1975937 : Nat := 450935744001395942711261

theorem tailTrace_1975937 : CollatzResearch.WordTrace tailWord_1975937 prefixEnd_1975937 450935744001395942711261 := by
  unfold tailWord_1975937
  simp only [CollatzResearch.WordTrace]
  refine ⟨72068343042525187017894065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48045562028350124678596043 72068343042525187017894065)
  ·
    refine ⟨54051257281893890263420549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72068343042525187017894065 54051257281893890263420549)
    ·
      refine ⟨10134610740355104424391353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54051257281893890263420549 10134610740355104424391353)
      ·
        refine ⟨7600958055266328318293515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134610740355104424391353 7600958055266328318293515)
        ·
          refine ⟨11401437082899492477440273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7600958055266328318293515 11401437082899492477440273)
          ·
            refine ⟨8551077812174619358080205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401437082899492477440273 8551077812174619358080205)
            ·
              refine ⟨3206654179565482259280077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8551077812174619358080205 3206654179565482259280077)
              ·
                refine ⟨1202495317337055847230029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3206654179565482259280077 1202495317337055847230029)
                ·
                  refine ⟨450935744001395942711261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202495317337055847230029 450935744001395942711261)
                  ·
                    rfl

theorem cell21_1975937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_1975937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1975937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1975937 prefixEnd_1975937 := by exact prefixLift 1975937
  have htrace : WordTrace (prefixWord ++ tailWord_1975937) baseStart_1975937 baseEnd_1975937 := by
    simpa [prefixWord, tailWord_1975937, baseEnd_1975937] using wordTrace_append hprefix tailTrace_1975937
  have hstable : (prefixWord ++ tailWord_1975937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975937).length < 2 ^ (prefixWord ++ tailWord_1975937).sum := by decide
  have hdescent : baseEnd_1975937 < baseStart_1975937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
