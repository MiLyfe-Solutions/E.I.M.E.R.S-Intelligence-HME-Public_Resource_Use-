import V185TrunkScan23Chunk1226

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7270604 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_7270604 : Nat := 118140960795 + 7270604 * 2 ^ 59
def prefixEnd_7270604 : Nat := 4983230072969 + 3 ^ 40 * 7270604 * 2
def baseEnd_7270604 : Nat := 1244438166833992320704369

theorem tailTrace_7270604 : CollatzResearch.WordTrace tailWord_7270604 prefixEnd_7270604 1244438166833992320704369 := by
  unfold tailWord_7270604
  simp only [CollatzResearch.WordTrace]
  refine ⟨132590356675925451574953433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176787142234567268766604577 132590356675925451574953433)
  ·
    refine ⟨99442767506944088681215075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132590356675925451574953433 99442767506944088681215075)
    ·
      refine ⟨149164151260416133021822613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99442767506944088681215075 149164151260416133021822613)
      ·
        refine ⟨6992069590332006235397935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149164151260416133021822613 6992069590332006235397935)
        ·
          refine ⟨10488104385498009353096903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992069590332006235397935 10488104385498009353096903)
          ·
            refine ⟨15732156578247014029645355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488104385498009353096903 15732156578247014029645355)
            ·
              refine ⟨23598234867370521044468033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732156578247014029645355 23598234867370521044468033)
              ·
                refine ⟨17698676150527890783351025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23598234867370521044468033 17698676150527890783351025)
                ·
                  refine ⟨13274007112895918087513269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17698676150527890783351025 13274007112895918087513269)
                  ·
                    refine ⟨1244438166833992320704369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13274007112895918087513269 1244438166833992320704369)
                    ·
                      rfl

theorem cell23_7270604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_7270604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270604 prefixEnd_7270604 := by exact prefixLift 7270604
  have htrace : WordTrace (prefixWord ++ tailWord_7270604) baseStart_7270604 baseEnd_7270604 := by
    simpa [prefixWord, tailWord_7270604, baseEnd_7270604] using wordTrace_append hprefix tailTrace_7270604
  have hstable : (prefixWord ++ tailWord_7270604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270604).length < 2 ^ (prefixWord ++ tailWord_7270604).sum := by decide
  have hdescent : baseEnd_7270604 < baseStart_7270604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270614 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7270614 : Nat := 118140960795 + 7270614 * 2 ^ 59
def prefixEnd_7270614 : Nat := 4983230072969 + 3 ^ 40 * 7270614 * 2
def baseEnd_7270614 : Nat := 3733319635308521922988061

theorem tailTrace_7270614 : CollatzResearch.WordTrace tailWord_7270614 prefixEnd_7270614 3733319635308521922988061 := by
  unfold tailWord_7270614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16573817380113417178610681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176787385387876449905180597 16573817380113417178610681)
  ·
    refine ⟨12430363035085062883958011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16573817380113417178610681 12430363035085062883958011)
    ·
      refine ⟨18645544552627594325937017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430363035085062883958011 18645544552627594325937017)
      ·
        refine ⟨13984158414470695744452763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18645544552627594325937017 13984158414470695744452763)
        ·
          refine ⟨20976237621706043616679145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13984158414470695744452763 20976237621706043616679145)
          ·
            refine ⟨15732178216279532712509359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20976237621706043616679145 15732178216279532712509359)
            ·
              refine ⟨23598267324419299068764039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732178216279532712509359 23598267324419299068764039)
              ·
                refine ⟨35397400986628948603146059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23598267324419299068764039 35397400986628948603146059)
                ·
                  refine ⟨53096101479943422904719089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35397400986628948603146059 53096101479943422904719089)
                  ·
                    refine ⟨39822076109957567178539317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53096101479943422904719089 39822076109957567178539317)
                    ·
                      refine ⟨3733319635308521922988061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39822076109957567178539317 3733319635308521922988061)
                      ·
                        rfl

theorem cell23_7270614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7270614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270614 prefixEnd_7270614 := by exact prefixLift 7270614
  have htrace : WordTrace (prefixWord ++ tailWord_7270614) baseStart_7270614 baseEnd_7270614 := by
    simpa [prefixWord, tailWord_7270614, baseEnd_7270614] using wordTrace_append hprefix tailTrace_7270614
  have hstable : (prefixWord ++ tailWord_7270614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270614).length < 2 ^ (prefixWord ++ tailWord_7270614).sum := by decide
  have hdescent : baseEnd_7270614 < baseStart_7270614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270617 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_7270617 : Nat := 118140960795 + 7270617 * 2 ^ 59
def prefixEnd_7270617 : Nat := 4983230072969 + 3 ^ 40 * 7270617 * 2
def baseEnd_7270617 : Nat := 1244440391916828470416849

theorem tailTrace_7270617 : CollatzResearch.WordTrace tailWord_7270617 prefixEnd_7270617 1244440391916828470416849 := by
  unfold tailWord_7270617
  simp only [CollatzResearch.WordTrace]
  refine ⟨265181187500803806370130105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176787458333869204246753403 265181187500803806370130105)
  ·
    refine ⟨198885890625602854777597579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265181187500803806370130105 198885890625602854777597579)
    ·
      refine ⟨298328835938404282166396369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198885890625602854777597579 298328835938404282166396369)
      ·
        refine ⟨223746626953803211624797277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298328835938404282166396369 223746626953803211624797277)
        ·
          refine ⟨83904985107676204359298979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223746626953803211624797277 83904985107676204359298979)
          ·
            refine ⟨125857477661514306538948469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83904985107676204359298979 125857477661514306538948469)
            ·
              refine ⟨11799138530766966238026419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125857477661514306538948469 11799138530766966238026419)
              ·
                refine ⟨17698707796150449357039629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799138530766966238026419 17698707796150449357039629)
                ·
                  refine ⟨6637015423556418508889861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17698707796150449357039629 6637015423556418508889861)
                  ·
                    refine ⟨1244440391916828470416849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637015423556418508889861 1244440391916828470416849)
                    ·
                      rfl

theorem cell23_7270617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_7270617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270617 prefixEnd_7270617 := by exact prefixLift 7270617
  have htrace : WordTrace (prefixWord ++ tailWord_7270617) baseStart_7270617 baseEnd_7270617 := by
    simpa [prefixWord, tailWord_7270617, baseEnd_7270617] using wordTrace_append hprefix tailTrace_7270617
  have hstable : (prefixWord ++ tailWord_7270617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270617).length < 2 ^ (prefixWord ++ tailWord_7270617).sum := by decide
  have hdescent : baseEnd_7270617 < baseStart_7270617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270640 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3]
def baseStart_7270640 : Nat := 118140960795 + 7270640 * 2 ^ 59
def prefixEnd_7270640 : Nat := 4983230072969 + 3 ^ 40 * 7270640 * 2
def baseEnd_7270640 : Nat := 3733332985805538821262941

theorem tailTrace_7270640 : CollatzResearch.WordTrace tailWord_7270640 prefixEnd_7270640 3733332985805538821262941 := by
  unfold tailWord_7270640
  simp only [CollatzResearch.WordTrace]
  refine ⟨132591013189860240649108687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176788017586480320865478249 132591013189860240649108687)
  ·
    refine ⟨198886519784790360973663031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132591013189860240649108687 198886519784790360973663031)
    ·
      refine ⟨298329779677185541460494547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198886519784790360973663031 298329779677185541460494547)
      ·
        refine ⟨447494669515778312190741821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298329779677185541460494547 447494669515778312190741821)
        ·
          refine ⟨167810501068416867071528183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447494669515778312190741821 167810501068416867071528183)
          ·
            refine ⟨251715751602625300607292275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167810501068416867071528183 251715751602625300607292275)
            ·
              refine ⟨377573627403937950910938413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251715751602625300607292275 377573627403937950910938413)
              ·
                refine ⟨141590110276476731591601905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377573627403937950910938413 141590110276476731591601905)
                ·
                  refine ⟨106192582707357548693701429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141590110276476731591601905 106192582707357548693701429)
                  ·
                    refine ⟨9955554628814770190034509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106192582707357548693701429 9955554628814770190034509)
                    ·
                      refine ⟨3733332985805538821262941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955554628814770190034509 3733332985805538821262941)
                      ·
                        rfl

theorem cell23_7270640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_7270640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270640 prefixEnd_7270640 := by exact prefixLift 7270640
  have htrace : WordTrace (prefixWord ++ tailWord_7270640) baseStart_7270640 baseEnd_7270640 := by
    simpa [prefixWord, tailWord_7270640, baseEnd_7270640] using wordTrace_append hprefix tailTrace_7270640
  have hstable : (prefixWord ++ tailWord_7270640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270640).length < 2 ^ (prefixWord ++ tailWord_7270640).sum := by decide
  have hdescent : baseEnd_7270640 < baseStart_7270640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270695 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_7270695 : Nat := 118140960795 + 7270695 * 2 ^ 59
def prefixEnd_7270695 : Nat := 4983230072969 + 3 ^ 40 * 7270695 * 2
def baseEnd_7270695 : Nat := 3733361227241536106075189

theorem tailTrace_7270695 : CollatzResearch.WordTrace tailWord_7270695 prefixEnd_7270695 3733361227241536106075189 := by
  unfold tailWord_7270695
  simp only [CollatzResearch.WordTrace]
  refine ⟨265184032394521225691469539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176789354929680817127646359 265184032394521225691469539)
  ·
    refine ⟨397776048591781838537204309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265184032394521225691469539 397776048591781838537204309)
    ·
      refine ⟨4661438069434943420357863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 397776048591781838537204309 4661438069434943420357863)
      ·
        refine ⟨6992157104152415130536795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661438069434943420357863 6992157104152415130536795)
        ·
          refine ⟨10488235656228622695805193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992157104152415130536795 10488235656228622695805193)
          ·
            refine ⟨7866176742171467021853895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10488235656228622695805193 7866176742171467021853895)
            ·
              refine ⟨11799265113257200532780843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866176742171467021853895 11799265113257200532780843)
              ·
                refine ⟨17698897669885800799171265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799265113257200532780843 17698897669885800799171265)
                ·
                  refine ⟨13274173252414350599378449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17698897669885800799171265 13274173252414350599378449)
                  ·
                    refine ⟨9955629939310762949533837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13274173252414350599378449 9955629939310762949533837)
                    ·
                      refine ⟨3733361227241536106075189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955629939310762949533837 3733361227241536106075189)
                      ·
                        rfl

theorem cell23_7270695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_7270695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270695 prefixEnd_7270695 := by exact prefixLift 7270695
  have htrace : WordTrace (prefixWord ++ tailWord_7270695) baseStart_7270695 baseEnd_7270695 := by
    simpa [prefixWord, tailWord_7270695, baseEnd_7270695] using wordTrace_append hprefix tailTrace_7270695
  have hstable : (prefixWord ++ tailWord_7270695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270695).length < 2 ^ (prefixWord ++ tailWord_7270695).sum := by decide
  have hdescent : baseEnd_7270695 < baseStart_7270695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270707 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 4, 4]
def baseStart_7270707 : Nat := 118140960795 + 7270707 * 2 ^ 59
def prefixEnd_7270707 : Nat := 4983230072969 + 3 ^ 40 * 7270707 * 2
def baseEnd_7270707 : Nat := 1244455796336463353041711

theorem tailTrace_7270707 : CollatzResearch.WordTrace tailWord_7270707 prefixEnd_7270707 1244455796336463353041711 := by
  unfold tailWord_7270707
  simp only [CollatzResearch.WordTrace]
  refine ⟨265184470070477751740906375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176789646713651834493937583 265184470070477751740906375)
  ·
    refine ⟨397776705105716627611359563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265184470070477751740906375 397776705105716627611359563)
    ·
      refine ⟨596665057658574941417039345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397776705105716627611359563 596665057658574941417039345)
      ·
        refine ⟨447498793243931206062779509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596665057658574941417039345 447498793243931206062779509)
        ·
          refine ⟨41953011866618550568385579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 447498793243931206062779509 41953011866618550568385579)
          ·
            refine ⟨62929517799927825852578369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41953011866618550568385579 62929517799927825852578369)
            ·
              refine ⟨47197138349945869389433777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62929517799927825852578369 47197138349945869389433777)
              ·
                refine ⟨35397853762459402042075333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47197138349945869389433777 35397853762459402042075333)
                ·
                  refine ⟨6637097580461137882889125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35397853762459402042075333 6637097580461137882889125)
                  ·
                    refine ⟨1244455796336463353041711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637097580461137882889125 1244455796336463353041711)
                    ·
                      rfl

theorem cell23_7270707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 4].length) (baseStart_7270707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270707 prefixEnd_7270707 := by exact prefixLift 7270707
  have htrace : WordTrace (prefixWord ++ tailWord_7270707) baseStart_7270707 baseEnd_7270707 := by
    simpa [prefixWord, tailWord_7270707, baseEnd_7270707] using wordTrace_append hprefix tailTrace_7270707
  have hstable : (prefixWord ++ tailWord_7270707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270707).length < 2 ^ (prefixWord ++ tailWord_7270707).sum := by decide
  have hdescent : baseEnd_7270707 < baseStart_7270707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270708 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7270708 : Nat := 118140960795 + 7270708 * 2 ^ 59
def prefixEnd_7270708 : Nat := 4983230072969 + 3 ^ 40 * 7270708 * 2
def baseEnd_7270708 : Nat := 3733367902490044555212629

theorem tailTrace_7270708 : CollatzResearch.WordTrace tailWord_7270708 prefixEnd_7270708 3733367902490044555212629 := by
  unfold tailWord_7270708
  simp only [CollatzResearch.WordTrace]
  refine ⟨132592253271737064455846389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176789671028982752607795185 132592253271737064455846389)
  ·
    refine ⟨12430523744225349792735599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132592253271737064455846389 12430523744225349792735599)
    ·
      refine ⟨18645785616338024689103399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430523744225349792735599 18645785616338024689103399)
      ·
        refine ⟨27968678424507037033655099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645785616338024689103399 27968678424507037033655099)
        ·
          refine ⟨41953017636760555550482649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27968678424507037033655099 41953017636760555550482649)
          ·
            refine ⟨31464763227570416662861987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41953017636760555550482649 31464763227570416662861987)
            ·
              refine ⟨47197144841355624994292981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31464763227570416662861987 47197144841355624994292981)
              ·
                refine ⟨4424732328877089843214967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47197144841355624994292981 4424732328877089843214967)
                ·
                  refine ⟨6637098493315634764822451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424732328877089843214967 6637098493315634764822451)
                  ·
                    refine ⟨9955647739973452147233677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637098493315634764822451 9955647739973452147233677)
                    ·
                      refine ⟨3733367902490044555212629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955647739973452147233677 3733367902490044555212629)
                      ·
                        rfl

theorem cell23_7270708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7270708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270708 prefixEnd_7270708 := by exact prefixLift 7270708
  have htrace : WordTrace (prefixWord ++ tailWord_7270708) baseStart_7270708 baseEnd_7270708 := by
    simpa [prefixWord, tailWord_7270708, baseEnd_7270708] using wordTrace_append hprefix tailTrace_7270708
  have hstable : (prefixWord ++ tailWord_7270708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270708).length < 2 ^ (prefixWord ++ tailWord_7270708).sum := by decide
  have hdescent : baseEnd_7270708 < baseStart_7270708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270714 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_7270714 : Nat := 118140960795 + 7270714 * 2 ^ 59
def prefixEnd_7270714 : Nat := 4983230072969 + 3 ^ 40 * 7270714 * 2
def baseEnd_7270714 : Nat := 3733370983373971531737601

theorem tailTrace_7270714 : CollatzResearch.WordTrace tailWord_7270714 prefixEnd_7270714 3733370983373971531737601 := by
  unfold tailWord_7270714
  simp only [CollatzResearch.WordTrace]
  refine ⟨66296181345363097984102799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176789816920968261290940797 66296181345363097984102799)
  ·
    refine ⟨99444272018044646976154199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66296181345363097984102799 99444272018044646976154199)
    ·
      refine ⟨149166408027066970464231299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99444272018044646976154199 149166408027066970464231299)
      ·
        refine ⟨223749612040600455696346949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149166408027066970464231299 223749612040600455696346949)
        ·
          refine ⟨41953052257612585443065053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223749612040600455696346949 41953052257612585443065053)
          ·
            refine ⟨15732394596604719541149395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41953052257612585443065053 15732394596604719541149395)
            ·
              refine ⟨23598591894907079311724093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732394596604719541149395 23598591894907079311724093)
              ·
                refine ⟨8849471960590154741896535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23598591894907079311724093 8849471960590154741896535)
                ·
                  refine ⟨13274207940885232112844803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849471960590154741896535 13274207940885232112844803)
                  ·
                    refine ⟨19911311911327848169267205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13274207940885232112844803 19911311911327848169267205)
                    ·
                      refine ⟨3733370983373971531737601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19911311911327848169267205 3733370983373971531737601)
                      ·
                        rfl

theorem cell23_7270714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_7270714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270714 prefixEnd_7270714 := by exact prefixLift 7270714
  have htrace : WordTrace (prefixWord ++ tailWord_7270714) baseStart_7270714 baseEnd_7270714 := by
    simpa [prefixWord, tailWord_7270714, baseEnd_7270714] using wordTrace_append hprefix tailTrace_7270714
  have hstable : (prefixWord ++ tailWord_7270714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270714).length < 2 ^ (prefixWord ++ tailWord_7270714).sum := by decide
  have hdescent : baseEnd_7270714 < baseStart_7270714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270730 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_7270730 : Nat := 118140960795 + 7270730 * 2 ^ 59
def prefixEnd_7270730 : Nat := 4983230072969 + 3 ^ 40 * 7270730 * 2
def baseEnd_7270730 : Nat := 3733379199064443469137527

theorem tailTrace_7270730 : CollatzResearch.WordTrace tailWord_7270730 prefixEnd_7270730 3733379199064443469137527 := by
  unfold tailWord_7270730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66296327237348606667248411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176790205966262951112662429 66296327237348606667248411)
  ·
    refine ⟨99444490856022910000872617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66296327237348606667248411 99444490856022910000872617)
    ·
      refine ⟨74583368142017182500654463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99444490856022910000872617 74583368142017182500654463)
      ·
        refine ⟨111875052213025773750981695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74583368142017182500654463 111875052213025773750981695)
        ·
          refine ⟨167812578319538660626472543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111875052213025773750981695 167812578319538660626472543)
          ·
            refine ⟨251718867479307990939708815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167812578319538660626472543 251718867479307990939708815)
            ·
              refine ⟨377578301218961986409563223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251718867479307990939708815 377578301218961986409563223)
              ·
                refine ⟨566367451828442979614344835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377578301218961986409563223 566367451828442979614344835)
                ·
                  refine ⟨849551177742664469421517253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566367451828442979614344835 849551177742664469421517253)
                  ·
                    refine ⟨159290845826749588016534485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 849551177742664469421517253 159290845826749588016534485)
                    ·
                      refine ⟨3733379199064443469137527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159290845826749588016534485 3733379199064443469137527)
                      ·
                        rfl

theorem cell23_7270730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_7270730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270730 prefixEnd_7270730 := by exact prefixLift 7270730
  have htrace : WordTrace (prefixWord ++ tailWord_7270730) baseStart_7270730 baseEnd_7270730 := by
    simpa [prefixWord, tailWord_7270730, baseEnd_7270730] using wordTrace_append hprefix tailTrace_7270730
  have hstable : (prefixWord ++ tailWord_7270730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270730).length < 2 ^ (prefixWord ++ tailWord_7270730).sum := by decide
  have hdescent : baseEnd_7270730 < baseStart_7270730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270741 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_7270741 : Nat := 118140960795 + 7270741 * 2 ^ 59
def prefixEnd_7270741 : Nat := 4983230072969 + 3 ^ 40 * 7270741 * 2
def baseEnd_7270741 : Nat := 1244461615783880975366659

theorem tailTrace_7270741 : CollatzResearch.WordTrace tailWord_7270741 prefixEnd_7270741 1244461615783880975366659 := by
  unfold tailWord_7270741
  simp only [CollatzResearch.WordTrace]
  refine ⟨265185710152354575547644077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176790473434903050365096051 265185710152354575547644077)
  ·
    refine ⟨99444641307132965830366529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265185710152354575547644077 99444641307132965830366529)
    ·
      refine ⟨74583480980349724372774897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99444641307132965830366529 74583480980349724372774897)
      ·
        refine ⟨55937610735262293279581173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74583480980349724372774897 55937610735262293279581173)
        ·
          refine ⟨5244151006430839994960735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55937610735262293279581173 5244151006430839994960735)
          ·
            refine ⟨7866226509646259992441103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244151006430839994960735 7866226509646259992441103)
            ·
              refine ⟨11799339764469389988661655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866226509646259992441103 11799339764469389988661655)
              ·
                refine ⟨17699009646704084982992483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799339764469389988661655 17699009646704084982992483)
                ·
                  refine ⟨26548514470056127474488725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17699009646704084982992483 26548514470056127474488725)
                  ·
                    refine ⟨1244461615783880975366659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26548514470056127474488725 1244461615783880975366659)
                    ·
                      rfl

theorem cell23_7270741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_7270741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270741 prefixEnd_7270741 := by exact prefixLift 7270741
  have htrace : WordTrace (prefixWord ++ tailWord_7270741) baseStart_7270741 baseEnd_7270741 := by
    simpa [prefixWord, tailWord_7270741, baseEnd_7270741] using wordTrace_append hprefix tailTrace_7270741
  have hstable : (prefixWord ++ tailWord_7270741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270741).length < 2 ^ (prefixWord ++ tailWord_7270741).sum := by decide
  have hdescent : baseEnd_7270741 < baseStart_7270741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270748 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7270748 : Nat := 118140960795 + 7270748 * 2 ^ 59
def prefixEnd_7270748 : Nat := 4983230072969 + 3 ^ 40 * 7270748 * 2
def baseEnd_7270748 : Nat := 3733388441716224398712445

theorem tailTrace_7270748 : CollatzResearch.WordTrace tailWord_7270748 prefixEnd_7270748 3733388441716224398712445 := by
  unfold tailWord_7270748
  simp only [CollatzResearch.WordTrace]
  refine ⟨132592982731664607871574449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176790643642219477162099265 132592982731664607871574449)
  ·
    refine ⟨99444737048748455903680837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132592982731664607871574449 99444737048748455903680837)
    ·
      refine ⟨18645888196640335481940157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99444737048748455903680837 18645888196640335481940157)
      ·
        refine ⟨6992208073740125805727559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18645888196640335481940157 6992208073740125805727559)
        ·
          refine ⟨10488312110610188708591339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992208073740125805727559 10488312110610188708591339)
          ·
            refine ⟨15732468165915283062887009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488312110610188708591339 15732468165915283062887009)
            ·
              refine ⟨11799351124436462297165257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15732468165915283062887009 11799351124436462297165257)
              ·
                refine ⟨8849513343327346722873943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11799351124436462297165257 8849513343327346722873943)
                ·
                  refine ⟨13274270014991020084310915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849513343327346722873943 13274270014991020084310915)
                  ·
                    refine ⟨19911405022486530126466373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13274270014991020084310915 19911405022486530126466373)
                    ·
                      refine ⟨3733388441716224398712445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19911405022486530126466373 3733388441716224398712445)
                      ·
                        rfl

theorem cell23_7270748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7270748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270748 prefixEnd_7270748 := by exact prefixLift 7270748
  have htrace : WordTrace (prefixWord ++ tailWord_7270748) baseStart_7270748 baseEnd_7270748 := by
    simpa [prefixWord, tailWord_7270748, baseEnd_7270748] using wordTrace_append hprefix tailTrace_7270748
  have hstable : (prefixWord ++ tailWord_7270748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270748).length < 2 ^ (prefixWord ++ tailWord_7270748).sum := by decide
  have hdescent : baseEnd_7270748 < baseStart_7270748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270754 : List Nat := [3, 3, 2, 1, 1, 2, 4, 7]
def baseStart_7270754 : Nat := 118140960795 + 7270754 * 2 ^ 59
def prefixEnd_7270754 : Nat := 4983230072969 + 3 ^ 40 * 7270754 * 2
def baseEnd_7270754 : Nat := 138273760096301902786571

theorem tailTrace_7270754 : CollatzResearch.WordTrace tailWord_7270754 prefixEnd_7270754 138273760096301902786571 := by
  unfold tailWord_7270754
  simp only [CollatzResearch.WordTrace]
  refine ⟨66296546075326869691966829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176790789534204985845244877 66296546075326869691966829)
  ·
    refine ⟨24861204778247576134487561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66296546075326869691966829 24861204778247576134487561)
    ·
      refine ⟨18645903583685682100865671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24861204778247576134487561 18645903583685682100865671)
      ·
        refine ⟨27968855375528523151298507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18645903583685682100865671 27968855375528523151298507)
        ·
          refine ⟨41953283063292784726947761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27968855375528523151298507 41953283063292784726947761)
          ·
            refine ⟨31464962297469588545210821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41953283063292784726947761 31464962297469588545210821)
            ·
              refine ⟨5899680430775547852227029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31464962297469588545210821 5899680430775547852227029)
              ·
                refine ⟨138273760096301902786571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5899680430775547852227029 138273760096301902786571)
                ·
                  rfl

theorem cell23_7270754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_7270754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270754 prefixEnd_7270754 := by exact prefixLift 7270754
  have htrace : WordTrace (prefixWord ++ tailWord_7270754) baseStart_7270754 baseEnd_7270754 := by
    simpa [prefixWord, tailWord_7270754, baseEnd_7270754] using wordTrace_append hprefix tailTrace_7270754
  have hstable : (prefixWord ++ tailWord_7270754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270754).length < 2 ^ (prefixWord ++ tailWord_7270754).sum := by decide
  have hdescent : baseEnd_7270754 < baseStart_7270754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270798 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7270798 : Nat := 118140960795 + 7270798 * 2 ^ 59
def prefixEnd_7270798 : Nat := 4983230072969 + 3 ^ 40 * 7270798 * 2
def baseEnd_7270798 : Nat := 3733414115748949203087215

theorem tailTrace_7270798 : CollatzResearch.WordTrace tailWord_7270798 prefixEnd_7270798 3733414115748949203087215 := by
  unfold tailWord_7270798
  simp only [CollatzResearch.WordTrace]
  refine ⟨33148473639143509285308631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176791859408765382854979365 33148473639143509285308631)
  ·
    refine ⟨49722710458715263927962947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33148473639143509285308631 49722710458715263927962947)
    ·
      refine ⟨74584065688072895891944421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49722710458715263927962947 74584065688072895891944421)
      ·
        refine ⟨13984512316513667979739579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74584065688072895891944421 13984512316513667979739579)
        ·
          refine ⟨20976768474770501969609369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13984512316513667979739579 20976768474770501969609369)
          ·
            refine ⟨15732576356077876477207027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20976768474770501969609369 15732576356077876477207027)
            ·
              refine ⟨23598864534116814715810541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732576356077876477207027 23598864534116814715810541)
              ·
                refine ⟨8849574200293805518428953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23598864534116814715810541 8849574200293805518428953)
                ·
                  refine ⟨6637180650220354138821715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8849574200293805518428953 6637180650220354138821715)
                  ·
                    refine ⟨9955770975330531208232573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637180650220354138821715 9955770975330531208232573)
                    ·
                      refine ⟨3733414115748949203087215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9955770975330531208232573 3733414115748949203087215)
                      ·
                        rfl

theorem cell23_7270798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7270798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270798 prefixEnd_7270798 := by exact prefixLift 7270798
  have htrace : WordTrace (prefixWord ++ tailWord_7270798) baseStart_7270798 baseEnd_7270798 := by
    simpa [prefixWord, tailWord_7270798, baseEnd_7270798] using wordTrace_append hprefix tailTrace_7270798
  have hstable : (prefixWord ++ tailWord_7270798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270798).length < 2 ^ (prefixWord ++ tailWord_7270798).sum := by decide
  have hdescent : baseEnd_7270798 < baseStart_7270798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270807 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_7270807 : Nat := 118140960795 + 7270807 * 2 ^ 59
def prefixEnd_7270807 : Nat := 4983230072969 + 3 ^ 40 * 7270807 * 2
def baseEnd_7270807 : Nat := 3733418737074839667874673

theorem tailTrace_7270807 : CollatzResearch.WordTrace tailWord_7270807 prefixEnd_7270807 3733418737074839667874673 := by
  unfold tailWord_7270807
  simp only [CollatzResearch.WordTrace]
  refine ⟨265188117370115468819546675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176792078246743645879697783 265188117370115468819546675)
  ·
    refine ⟨397782176055173203229320013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265188117370115468819546675 397782176055173203229320013)
    ·
      refine ⟨149168316020689951210995005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397782176055173203229320013 149168316020689951210995005)
      ·
        refine ⟨55938118507758731704123127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149168316020689951210995005 55938118507758731704123127)
        ·
          refine ⟨83907177761638097556184691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55938118507758731704123127 83907177761638097556184691)
          ·
            refine ⟨125860766642457146334277037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83907177761638097556184691 125860766642457146334277037)
            ·
              refine ⟨47197787490921429875353889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125860766642457146334277037 47197787490921429875353889)
              ·
                refine ⟨35398340618191072406515417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47197787490921429875353889 35398340618191072406515417)
                ·
                  refine ⟨26548755463643304304886563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35398340618191072406515417 26548755463643304304886563)
                  ·
                    refine ⟨39823133195464956457329845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26548755463643304304886563 39823133195464956457329845)
                    ·
                      refine ⟨3733418737074839667874673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39823133195464956457329845 3733418737074839667874673)
                      ·
                        rfl

theorem cell23_7270807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_7270807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270807 prefixEnd_7270807 := by exact prefixLift 7270807
  have htrace : WordTrace (prefixWord ++ tailWord_7270807) baseStart_7270807 baseEnd_7270807 := by
    simpa [prefixWord, tailWord_7270807, baseEnd_7270807] using wordTrace_append hprefix tailTrace_7270807
  have hstable : (prefixWord ++ tailWord_7270807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270807).length < 2 ^ (prefixWord ++ tailWord_7270807).sum := by decide
  have hdescent : baseEnd_7270807 < baseStart_7270807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270808 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2]
def baseStart_7270808 : Nat := 118140960795 + 7270808 * 2 ^ 59
def prefixEnd_7270808 : Nat := 4983230072969 + 3 ^ 40 * 7270808 * 2
def baseEnd_7270808 : Nat := 3733419250555494163962169

theorem tailTrace_7270808 : CollatzResearch.WordTrace tailWord_7270808 prefixEnd_7270808 3733419250555494163962169 := by
  unfold tailWord_7270808
  simp only [CollatzResearch.WordTrace]
  refine ⟨132594076921555922995166539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176792102562074563993555385 132594076921555922995166539)
  ·
    refine ⟨198891115382333884492749809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132594076921555922995166539 198891115382333884492749809)
    ·
      refine ⟨149168336536750413369562357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198891115382333884492749809 149168336536750413369562357)
      ·
        refine ⟨13984531550320351253396471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149168336536750413369562357 13984531550320351253396471)
        ·
          refine ⟨20976797325480526880094707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13984531550320351253396471 20976797325480526880094707)
          ·
            refine ⟨31465195988220790320142061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20976797325480526880094707 31465195988220790320142061)
            ·
              refine ⟨11799448495582796370053273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31465195988220790320142061 11799448495582796370053273)
              ·
                refine ⟨8849586371687097277539955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11799448495582796370053273 8849586371687097277539955)
                ·
                  refine ⟨13274379557530645916309933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849586371687097277539955 13274379557530645916309933)
                  ·
                    refine ⟨4977892334073992218616225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13274379557530645916309933 4977892334073992218616225)
                    ·
                      refine ⟨3733419250555494163962169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4977892334073992218616225 3733419250555494163962169)
                      ·
                        rfl

theorem cell23_7270808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_7270808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270808 prefixEnd_7270808 := by exact prefixLift 7270808
  have htrace : WordTrace (prefixWord ++ tailWord_7270808) baseStart_7270808 baseEnd_7270808 := by
    simpa [prefixWord, tailWord_7270808, baseEnd_7270808] using wordTrace_append hprefix tailTrace_7270808
  have hstable : (prefixWord ++ tailWord_7270808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270808).length < 2 ^ (prefixWord ++ tailWord_7270808).sum := by decide
  have hdescent : baseEnd_7270808 < baseStart_7270808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270857 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_7270857 : Nat := 118140960795 + 7270857 * 2 ^ 59
def prefixEnd_7270857 : Nat := 4983230072969 + 3 ^ 40 * 7270857 * 2
def baseEnd_7270857 : Nat := 1244481470369188157416481

theorem tailTrace_7270857 : CollatzResearch.WordTrace tailWord_7270857 prefixEnd_7270857 1244481470369188157416481 := by
  unfold tailWord_7270857
  simp only [CollatzResearch.WordTrace]
  refine ⟨265189941019934327358866825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176793294013289551572577883 265189941019934327358866825)
  ·
    refine ⟨198892455764950745519150119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265189941019934327358866825 198892455764950745519150119)
    ·
      refine ⟨298338683647426118278725179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198892455764950745519150119 298338683647426118278725179)
      ·
        refine ⟨447508025471139177418087769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298338683647426118278725179 447508025471139177418087769)
        ·
          refine ⟨335631019103354383063565827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447508025471139177418087769 335631019103354383063565827)
          ·
            refine ⟨503446528655031574595348741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335631019103354383063565827 503446528655031574595348741)
            ·
              refine ⟨94396224122818420236627889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503446528655031574595348741 94396224122818420236627889)
              ·
                refine ⟨70797168092113815177470917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94396224122818420236627889 70797168092113815177470917)
                ·
                  refine ⟨13274469017271340345775797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70797168092113815177470917 13274469017271340345775797)
                  ·
                    refine ⟨1244481470369188157416481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13274469017271340345775797 1244481470369188157416481)
                    ·
                      rfl

theorem cell23_7270857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_7270857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270857 prefixEnd_7270857 := by exact prefixLift 7270857
  have htrace : WordTrace (prefixWord ++ tailWord_7270857) baseStart_7270857 baseEnd_7270857 := by
    simpa [prefixWord, tailWord_7270857, baseEnd_7270857] using wordTrace_append hprefix tailTrace_7270857
  have hstable : (prefixWord ++ tailWord_7270857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270857).length < 2 ^ (prefixWord ++ tailWord_7270857).sum := by decide
  have hdescent : baseEnd_7270857 < baseStart_7270857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270907 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_7270907 : Nat := 118140960795 + 7270907 * 2 ^ 59
def prefixEnd_7270907 : Nat := 4983230072969 + 3 ^ 40 * 7270907 * 2
def baseEnd_7270907 : Nat := 3733470085140289276624213

theorem tailTrace_7270907 : CollatzResearch.WordTrace tailWord_7270907 prefixEnd_7270907 3733470085140289276624213 := by
  unfold tailWord_7270907
  simp only [CollatzResearch.WordTrace]
  refine ⟨265191764669753185898186975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176794509779835457265457983 265191764669753185898186975)
  ·
    refine ⟨397787647004629778847280463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265191764669753185898186975 397787647004629778847280463)
    ·
      refine ⟨596681470506944668270920695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397787647004629778847280463 596681470506944668270920695)
      ·
        refine ⟨895022205760417002406381043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596681470506944668270920695 895022205760417002406381043)
        ·
          refine ⟨1342533308640625503609571565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895022205760417002406381043 1342533308640625503609571565)
          ·
            refine ⟨503449990740234563853589337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1342533308640625503609571565 503449990740234563853589337)
            ·
              refine ⟨377587493055175922890192003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503449990740234563853589337 377587493055175922890192003)
              ·
                refine ⟨566381239582763884335288005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377587493055175922890192003 566381239582763884335288005)
                ·
                  refine ⟨106196482421768228312866501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 566381239582763884335288005 106196482421768228312866501)
                  ·
                    refine ⟨19911840454081542808662469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106196482421768228312866501 19911840454081542808662469)
                    ·
                      refine ⟨3733470085140289276624213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19911840454081542808662469 3733470085140289276624213)
                      ·
                        rfl

theorem cell23_7270907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_7270907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270907 prefixEnd_7270907 := by exact prefixLift 7270907
  have htrace : WordTrace (prefixWord ++ tailWord_7270907) baseStart_7270907 baseEnd_7270907 := by
    simpa [prefixWord, tailWord_7270907, baseEnd_7270907] using wordTrace_append hprefix tailTrace_7270907
  have hstable : (prefixWord ++ tailWord_7270907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270907).length < 2 ^ (prefixWord ++ tailWord_7270907).sum := by decide
  have hdescent : baseEnd_7270907 < baseStart_7270907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270937 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_7270937 : Nat := 118140960795 + 7270937 * 2 ^ 59
def prefixEnd_7270937 : Nat := 4983230072969 + 3 ^ 40 * 7270937 * 2
def baseEnd_7270937 : Nat := 3733485489559924159249075

theorem tailTrace_7270937 : CollatzResearch.WordTrace tailWord_7270937 prefixEnd_7270937 3733485489559924159249075 := by
  unfold tailWord_7270937
  simp only [CollatzResearch.WordTrace]
  refine ⟨265192858859644501021779065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176795239239763000681186043 265192858859644501021779065)
  ·
    refine ⟨198894644144733375766334299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265192858859644501021779065 198894644144733375766334299)
    ·
      refine ⟨298341966217100063649501449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198894644144733375766334299 298341966217100063649501449)
      ·
        refine ⟨223756474662825047737126087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298341966217100063649501449 223756474662825047737126087)
        ·
          refine ⟨335634711994237571605689131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223756474662825047737126087 335634711994237571605689131)
          ·
            refine ⟨503452067991356357408533697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335634711994237571605689131 503452067991356357408533697)
            ·
              refine ⟨377589050993517268056400273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503452067991356357408533697 377589050993517268056400273)
              ·
                refine ⟨283191788245137951042300205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377589050993517268056400273 283191788245137951042300205)
                ·
                  refine ⟨106196920591926731640862577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283191788245137951042300205 106196920591926731640862577)
                  ·
                    refine ⟨79647690443945048730646933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106196920591926731640862577 79647690443945048730646933)
                    ·
                      refine ⟨3733485489559924159249075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79647690443945048730646933 3733485489559924159249075)
                      ·
                        rfl

theorem cell23_7270937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_7270937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270937 prefixEnd_7270937 := by exact prefixLift 7270937
  have htrace : WordTrace (prefixWord ++ tailWord_7270937) baseStart_7270937 baseEnd_7270937 := by
    simpa [prefixWord, tailWord_7270937, baseEnd_7270937] using wordTrace_append hprefix tailTrace_7270937
  have hstable : (prefixWord ++ tailWord_7270937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270937).length < 2 ^ (prefixWord ++ tailWord_7270937).sum := by decide
  have hdescent : baseEnd_7270937 < baseStart_7270937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270938 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_7270938 : Nat := 118140960795 + 7270938 * 2 ^ 59
def prefixEnd_7270938 : Nat := 4983230072969 + 3 ^ 40 * 7270938 * 2
def baseEnd_7270938 : Nat := 1244495334346859551778857

theorem tailTrace_7270938 : CollatzResearch.WordTrace tailWord_7270938 prefixEnd_7270938 1244495334346859551778857 := by
  unfold tailWord_7270938
  simp only [CollatzResearch.WordTrace]
  refine ⟨66298223833160219548141367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176795263555093918795043645 66298223833160219548141367)
  ·
    refine ⟨99447335749740329322212051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66298223833160219548141367 99447335749740329322212051)
    ·
      refine ⟨149171003624610493983318077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99447335749740329322212051 149171003624610493983318077)
      ·
        refine ⟨55939126359228935243744279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149171003624610493983318077 55939126359228935243744279)
        ·
          refine ⟨83908689538843402865616419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55939126359228935243744279 83908689538843402865616419)
          ·
            refine ⟨125863034308265104298424629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83908689538843402865616419 125863034308265104298424629)
            ·
              refine ⟨11799659466399853527977309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125863034308265104298424629 11799659466399853527977309)
              ·
                refine ⟨4424872299899945072991491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11799659466399853527977309 4424872299899945072991491)
                ·
                  refine ⟨6637308449849917609487237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4424872299899945072991491 6637308449849917609487237)
                  ·
                    refine ⟨1244495334346859551778857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637308449849917609487237 1244495334346859551778857)
                    ·
                      rfl

theorem cell23_7270938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_7270938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270938 prefixEnd_7270938 := by exact prefixLift 7270938
  have htrace : WordTrace (prefixWord ++ tailWord_7270938) baseStart_7270938 baseEnd_7270938 := by
    simpa [prefixWord, tailWord_7270938, baseEnd_7270938] using wordTrace_append hprefix tailTrace_7270938
  have hstable : (prefixWord ++ tailWord_7270938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270938).length < 2 ^ (prefixWord ++ tailWord_7270938).sum := by decide
  have hdescent : baseEnd_7270938 < baseStart_7270938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270981 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_7270981 : Nat := 118140960795 + 7270981 * 2 ^ 59
def prefixEnd_7270981 : Nat := 4983230072969 + 3 ^ 40 * 7270981 * 2
def baseEnd_7270981 : Nat := 1244502694236240662366291

theorem tailTrace_7270981 : CollatzResearch.WordTrace tailWord_7270981 prefixEnd_7270981 1244502694236240662366291 := by
  unfold tailWord_7270981
  simp only [CollatzResearch.WordTrace]
  refine ⟨265194463671485096536380797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176796309114323397690920531 265194463671485096536380797)
  ·
    refine ⟨99447923876806911201142799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265194463671485096536380797 99447923876806911201142799)
    ·
      refine ⟨149171885815210366801714199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99447923876806911201142799 149171885815210366801714199)
      ·
        refine ⟨223757828722815550202571299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149171885815210366801714199 223757828722815550202571299)
        ·
          refine ⟨335636743084223325303856949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223757828722815550202571299 335636743084223325303856949)
          ·
            refine ⟨31465944664145936747236589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335636743084223325303856949 31465944664145936747236589)
            ·
              refine ⟨11799729249054726280213721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31465944664145936747236589 11799729249054726280213721)
              ·
                refine ⟨8849796936791044710160291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11799729249054726280213721 8849796936791044710160291)
                ·
                  refine ⟨13274695405186567065240437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8849796936791044710160291 13274695405186567065240437)
                  ·
                    refine ⟨1244502694236240662366291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13274695405186567065240437 1244502694236240662366291)
                    ·
                      rfl

theorem cell23_7270981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_7270981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270981 prefixEnd_7270981 := by exact prefixLift 7270981
  have htrace : WordTrace (prefixWord ++ tailWord_7270981) baseStart_7270981 baseEnd_7270981 := by
    simpa [prefixWord, tailWord_7270981, baseEnd_7270981] using wordTrace_append hprefix tailTrace_7270981
  have hstable : (prefixWord ++ tailWord_7270981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270981).length < 2 ^ (prefixWord ++ tailWord_7270981).sum := by decide
  have hdescent : baseEnd_7270981 < baseStart_7270981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7270988 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7270988 : Nat := 118140960795 + 7270988 * 2 ^ 59
def prefixEnd_7270988 : Nat := 4983230072969 + 3 ^ 40 * 7270988 * 2
def baseEnd_7270988 : Nat := 3733511677073303459711341

theorem tailTrace_7270988 : CollatzResearch.WordTrace tailWord_7270988 prefixEnd_7270988 3733511677073303459711341 := by
  unfold tailWord_7270988
  simp only [CollatzResearch.WordTrace]
  refine ⟨132597359491229868365942809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176796479321639824487923745 132597359491229868365942809)
  ·
    refine ⟨99448019618422401274457107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132597359491229868365942809 99448019618422401274457107)
    ·
      refine ⟨149172029427633601911685661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99448019618422401274457107 149172029427633601911685661)
      ·
        refine ⟨55939511035362600716882123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149172029427633601911685661 55939511035362600716882123)
        ·
          refine ⟨83909266553043901075323185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55939511035362600716882123 83909266553043901075323185)
          ·
            refine ⟨62931949914782925806492389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83909266553043901075323185 62931949914782925806492389)
            ·
              refine ⟨11799740609021798588717323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62931949914782925806492389 11799740609021798588717323)
              ·
                refine ⟨17699610913532697883075985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799740609021798588717323 17699610913532697883075985)
                ·
                  refine ⟨13274708185149523412306989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17699610913532697883075985 13274708185149523412306989)
                  ·
                    refine ⟨4978015569431071279615121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13274708185149523412306989 4978015569431071279615121)
                    ·
                      refine ⟨3733511677073303459711341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978015569431071279615121 3733511677073303459711341)
                      ·
                        rfl

theorem cell23_7270988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7270988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7270988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7270988 prefixEnd_7270988 := by exact prefixLift 7270988
  have htrace : WordTrace (prefixWord ++ tailWord_7270988) baseStart_7270988 baseEnd_7270988 := by
    simpa [prefixWord, tailWord_7270988, baseEnd_7270988] using wordTrace_append hprefix tailTrace_7270988
  have hstable : (prefixWord ++ tailWord_7270988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7270988).length < 2 ^ (prefixWord ++ tailWord_7270988).sum := by decide
  have hdescent : baseEnd_7270988 < baseStart_7270988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7270988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271041 : List Nat := [1, 2, 4, 2, 1, 1, 5, 7]
def baseStart_7271041 : Nat := 118140960795 + 7271041 * 2 ^ 59
def prefixEnd_7271041 : Nat := 4983230072969 + 3 ^ 40 * 7271041 * 2
def baseEnd_7271041 : Nat := 138279218205481176012911

theorem tailTrace_7271041 : CollatzResearch.WordTrace tailWord_7271041 prefixEnd_7271041 138279218205481176012911 := by
  unfold tailWord_7271041
  simp only [CollatzResearch.WordTrace]
  refine ⟨265196652051267726783564977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176797768034178484522376651 265196652051267726783564977)
  ·
    refine ⟨198897489038450795087673733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265196652051267726783564977 198897489038450795087673733)
    ·
      refine ⟨37293279194709524078938825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198897489038450795087673733 37293279194709524078938825)
      ·
        refine ⟨27969959396032143059204119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37293279194709524078938825 27969959396032143059204119)
        ·
          refine ⟨41954939094048214588806179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27969959396032143059204119 41954939094048214588806179)
          ·
            refine ⟨62932408641072321883209269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41954939094048214588806179 62932408641072321883209269)
            ·
              refine ⟨5899913310100530176550869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62932408641072321883209269 5899913310100530176550869)
              ·
                refine ⟨138279218205481176012911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5899913310100530176550869 138279218205481176012911)
                ·
                  rfl

theorem cell23_7271041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 7].length) (baseStart_7271041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271041 prefixEnd_7271041 := by exact prefixLift 7271041
  have htrace : WordTrace (prefixWord ++ tailWord_7271041) baseStart_7271041 baseEnd_7271041 := by
    simpa [prefixWord, tailWord_7271041, baseEnd_7271041] using wordTrace_append hprefix tailTrace_7271041
  have hstable : (prefixWord ++ tailWord_7271041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271041).length < 2 ^ (prefixWord ++ tailWord_7271041).sum := by decide
  have hdescent : baseEnd_7271041 < baseStart_7271041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271082 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7271082 : Nat := 118140960795 + 7271082 * 2 ^ 59
def prefixEnd_7271082 : Nat := 4983230072969 + 3 ^ 40 * 7271082 * 2
def baseEnd_7271082 : Nat := 3733559944254826091935909

theorem tailTrace_7271082 : CollatzResearch.WordTrace tailWord_7271082 prefixEnd_7271082 3733559944254826091935909 := by
  unfold tailWord_7271082
  simp only [CollatzResearch.WordTrace]
  refine ⟨66299536861029797696451875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176798764962746127190538333 66299536861029797696451875)
  ·
    refine ⟨99449305291544696544677813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66299536861029797696451875 99449305291544696544677813)
    ·
      refine ⟨9323372371082315301063545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99449305291544696544677813 9323372371082315301063545)
      ·
        refine ⟨6992529278311736475797659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9323372371082315301063545 6992529278311736475797659)
        ·
          refine ⟨10488793917467604713696489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992529278311736475797659 10488793917467604713696489)
          ·
            refine ⟨7866595438100703535272367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10488793917467604713696489 7866595438100703535272367)
            ·
              refine ⟨11799893157151055302908551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866595438100703535272367 11799893157151055302908551)
              ·
                refine ⟨17699839735726582954362827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799893157151055302908551 17699839735726582954362827)
                ·
                  refine ⟨26549759603589874431544241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17699839735726582954362827 26549759603589874431544241)
                  ·
                    refine ⟨19912319702692405823658181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26549759603589874431544241 19912319702692405823658181)
                    ·
                      refine ⟨3733559944254826091935909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19912319702692405823658181 3733559944254826091935909)
                      ·
                        rfl

theorem cell23_7271082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7271082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271082 prefixEnd_7271082 := by exact prefixLift 7271082
  have htrace : WordTrace (prefixWord ++ tailWord_7271082) baseStart_7271082 baseEnd_7271082 := by
    simpa [prefixWord, tailWord_7271082, baseEnd_7271082] using wordTrace_append hprefix tailTrace_7271082
  have hstable : (prefixWord ++ tailWord_7271082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271082).length < 2 ^ (prefixWord ++ tailWord_7271082).sum := by decide
  have hdescent : baseEnd_7271082 < baseStart_7271082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271085 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_7271085 : Nat := 118140960795 + 7271085 * 2 ^ 59
def prefixEnd_7271085 : Nat := 4983230072969 + 3 ^ 40 * 7271085 * 2
def baseEnd_7271085 : Nat := 3733561484696789580198395

theorem tailTrace_7271085 : CollatzResearch.WordTrace tailWord_7271085 prefixEnd_7271085 3733561484696789580198395 := by
  unfold tailWord_7271085
  simp only [CollatzResearch.WordTrace]
  refine ⟨265198256863108322298166709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176798837908738881532111139 265198256863108322298166709)
  ·
    refine ⟨24862336580916405215453129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265198256863108322298166709 24862336580916405215453129)
    ·
      refine ⟨18646752435687303911589847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24862336580916405215453129 18646752435687303911589847)
      ·
        refine ⟨27970128653530955867384771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18646752435687303911589847 27970128653530955867384771)
        ·
          refine ⟨41955192980296433801077157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27970128653530955867384771 41955192980296433801077157)
          ·
            refine ⟨7866598683805581337701967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41955192980296433801077157 7866598683805581337701967)
            ·
              refine ⟨11799898025708372006552951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866598683805581337701967 11799898025708372006552951)
              ·
                refine ⟨17699847038562558009829427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11799898025708372006552951 17699847038562558009829427)
                ·
                  refine ⟨26549770557843837014744141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17699847038562558009829427 26549770557843837014744141)
                  ·
                    refine ⟨9956163959191438880529053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26549770557843837014744141 9956163959191438880529053)
                    ·
                      refine ⟨3733561484696789580198395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956163959191438880529053 3733561484696789580198395)
                      ·
                        rfl

theorem cell23_7271085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_7271085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271085 prefixEnd_7271085 := by exact prefixLift 7271085
  have htrace : WordTrace (prefixWord ++ tailWord_7271085) baseStart_7271085 baseEnd_7271085 := by
    simpa [prefixWord, tailWord_7271085, baseEnd_7271085] using wordTrace_append hprefix tailTrace_7271085
  have hstable : (prefixWord ++ tailWord_7271085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271085).length < 2 ^ (prefixWord ++ tailWord_7271085).sum := by decide
  have hdescent : baseEnd_7271085 < baseStart_7271085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271218 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_7271218 : Nat := 118140960795 + 7271218 * 2 ^ 59
def prefixEnd_7271218 : Nat := 4983230072969 + 3 ^ 40 * 7271218 * 2
def baseEnd_7271218 : Nat := 3733629777623837559835283

theorem tailTrace_7271218 : CollatzResearch.WordTrace tailWord_7271218 prefixEnd_7271218 3733629777623837559835283 := by
  unfold tailWord_7271218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66300776942906621503189577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176802071847750990675172205 66300776942906621503189577)
  ·
    refine ⟨49725582707179966127392183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66300776942906621503189577 49725582707179966127392183)
    ·
      refine ⟨74588374060769949191088275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49725582707179966127392183 74588374060769949191088275)
      ·
        refine ⟨111882561091154923786632413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74588374060769949191088275 111882561091154923786632413)
        ·
          refine ⟨41955960409183096419987155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111882561091154923786632413 41955960409183096419987155)
          ·
            refine ⟨62933940613774644629980733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41955960409183096419987155 62933940613774644629980733)
            ·
              refine ⟨23600227730165491736242775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62933940613774644629980733 23600227730165491736242775)
              ·
                refine ⟨35400341595248237604364163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23600227730165491736242775 35400341595248237604364163)
                ·
                  refine ⟨53100512392872356406546245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35400341595248237604364163 53100512392872356406546245)
                  ·
                    refine ⟨9956346073663566826227421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53100512392872356406546245 9956346073663566826227421)
                    ·
                      refine ⟨3733629777623837559835283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956346073663566826227421 3733629777623837559835283)
                      ·
                        rfl

theorem cell23_7271218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_7271218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271218 prefixEnd_7271218 := by exact prefixLift 7271218
  have htrace : WordTrace (prefixWord ++ tailWord_7271218) baseStart_7271218 baseEnd_7271218 := by
    simpa [prefixWord, tailWord_7271218, baseEnd_7271218] using wordTrace_append hprefix tailTrace_7271218
  have hstable : (prefixWord ++ tailWord_7271218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271218).length < 2 ^ (prefixWord ++ tailWord_7271218).sum := by decide
  have hdescent : baseEnd_7271218 < baseStart_7271218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271241 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_7271241 : Nat := 118140960795 + 7271241 * 2 ^ 59
def prefixEnd_7271241 : Nat := 4983230072969 + 3 ^ 40 * 7271241 * 2
def baseEnd_7271241 : Nat := 3733641587678890969847677

theorem tailTrace_7271241 : CollatzResearch.WordTrace tailWord_7271241 prefixEnd_7271241 3733641587678890969847677 := by
  unfold tailWord_7271241
  simp only [CollatzResearch.WordTrace]
  refine ⟨265203946650543160940845577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176802631100362107293897051 265203946650543160940845577)
  ·
    refine ⟨198902959987907370705634183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265203946650543160940845577 198902959987907370705634183)
    ·
      refine ⟨298354439981861056058451275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198902959987907370705634183 298354439981861056058451275)
      ·
        refine ⟨447531659972791584087676913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298354439981861056058451275 447531659972791584087676913)
        ·
          refine ⟨335648744979593688065757685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447531659972791584087676913 335648744979593688065757685)
          ·
            refine ⟨31467069841836908256164783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335648744979593688065757685 31467069841836908256164783)
            ·
              refine ⟨47200604762755362384247175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31467069841836908256164783 47200604762755362384247175)
              ·
                refine ⟨70800907144133043576370763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47200604762755362384247175 70800907144133043576370763)
                ·
                  refine ⟨106201360716199565364556145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70800907144133043576370763 106201360716199565364556145)
                  ·
                    refine ⟨79651020537149674023417109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106201360716199565364556145 79651020537149674023417109)
                    ·
                      refine ⟨3733641587678890969847677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79651020537149674023417109 3733641587678890969847677)
                      ·
                        rfl

theorem cell23_7271241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_7271241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271241 prefixEnd_7271241 := by exact prefixLift 7271241
  have htrace : WordTrace (prefixWord ++ tailWord_7271241) baseStart_7271241 baseEnd_7271241 := by
    simpa [prefixWord, tailWord_7271241, baseEnd_7271241] using wordTrace_append hprefix tailTrace_7271241
  have hstable : (prefixWord ++ tailWord_7271241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271241).length < 2 ^ (prefixWord ++ tailWord_7271241).sum := by decide
  have hdescent : baseEnd_7271241 < baseStart_7271241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271251 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 5, 5]
def baseStart_7271251 : Nat := 118140960795 + 7271251 * 2 ^ 59
def prefixEnd_7271251 : Nat := 4983230072969 + 3 ^ 40 * 7271251 * 2
def baseEnd_7271251 : Nat := 1244548907495145310240877

theorem tailTrace_7271251 : CollatzResearch.WordTrace tailWord_7271251 prefixEnd_7271251 1244548907495145310240877 := by
  unfold tailWord_7271251
  simp only [CollatzResearch.WordTrace]
  refine ⟨265204311380506932648709607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176802874253671288432473071 265204311380506932648709607)
  ·
    refine ⟨397806467070760398973064411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265204311380506932648709607 397806467070760398973064411)
    ·
      refine ⟨596709700606140598459596617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397806467070760398973064411 596709700606140598459596617)
      ·
        refine ⟨447532275454605448844697463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596709700606140598459596617 447532275454605448844697463)
        ·
          refine ⟨671298413181908173267046195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447532275454605448844697463 671298413181908173267046195)
          ·
            refine ⟨1006947619772862259900569293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671298413181908173267046195 1006947619772862259900569293)
            ·
              refine ⟨377605357414823347462713485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006947619772862259900569293 377605357414823347462713485)
              ·
                refine ⟨141602009030558755298517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377605357414823347462713485 141602009030558755298517557)
                ·
                  refine ⟨13275188346614883309236021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141602009030558755298517557 13275188346614883309236021)
                  ·
                    refine ⟨1244548907495145310240877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13275188346614883309236021 1244548907495145310240877)
                    ·
                      rfl

theorem cell23_7271251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 5].length) (baseStart_7271251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271251 prefixEnd_7271251 := by exact prefixLift 7271251
  have htrace : WordTrace (prefixWord ++ tailWord_7271251) baseStart_7271251 baseEnd_7271251 := by
    simpa [prefixWord, tailWord_7271251, baseEnd_7271251] using wordTrace_append hprefix tailTrace_7271251
  have hstable : (prefixWord ++ tailWord_7271251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271251).length < 2 ^ (prefixWord ++ tailWord_7271251).sum := by decide
  have hdescent : baseEnd_7271251 < baseStart_7271251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271255 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 6]
def baseStart_7271255 : Nat := 118140960795 + 7271255 * 2 ^ 59
def prefixEnd_7271255 : Nat := 4983230072969 + 3 ^ 40 * 7271255 * 2
def baseEnd_7271255 : Nat := 414849864045339323896957

theorem tailTrace_7271255 : CollatzResearch.WordTrace tailWord_7271255 prefixEnd_7271255 414849864045339323896957 := by
  unfold tailWord_7271255
  simp only [CollatzResearch.WordTrace]
  refine ⟨265204457272492441331855219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176802971514994960887903479 265204457272492441331855219)
  ·
    refine ⟨397806685908738661997782829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265204457272492441331855219 397806685908738661997782829)
    ·
      refine ⟨149177507215776998249168561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397806685908738661997782829 149177507215776998249168561)
      ·
        refine ⟨111883130411832748686876421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149177507215776998249168561 111883130411832748686876421)
        ·
          refine ⟨20978086952218640378789329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111883130411832748686876421 20978086952218640378789329)
          ·
            refine ⟨15733565214163980284091997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20978086952218640378789329 15733565214163980284091997)
            ·
              refine ⟨5900086955311492606534499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15733565214163980284091997 5900086955311492606534499)
              ·
                refine ⟨8850130432967238909801749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900086955311492606534499 8850130432967238909801749)
                ·
                  refine ⟨414849864045339323896957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8850130432967238909801749 414849864045339323896957)
                  ·
                    rfl

theorem cell23_7271255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 6].length) (baseStart_7271255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271255 prefixEnd_7271255 := by exact prefixLift 7271255
  have htrace : WordTrace (prefixWord ++ tailWord_7271255) baseStart_7271255 baseEnd_7271255 := by
    simpa [prefixWord, tailWord_7271255, baseEnd_7271255] using wordTrace_append hprefix tailTrace_7271255
  have hstable : (prefixWord ++ tailWord_7271255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271255).length < 2 ^ (prefixWord ++ tailWord_7271255).sum := by decide
  have hdescent : baseEnd_7271255 < baseStart_7271255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271285 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_7271285 : Nat := 118140960795 + 7271285 * 2 ^ 59
def prefixEnd_7271285 : Nat := 4983230072969 + 3 ^ 40 * 7271285 * 2
def baseEnd_7271285 : Nat := 1244554726942562932565825

theorem tailTrace_7271285 : CollatzResearch.WordTrace tailWord_7271285 prefixEnd_7271285 1244554726942562932565825 := by
  unfold tailWord_7271285
  simp only [CollatzResearch.WordTrace]
  refine ⟨265205551462383756455447309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176803700974922504303631539 265205551462383756455447309)
  ·
    refine ⟨99452081798393908670792741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265205551462383756455447309 99452081798393908670792741)
    ·
      refine ⟨18647265337198857875773639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99452081798393908670792741 18647265337198857875773639)
      ·
        refine ⟨27970898005798286813660459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18647265337198857875773639 27970898005798286813660459)
        ·
          refine ⟨41956347008697430220490689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27970898005798286813660459 41956347008697430220490689)
          ·
            refine ⟨31467260256523072665368017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41956347008697430220490689 31467260256523072665368017)
            ·
              refine ⟨23600445192392304499026013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31467260256523072665368017 23600445192392304499026013)
              ·
                refine ⟨8850166947147114187134755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23600445192392304499026013 8850166947147114187134755)
                ·
                  refine ⟨13275250420720671280702133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850166947147114187134755 13275250420720671280702133)
                  ·
                    refine ⟨1244554726942562932565825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13275250420720671280702133 1244554726942562932565825)
                    ·
                      rfl

theorem cell23_7271285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_7271285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271285 prefixEnd_7271285 := by exact prefixLift 7271285
  have htrace : WordTrace (prefixWord ++ tailWord_7271285) baseStart_7271285 baseEnd_7271285 := by
    simpa [prefixWord, tailWord_7271285, baseEnd_7271285] using wordTrace_append hprefix tailTrace_7271285
  have hstable : (prefixWord ++ tailWord_7271285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271285).length < 2 ^ (prefixWord ++ tailWord_7271285).sum := by decide
  have hdescent : baseEnd_7271285 < baseStart_7271285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271299 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 1, 1, 3]
def baseStart_7271299 : Nat := 118140960795 + 7271299 * 2 ^ 59
def prefixEnd_7271299 : Nat := 4983230072969 + 3 ^ 40 * 7271299 * 2
def baseEnd_7271299 : Nat := 3733671369556851742922411

theorem tailTrace_7271299 : CollatzResearch.WordTrace tailWord_7271299 prefixEnd_7271299 3733671369556851742922411 := by
  unfold tailWord_7271299
  simp only [CollatzResearch.WordTrace]
  refine ⟨265206062084333036846456951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176804041389555357897637967 265206062084333036846456951)
  ·
    refine ⟨397809093126499555269685427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265206062084333036846456951 397809093126499555269685427)
    ·
      refine ⟨596713639689749332904528141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397809093126499555269685427 596713639689749332904528141)
      ·
        refine ⟨223767614883655999839198053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596713639689749332904528141 223767614883655999839198053)
        ·
          refine ⟨41956427790685499969849635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223767614883655999839198053 41956427790685499969849635)
          ·
            refine ⟨62934641686028249954774453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41956427790685499969849635 62934641686028249954774453)
            ·
              refine ⟨5900122658065148433260105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62934641686028249954774453 5900122658065148433260105)
              ·
                refine ⟨4425091993548861324945079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5900122658065148433260105 4425091993548861324945079)
                ·
                  refine ⟨6637637990323291987417619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425091993548861324945079 6637637990323291987417619)
                  ·
                    refine ⟨9956456985484937981126429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637637990323291987417619 9956456985484937981126429)
                    ·
                      refine ⟨3733671369556851742922411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956456985484937981126429 3733671369556851742922411)
                      ·
                        rfl

theorem cell23_7271299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_7271299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271299 prefixEnd_7271299 := by exact prefixLift 7271299
  have htrace : WordTrace (prefixWord ++ tailWord_7271299) baseStart_7271299 baseEnd_7271299 := by
    simpa [prefixWord, tailWord_7271299, baseEnd_7271299] using wordTrace_append hprefix tailTrace_7271299
  have hstable : (prefixWord ++ tailWord_7271299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271299).length < 2 ^ (prefixWord ++ tailWord_7271299).sum := by decide
  have hdescent : baseEnd_7271299 < baseStart_7271299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271308 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7271308 : Nat := 118140960795 + 7271308 * 2 ^ 59
def prefixEnd_7271308 : Nat := 4983230072969 + 3 ^ 40 * 7271308 * 2
def baseEnd_7271308 : Nat := 3733675990882742207709869

theorem tailTrace_7271308 : CollatzResearch.WordTrace tailWord_7271308 prefixEnd_7271308 3733675990882742207709869 := by
  unfold tailWord_7271308
  simp only [CollatzResearch.WordTrace]
  refine ⟨132603195170650215691767289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176804260227533620922356385 132603195170650215691767289)
  ·
    refine ⟨99452396377987661768825467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132603195170650215691767289 99452396377987661768825467)
    ·
      refine ⟨149178594566981492653238201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99452396377987661768825467 149178594566981492653238201)
      ·
        refine ⟨111883945925236119489928651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149178594566981492653238201 111883945925236119489928651)
        ·
          refine ⟨167825918887854179234892977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111883945925236119489928651 167825918887854179234892977)
          ·
            refine ⟨125869439165890634426169733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167825918887854179234892977 125869439165890634426169733)
            ·
              refine ⟨23600519843604493954906825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125869439165890634426169733 23600519843604493954906825)
              ·
                refine ⟨17700389882703370466180119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23600519843604493954906825 17700389882703370466180119)
                ·
                  refine ⟨26550584824055055699270179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17700389882703370466180119 26550584824055055699270179)
                  ·
                    refine ⟨39825877236082583548905269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26550584824055055699270179 39825877236082583548905269)
                    ·
                      refine ⟨3733675990882742207709869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39825877236082583548905269 3733675990882742207709869)
                      ·
                        rfl

theorem cell23_7271308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7271308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271308 prefixEnd_7271308 := by exact prefixLift 7271308
  have htrace : WordTrace (prefixWord ++ tailWord_7271308) baseStart_7271308 baseEnd_7271308 := by
    simpa [prefixWord, tailWord_7271308, baseEnd_7271308] using wordTrace_append hprefix tailTrace_7271308
  have hstable : (prefixWord ++ tailWord_7271308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271308).length < 2 ^ (prefixWord ++ tailWord_7271308).sum := by decide
  have hdescent : baseEnd_7271308 < baseStart_7271308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271325 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_7271325 : Nat := 118140960795 + 7271325 * 2 ^ 59
def prefixEnd_7271325 : Nat := 4983230072969 + 3 ^ 40 * 7271325 * 2
def baseEnd_7271325 : Nat := 3733684720053868641197291

theorem tailTrace_7271325 : CollatzResearch.WordTrace tailWord_7271325 prefixEnd_7271325 3733684720053868641197291 := by
  unfold tailWord_7271325
  simp only [CollatzResearch.WordTrace]
  refine ⟨265207010382238843286903429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176804673588159228857935619 265207010382238843286903429)
  ·
    refine ⟨49726314446669783116294393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265207010382238843286903429 49726314446669783116294393)
    ·
      refine ⟨37294735835002337337220795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49726314446669783116294393 37294735835002337337220795)
      ·
        refine ⟨55942103752503506005831193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37294735835002337337220795 55942103752503506005831193)
        ·
          refine ⟨41956577814377629504373395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55942103752503506005831193 41956577814377629504373395)
          ·
            refine ⟨62934866721566444256560093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41956577814377629504373395 62934866721566444256560093)
            ·
              refine ⟨23600575020587416596210035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62934866721566444256560093 23600575020587416596210035)
              ·
                refine ⟨35400862530881124894315053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23600575020587416596210035 35400862530881124894315053)
                ·
                  refine ⟨13275323449080421835368145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35400862530881124894315053 13275323449080421835368145)
                  ·
                    refine ⟨9956492586810316376526109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13275323449080421835368145 9956492586810316376526109)
                    ·
                      refine ⟨3733684720053868641197291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956492586810316376526109 3733684720053868641197291)
                      ·
                        rfl

theorem cell23_7271325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_7271325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271325 prefixEnd_7271325 := by exact prefixLift 7271325
  have htrace : WordTrace (prefixWord ++ tailWord_7271325) baseStart_7271325 baseEnd_7271325 := by
    simpa [prefixWord, tailWord_7271325, baseEnd_7271325] using wordTrace_append hprefix tailTrace_7271325
  have hstable : (prefixWord ++ tailWord_7271325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271325).length < 2 ^ (prefixWord ++ tailWord_7271325).sum := by decide
  have hdescent : baseEnd_7271325 < baseStart_7271325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271350 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_7271350 : Nat := 118140960795 + 7271350 * 2 ^ 59
def prefixEnd_7271350 : Nat := 4983230072969 + 3 ^ 40 * 7271350 * 2
def baseEnd_7271350 : Nat := 3733697557070231043384677

theorem tailTrace_7271350 : CollatzResearch.WordTrace tailWord_7271350 prefixEnd_7271350 3733697557070231043384677 := by
  unfold tailWord_7271350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575495137946767034785219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176805281471432181704375669 16575495137946767034785219)
  ·
    refine ⟨24863242706920150552177829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16575495137946767034785219 24863242706920150552177829)
    ·
      refine ⟨4661858007547528228533343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24863242706920150552177829 4661858007547528228533343)
      ·
        refine ⟨6992787011321292342800015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661858007547528228533343 6992787011321292342800015)
        ·
          refine ⟨10489180516981938514200023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6992787011321292342800015 10489180516981938514200023)
          ·
            refine ⟨15733770775472907771300035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489180516981938514200023 15733770775472907771300035)
            ·
              refine ⟨23600656163209361656950053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15733770775472907771300035 23600656163209361656950053)
              ·
                refine ⟨4425123030601755310678135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23600656163209361656950053 4425123030601755310678135)
                ·
                  refine ⟨6637684545902632966017203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425123030601755310678135 6637684545902632966017203)
                  ·
                    refine ⟨9956526818853949449025805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637684545902632966017203 9956526818853949449025805)
                    ·
                      refine ⟨3733697557070231043384677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956526818853949449025805 3733697557070231043384677)
                      ·
                        rfl

theorem cell23_7271350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_7271350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271350 prefixEnd_7271350 := by exact prefixLift 7271350
  have htrace : WordTrace (prefixWord ++ tailWord_7271350) baseStart_7271350 baseEnd_7271350 := by
    simpa [prefixWord, tailWord_7271350, baseEnd_7271350] using wordTrace_append hprefix tailTrace_7271350
  have hstable : (prefixWord ++ tailWord_7271350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271350).length < 2 ^ (prefixWord ++ tailWord_7271350).sum := by decide
  have hdescent : baseEnd_7271350 < baseStart_7271350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271358 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_7271358 : Nat := 118140960795 + 7271358 * 2 ^ 59
def prefixEnd_7271358 : Nat := 4983230072969 + 3 ^ 40 * 7271358 * 2
def baseEnd_7271358 : Nat := 1244567221638489004028213

theorem tailTrace_7271358 : CollatzResearch.WordTrace tailWord_7271358 prefixEnd_7271358 1244567221638489004028213 := by
  unfold tailWord_7271358
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151026748889911240356841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176805475994079526615236485 33151026748889911240356841)
  ·
    refine ⟨24863270061667433430267631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33151026748889911240356841 24863270061667433430267631)
    ·
      refine ⟨37294905092501150145401447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24863270061667433430267631 37294905092501150145401447)
      ·
        refine ⟨55942357638751725218102171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37294905092501150145401447 55942357638751725218102171)
        ·
          refine ⟨83913536458127587827153257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55942357638751725218102171 83913536458127587827153257)
          ·
            refine ⟨62935152343595690870364943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83913536458127587827153257 62935152343595690870364943)
            ·
              refine ⟨94402728515393536305547415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62935152343595690870364943 94402728515393536305547415)
              ·
                refine ⟨141604092773090304458321123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94402728515393536305547415 141604092773090304458321123)
                ·
                  refine ⟨212406139159635456687481685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141604092773090304458321123 212406139159635456687481685)
                  ·
                    refine ⟨1244567221638489004028213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212406139159635456687481685 1244567221638489004028213)
                    ·
                      rfl

theorem cell23_7271358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_7271358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271358 prefixEnd_7271358 := by exact prefixLift 7271358
  have htrace : WordTrace (prefixWord ++ tailWord_7271358) baseStart_7271358 baseEnd_7271358 := by
    simpa [prefixWord, tailWord_7271358, baseEnd_7271358] using wordTrace_append hprefix tailTrace_7271358
  have hstable : (prefixWord ++ tailWord_7271358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271358).length < 2 ^ (prefixWord ++ tailWord_7271358).sum := by decide
  have hdescent : baseEnd_7271358 < baseStart_7271358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271372 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7271372 : Nat := 118140960795 + 7271372 * 2 ^ 59
def prefixEnd_7271372 : Nat := 4983230072969 + 3 ^ 40 * 7271372 * 2
def baseEnd_7271372 : Nat := 3733708853644629957309575

theorem tailTrace_7271372 : CollatzResearch.WordTrace tailWord_7271372 prefixEnd_7271372 3733708853644629957309575 := by
  unfold tailWord_7271372
  simp only [CollatzResearch.WordTrace]
  refine ⟨132604362306534285156932185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176805816408712380209242913 132604362306534285156932185)
  ·
    refine ⟨99453271729900713867699139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132604362306534285156932185 99453271729900713867699139)
    ·
      refine ⟨149179907594851070801548709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99453271729900713867699139 149179907594851070801548709)
      ·
        refine ⟨27971232674034575775290383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149179907594851070801548709 27971232674034575775290383)
        ·
          refine ⟨41956849011051863662935575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27971232674034575775290383 41956849011051863662935575)
          ·
            refine ⟨62935273516577795494403363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41956849011051863662935575 62935273516577795494403363)
            ·
              refine ⟨94402910274866693241605045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62935273516577795494403363 94402910274866693241605045)
              ·
                refine ⟨8850272838268752491400473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94402910274866693241605045 8850272838268752491400473)
                ·
                  refine ⟨6637704628701564368550355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8850272838268752491400473 6637704628701564368550355)
                  ·
                    refine ⟨9956556943052346552825533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637704628701564368550355 9956556943052346552825533)
                    ·
                      refine ⟨3733708853644629957309575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956556943052346552825533 3733708853644629957309575)
                      ·
                        rfl

theorem cell23_7271372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7271372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271372 prefixEnd_7271372 := by exact prefixLift 7271372
  have htrace : WordTrace (prefixWord ++ tailWord_7271372) baseStart_7271372 baseEnd_7271372 := by
    simpa [prefixWord, tailWord_7271372, baseEnd_7271372] using wordTrace_append hprefix tailTrace_7271372
  have hstable : (prefixWord ++ tailWord_7271372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271372).length < 2 ^ (prefixWord ++ tailWord_7271372).sum := by decide
  have hdescent : baseEnd_7271372 < baseStart_7271372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271399 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7271399 : Nat := 118140960795 + 7271399 * 2 ^ 59
def prefixEnd_7271399 : Nat := 4983230072969 + 3 ^ 40 * 7271399 * 2
def baseEnd_7271399 : Nat := 3733722717622301351671951

theorem tailTrace_7271399 : CollatzResearch.WordTrace tailWord_7271399 prefixEnd_7271399 3733722717622301351671951 := by
  unfold tailWord_7271399
  simp only [CollatzResearch.WordTrace]
  refine ⟨265209709383970753925097251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176806472922647169283398167 265209709383970753925097251)
  ·
    refine ⟨397814564075956130887645877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265209709383970753925097251 397814564075956130887645877)
    ·
      refine ⟨37295115382120887270716801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397814564075956130887645877 37295115382120887270716801)
      ·
        refine ⟨27971336536590665453037601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37295115382120887270716801 27971336536590665453037601)
        ·
          refine ⟨20978502402442999089778201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27971336536590665453037601 20978502402442999089778201)
          ·
            refine ⟨15733876801832249317333651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20978502402442999089778201 15733876801832249317333651)
            ·
              refine ⟨23600815202748373976000477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15733876801832249317333651 23600815202748373976000477)
              ·
                refine ⟨8850305701030640241000179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23600815202748373976000477 8850305701030640241000179)
                ·
                  refine ⟨13275458551545960361500269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850305701030640241000179 13275458551545960361500269)
                  ·
                    refine ⟨4978296956829735135562601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13275458551545960361500269 4978296956829735135562601)
                    ·
                      refine ⟨3733722717622301351671951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978296956829735135562601 3733722717622301351671951)
                      ·
                        rfl

theorem cell23_7271399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7271399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271399 prefixEnd_7271399 := by exact prefixLift 7271399
  have htrace : WordTrace (prefixWord ++ tailWord_7271399) baseStart_7271399 baseEnd_7271399 := by
    simpa [prefixWord, tailWord_7271399, baseEnd_7271399] using wordTrace_append hprefix tailTrace_7271399
  have hstable : (prefixWord ++ tailWord_7271399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271399).length < 2 ^ (prefixWord ++ tailWord_7271399).sum := by decide
  have hdescent : baseEnd_7271399 < baseStart_7271399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271406 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_7271406 : Nat := 118140960795 + 7271406 * 2 ^ 59
def prefixEnd_7271406 : Nat := 4983230072969 + 3 ^ 40 * 7271406 * 2
def baseEnd_7271406 : Nat := 3733726311986882824284419

theorem tailTrace_7271406 : CollatzResearch.WordTrace tailWord_7271406 prefixEnd_7271406 3733726311986882824284419 := by
  unfold tailWord_7271406
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151245586868174265075259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176806643129963596080401381 33151245586868174265075259)
  ·
    refine ⟨49726868380302261397612889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33151245586868174265075259 49726868380302261397612889)
    ·
      refine ⟨37295151285226696048209667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49726868380302261397612889 37295151285226696048209667)
      ·
        refine ⟨55942726927840044072314501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37295151285226696048209667 55942726927840044072314501)
        ·
          refine ⟨10489261298970008263558969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55942726927840044072314501 10489261298970008263558969)
          ·
            refine ⟨7866945974227506197669227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10489261298970008263558969 7866945974227506197669227)
            ·
              refine ⟨11800418961341259296503841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866945974227506197669227 11800418961341259296503841)
              ·
                refine ⟨8850314221005944472377881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11800418961341259296503841 8850314221005944472377881)
                ·
                  refine ⟨6637735665754458354283411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8850314221005944472377881 6637735665754458354283411)
                  ·
                    refine ⟨9956603498631687531425117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637735665754458354283411 9956603498631687531425117)
                    ·
                      refine ⟨3733726311986882824284419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956603498631687531425117 3733726311986882824284419)
                      ·
                        rfl

theorem cell23_7271406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_7271406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271406 prefixEnd_7271406 := by exact prefixLift 7271406
  have htrace : WordTrace (prefixWord ++ tailWord_7271406) baseStart_7271406 baseEnd_7271406 := by
    simpa [prefixWord, tailWord_7271406, baseEnd_7271406] using wordTrace_append hprefix tailTrace_7271406
  have hstable : (prefixWord ++ tailWord_7271406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271406).length < 2 ^ (prefixWord ++ tailWord_7271406).sum := by decide
  have hdescent : baseEnd_7271406 < baseStart_7271406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271425 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7271425 : Nat := 118140960795 + 7271425 * 2 ^ 59
def prefixEnd_7271425 : Nat := 4983230072969 + 3 ^ 40 * 7271425 * 2
def baseEnd_7271425 : Nat := 3733736068119318249946831

theorem tailTrace_7271425 : CollatzResearch.WordTrace tailWord_7271425 prefixEnd_7271425 3733736068119318249946831 := by
  unfold tailWord_7271425
  simp only [CollatzResearch.WordTrace]
  refine ⟨265210657681876560365543729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176807105121251040243695819 265210657681876560365543729)
  ·
    refine ⟨198907993261407420274157797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265210657681876560365543729 198907993261407420274157797)
    ·
      refine ⟨37295248736513891301404587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198907993261407420274157797 37295248736513891301404587)
      ·
        refine ⟨55942873104770836952106881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37295248736513891301404587 55942873104770836952106881)
        ·
          refine ⟨41957154828578127714080161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55942873104770836952106881 41957154828578127714080161)
          ·
            refine ⟨31467866121433595785560121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41957154828578127714080161 31467866121433595785560121)
            ·
              refine ⟨23600899591075196839170091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31467866121433595785560121 23600899591075196839170091)
              ·
                refine ⟨35401349386612795258755137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23600899591075196839170091 35401349386612795258755137)
                ·
                  refine ⟨26551012039959596444066353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35401349386612795258755137 26551012039959596444066353)
                  ·
                    refine ⟨19913259029969697333049765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26551012039959596444066353 19913259029969697333049765)
                    ·
                      refine ⟨3733736068119318249946831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19913259029969697333049765 3733736068119318249946831)
                      ·
                        rfl

theorem cell23_7271425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7271425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271425 prefixEnd_7271425 := by exact prefixLift 7271425
  have htrace : WordTrace (prefixWord ++ tailWord_7271425) baseStart_7271425 baseEnd_7271425 := by
    simpa [prefixWord, tailWord_7271425, baseEnd_7271425] using wordTrace_append hprefix tailTrace_7271425
  have hstable : (prefixWord ++ tailWord_7271425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271425).length < 2 ^ (prefixWord ++ tailWord_7271425).sum := by decide
  have hdescent : baseEnd_7271425 < baseStart_7271425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271502 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_7271502 : Nat := 118140960795 + 7271502 * 2 ^ 59
def prefixEnd_7271502 : Nat := 4983230072969 + 3 ^ 40 * 7271502 * 2
def baseEnd_7271502 : Nat := 3733775606129714448683977

theorem tailTrace_7271502 : CollatzResearch.WordTrace tailWord_7271502 prefixEnd_7271502 3733775606129714448683977 := by
  unfold tailWord_7271502
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151683262824700314512095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176808977401731735010731173 33151683262824700314512095)
  ·
    refine ⟨49727524894237050471768143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33151683262824700314512095 49727524894237050471768143)
    ·
      refine ⟨74591287341355575707652215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49727524894237050471768143 74591287341355575707652215)
      ·
        refine ⟨111886931012033363561478323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74591287341355575707652215 111886931012033363561478323)
        ·
          refine ⟨167830396518050045342217485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111886931012033363561478323 167830396518050045342217485)
          ·
            refine ⟨62936398694268767003331557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167830396518050045342217485 62936398694268767003331557)
            ·
              refine ⟨11800574755175393813124667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62936398694268767003331557 11800574755175393813124667)
              ·
                refine ⟨17700862132763090719687001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800574755175393813124667 17700862132763090719687001)
                ·
                  refine ⟨13275646599572318039765251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17700862132763090719687001 13275646599572318039765251)
                  ·
                    refine ⟨19913469899358477059647877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13275646599572318039765251 19913469899358477059647877)
                    ·
                      refine ⟨3733775606129714448683977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19913469899358477059647877 3733775606129714448683977)
                      ·
                        rfl

theorem cell23_7271502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_7271502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271502 prefixEnd_7271502 := by exact prefixLift 7271502
  have htrace : WordTrace (prefixWord ++ tailWord_7271502) baseStart_7271502 baseEnd_7271502 := by
    simpa [prefixWord, tailWord_7271502, baseEnd_7271502] using wordTrace_append hprefix tailTrace_7271502
  have hstable : (prefixWord ++ tailWord_7271502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271502).length < 2 ^ (prefixWord ++ tailWord_7271502).sum := by decide
  have hdescent : baseEnd_7271502 < baseStart_7271502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271505 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_7271505 : Nat := 118140960795 + 7271505 * 2 ^ 59
def prefixEnd_7271505 : Nat := 4983230072969 + 3 ^ 40 * 7271505 * 2
def baseEnd_7271505 : Nat := 3733777146571677936946463

theorem tailTrace_7271505 : CollatzResearch.WordTrace tailWord_7271505 prefixEnd_7271505 3733777146571677936946463 := by
  unfold tailWord_7271505
  simp only [CollatzResearch.WordTrace]
  refine ⟨265213575521586734028455969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176809050347724489352303979 265213575521586734028455969)
  ·
    refine ⟨198910181641190050521341977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265213575521586734028455969 198910181641190050521341977)
    ·
      refine ⟨149182636230892537891006483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198910181641190050521341977 149182636230892537891006483)
      ·
        refine ⟨223773954346338806836509725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149182636230892537891006483 223773954346338806836509725)
        ·
          refine ⟨83915232879877052563691147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223773954346338806836509725 83915232879877052563691147)
          ·
            refine ⟨125872849319815578845536721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83915232879877052563691147 125872849319815578845536721)
            ·
              refine ⟨94404636989861684134152541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125872849319815578845536721 94404636989861684134152541)
              ·
                refine ⟨35401738871198131550307203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94404636989861684134152541 35401738871198131550307203)
                ·
                  refine ⟨53102608306797197325460805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35401738871198131550307203 53102608306797197325460805)
                  ·
                    refine ⟨9956739057524474498523901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53102608306797197325460805 9956739057524474498523901)
                    ·
                      refine ⟨3733777146571677936946463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956739057524474498523901 3733777146571677936946463)
                      ·
                        rfl

theorem cell23_7271505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_7271505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271505 prefixEnd_7271505 := by exact prefixLift 7271505
  have htrace : WordTrace (prefixWord ++ tailWord_7271505) baseStart_7271505 baseEnd_7271505 := by
    simpa [prefixWord, tailWord_7271505, baseEnd_7271505] using wordTrace_append hprefix tailTrace_7271505
  have hstable : (prefixWord ++ tailWord_7271505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271505).length < 2 ^ (prefixWord ++ tailWord_7271505).sum := by decide
  have hdescent : baseEnd_7271505 < baseStart_7271505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271529 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 1, 4]
def baseStart_7271529 : Nat := 118140960795 + 7271529 * 2 ^ 59
def prefixEnd_7271529 : Nat := 4983230072969 + 3 ^ 40 * 7271529 * 2
def baseEnd_7271529 : Nat := 1244596490035795281015451

theorem tailTrace_7271529 : CollatzResearch.WordTrace tailWord_7271529 prefixEnd_7271529 1244596490035795281015451 := by
  unfold tailWord_7271529
  simp only [CollatzResearch.WordTrace]
  refine ⟨265214450873499786127329641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176809633915666524084886427 265214450873499786127329641)
  ·
    refine ⟨198910838155124839595497231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265214450873499786127329641 198910838155124839595497231)
    ·
      refine ⟨298366257232687259393245847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198910838155124839595497231 298366257232687259393245847)
      ·
        refine ⟨447549385849030889089868771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298366257232687259393245847 447549385849030889089868771)
        ·
          refine ⟨671324078773546333634803157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447549385849030889089868771 671324078773546333634803157)
          ·
            refine ⟨15734158096254992194565699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 671324078773546333634803157 15734158096254992194565699)
            ·
              refine ⟨23601237144382488291848549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15734158096254992194565699 23601237144382488291848549)
              ·
                refine ⟨4425231964571716554721603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23601237144382488291848549 4425231964571716554721603)
                ·
                  refine ⟨6637847946857574832082405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425231964571716554721603 6637847946857574832082405)
                  ·
                    refine ⟨1244596490035795281015451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637847946857574832082405 1244596490035795281015451)
                    ·
                      rfl

theorem cell23_7271529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 4].length) (baseStart_7271529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271529 prefixEnd_7271529 := by exact prefixLift 7271529
  have htrace : WordTrace (prefixWord ++ tailWord_7271529) baseStart_7271529 baseEnd_7271529 := by
    simpa [prefixWord, tailWord_7271529, baseEnd_7271529] using wordTrace_append hprefix tailTrace_7271529
  have hstable : (prefixWord ++ tailWord_7271529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271529).length < 2 ^ (prefixWord ++ tailWord_7271529).sum := by decide
  have hdescent : baseEnd_7271529 < baseStart_7271529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271542 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_7271542 : Nat := 118140960795 + 7271542 * 2 ^ 59
def prefixEnd_7271542 : Nat := 4983230072969 + 3 ^ 40 * 7271542 * 2
def baseEnd_7271542 : Nat := 414866238372877143575977

theorem tailTrace_7271542 : CollatzResearch.WordTrace tailWord_7271542 prefixEnd_7271542 414866238372877143575977 := by
  unfold tailWord_7271542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575932813903293084222055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176809950014968459565035253 16575932813903293084222055)
  ·
    refine ⟨24863899220854939626333083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16575932813903293084222055 24863899220854939626333083)
    ·
      refine ⟨37295848831282409439499625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24863899220854939626333083 37295848831282409439499625)
      ·
        refine ⟨27971886623461807079624719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37295848831282409439499625 27971886623461807079624719)
        ·
          refine ⟨41957829935192710619437079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27971886623461807079624719 41957829935192710619437079)
          ·
            refine ⟨62936744902789065929155619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41957829935192710619437079 62936744902789065929155619)
            ·
              refine ⟨94405117354183598893733429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62936744902789065929155619 94405117354183598893733429)
              ·
                refine ⟨8850479751954712396287509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94405117354183598893733429 8850479751954712396287509)
                ·
                  refine ⟨414866238372877143575977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8850479751954712396287509 414866238372877143575977)
                  ·
                    rfl

theorem cell23_7271542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_7271542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271542 prefixEnd_7271542 := by exact prefixLift 7271542
  have htrace : WordTrace (prefixWord ++ tailWord_7271542) baseStart_7271542 baseEnd_7271542 := by
    simpa [prefixWord, tailWord_7271542, baseEnd_7271542] using wordTrace_append hprefix tailTrace_7271542
  have hstable : (prefixWord ++ tailWord_7271542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271542).length < 2 ^ (prefixWord ++ tailWord_7271542).sum := by decide
  have hdescent : baseEnd_7271542 < baseStart_7271542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271550 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7271550 : Nat := 118140960795 + 7271550 * 2 ^ 59
def prefixEnd_7271550 : Nat := 4983230072969 + 3 ^ 40 * 7271550 * 2
def baseEnd_7271550 : Nat := 1244600084400376753627919

theorem tailTrace_7271550 : CollatzResearch.WordTrace tailWord_7271550 prefixEnd_7271550 1244600084400376753627919 := by
  unfold tailWord_7271550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151902100802963339230513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176810144537615804475896069 33151902100802963339230513)
  ·
    refine ⟨24863926575602222504422885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33151902100802963339230513 24863926575602222504422885)
    ·
      refine ⟨4661986232925416719579291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24863926575602222504422885 4661986232925416719579291)
      ·
        refine ⟨6992979349388125079368937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661986232925416719579291 6992979349388125079368937)
        ·
          refine ⟨5244734512041093809526703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992979349388125079368937 5244734512041093809526703)
          ·
            refine ⟨7867101768061640714290055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244734512041093809526703 7867101768061640714290055)
            ·
              refine ⟨11800652652092461071435083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867101768061640714290055 11800652652092461071435083)
              ·
                refine ⟨17700978978138691607152625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800652652092461071435083 17700978978138691607152625)
                ·
                  refine ⟨13275734233604018705364469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17700978978138691607152625 13275734233604018705364469)
                  ·
                    refine ⟨1244600084400376753627919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13275734233604018705364469 1244600084400376753627919)
                    ·
                      rfl

theorem cell23_7271550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7271550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271550 prefixEnd_7271550 := by exact prefixLift 7271550
  have htrace : WordTrace (prefixWord ++ tailWord_7271550) baseStart_7271550 baseEnd_7271550 := by
    simpa [prefixWord, tailWord_7271550, baseEnd_7271550] using wordTrace_append hprefix tailTrace_7271550
  have hstable : (prefixWord ++ tailWord_7271550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271550).length < 2 ^ (prefixWord ++ tailWord_7271550).sum := by decide
  have hdescent : baseEnd_7271550 < baseStart_7271550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271552 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3]
def baseStart_7271552 : Nat := 118140960795 + 7271552 * 2 ^ 59
def prefixEnd_7271552 : Nat := 4983230072969 + 3 ^ 40 * 7271552 * 2
def baseEnd_7271552 : Nat := 3733801280162439253058747

theorem tailTrace_7271552 : CollatzResearch.WordTrace tailWord_7271552 prefixEnd_7271552 3733801280162439253058747 := by
  unfold tailWord_7271552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132607644876208230527708455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176810193168277640703611273 132607644876208230527708455)
  ·
    refine ⟨198911467314312345791562683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132607644876208230527708455 198911467314312345791562683)
    ·
      refine ⟨298367200971468518687344025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198911467314312345791562683 298367200971468518687344025)
      ·
        refine ⟨223775400728601389015508019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298367200971468518687344025 223775400728601389015508019)
        ·
          refine ⟨335663101092902083523262029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223775400728601389015508019 335663101092902083523262029)
          ·
            refine ⟨125873662909838281321223261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335663101092902083523262029 125873662909838281321223261)
            ·
              refine ⟨47202623591189355495458723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125873662909838281321223261 47202623591189355495458723)
              ·
                refine ⟨70803935386784033243188085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47202623591189355495458723 70803935386784033243188085)
                ·
                  refine ⟨6637868942511003116548883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70803935386784033243188085 6637868942511003116548883)
                  ·
                    refine ⟨9956803413766504674823325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637868942511003116548883 9956803413766504674823325)
                    ·
                      refine ⟨3733801280162439253058747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956803413766504674823325 3733801280162439253058747)
                      ·
                        rfl

theorem cell23_7271552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_7271552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271552 prefixEnd_7271552 := by exact prefixLift 7271552
  have htrace : WordTrace (prefixWord ++ tailWord_7271552) baseStart_7271552 baseEnd_7271552 := by
    simpa [prefixWord, tailWord_7271552, baseEnd_7271552] using wordTrace_append hprefix tailTrace_7271552
  have hstable : (prefixWord ++ tailWord_7271552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271552).length < 2 ^ (prefixWord ++ tailWord_7271552).sum := by decide
  have hdescent : baseEnd_7271552 < baseStart_7271552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271555 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 3, 5]
def baseStart_7271555 : Nat := 118140960795 + 7271555 * 2 ^ 59
def prefixEnd_7271555 : Nat := 4983230072969 + 3 ^ 40 * 7271555 * 2
def baseEnd_7271555 : Nat := 1244600940201467580440411

theorem tailTrace_7271555 : CollatzResearch.WordTrace tailWord_7271555 prefixEnd_7271555 1244600940201467580440411 := by
  unfold tailWord_7271555
  simp only [CollatzResearch.WordTrace]
  refine ⟨265215399171405592567776119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176810266114270395045184079 265215399171405592567776119)
  ·
    refine ⟨397823098757108388851664179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265215399171405592567776119 397823098757108388851664179)
    ·
      refine ⟨596734648135662583277496269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397823098757108388851664179 596734648135662583277496269)
      ·
        refine ⟨223775493050873468729061101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596734648135662583277496269 223775493050873468729061101)
        ·
          refine ⟨83915809894077550773397913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223775493050873468729061101 83915809894077550773397913)
          ·
            refine ⟨62936857420558163080048435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83915809894077550773397913 62936857420558163080048435)
            ·
              refine ⟨94405286130837244620072653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62936857420558163080048435 94405286130837244620072653)
              ·
                refine ⟨35401982299063966732527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94405286130837244620072653 35401982299063966732527245)
                ·
                  refine ⟨13275743362148987524697717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35401982299063966732527245 13275743362148987524697717)
                  ·
                    refine ⟨1244600940201467580440411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13275743362148987524697717 1244600940201467580440411)
                    ·
                      rfl

theorem cell23_7271555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 5].length) (baseStart_7271555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271555 prefixEnd_7271555 := by exact prefixLift 7271555
  have htrace : WordTrace (prefixWord ++ tailWord_7271555) baseStart_7271555 baseEnd_7271555 := by
    simpa [prefixWord, tailWord_7271555, baseEnd_7271555] using wordTrace_append hprefix tailTrace_7271555
  have hstable : (prefixWord ++ tailWord_7271555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271555).length < 2 ^ (prefixWord ++ tailWord_7271555).sum := by decide
  have hdescent : baseEnd_7271555 < baseStart_7271555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271602 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_7271602 : Nat := 118140960795 + 7271602 * 2 ^ 59
def prefixEnd_7271602 : Nat := 4983230072969 + 3 ^ 40 * 7271602 * 2
def baseEnd_7271602 : Nat := 1244608984731721352477839

theorem tailTrace_7271602 : CollatzResearch.WordTrace tailWord_7271602 prefixEnd_7271602 1244608984731721352477839 := by
  unfold tailWord_7271602
  simp only [CollatzResearch.WordTrace]
  refine ⟨66304278350558829898684265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176811408934823546396491373 66304278350558829898684265)
  ·
    refine ⟨49728208762919122424013199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66304278350558829898684265 49728208762919122424013199)
    ·
      refine ⟨74592313144378683636019799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49728208762919122424013199 74592313144378683636019799)
      ·
        refine ⟨111888469716568025454029699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74592313144378683636019799 111888469716568025454029699)
        ·
          refine ⟨167832704574852038181044549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111888469716568025454029699 167832704574852038181044549)
          ·
            refine ⟨31468632107784757158945853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167832704574852038181044549 31468632107784757158945853)
            ·
              refine ⟨11800737040419283934604695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31468632107784757158945853 11800737040419283934604695)
              ·
                refine ⟨17701105560628925901907043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800737040419283934604695 17701105560628925901907043)
                ·
                  refine ⟨26551658340943388852860565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17701105560628925901907043 26551658340943388852860565)
                  ·
                    refine ⟨1244608984731721352477839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26551658340943388852860565 1244608984731721352477839)
                    ·
                      rfl

theorem cell23_7271602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_7271602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271602 prefixEnd_7271602 := by exact prefixLift 7271602
  have htrace : WordTrace (prefixWord ++ tailWord_7271602) baseStart_7271602 baseEnd_7271602 := by
    simpa [prefixWord, tailWord_7271602, baseEnd_7271602] using wordTrace_append hprefix tailTrace_7271602
  have hstable : (prefixWord ++ tailWord_7271602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271602).length < 2 ^ (prefixWord ++ tailWord_7271602).sum := by decide
  have hdescent : baseEnd_7271602 < baseStart_7271602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271609 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7271609 : Nat := 118140960795 + 7271609 * 2 ^ 59
def prefixEnd_7271609 : Nat := 4983230072969 + 3 ^ 40 * 7271609 * 2
def baseEnd_7271609 : Nat := 3733830548559745530045985

theorem tailTrace_7271609 : CollatzResearch.WordTrace tailWord_7271609 prefixEnd_7271609 3733830548559745530045985 := by
  unfold tailWord_7271609
  simp only [CollatzResearch.WordTrace]
  refine ⟨265217368713209959790241881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176811579142139973193494587 265217368713209959790241881)
  ·
    refine ⟨198913026534907469842681411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265217368713209959790241881 198913026534907469842681411)
    ·
      refine ⟨298369539802361204764022117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198913026534907469842681411 298369539802361204764022117)
      ·
        refine ⟨55944288712942725893254147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298369539802361204764022117 55944288712942725893254147)
        ·
          refine ⟨83916433069414088839881221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55944288712942725893254147 83916433069414088839881221)
          ·
            refine ⟨15734331200515141657477729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83916433069414088839881221 15734331200515141657477729)
            ·
              refine ⟨11800748400386356243108297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15734331200515141657477729 11800748400386356243108297)
              ·
                refine ⟨8850561300289767182331223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11800748400386356243108297 8850561300289767182331223)
                ·
                  refine ⟨13275841950434650773496835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850561300289767182331223 13275841950434650773496835)
                  ·
                    refine ⟨19913762925651976160245253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13275841950434650773496835 19913762925651976160245253)
                    ·
                      refine ⟨3733830548559745530045985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19913762925651976160245253 3733830548559745530045985)
                      ·
                        rfl

theorem cell23_7271609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7271609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271609 prefixEnd_7271609 := by exact prefixLift 7271609
  have htrace : WordTrace (prefixWord ++ tailWord_7271609) baseStart_7271609 baseEnd_7271609 := by
    simpa [prefixWord, tailWord_7271609, baseEnd_7271609] using wordTrace_append hprefix tailTrace_7271609
  have hstable : (prefixWord ++ tailWord_7271609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271609).length < 2 ^ (prefixWord ++ tailWord_7271609).sum := by decide
  have hdescent : baseEnd_7271609 < baseStart_7271609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271620 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_7271620 : Nat := 118140960795 + 7271620 * 2 ^ 59
def prefixEnd_7271620 : Nat := 4983230072969 + 3 ^ 40 * 7271620 * 2
def baseEnd_7271620 : Nat := 3733836196846944987008435

theorem tailTrace_7271620 : CollatzResearch.WordTrace tailWord_7271620 prefixEnd_7271620 3733836196846944987008435 := by
  unfold tailWord_7271620
  simp only [CollatzResearch.WordTrace]
  refine ⟨132608884958085054334446157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176811846610780072445928209 132608884958085054334446157)
  ·
    refine ⟨49728331859281895375417309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132608884958085054334446157 49728331859281895375417309)
    ·
      refine ⟨18648124447230710765781491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49728331859281895375417309 18648124447230710765781491)
      ·
        refine ⟨27972186670846066148672237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18648124447230710765781491 27972186670846066148672237)
        ·
          refine ⟨10489570001567274805752089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27972186670846066148672237 10489570001567274805752089)
          ·
            refine ⟨7867177501175456104314067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10489570001567274805752089 7867177501175456104314067)
            ·
              refine ⟨11800766251763184156471101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867177501175456104314067 11800766251763184156471101)
              ·
                refine ⟨4425287344411194058676663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11800766251763184156471101 4425287344411194058676663)
                ·
                  refine ⟨6637931016616791088014995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425287344411194058676663 6637931016616791088014995)
                  ·
                    refine ⟨9956896524925186632022493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6637931016616791088014995 9956896524925186632022493)
                    ·
                      refine ⟨3733836196846944987008435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956896524925186632022493 3733836196846944987008435)
                      ·
                        rfl

theorem cell23_7271620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_7271620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271620 prefixEnd_7271620 := by exact prefixLift 7271620
  have htrace : WordTrace (prefixWord ++ tailWord_7271620) baseStart_7271620 baseEnd_7271620 := by
    simpa [prefixWord, tailWord_7271620, baseEnd_7271620] using wordTrace_append hprefix tailTrace_7271620
  have hstable : (prefixWord ++ tailWord_7271620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271620).length < 2 ^ (prefixWord ++ tailWord_7271620).sum := by decide
  have hdescent : baseEnd_7271620 < baseStart_7271620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271653 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_7271653 : Nat := 118140960795 + 7271653 * 2 ^ 59
def prefixEnd_7271653 : Nat := 4983230072969 + 3 ^ 40 * 7271653 * 2
def baseEnd_7271653 : Nat := 1244617713902847785965261

theorem tailTrace_7271653 : CollatzResearch.WordTrace tailWord_7271653 prefixEnd_7271653 1244617713902847785965261 := by
  unfold tailWord_7271653
  simp only [CollatzResearch.WordTrace]
  refine ⟨265218973525050555304843613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176812649016700370203229075 265218973525050555304843613)
  ·
    refine ⟨99457115071893958239316355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265218973525050555304843613 99457115071893958239316355)
    ·
      refine ⟨149185672607840937358974533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99457115071893958239316355 149185672607840937358974533)
      ·
        refine ⟨27972313613970175754807725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149185672607840937358974533 27972313613970175754807725)
        ·
          refine ⟨10489617605238815908052897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27972313613970175754807725 10489617605238815908052897)
          ·
            refine ⟨7867213203929111931039673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10489617605238815908052897 7867213203929111931039673)
            ·
              refine ⟨5900409902946833948279755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7867213203929111931039673 5900409902946833948279755)
              ·
                refine ⟨8850614854420250922419633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900409902946833948279755 8850614854420250922419633)
                ·
                  refine ⟨6637961140815188191814725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8850614854420250922419633 6637961140815188191814725)
                  ·
                    refine ⟨1244617713902847785965261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6637961140815188191814725 1244617713902847785965261)
                    ·
                      rfl

theorem cell23_7271653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_7271653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271653 prefixEnd_7271653 := by exact prefixLift 7271653
  have htrace : WordTrace (prefixWord ++ tailWord_7271653) baseStart_7271653 baseEnd_7271653 := by
    simpa [prefixWord, tailWord_7271653, baseEnd_7271653] using wordTrace_append hprefix tailTrace_7271653
  have hstable : (prefixWord ++ tailWord_7271653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271653).length < 2 ^ (prefixWord ++ tailWord_7271653).sum := by decide
  have hdescent : baseEnd_7271653 < baseStart_7271653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271663 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 1, 2, 3]
def baseStart_7271663 : Nat := 118140960795 + 7271663 * 2 ^ 59
def prefixEnd_7271663 : Nat := 4983230072969 + 3 ^ 40 * 7271663 * 2
def baseEnd_7271663 : Nat := 3733858276515088318770737

theorem tailTrace_7271663 : CollatzResearch.WordTrace tailWord_7271663 prefixEnd_7271663 3733858276515088318770737 := by
  unfold tailWord_7271663
  simp only [CollatzResearch.WordTrace]
  refine ⟨265219338255014327012707643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176812892170009551341805095 265219338255014327012707643)
  ·
    refine ⟨397829007382521490519061465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265219338255014327012707643 397829007382521490519061465)
    ·
      refine ⟨298371755536891117889296099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397829007382521490519061465 298371755536891117889296099)
      ·
        refine ⟨447557633305336676833944149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298371755536891117889296099 447557633305336676833944149)
        ·
          refine ⟨5244816015296914181647783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 447557633305336676833944149 5244816015296914181647783)
          ·
            refine ⟨7867224022945371272471675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244816015296914181647783 7867224022945371272471675)
            ·
              refine ⟨11800836034418056908707513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867224022945371272471675 11800836034418056908707513)
              ·
                refine ⟨8850627025813542681530635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11800836034418056908707513 8850627025813542681530635)
                ·
                  refine ⟨13275940538720314022295953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850627025813542681530635 13275940538720314022295953)
                  ·
                    refine ⟨9956955404040235516721965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13275940538720314022295953 9956955404040235516721965)
                    ·
                      refine ⟨3733858276515088318770737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9956955404040235516721965 3733858276515088318770737)
                      ·
                        rfl

theorem cell23_7271663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 1, 2, 3].length) (baseStart_7271663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271663 prefixEnd_7271663 := by exact prefixLift 7271663
  have htrace : WordTrace (prefixWord ++ tailWord_7271663) baseStart_7271663 baseEnd_7271663 := by
    simpa [prefixWord, tailWord_7271663, baseEnd_7271663] using wordTrace_append hprefix tailTrace_7271663
  have hstable : (prefixWord ++ tailWord_7271663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271663).length < 2 ^ (prefixWord ++ tailWord_7271663).sum := by decide
  have hdescent : baseEnd_7271663 < baseStart_7271663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271665 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_7271665 : Nat := 118140960795 + 7271665 * 2 ^ 59
def prefixEnd_7271665 : Nat := 4983230072969 + 3 ^ 40 * 7271665 * 2
def baseEnd_7271665 : Nat := 3733859303476397310945727

theorem tailTrace_7271665 : CollatzResearch.WordTrace tailWord_7271665 prefixEnd_7271665 3733859303476397310945727 := by
  unfold tailWord_7271665
  simp only [CollatzResearch.WordTrace]
  refine ⟨265219411201007081354280449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176812940800671387569520299 265219411201007081354280449)
  ·
    refine ⟨198914558400755311015710337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265219411201007081354280449 198914558400755311015710337)
    ·
      refine ⟨149185918800566483261782753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198914558400755311015710337 149185918800566483261782753)
      ·
        refine ⟨111889439100424862446337065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149185918800566483261782753 111889439100424862446337065)
        ·
          refine ⟨83917079325318646834752799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111889439100424862446337065 83917079325318646834752799)
          ·
            refine ⟨125875618987977970252129199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83917079325318646834752799 125875618987977970252129199)
            ·
              refine ⟨188813428481966955378193799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125875618987977970252129199 188813428481966955378193799)
              ·
                refine ⟨283220142722950433067290699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188813428481966955378193799 283220142722950433067290699)
                ·
                  refine ⟨424830214084425649600936049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283220142722950433067290699 424830214084425649600936049)
                  ·
                    refine ⟨318622660563319237200702037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424830214084425649600936049 318622660563319237200702037)
                    ·
                      refine ⟨3733859303476397310945727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 318622660563319237200702037 3733859303476397310945727)
                      ·
                        rfl

theorem cell23_7271665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_7271665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271665 prefixEnd_7271665 := by exact prefixLift 7271665
  have htrace : WordTrace (prefixWord ++ tailWord_7271665) baseStart_7271665 baseEnd_7271665 := by
    simpa [prefixWord, tailWord_7271665, baseEnd_7271665] using wordTrace_append hprefix tailTrace_7271665
  have hstable : (prefixWord ++ tailWord_7271665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271665).length < 2 ^ (prefixWord ++ tailWord_7271665).sum := by decide
  have hdescent : baseEnd_7271665 < baseStart_7271665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271695 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_7271695 : Nat := 118140960795 + 7271695 * 2 ^ 59
def prefixEnd_7271695 : Nat := 4983230072969 + 3 ^ 40 * 7271695 * 2
def baseEnd_7271695 : Nat := 3733874707896032193570589

theorem tailTrace_7271695 : CollatzResearch.WordTrace tailWord_7271695 prefixEnd_7271695 3733874707896032193570589 := by
  unfold tailWord_7271695
  simp only [CollatzResearch.WordTrace]
  refine ⟨265220505390898396477872539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176813670260598930985248359 265220505390898396477872539)
  ·
    refine ⟨397830758086347594716808809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265220505390898396477872539 397830758086347594716808809)
    ·
      refine ⟨298373068564760696037606607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397830758086347594716808809 298373068564760696037606607)
      ·
        refine ⟨447559602847141044056409911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298373068564760696037606607 447559602847141044056409911)
        ·
          refine ⟨671339404270711566084614867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447559602847141044056409911 671339404270711566084614867)
          ·
            refine ⟨1007009106406067349126922301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671339404270711566084614867 1007009106406067349126922301)
            ·
              refine ⟨377628414902275255922595863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1007009106406067349126922301 377628414902275255922595863)
              ·
                refine ⟨566442622353412883883893795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377628414902275255922595863 566442622353412883883893795)
                ·
                  refine ⟨849663933530119325825840693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566442622353412883883893795 849663933530119325825840693)
                  ·
                    refine ⟨79655993768448686796172565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 849663933530119325825840693 79655993768448686796172565)
                    ·
                      refine ⟨3733874707896032193570589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79655993768448686796172565 3733874707896032193570589)
                      ·
                        rfl

theorem cell23_7271695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_7271695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271695 prefixEnd_7271695 := by exact prefixLift 7271695
  have htrace : WordTrace (prefixWord ++ tailWord_7271695) baseStart_7271695 baseEnd_7271695 := by
    simpa [prefixWord, tailWord_7271695, baseEnd_7271695] using wordTrace_append hprefix tailTrace_7271695
  have hstable : (prefixWord ++ tailWord_7271695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271695).length < 2 ^ (prefixWord ++ tailWord_7271695).sum := by decide
  have hdescent : baseEnd_7271695 < baseStart_7271695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271705 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 13]
def baseStart_7271705 : Nat := 118140960795 + 7271705 * 2 ^ 59
def prefixEnd_7271705 : Nat := 4983230072969 + 3 ^ 40 * 7271705 * 2
def baseEnd_7271705 : Nat := 414875538078064128271727

theorem tailTrace_7271705 : CollatzResearch.WordTrace tailWord_7271705 prefixEnd_7271705 414875538078064128271727 := by
  unfold tailWord_7271705
  simp only [CollatzResearch.WordTrace]
  refine ⟨265220870120862168185736569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176813913413908112123824379 265220870120862168185736569)
  ·
    refine ⟨198915652590646626139302427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265220870120862168185736569 198915652590646626139302427)
    ·
      refine ⟨298373478885969939208953641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198915652590646626139302427 298373478885969939208953641)
      ·
        refine ⟨223780109164477454406715231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298373478885969939208953641 223780109164477454406715231)
        ·
          refine ⟨335670163746716181610072847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223780109164477454406715231 335670163746716181610072847)
          ·
            refine ⟨503505245620074272415109271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335670163746716181610072847 503505245620074272415109271)
            ·
              refine ⟨755257868430111408622663907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503505245620074272415109271 755257868430111408622663907)
              ·
                refine ⟨1132886802645167112933995861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755257868430111408622663907 1132886802645167112933995861)
                ·
                  refine ⟨414875538078064128271727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1132886802645167112933995861 414875538078064128271727)
                  ·
                    rfl

theorem cell23_7271705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_7271705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271705 prefixEnd_7271705 := by exact prefixLift 7271705
  have htrace : WordTrace (prefixWord ++ tailWord_7271705) baseStart_7271705 baseEnd_7271705 := by
    simpa [prefixWord, tailWord_7271705, baseEnd_7271705] using wordTrace_append hprefix tailTrace_7271705
  have hstable : (prefixWord ++ tailWord_7271705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271705).length < 2 ^ (prefixWord ++ tailWord_7271705).sum := by decide
  have hdescent : baseEnd_7271705 < baseStart_7271705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271709 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7271709 : Nat := 118140960795 + 7271709 * 2 ^ 59
def prefixEnd_7271709 : Nat := 4983230072969 + 3 ^ 40 * 7271709 * 2
def baseEnd_7271709 : Nat := 1244627298875065046265175

theorem tailTrace_7271709 : CollatzResearch.WordTrace tailWord_7271709 prefixEnd_7271709 1244627298875065046265175 := by
  unfold tailWord_7271709
  simp only [CollatzResearch.WordTrace]
  refine ⟨265221016012847676868882181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176814010675231784579254787 265221016012847676868882181)
  ·
    refine ⟨49728940502408939412915409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265221016012847676868882181 49728940502408939412915409)
    ·
      refine ⟨37296705376806704559686557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49728940502408939412915409 37296705376806704559686557)
      ·
        refine ⟨13986264516302514209882459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37296705376806704559686557 13986264516302514209882459)
        ·
          refine ⟨20979396774453771314823689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13986264516302514209882459 20979396774453771314823689)
          ·
            refine ⟨15734547580840328486117767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20979396774453771314823689 15734547580840328486117767)
            ·
              refine ⟨23601821371260492729176651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15734547580840328486117767 23601821371260492729176651)
              ·
                refine ⟨35402732056890739093764977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23601821371260492729176651 35402732056890739093764977)
                ·
                  refine ⟨26552049042668054320323733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35402732056890739093764977 26552049042668054320323733)
                  ·
                    refine ⟨1244627298875065046265175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26552049042668054320323733 1244627298875065046265175)
                    ·
                      rfl

theorem cell23_7271709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7271709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271709 prefixEnd_7271709 := by exact prefixLift 7271709
  have htrace : WordTrace (prefixWord ++ tailWord_7271709) baseStart_7271709 baseEnd_7271709 := by
    simpa [prefixWord, tailWord_7271709, baseEnd_7271709] using wordTrace_append hprefix tailTrace_7271709
  have hstable : (prefixWord ++ tailWord_7271709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271709).length < 2 ^ (prefixWord ++ tailWord_7271709).sum := by decide
  have hdescent : baseEnd_7271709 < baseStart_7271709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271716 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_7271716 : Nat := 118140960795 + 7271716 * 2 ^ 59
def prefixEnd_7271716 : Nat := 4983230072969 + 3 ^ 40 * 7271716 * 2
def baseEnd_7271716 : Nat := 3733885490989776611407993

theorem tailTrace_7271716 : CollatzResearch.WordTrace tailWord_7271716 prefixEnd_7271716 3733885490989776611407993 := by
  unfold tailWord_7271716
  simp only [CollatzResearch.WordTrace]
  refine ⟨132610635661911158532193501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176814180882548211376258001 132610635661911158532193501)
  ·
    refine ⟨49728988373216684449572563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132610635661911158532193501 49728988373216684449572563)
    ·
      refine ⟨74593482559825026674358845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49728988373216684449572563 74593482559825026674358845)
      ·
        refine ⟨27972555959934385002884567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74593482559825026674358845 27972555959934385002884567)
        ·
          refine ⟨41958833939901577504326851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27972555959934385002884567 41958833939901577504326851)
          ·
            refine ⟨62938250909852366256490277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41958833939901577504326851 62938250909852366256490277)
            ·
              refine ⟨11800922045597318673091927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62938250909852366256490277 11800922045597318673091927)
              ·
                refine ⟨17701383068395978009637891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11800922045597318673091927 17701383068395978009637891)
                ·
                  refine ⟨26552074602593967014456837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17701383068395978009637891 26552074602593967014456837)
                  ·
                    refine ⟨4978513987986368815210657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26552074602593967014456837 4978513987986368815210657)
                    ·
                      refine ⟨3733885490989776611407993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978513987986368815210657 3733885490989776611407993)
                      ·
                        rfl

theorem cell23_7271716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_7271716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271716 prefixEnd_7271716 := by exact prefixLift 7271716
  have htrace : WordTrace (prefixWord ++ tailWord_7271716) baseStart_7271716 baseEnd_7271716 := by
    simpa [prefixWord, tailWord_7271716, baseEnd_7271716] using wordTrace_append hprefix tailTrace_7271716
  have hstable : (prefixWord ++ tailWord_7271716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271716).length < 2 ^ (prefixWord ++ tailWord_7271716).sum := by decide
  have hdescent : baseEnd_7271716 < baseStart_7271716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271737 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7271737 : Nat := 118140960795 + 7271737 * 2 ^ 59
def prefixEnd_7271737 : Nat := 4983230072969 + 3 ^ 40 * 7271737 * 2
def baseEnd_7271737 : Nat := 3733896274083521029245397

theorem tailTrace_7271737 : CollatzResearch.WordTrace tailWord_7271737 prefixEnd_7271737 3733896274083521029245397 := by
  unfold tailWord_7271737
  simp only [CollatzResearch.WordTrace]
  refine ⟨265222037256746237650901465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176814691504497491767267643 265222037256746237650901465)
  ·
    refine ⟨198916527942559678238176099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265222037256746237650901465 198916527942559678238176099)
    ·
      refine ⟨298374791913839517357264149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198916527942559678238176099 298374791913839517357264149)
      ·
        refine ⟨13986318370961227376121757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 298374791913839517357264149 13986318370961227376121757)
        ·
          refine ⟨5244869389110460266045659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13986318370961227376121757 5244869389110460266045659)
          ·
            refine ⟨7867304083665690399068489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5244869389110460266045659 7867304083665690399068489)
            ·
              refine ⟨5900478062749267799301367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7867304083665690399068489 5900478062749267799301367)
              ·
                refine ⟨8850717094123901698952051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900478062749267799301367 8850717094123901698952051)
                ·
                  refine ⟨13276075641185852548428077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850717094123901698952051 13276075641185852548428077)
                  ·
                    refine ⟨4978528365444694705660529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13276075641185852548428077 4978528365444694705660529)
                    ·
                      refine ⟨3733896274083521029245397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978528365444694705660529 3733896274083521029245397)
                      ·
                        rfl

theorem cell23_7271737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7271737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271737 prefixEnd_7271737 := by exact prefixLift 7271737
  have htrace : WordTrace (prefixWord ++ tailWord_7271737) baseStart_7271737 baseEnd_7271737 := by
    simpa [prefixWord, tailWord_7271737, baseEnd_7271737] using wordTrace_append hprefix tailTrace_7271737
  have hstable : (prefixWord ++ tailWord_7271737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271737).length < 2 ^ (prefixWord ++ tailWord_7271737).sum := by decide
  have hdescent : baseEnd_7271737 < baseStart_7271737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271752 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_7271752 : Nat := 118140960795 + 7271752 * 2 ^ 59
def prefixEnd_7271752 : Nat := 4983230072969 + 3 ^ 40 * 7271752 * 2
def baseEnd_7271752 : Nat := 1244634658764446156852609

theorem tailTrace_7271752 : CollatzResearch.WordTrace tailWord_7271752 prefixEnd_7271752 1244634658764446156852609 := by
  unfold tailWord_7271752
  simp only [CollatzResearch.WordTrace]
  refine ⟨132611292175845947606348755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176815056234461263475131673 132611292175845947606348755)
  ·
    refine ⟨198916938263768921409523133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132611292175845947606348755 198916938263768921409523133)
    ·
      refine ⟨74593851848913345528571175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198916938263768921409523133 74593851848913345528571175)
      ·
        refine ⟨111890777773370018292856763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74593851848913345528571175 111890777773370018292856763)
        ·
          refine ⟨167836166660055027439285145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111890777773370018292856763 167836166660055027439285145)
          ·
            refine ⟨125877124995041270579463859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167836166660055027439285145 125877124995041270579463859)
            ·
              refine ⟨188815687492561905869195789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125877124995041270579463859 188815687492561905869195789)
              ·
                refine ⟨70805882809710714700948421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188815687492561905869195789 70805882809710714700948421)
                ·
                  refine ⟨13276103026820759006427829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70805882809710714700948421 13276103026820759006427829)
                  ·
                    refine ⟨1244634658764446156852609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13276103026820759006427829 1244634658764446156852609)
                    ·
                      rfl

theorem cell23_7271752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_7271752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271752 prefixEnd_7271752 := by exact prefixLift 7271752
  have htrace : WordTrace (prefixWord ++ tailWord_7271752) baseStart_7271752 baseEnd_7271752 := by
    simpa [prefixWord, tailWord_7271752, baseEnd_7271752] using wordTrace_append hprefix tailTrace_7271752
  have hstable : (prefixWord ++ tailWord_7271752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271752).length < 2 ^ (prefixWord ++ tailWord_7271752).sum := by decide
  have hdescent : baseEnd_7271752 < baseStart_7271752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271762 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7271762 : Nat := 118140960795 + 7271762 * 2 ^ 59
def prefixEnd_7271762 : Nat := 4983230072969 + 3 ^ 40 * 7271762 * 2
def baseEnd_7271762 : Nat := 3733909111099883431432781

theorem tailTrace_7271762 : CollatzResearch.WordTrace tailWord_7271762 prefixEnd_7271762 3733909111099883431432781 := by
  unfold tailWord_7271762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66305737270413916730140385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176815299387770444613707693 66305737270413916730140385)
  ·
    refine ⟨49729302952810437547605289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66305737270413916730140385 49729302952810437547605289)
    ·
      refine ⟨37296977214607828160703967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49729302952810437547605289 37296977214607828160703967)
      ·
        refine ⟨55945465821911742241055951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37296977214607828160703967 55945465821911742241055951)
        ·
          refine ⟨83918198732867613361583927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55945465821911742241055951 83918198732867613361583927)
          ·
            refine ⟨125877298099301420042375891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83918198732867613361583927 125877298099301420042375891)
            ·
              refine ⟨188815947148952130063563837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125877298099301420042375891 188815947148952130063563837)
              ·
                refine ⟨70805980180857048773836439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188815947148952130063563837 70805980180857048773836439)
                ·
                  refine ⟨106208970271285573160754659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70805980180857048773836439 106208970271285573160754659)
                  ·
                    refine ⟨159313455406928359741131989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106208970271285573160754659 159313455406928359741131989)
                    ·
                      refine ⟨3733909111099883431432781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159313455406928359741131989 3733909111099883431432781)
                      ·
                        rfl

theorem cell23_7271762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7271762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271762 prefixEnd_7271762 := by exact prefixLift 7271762
  have htrace : WordTrace (prefixWord ++ tailWord_7271762) baseStart_7271762 baseEnd_7271762 := by
    simpa [prefixWord, tailWord_7271762, baseEnd_7271762] using wordTrace_append hprefix tailTrace_7271762
  have hstable : (prefixWord ++ tailWord_7271762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271762).length < 2 ^ (prefixWord ++ tailWord_7271762).sum := by decide
  have hdescent : baseEnd_7271762 < baseStart_7271762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271789 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7271789 : Nat := 118140960795 + 7271789 * 2 ^ 59
def prefixEnd_7271789 : Nat := 4983230072969 + 3 ^ 40 * 7271789 * 2
def baseEnd_7271789 : Nat := 3733922975077554825795157

theorem tailTrace_7271789 : CollatzResearch.WordTrace tailWord_7271789 prefixEnd_7271789 3733922975077554825795157 := by
  unfold tailWord_7271789
  simp only [CollatzResearch.WordTrace]
  refine ⟨265223933852557850531794421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176815955901705233687862947 265223933852557850531794421)
  ·
    refine ⟨24864743798677298487355727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265223933852557850531794421 24864743798677298487355727)
    ·
      refine ⟨37297115698015947731033591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24864743798677298487355727 37297115698015947731033591)
      ·
        refine ⟨55945673547023921596550387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37297115698015947731033591 55945673547023921596550387)
        ·
          refine ⟨83918510320535882394825581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55945673547023921596550387 83918510320535882394825581)
          ·
            refine ⟨31469441370200955898059593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83918510320535882394825581 31469441370200955898059593)
            ·
              refine ⟨23602081027650716923544695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31469441370200955898059593 23602081027650716923544695)
              ·
                refine ⟨35403121541476075385317043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23602081027650716923544695 35403121541476075385317043)
                ·
                  refine ⟨53104682312214113077975565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35403121541476075385317043 53104682312214113077975565)
                  ·
                    refine ⟨19914255867080292404240837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53104682312214113077975565 19914255867080292404240837)
                    ·
                      refine ⟨3733922975077554825795157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19914255867080292404240837 3733922975077554825795157)
                      ·
                        rfl

theorem cell23_7271789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7271789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271789 prefixEnd_7271789 := by exact prefixLift 7271789
  have htrace : WordTrace (prefixWord ++ tailWord_7271789) baseStart_7271789 baseEnd_7271789 := by
    simpa [prefixWord, tailWord_7271789, baseEnd_7271789] using wordTrace_append hprefix tailTrace_7271789
  have hstable : (prefixWord ++ tailWord_7271789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271789).length < 2 ^ (prefixWord ++ tailWord_7271789).sum := by decide
  have hdescent : baseEnd_7271789 < baseStart_7271789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271790 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_7271790 : Nat := 118140960795 + 7271790 * 2 ^ 59
def prefixEnd_7271790 : Nat := 4983230072969 + 3 ^ 40 * 7271790 * 2
def baseEnd_7271790 : Nat := 414880387617578813542517

theorem tailTrace_7271790 : CollatzResearch.WordTrace tailWord_7271790 prefixEnd_7271790 414880387617578813542517 := by
  unfold tailWord_7271790
  simp only [CollatzResearch.WordTrace]
  refine ⟨33152996290694278462822603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176815980217036151801720549 33152996290694278462822603)
  ·
    refine ⟨49729494436041417694233905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33152996290694278462822603 49729494436041417694233905)
    ·
      refine ⟨37297120827031063270675429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49729494436041417694233905 37297120827031063270675429)
      ·
        refine ⟨6993210155068324363251643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37297120827031063270675429 6993210155068324363251643)
        ·
          refine ⟨10489815232602486544877465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993210155068324363251643 10489815232602486544877465)
          ·
            refine ⟨7867361424451864908658099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10489815232602486544877465 7867361424451864908658099)
            ·
              refine ⟨11801042136677797362987149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867361424451864908658099 11801042136677797362987149)
              ·
                refine ⟨4425390801254174011120181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11801042136677797362987149 4425390801254174011120181)
                ·
                  refine ⟨414880387617578813542517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4425390801254174011120181 414880387617578813542517)
                  ·
                    rfl

theorem cell23_7271790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_7271790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271790 prefixEnd_7271790 := by exact prefixLift 7271790
  have htrace : WordTrace (prefixWord ++ tailWord_7271790) baseStart_7271790 baseEnd_7271790 := by
    simpa [prefixWord, tailWord_7271790, baseEnd_7271790] using wordTrace_append hprefix tailTrace_7271790
  have hstable : (prefixWord ++ tailWord_7271790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271790).length < 2 ^ (prefixWord ++ tailWord_7271790).sum := by decide
  have hdescent : baseEnd_7271790 < baseStart_7271790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271802 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_7271802 : Nat := 118140960795 + 7271802 * 2 ^ 59
def prefixEnd_7271802 : Nat := 4983230072969 + 3 ^ 40 * 7271802 * 2
def baseEnd_7271802 : Nat := 3733929650326063274932597

theorem tailTrace_7271802 : CollatzResearch.WordTrace tailWord_7271802 prefixEnd_7271802 3733929650326063274932597 := by
  unfold tailWord_7271802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66306102000377688438004415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176816272001007169168011773 66306102000377688438004415)
  ·
    refine ⟨99459153000566532657006623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66306102000377688438004415 99459153000566532657006623)
    ·
      refine ⟨149188729500849798985509935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99459153000566532657006623 149188729500849798985509935)
      ·
        refine ⟨223783094251274698478264903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149188729500849798985509935 223783094251274698478264903)
        ·
          refine ⟨335674641376912047717397355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223783094251274698478264903 335674641376912047717397355)
          ·
            refine ⟨503511962065368071576096033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335674641376912047717397355 503511962065368071576096033)
            ·
              refine ⟨377633971549026053682072025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503511962065368071576096033 377633971549026053682072025)
              ·
                refine ⟨283225478661769540261554019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377633971549026053682072025 283225478661769540261554019)
                ·
                  refine ⟨424838217992654310392331029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283225478661769540261554019 424838217992654310392331029)
                  ·
                    refine ⟨19914291468405670799640517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 424838217992654310392331029 19914291468405670799640517)
                    ·
                      refine ⟨3733929650326063274932597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19914291468405670799640517 3733929650326063274932597)
                      ·
                        rfl

theorem cell23_7271802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_7271802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271802 prefixEnd_7271802 := by exact prefixLift 7271802
  have htrace : WordTrace (prefixWord ++ tailWord_7271802) baseStart_7271802 baseEnd_7271802 := by
    simpa [prefixWord, tailWord_7271802, baseEnd_7271802] using wordTrace_append hprefix tailTrace_7271802
  have hstable : (prefixWord ++ tailWord_7271802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271802).length < 2 ^ (prefixWord ++ tailWord_7271802).sum := by decide
  have hdescent : baseEnd_7271802 < baseStart_7271802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271816 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_7271816 : Nat := 118140960795 + 7271816 * 2 ^ 59
def prefixEnd_7271816 : Nat := 4983230072969 + 3 ^ 40 * 7271816 * 2
def baseEnd_7271816 : Nat := 1244645613018408740052511

theorem tailTrace_7271816 : CollatzResearch.WordTrace tailWord_7271816 prefixEnd_7271816 1244645613018408740052511 := by
  unfold tailWord_7271816
  simp only [CollatzResearch.WordTrace]
  refine ⟨132612459311730017071513651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176816612415640022762018201 132612459311730017071513651)
  ·
    refine ⟨198918688967595025607270477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132612459311730017071513651 198918688967595025607270477)
    ·
      refine ⟨74594508362848134602726429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198918688967595025607270477 74594508362848134602726429)
      ·
        refine ⟨27972940636068050476022411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74594508362848134602726429 27972940636068050476022411)
        ·
          refine ⟨41959410954102075714033617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27972940636068050476022411 41959410954102075714033617)
          ·
            refine ⟨31469558215576556785525213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41959410954102075714033617 31469558215576556785525213)
            ·
              refine ⟨11801084330841208794571955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31469558215576556785525213 11801084330841208794571955)
              ·
                refine ⟨17701626496261813191857933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801084330841208794571955 17701626496261813191857933)
                ·
                  refine ⟨6638109936098179946946725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17701626496261813191857933 6638109936098179946946725)
                  ·
                    refine ⟨1244645613018408740052511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6638109936098179946946725 1244645613018408740052511)
                    ·
                      rfl

theorem cell23_7271816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_7271816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271816 prefixEnd_7271816 := by exact prefixLift 7271816
  have htrace : WordTrace (prefixWord ++ tailWord_7271816) baseStart_7271816 baseEnd_7271816 := by
    simpa [prefixWord, tailWord_7271816, baseEnd_7271816] using wordTrace_append hprefix tailTrace_7271816
  have hstable : (prefixWord ++ tailWord_7271816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271816).length < 2 ^ (prefixWord ++ tailWord_7271816).sum := by decide
  have hdescent : baseEnd_7271816 < baseStart_7271816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271859 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 1, 5]
def baseStart_7271859 : Nat := 118140960795 + 7271859 * 2 ^ 59
def prefixEnd_7271859 : Nat := 4983230072969 + 3 ^ 40 * 7271859 * 2
def baseEnd_7271859 : Nat := 1244652972907789850639945

theorem tailTrace_7271859 : CollatzResearch.WordTrace tailWord_7271859 prefixEnd_7271859 1244652972907789850639945 := by
  unfold tailWord_7271859
  simp only [CollatzResearch.WordTrace]
  refine ⟨265226486962304252486842631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176817657974869501657895087 265226486962304252486842631)
  ·
    refine ⟨397839730443456378730263947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265226486962304252486842631 397839730443456378730263947)
    ·
      refine ⟨596759595665184568095395921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397839730443456378730263947 596759595665184568095395921)
      ·
        refine ⟨447569696748888426071546941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596759595665184568095395921 447569696748888426071546941)
        ·
          refine ⟨167838636280833159776830103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447569696748888426071546941 167838636280833159776830103)
          ·
            refine ⟨251757954421249739665245155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167838636280833159776830103 251757954421249739665245155)
            ·
              refine ⟨377636931631874609497867733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251757954421249739665245155 377636931631874609497867733)
              ·
                refine ⟨8850865585122061160106275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 377636931631874609497867733 8850865585122061160106275)
                ·
                  refine ⟨13276298377683091740159413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850865585122061160106275 13276298377683091740159413)
                  ·
                    refine ⟨1244652972907789850639945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13276298377683091740159413 1244652972907789850639945)
                    ·
                      rfl

theorem cell23_7271859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 5].length) (baseStart_7271859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271859 prefixEnd_7271859 := by exact prefixLift 7271859
  have htrace : WordTrace (prefixWord ++ tailWord_7271859) baseStart_7271859 baseEnd_7271859 := by
    simpa [prefixWord, tailWord_7271859, baseEnd_7271859] using wordTrace_append hprefix tailTrace_7271859
  have hstable : (prefixWord ++ tailWord_7271859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271859).length < 2 ^ (prefixWord ++ tailWord_7271859).sum := by decide
  have hdescent : baseEnd_7271859 < baseStart_7271859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271874 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7271874 : Nat := 118140960795 + 7271874 * 2 ^ 59
def prefixEnd_7271874 : Nat := 4983230072969 + 3 ^ 40 * 7271874 * 2
def baseEnd_7271874 : Nat := 3733966620933186993232267

theorem tailTrace_7271874 : CollatzResearch.WordTrace tailWord_7271874 prefixEnd_7271874 3733966620933186993232267 := by
  unfold tailWord_7271874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66306758514312477512159669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176818022704833273365759117 66306758514312477512159669)
  ·
    refine ⟨6216258610716794766764969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66306758514312477512159669 6216258610716794766764969)
    ·
      refine ⟨4662193958037596075073727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6216258610716794766764969 4662193958037596075073727)
      ·
        refine ⟨6993290937056394112610591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662193958037596075073727 6993290937056394112610591)
        ·
          refine ⟨10489936405584591168915887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993290937056394112610591 10489936405584591168915887)
          ·
            refine ⟨15734904608376886753373831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489936405584591168915887 15734904608376886753373831)
            ·
              refine ⟨23602356912565330130060747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15734904608376886753373831 23602356912565330130060747)
              ·
                refine ⟨35403535368847995195091121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23602356912565330130060747 35403535368847995195091121)
                ·
                  refine ⟨26552651526635996396318341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35403535368847995195091121 26552651526635996396318341)
                  ·
                    refine ⟨4978622161244249324309689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26552651526635996396318341 4978622161244249324309689)
                    ·
                      refine ⟨3733966620933186993232267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978622161244249324309689 3733966620933186993232267)
                      ·
                        rfl

theorem cell23_7271874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7271874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271874 prefixEnd_7271874 := by exact prefixLift 7271874
  have htrace : WordTrace (prefixWord ++ tailWord_7271874) baseStart_7271874 baseEnd_7271874 := by
    simpa [prefixWord, tailWord_7271874, baseEnd_7271874] using wordTrace_append hprefix tailTrace_7271874
  have hstable : (prefixWord ++ tailWord_7271874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271874).length < 2 ^ (prefixWord ++ tailWord_7271874).sum := by decide
  have hdescent : baseEnd_7271874 < baseStart_7271874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271876 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7271876 : Nat := 118140960795 + 7271876 * 2 ^ 59
def prefixEnd_7271876 : Nat := 4983230072969 + 3 ^ 40 * 7271876 * 2
def baseEnd_7271876 : Nat := 1244655882631498661802419

theorem tailTrace_7271876 : CollatzResearch.WordTrace tailWord_7271876 prefixEnd_7271876 1244655882631498661802419 := by
  unfold tailWord_7271876
  simp only [CollatzResearch.WordTrace]
  refine ⟨132613553501621332195105741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176818071335495109593474321 132613553501621332195105741)
  ·
    refine ⟨49730082563107999573164653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132613553501621332195105741 49730082563107999573164653)
    ·
      refine ⟨18648780961165499839936745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49730082563107999573164653 18648780961165499839936745)
      ·
        refine ⟨13986585720874124879952559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18648780961165499839936745 13986585720874124879952559)
        ·
          refine ⟨20979878581311187319928839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13986585720874124879952559 20979878581311187319928839)
          ·
            refine ⟨31469817871966780979893259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20979878581311187319928839 31469817871966780979893259)
            ·
              refine ⟨47204726807950171469839889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31469817871966780979893259 47204726807950171469839889)
              ·
                refine ⟨35403545105962628602379917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47204726807950171469839889 35403545105962628602379917)
                ·
                  refine ⟨13276329414735985725892469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35403545105962628602379917 13276329414735985725892469)
                  ·
                    refine ⟨1244655882631498661802419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13276329414735985725892469 1244655882631498661802419)
                    ·
                      rfl

theorem cell23_7271876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7271876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271876 prefixEnd_7271876 := by exact prefixLift 7271876
  have htrace : WordTrace (prefixWord ++ tailWord_7271876) baseStart_7271876 baseEnd_7271876 := by
    simpa [prefixWord, tailWord_7271876, baseEnd_7271876] using wordTrace_append hprefix tailTrace_7271876
  have hstable : (prefixWord ++ tailWord_7271876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271876).length < 2 ^ (prefixWord ++ tailWord_7271876).sum := by decide
  have hdescent : baseEnd_7271876 < baseStart_7271876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271879 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_7271879 : Nat := 118140960795 + 7271879 * 2 ^ 59
def prefixEnd_7271879 : Nat := 4983230072969 + 3 ^ 40 * 7271879 * 2
def baseEnd_7271879 : Nat := 3733969188336459473669743

theorem tailTrace_7271879 : CollatzResearch.WordTrace tailWord_7271879 prefixEnd_7271879 3733969188336459473669743 := by
  unfold tailWord_7271879
  simp only [CollatzResearch.WordTrace]
  refine ⟨265227216422231795902570691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176818144281487863935047127 265227216422231795902570691)
  ·
    refine ⟨397840824633347693853856037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265227216422231795902570691 397840824633347693853856037)
    ·
      refine ⟨74595154618752692597598007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397840824633347693853856037 74595154618752692597598007)
      ·
        refine ⟨111892731928129038896397011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74595154618752692597598007 111892731928129038896397011)
        ·
          refine ⟨167839097892193558344595517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111892731928129038896397011 167839097892193558344595517)
          ·
            refine ⟨62939661709572584379223319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167839097892193558344595517 62939661709572584379223319)
            ·
              refine ⟨94409492564358876568834979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62939661709572584379223319 94409492564358876568834979)
              ·
                refine ⟨141614238846538314853252469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94409492564358876568834979 141614238846538314853252469)
                ·
                  refine ⟨13276334891862967017492419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141614238846538314853252469 13276334891862967017492419)
                  ·
                    refine ⟨19914502337794450526238629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13276334891862967017492419 19914502337794450526238629)
                    ·
                      refine ⟨3733969188336459473669743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19914502337794450526238629 3733969188336459473669743)
                      ·
                        rfl

theorem cell23_7271879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_7271879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271879 prefixEnd_7271879 := by exact prefixLift 7271879
  have htrace : WordTrace (prefixWord ++ tailWord_7271879) baseStart_7271879 baseEnd_7271879 := by
    simpa [prefixWord, tailWord_7271879, baseEnd_7271879] using wordTrace_append hprefix tailTrace_7271879
  have hstable : (prefixWord ++ tailWord_7271879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271879).length < 2 ^ (prefixWord ++ tailWord_7271879).sum := by decide
  have hdescent : baseEnd_7271879 < baseStart_7271879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271889 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_7271889 : Nat := 118140960795 + 7271889 * 2 ^ 59
def prefixEnd_7271889 : Nat := 4983230072969 + 3 ^ 40 * 7271889 * 2
def baseEnd_7271889 : Nat := 1244658107714334811514899

theorem tailTrace_7271889 : CollatzResearch.WordTrace tailWord_7271889 prefixEnd_7271889 1244658107714334811514899 := by
  unfold tailWord_7271889
  simp only [CollatzResearch.WordTrace]
  refine ⟨265227581152195567610434721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176818387434797045073623147 265227581152195567610434721)
  ·
    refine ⟨198920685864146675707826041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265227581152195567610434721 198920685864146675707826041)
    ·
      refine ⟨149190514398110006780869531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198920685864146675707826041 149190514398110006780869531)
      ·
        refine ⟨223785771597165010171304297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149190514398110006780869531 223785771597165010171304297)
        ·
          refine ⟨167839328697873757628478223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223785771597165010171304297 167839328697873757628478223)
          ·
            refine ⟨251758993046810636442717335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167839328697873757628478223 251758993046810636442717335)
            ·
              refine ⟨377638489570215954664076003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251758993046810636442717335 377638489570215954664076003)
              ·
                refine ⟨566457734355323931996114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377638489570215954664076003 566457734355323931996114005)
                ·
                  refine ⟨6638176574476452328079461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 566457734355323931996114005 6638176574476452328079461)
                  ·
                    refine ⟨1244658107714334811514899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6638176574476452328079461 1244658107714334811514899)
                    ·
                      rfl

theorem cell23_7271889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_7271889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271889 prefixEnd_7271889 := by exact prefixLift 7271889
  have htrace : WordTrace (prefixWord ++ tailWord_7271889) baseStart_7271889 baseEnd_7271889 := by
    simpa [prefixWord, tailWord_7271889, baseEnd_7271889] using wordTrace_append hprefix tailTrace_7271889
  have hstable : (prefixWord ++ tailWord_7271889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271889).length < 2 ^ (prefixWord ++ tailWord_7271889).sum := by decide
  have hdescent : baseEnd_7271889 < baseStart_7271889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271930 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2]
def baseStart_7271930 : Nat := 118140960795 + 7271930 * 2 ^ 59
def prefixEnd_7271930 : Nat := 4983230072969 + 3 ^ 40 * 7271930 * 2
def baseEnd_7271930 : Nat := 3733995375849838774132009

theorem tailTrace_7271930 : CollatzResearch.WordTrace tailWord_7271930 prefixEnd_7271930 3733995375849838774132009 := by
  unfold tailWord_7271930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307269136261757903169311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176819384363364687741784829 66307269136261757903169311)
  ·
    refine ⟨99460903704392636854753967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66307269136261757903169311 99460903704392636854753967)
    ·
      refine ⟨149191355556588955282130951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99460903704392636854753967 149191355556588955282130951)
      ·
        refine ⟨223787033334883432923196427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149191355556588955282130951 223787033334883432923196427)
        ·
          refine ⟨335680550002325149384794641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223787033334883432923196427 335680550002325149384794641)
          ·
            refine ⟨251760412501743862038595981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335680550002325149384794641 251760412501743862038595981)
            ·
              refine ⟨94410154688153948264473493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251760412501743862038595981 94410154688153948264473493)
              ·
                refine ⟨4425476001007216324897195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94410154688153948264473493 4425476001007216324897195)
                ·
                  refine ⟨6638214001510824487345793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425476001007216324897195 6638214001510824487345793)
                  ·
                    refine ⟨4978660501133118365509345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6638214001510824487345793 4978660501133118365509345)
                    ·
                      refine ⟨3733995375849838774132009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978660501133118365509345 3733995375849838774132009)
                      ·
                        rfl

theorem cell23_7271930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_7271930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271930 prefixEnd_7271930 := by exact prefixLift 7271930
  have htrace : WordTrace (prefixWord ++ tailWord_7271930) baseStart_7271930 baseEnd_7271930 := by
    simpa [prefixWord, tailWord_7271930, baseEnd_7271930] using wordTrace_append hprefix tailTrace_7271930
  have hstable : (prefixWord ++ tailWord_7271930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271930).length < 2 ^ (prefixWord ++ tailWord_7271930).sum := by decide
  have hdescent : baseEnd_7271930 < baseStart_7271930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271940 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_7271940 : Nat := 118140960795 + 7271940 * 2 ^ 59
def prefixEnd_7271940 : Nat := 4983230072969 + 3 ^ 40 * 7271940 * 2
def baseEnd_7271940 : Nat := 1244666836885461245002321

theorem tailTrace_7271940 : CollatzResearch.WordTrace tailWord_7271940 prefixEnd_7271940 1244666836885461245002321 := by
  unfold tailWord_7271940
  simp only [CollatzResearch.WordTrace]
  refine ⟨132614720637505401660270637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176819627516673868880360849 132614720637505401660270637)
  ·
    refine ⟨49730520239064525622601489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132614720637505401660270637 49730520239064525622601489)
    ·
      refine ⟨37297890179298394216951117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49730520239064525622601489 37297890179298394216951117)
      ·
        refine ⟨13986708817236897831356669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37297890179298394216951117 13986708817236897831356669)
        ·
          refine ⟨5245015806463836686758751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13986708817236897831356669 5245015806463836686758751)
          ·
            refine ⟨7867523709695755030138127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245015806463836686758751 7867523709695755030138127)
            ·
              refine ⟨11801285564543632545207191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867523709695755030138127 11801285564543632545207191)
              ·
                refine ⟨17701928346815448817810787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801285564543632545207191 17701928346815448817810787)
                ·
                  refine ⟨26552892520223173226716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17701928346815448817810787 26552892520223173226716181)
                  ·
                    refine ⟨1244666836885461245002321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26552892520223173226716181 1244666836885461245002321)
                    ·
                      rfl

theorem cell23_7271940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_7271940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271940 prefixEnd_7271940 := by exact prefixLift 7271940
  have htrace : WordTrace (prefixWord ++ tailWord_7271940) baseStart_7271940 baseEnd_7271940 := by
    simpa [prefixWord, tailWord_7271940, baseEnd_7271940] using wordTrace_append hprefix tailTrace_7271940
  have hstable : (prefixWord ++ tailWord_7271940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271940).length < 2 ^ (prefixWord ++ tailWord_7271940).sum := by decide
  have hdescent : baseEnd_7271940 < baseStart_7271940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271943 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7271943 : Nat := 118140960795 + 7271943 * 2 ^ 59
def prefixEnd_7271943 : Nat := 4983230072969 + 3 ^ 40 * 7271943 * 2
def baseEnd_7271943 : Nat := 3734002051098347223269449

theorem tailTrace_7271943 : CollatzResearch.WordTrace tailWord_7271943 prefixEnd_7271943 3734002051098347223269449 := by
  unfold tailWord_7271943
  simp only [CollatzResearch.WordTrace]
  refine ⟨265229550693999934832900483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176819700462666623221933655 265229550693999934832900483)
  ·
    refine ⟨397844326040999902249350725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265229550693999934832900483 397844326040999902249350725)
    ·
      refine ⟨74595811132687481671753261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397844326040999902249350725 74595811132687481671753261)
      ·
        refine ⟨27973429174757805626907473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74595811132687481671753261 27973429174757805626907473)
        ·
          refine ⟨20980071881068354220180605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27973429174757805626907473 20980071881068354220180605)
          ·
            refine ⟨7867526955400632832567727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20980071881068354220180605 7867526955400632832567727)
            ·
              refine ⟨11801290433100949248851591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867526955400632832567727 11801290433100949248851591)
              ·
                refine ⟨17701935649651423873277387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801290433100949248851591 17701935649651423873277387)
                ·
                  refine ⟨26552903474477135809916081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17701935649651423873277387 26552903474477135809916081)
                  ·
                    refine ⟨19914677605857851857437061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26552903474477135809916081 19914677605857851857437061)
                    ·
                      refine ⟨3734002051098347223269449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19914677605857851857437061 3734002051098347223269449)
                      ·
                        rfl

theorem cell23_7271943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7271943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271943 prefixEnd_7271943 := by exact prefixLift 7271943
  have htrace : WordTrace (prefixWord ++ tailWord_7271943) baseStart_7271943 baseEnd_7271943 := by
    simpa [prefixWord, tailWord_7271943, baseEnd_7271943] using wordTrace_append hprefix tailTrace_7271943
  have hstable : (prefixWord ++ tailWord_7271943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271943).length < 2 ^ (prefixWord ++ tailWord_7271943).sum := by decide
  have hdescent : baseEnd_7271943 < baseStart_7271943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7271950 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7271950 : Nat := 118140960795 + 7271950 * 2 ^ 59
def prefixEnd_7271950 : Nat := 4983230072969 + 3 ^ 40 * 7271950 * 2
def baseEnd_7271950 : Nat := 3734005645462928695881917

theorem tailTrace_7271950 : CollatzResearch.WordTrace tailWord_7271950 prefixEnd_7271950 3734005645462928695881917 := by
  unfold tailWord_7271950
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153725750621821878550663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176819870669983050018936869 33153725750621821878550663)
  ·
    refine ⟨49730588625932732817825995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33153725750621821878550663 49730588625932732817825995)
    ·
      refine ⟨74595882938899099226738993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49730588625932732817825995 74595882938899099226738993)
      ·
        refine ⟨55946912204174324420054245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74595882938899099226738993 55946912204174324420054245)
        ·
          refine ⟨10490046038282685828760171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55946912204174324420054245 10490046038282685828760171)
          ·
            refine ⟨15735069057424028743140257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10490046038282685828760171 15735069057424028743140257)
            ·
              refine ⟨11801301793068021557355193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15735069057424028743140257 11801301793068021557355193)
              ·
                refine ⟨8850976344801016168016395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801301793068021557355193 8850976344801016168016395)
                ·
                  refine ⟨13276464517201524252024593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8850976344801016168016395 13276464517201524252024593)
                  ·
                    refine ⟨9957348387901143189018445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13276464517201524252024593 9957348387901143189018445)
                    ·
                      refine ⟨3734005645462928695881917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957348387901143189018445 3734005645462928695881917)
                      ·
                        rfl

theorem cell23_7271950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7271950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7271950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7271950 prefixEnd_7271950 := by exact prefixLift 7271950
  have htrace : WordTrace (prefixWord ++ tailWord_7271950) baseStart_7271950 baseEnd_7271950 := by
    simpa [prefixWord, tailWord_7271950, baseEnd_7271950] using wordTrace_append hprefix tailTrace_7271950
  have hstable : (prefixWord ++ tailWord_7271950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7271950).length < 2 ^ (prefixWord ++ tailWord_7271950).sum := by decide
  have hdescent : baseEnd_7271950 < baseStart_7271950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7271950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272007 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_7272007 : Nat := 118140960795 + 7272007 * 2 ^ 59
def prefixEnd_7272007 : Nat := 4983230072969 + 3 ^ 40 * 7272007 * 2
def baseEnd_7272007 : Nat := 3734034913860234972869155

theorem tailTrace_7272007 : CollatzResearch.WordTrace tailWord_7272007 prefixEnd_7272007 3734034913860234972869155 := by
  unfold tailWord_7272007
  simp only [CollatzResearch.WordTrace]
  refine ⟨265231884965768073763230275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176821256643845382508820183 265231884965768073763230275)
  ·
    refine ⟨397847827448652110644845413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265231884965768073763230275 397847827448652110644845413)
    ·
      refine ⟨74596467646622270745908515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397847827448652110644845413 74596467646622270745908515)
      ·
        refine ⟨111894701469933406118862773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74596467646622270745908515 111894701469933406118862773)
        ·
          refine ⟨10490128262806256823643385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111894701469933406118862773 10490128262806256823643385)
          ·
            refine ⟨7867596197104692617732539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10490128262806256823643385 7867596197104692617732539)
            ·
              refine ⟨11801394295657038926598809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867596197104692617732539 11801394295657038926598809)
              ·
                refine ⟨8851045721742779194949107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801394295657038926598809 8851045721742779194949107)
                ·
                  refine ⟨13276568582614168792423661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851045721742779194949107 13276568582614168792423661)
                  ·
                    refine ⟨4978713218480313297158873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13276568582614168792423661 4978713218480313297158873)
                    ·
                      refine ⟨3734034913860234972869155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978713218480313297158873 3734034913860234972869155)
                      ·
                        rfl

theorem cell23_7272007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_7272007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272007 prefixEnd_7272007 := by exact prefixLift 7272007
  have htrace : WordTrace (prefixWord ++ tailWord_7272007) baseStart_7272007 baseEnd_7272007 := by
    simpa [prefixWord, tailWord_7272007, baseEnd_7272007] using wordTrace_append hprefix tailTrace_7272007
  have hstable : (prefixWord ++ tailWord_7272007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272007).length < 2 ^ (prefixWord ++ tailWord_7272007).sum := by decide
  have hdescent : baseEnd_7272007 < baseStart_7272007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272009 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 7]
def baseStart_7272009 : Nat := 118140960795 + 7272009 * 2 ^ 59
def prefixEnd_7272009 : Nat := 4983230072969 + 3 ^ 40 * 7272009 * 2
def baseEnd_7272009 : Nat := 414892882313504885004905

theorem tailTrace_7272009 : CollatzResearch.WordTrace tailWord_7272009 prefixEnd_7272009 414892882313504885004905 := by
  unfold tailWord_7272009
  simp only [CollatzResearch.WordTrace]
  refine ⟨265231957911760828104803081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176821305274507218736535387 265231957911760828104803081)
  ·
    refine ⟨198923968433820621078602311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265231957911760828104803081 198923968433820621078602311)
    ·
      refine ⟨298385952650730931617903467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198923968433820621078602311 298385952650730931617903467)
      ·
        refine ⟨447578928976096397426855201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298385952650730931617903467 447578928976096397426855201)
        ·
          refine ⟨335684196732072298070141401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447578928976096397426855201 335684196732072298070141401)
          ·
            refine ⟨251763147549054223552606051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335684196732072298070141401 251763147549054223552606051)
            ·
              refine ⟨377644721323581335328909077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251763147549054223552606051 377644721323581335328909077)
              ·
                refine ⟨17702096312042875093542613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377644721323581335328909077 17702096312042875093542613)
                ·
                  refine ⟨414892882313504885004905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17702096312042875093542613 414892882313504885004905)
                  ·
                    rfl

theorem cell23_7272009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_7272009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272009 prefixEnd_7272009 := by exact prefixLift 7272009
  have htrace : WordTrace (prefixWord ++ tailWord_7272009) baseStart_7272009 baseEnd_7272009 := by
    simpa [prefixWord, tailWord_7272009, baseEnd_7272009] using wordTrace_append hprefix tailTrace_7272009
  have hstable : (prefixWord ++ tailWord_7272009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272009).length < 2 ^ (prefixWord ++ tailWord_7272009).sum := by decide
  have hdescent : baseEnd_7272009 < baseStart_7272009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272037 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_7272037 : Nat := 118140960795 + 7272037 * 2 ^ 59
def prefixEnd_7272037 : Nat := 4983230072969 + 3 ^ 40 * 7272037 * 2
def baseEnd_7272037 : Nat := 3734050318279869855494017

theorem tailTrace_7272037 : CollatzResearch.WordTrace tailWord_7272037 prefixEnd_7272037 3734050318279869855494017 := by
  unfold tailWord_7272037
  simp only [CollatzResearch.WordTrace]
  refine ⟨265232979155659388886822365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176821986103772925924548243 265232979155659388886822365)
  ·
    refine ⟨99462367183372270832558387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265232979155659388886822365 99462367183372270832558387)
    ·
      refine ⟨149193550775058406248837581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99462367183372270832558387 149193550775058406248837581)
      ·
        refine ⟨55947581540646902343314093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149193550775058406248837581 55947581540646902343314093)
        ·
          refine ⟨20980343077742588378742785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55947581540646902343314093 20980343077742588378742785)
          ·
            refine ⟨15735257308306941284057089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20980343077742588378742785 15735257308306941284057089)
            ·
              refine ⟨11801442981230205963042817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15735257308306941284057089 11801442981230205963042817)
              ·
                refine ⟨8851082235922654472282113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801442981230205963042817 8851082235922654472282113)
                ·
                  refine ⟨6638311676941990854211585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8851082235922654472282113 6638311676941990854211585)
                  ·
                    refine ⟨4978733757706493140658689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6638311676941990854211585 4978733757706493140658689)
                    ·
                      refine ⟨3734050318279869855494017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978733757706493140658689 3734050318279869855494017)
                      ·
                        rfl

theorem cell23_7272037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_7272037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272037 prefixEnd_7272037 := by exact prefixLift 7272037
  have htrace : WordTrace (prefixWord ++ tailWord_7272037) baseStart_7272037 baseEnd_7272037 := by
    simpa [prefixWord, tailWord_7272037, baseEnd_7272037] using wordTrace_append hprefix tailTrace_7272037
  have hstable : (prefixWord ++ tailWord_7272037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272037).length < 2 ^ (prefixWord ++ tailWord_7272037).sum := by decide
  have hdescent : baseEnd_7272037 < baseStart_7272037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272053 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7272053 : Nat := 118140960795 + 7272053 * 2 ^ 59
def prefixEnd_7272053 : Nat := 4983230072969 + 3 ^ 40 * 7272053 * 2
def baseEnd_7272053 : Nat := 3734058533970341792893943

theorem tailTrace_7272053 : CollatzResearch.WordTrace tailWord_7272053 prefixEnd_7272053 3734058533970341792893943 := by
  unfold tailWord_7272053
  simp only [CollatzResearch.WordTrace]
  refine ⟨265233562723601423619404813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176822375149067615746269875 265233562723601423619404813)
  ·
    refine ⟨99462586021350533857276805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265233562723601423619404813 99462586021350533857276805)
    ·
      refine ⟨18649234879003225098239401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99462586021350533857276805 18649234879003225098239401)
      ·
        refine ⟨13986926159252418823679551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18649234879003225098239401 13986926159252418823679551)
        ·
          refine ⟨20980389238878628235519327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13986926159252418823679551 20980389238878628235519327)
          ·
            refine ⟨31470583858317942353278991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20980389238878628235519327 31470583858317942353278991)
            ·
              refine ⟨47205875787476913529918487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31470583858317942353278991 47205875787476913529918487)
              ·
                refine ⟨70808813681215370294877731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47205875787476913529918487 70808813681215370294877731)
                ·
                  refine ⟨106213220521823055442316597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70808813681215370294877731 106213220521823055442316597)
                  ·
                    refine ⟨9957489423920911447717181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106213220521823055442316597 9957489423920911447717181)
                    ·
                      refine ⟨3734058533970341792893943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957489423920911447717181 3734058533970341792893943)
                      ·
                        rfl

theorem cell23_7272053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7272053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272053 prefixEnd_7272053 := by exact prefixLift 7272053
  have htrace : WordTrace (prefixWord ++ tailWord_7272053) baseStart_7272053 baseEnd_7272053 := by
    simpa [prefixWord, tailWord_7272053, baseEnd_7272053] using wordTrace_append hprefix tailTrace_7272053
  have hstable : (prefixWord ++ tailWord_7272053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272053).length < 2 ^ (prefixWord ++ tailWord_7272053).sum := by decide
  have hdescent : baseEnd_7272053 < baseStart_7272053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272076 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7272076 : Nat := 118140960795 + 7272076 * 2 ^ 59
def prefixEnd_7272076 : Nat := 4983230072969 + 3 ^ 40 * 7272076 * 2
def baseEnd_7272076 : Nat := 3734070344025395202906337

theorem tailTrace_7272076 : CollatzResearch.WordTrace tailWord_7272076 prefixEnd_7272076 3734070344025395202906337 := by
  unfold tailWord_7272076
  simp only [CollatzResearch.WordTrace]
  refine ⟨132617200801259049273746041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176822934401678732364994721 132617200801259049273746041)
  ·
    refine ⟨99462900600944286955309531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132617200801259049273746041 99462900600944286955309531)
    ·
      refine ⟨149194350901416430432964297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99462900600944286955309531 149194350901416430432964297)
      ·
        refine ⟨111895763176062322824723223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149194350901416430432964297 111895763176062322824723223)
        ·
          refine ⟨167843644764093484237084835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111895763176062322824723223 167843644764093484237084835)
          ·
            refine ⟨251765467146140226355627253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167843644764093484237084835 251765467146140226355627253)
            ·
              refine ⟨23603012544950646220840055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251765467146140226355627253 23603012544950646220840055)
              ·
                refine ⟨35404518817425969331260083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23603012544950646220840055 35404518817425969331260083)
                ·
                  refine ⟨53106778226138953996890125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35404518817425969331260083 53106778226138953996890125)
                  ·
                    refine ⟨19915041834802107748833797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53106778226138953996890125 19915041834802107748833797)
                    ·
                      refine ⟨3734070344025395202906337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19915041834802107748833797 3734070344025395202906337)
                      ·
                        rfl

theorem cell23_7272076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7272076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272076 prefixEnd_7272076 := by exact prefixLift 7272076
  have htrace : WordTrace (prefixWord ++ tailWord_7272076) baseStart_7272076 baseEnd_7272076 := by
    simpa [prefixWord, tailWord_7272076, baseEnd_7272076] using wordTrace_append hprefix tailTrace_7272076
  have hstable : (prefixWord ++ tailWord_7272076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272076).length < 2 ^ (prefixWord ++ tailWord_7272076).sum := by decide
  have hdescent : baseEnd_7272076 < baseStart_7272076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272079 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_7272079 : Nat := 118140960795 + 7272079 * 2 ^ 59
def prefixEnd_7272079 : Nat := 4983230072969 + 3 ^ 40 * 7272079 * 2
def baseEnd_7272079 : Nat := 3734071884467358691168823

theorem tailTrace_7272079 : CollatzResearch.WordTrace tailWord_7272079 prefixEnd_7272079 3734071884467358691168823 := by
  unfold tailWord_7272079
  simp only [CollatzResearch.WordTrace]
  refine ⟨265234511021507230059851291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176823007347671486706567527 265234511021507230059851291)
  ·
    refine ⟨397851766532260845089776937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265234511021507230059851291 397851766532260845089776937)
    ·
      refine ⟨298388824899195633817332703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397851766532260845089776937 298388824899195633817332703)
      ·
        refine ⟨447583237348793450725999055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298388824899195633817332703 447583237348793450725999055)
        ·
          refine ⟨671374856023190176088998583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447583237348793450725999055 671374856023190176088998583)
          ·
            refine ⟨1007062284034785264133497875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671374856023190176088998583 1007062284034785264133497875)
            ·
              refine ⟨1510593426052177896200246813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007062284034785264133497875 1510593426052177896200246813)
              ·
                refine ⟨566472534769566711075092555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1510593426052177896200246813 566472534769566711075092555)
                ·
                  refine ⟨849708802154350066612638833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566472534769566711075092555 849708802154350066612638833)
                  ·
                    refine ⟨637281601615762549959479125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849708802154350066612638833 637281601615762549959479125)
                    ·
                      refine ⟨3734071884467358691168823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 637281601615762549959479125 3734071884467358691168823)
                      ·
                        rfl

theorem cell23_7272079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_7272079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272079 prefixEnd_7272079 := by exact prefixLift 7272079
  have htrace : WordTrace (prefixWord ++ tailWord_7272079) baseStart_7272079 baseEnd_7272079 := by
    simpa [prefixWord, tailWord_7272079, baseEnd_7272079] using wordTrace_append hprefix tailTrace_7272079
  have hstable : (prefixWord ++ tailWord_7272079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272079).length < 2 ^ (prefixWord ++ tailWord_7272079).sum := by decide
  have hdescent : baseEnd_7272079 < baseStart_7272079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272143 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 3]
def baseStart_7272143 : Nat := 118140960795 + 7272143 * 2 ^ 59
def prefixEnd_7272143 : Nat := 4983230072969 + 3 ^ 40 * 7272143 * 2
def baseEnd_7272143 : Nat := 3734104747229246440768529

theorem tailTrace_7272143 : CollatzResearch.WordTrace tailWord_7272143 prefixEnd_7272143 3734104747229246440768529 := by
  unfold tailWord_7272143
  simp only [CollatzResearch.WordTrace]
  refine ⟨265236845293275368990181083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176824563528850245993454055 265236845293275368990181083)
  ·
    refine ⟨397855267939913053485271625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265236845293275368990181083 397855267939913053485271625)
    ·
      refine ⟨298391450954934790113953719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397855267939913053485271625 298391450954934790113953719)
      ·
        refine ⟨447587176432402185170930579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298391450954934790113953719 447587176432402185170930579)
        ·
          refine ⟨671380764648603277756395869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447587176432402185170930579 671380764648603277756395869)
          ·
            refine ⟨251767786743226229158648451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 671380764648603277756395869 251767786743226229158648451)
            ·
              refine ⟨377651680114839343737972677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251767786743226229158648451 377651680114839343737972677)
              ·
                refine ⟨70809690021532376950869877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377651680114839343737972677 70809690021532376950869877)
                ·
                  refine ⟨6638408439518660339144051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70809690021532376950869877 6638408439518660339144051)
                  ·
                    refine ⟨9957612659277990508716077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638408439518660339144051 9957612659277990508716077)
                    ·
                      refine ⟨3734104747229246440768529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957612659277990508716077 3734104747229246440768529)
                      ·
                        rfl

theorem cell23_7272143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_7272143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272143 prefixEnd_7272143 := by exact prefixLift 7272143
  have htrace : WordTrace (prefixWord ++ tailWord_7272143) baseStart_7272143 baseEnd_7272143 := by
    simpa [prefixWord, tailWord_7272143, baseEnd_7272143] using wordTrace_append hprefix tailTrace_7272143
  have hstable : (prefixWord ++ tailWord_7272143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272143).length < 2 ^ (prefixWord ++ tailWord_7272143).sum := by decide
  have hdescent : baseEnd_7272143 < baseStart_7272143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272160 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3]
def baseStart_7272160 : Nat := 118140960795 + 7272160 * 2 ^ 59
def prefixEnd_7272160 : Nat := 4983230072969 + 3 ^ 40 * 7272160 * 2
def baseEnd_7272160 : Nat := 3734113476400372874255951

theorem tailTrace_7272160 : CollatzResearch.WordTrace tailWord_7272160 prefixEnd_7272160 3734113476400372874255951 := by
  unfold tailWord_7272160
  simp only [CollatzResearch.WordTrace]
  refine ⟨132618732667106890446774967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176824976889475853929033289 132618732667106890446774967)
  ·
    refine ⟨198928099000660335670162451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132618732667106890446774967 198928099000660335670162451)
    ·
      refine ⟨298392148500990503505243677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198928099000660335670162451 298392148500990503505243677)
      ·
        refine ⟨111897055687871438814466379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298392148500990503505243677 111897055687871438814466379)
        ·
          refine ⟨167845583531807158221699569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111897055687871438814466379 167845583531807158221699569)
          ·
            refine ⟨125884187648855368666274677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167845583531807158221699569 125884187648855368666274677)
            ·
              refine ⟨11801642592080190812463251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125884187648855368666274677 11801642592080190812463251)
              ·
                refine ⟨17702463888120286218694877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801642592080190812463251 17702463888120286218694877)
                ·
                  refine ⟨6638423958045107332010579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17702463888120286218694877 6638423958045107332010579)
                  ·
                    refine ⟨9957635937067660998015869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638423958045107332010579 9957635937067660998015869)
                    ·
                      refine ⟨3734113476400372874255951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957635937067660998015869 3734113476400372874255951)
                      ·
                        rfl

theorem cell23_7272160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_7272160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272160 prefixEnd_7272160 := by exact prefixLift 7272160
  have htrace : WordTrace (prefixWord ++ tailWord_7272160) baseStart_7272160 baseEnd_7272160 := by
    simpa [prefixWord, tailWord_7272160, baseEnd_7272160] using wordTrace_append hprefix tailTrace_7272160
  have hstable : (prefixWord ++ tailWord_7272160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272160).length < 2 ^ (prefixWord ++ tailWord_7272160).sum := by decide
  have hdescent : baseEnd_7272160 < baseStart_7272160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272183 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_7272183 : Nat := 118140960795 + 7272183 * 2 ^ 59
def prefixEnd_7272183 : Nat := 4983230072969 + 3 ^ 40 * 7272183 * 2
def baseEnd_7272183 : Nat := 3734125286455426284268345

theorem tailTrace_7272183 : CollatzResearch.WordTrace tailWord_7272183 prefixEnd_7272183 3734125286455426284268345 := by
  unfold tailWord_7272183
  simp only [CollatzResearch.WordTrace]
  refine ⟨265238304213130455821637203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176825536142086970547758135 265238304213130455821637203)
  ·
    refine ⟨397857456319695683732455805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265238304213130455821637203 397857456319695683732455805)
    ·
      refine ⟨149196546119885881399670927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397857456319695683732455805 149196546119885881399670927)
      ·
        refine ⟨223794819179828822099506391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149196546119885881399670927 223794819179828822099506391)
        ·
          refine ⟨335692228769743233149259587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223794819179828822099506391 335692228769743233149259587)
          ·
            refine ⟨503538343154614849723889381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335692228769743233149259587 503538343154614849723889381)
            ·
              refine ⟨94413439341490284323229259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503538343154614849723889381 94413439341490284323229259)
              ·
                refine ⟨141620159012235426484843889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94413439341490284323229259 141620159012235426484843889)
                ·
                  refine ⟨106215119259176569863632917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141620159012235426484843889 106215119259176569863632917)
                  ·
                    refine ⟨4978833715273901712357793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106215119259176569863632917 4978833715273901712357793)
                    ·
                      refine ⟨3734125286455426284268345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4978833715273901712357793 3734125286455426284268345)
                      ·
                        rfl

theorem cell23_7272183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_7272183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272183 prefixEnd_7272183 := by exact prefixLift 7272183
  have htrace : WordTrace (prefixWord ++ tailWord_7272183) baseStart_7272183 baseEnd_7272183 := by
    simpa [prefixWord, tailWord_7272183, baseEnd_7272183] using wordTrace_append hprefix tailTrace_7272183
  have hstable : (prefixWord ++ tailWord_7272183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272183).length < 2 ^ (prefixWord ++ tailWord_7272183).sum := by decide
  have hdescent : baseEnd_7272183 < baseStart_7272183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272193 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7272193 : Nat := 118140960795 + 7272193 * 2 ^ 59
def prefixEnd_7272193 : Nat := 4983230072969 + 3 ^ 40 * 7272193 * 2
def baseEnd_7272193 : Nat := 1244710140420657081714433

theorem tailTrace_7272193 : CollatzResearch.WordTrace tailWord_7272193 prefixEnd_7272193 1244710140420657081714433 := by
  unfold tailWord_7272193
  simp only [CollatzResearch.WordTrace]
  refine ⟨265238668943094227529501233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176825779295396151686334155 265238668943094227529501233)
  ·
    refine ⟨198929001707320670647125925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265238668943094227529501233 198929001707320670647125925)
    ·
      refine ⟨37299187820122625746336111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198929001707320670647125925 37299187820122625746336111)
      ·
        refine ⟨55948781730183938619504167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37299187820122625746336111 55948781730183938619504167)
        ·
          refine ⟨83923172595275907929256251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55948781730183938619504167 83923172595275907929256251)
          ·
            refine ⟨125884758892913861893884377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83923172595275907929256251 125884758892913861893884377)
            ·
              refine ⟨94413569169685396420413283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125884758892913861893884377 94413569169685396420413283)
              ·
                refine ⟨141620353754528094630619925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94413569169685396420413283 141620353754528094630619925)
                ·
                  refine ⟨6638454082243504435810309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141620353754528094630619925 6638454082243504435810309)
                  ·
                    refine ⟨1244710140420657081714433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6638454082243504435810309 1244710140420657081714433)
                    ·
                      rfl

theorem cell23_7272193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7272193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272193 prefixEnd_7272193 := by exact prefixLift 7272193
  have htrace : WordTrace (prefixWord ++ tailWord_7272193) baseStart_7272193 baseEnd_7272193 := by
    simpa [prefixWord, tailWord_7272193, baseEnd_7272193] using wordTrace_append hprefix tailTrace_7272193
  have hstable : (prefixWord ++ tailWord_7272193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272193).length < 2 ^ (prefixWord ++ tailWord_7272193).sum := by decide
  have hdescent : baseEnd_7272193 < baseStart_7272193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272194 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_7272194 : Nat := 118140960795 + 7272194 * 2 ^ 59
def prefixEnd_7272194 : Nat := 4983230072969 + 3 ^ 40 * 7272194 * 2
def baseEnd_7272194 : Nat := 3734130934742625741230795

theorem tailTrace_7272194 : CollatzResearch.WordTrace tailWord_7272194 prefixEnd_7272194 3734130934742625741230795 := by
  unfold tailWord_7272194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66309676354022651175071909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176825803610727069800191757 66309676354022651175071909)
  ·
    refine ⟨12433064316379247095325983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66309676354022651175071909 12433064316379247095325983)
    ·
      refine ⟨18649596474568870642988975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12433064316379247095325983 18649596474568870642988975)
      ·
        refine ⟨27974394711853305964483463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18649596474568870642988975 27974394711853305964483463)
        ·
          refine ⟨41961592067779958946725195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27974394711853305964483463 41961592067779958946725195)
          ·
            refine ⟨62942388101669938420087793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41961592067779958946725195 62942388101669938420087793)
            ·
              refine ⟨47206791076252453815065845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62942388101669938420087793 47206791076252453815065845)
              ·
                refine ⟨4425636663398667545162423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47206791076252453815065845 4425636663398667545162423)
                ·
                  refine ⟨6638454995098001317743635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425636663398667545162423 6638454995098001317743635)
                  ·
                    refine ⟨9957682492647001976615453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638454995098001317743635 9957682492647001976615453)
                    ·
                      refine ⟨3734130934742625741230795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957682492647001976615453 3734130934742625741230795)
                      ·
                        rfl

theorem cell23_7272194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_7272194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272194 prefixEnd_7272194 := by exact prefixLift 7272194
  have htrace : WordTrace (prefixWord ++ tailWord_7272194) baseStart_7272194 baseEnd_7272194 := by
    simpa [prefixWord, tailWord_7272194, baseEnd_7272194] using wordTrace_append hprefix tailTrace_7272194
  have hstable : (prefixWord ++ tailWord_7272194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272194).length < 2 ^ (prefixWord ++ tailWord_7272194).sum := by decide
  have hdescent : baseEnd_7272194 < baseStart_7272194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272203 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5]
def baseStart_7272203 : Nat := 118140960795 + 7272203 * 2 ^ 59
def prefixEnd_7272203 : Nat := 4983230072969 + 3 ^ 40 * 7272203 * 2
def baseEnd_7272203 : Nat := 3734135556068516206018253

theorem tailTrace_7272203 : CollatzResearch.WordTrace tailWord_7272203 prefixEnd_7272203 3734135556068516206018253 := by
  unfold tailWord_7272203
  simp only [CollatzResearch.WordTrace]
  refine ⟨265239033673057999237365263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176826022448705332824910175 265239033673057999237365263)
  ·
    refine ⟨397858550509586998856047895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265239033673057999237365263 397858550509586998856047895)
    ·
      refine ⟨596787825764380498284071843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397858550509586998856047895 596787825764380498284071843)
      ·
        refine ⟨895181738646570747426107765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596787825764380498284071843 895181738646570747426107765)
        ·
          refine ⟨83923287998116007571197603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 895181738646570747426107765 83923287998116007571197603)
          ·
            refine ⟨125884931997174011356796405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83923287998116007571197603 125884931997174011356796405)
            ·
              refine ⟨11801712374735063564699663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125884931997174011356796405 11801712374735063564699663)
              ·
                refine ⟨17702568562102595347049495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801712374735063564699663 17702568562102595347049495)
                ·
                  refine ⟨26553852843153893020574243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17702568562102595347049495 26553852843153893020574243)
                  ·
                    refine ⟨39830779264730839530861365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26553852843153893020574243 39830779264730839530861365)
                    ·
                      refine ⟨3734135556068516206018253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39830779264730839530861365 3734135556068516206018253)
                      ·
                        rfl

theorem cell23_7272203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 5].length) (baseStart_7272203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272203 prefixEnd_7272203 := by exact prefixLift 7272203
  have htrace : WordTrace (prefixWord ++ tailWord_7272203) baseStart_7272203 baseEnd_7272203 := by
    simpa [prefixWord, tailWord_7272203, baseEnd_7272203] using wordTrace_append hprefix tailTrace_7272203
  have hstable : (prefixWord ++ tailWord_7272203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272203).length < 2 ^ (prefixWord ++ tailWord_7272203).sum := by decide
  have hdescent : baseEnd_7272203 < baseStart_7272203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272250 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_7272250 : Nat := 118140960795 + 7272250 * 2 ^ 59
def prefixEnd_7272250 : Nat := 4983230072969 + 3 ^ 40 * 7272250 * 2
def baseEnd_7272250 : Nat := 3734159689659277522130537

theorem tailTrace_7272250 : CollatzResearch.WordTrace tailWord_7272250 prefixEnd_7272250 3734159689659277522130537 := by
  unfold tailWord_7272250
  simp only [CollatzResearch.WordTrace]
  refine ⟨66310186975971931566081551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176827165269258484176217469 66310186975971931566081551)
  ·
    refine ⟨99465280463957897349122327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66310186975971931566081551 99465280463957897349122327)
    ·
      refine ⟨149197920695936846023683491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99465280463957897349122327 149197920695936846023683491)
      ·
        refine ⟨223796881043905269035525237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149197920695936846023683491 223796881043905269035525237)
        ·
          refine ⟨20980957597866118972080491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223796881043905269035525237 20980957597866118972080491)
          ·
            refine ⟨31471436396799178458120737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20980957597866118972080491 31471436396799178458120737)
            ·
              refine ⟨23603577297599383843590553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31471436396799178458120737 23603577297599383843590553)
              ·
                refine ⟨17702682973199537882692915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23603577297599383843590553 17702682973199537882692915)
                ·
                  refine ⟨26554024459799306824039373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17702682973199537882692915 26554024459799306824039373)
                  ·
                    refine ⟨9957759172424740059014765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26554024459799306824039373 9957759172424740059014765)
                    ·
                      refine ⟨3734159689659277522130537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957759172424740059014765 3734159689659277522130537)
                      ·
                        rfl

theorem cell23_7272250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_7272250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272250 prefixEnd_7272250 := by exact prefixLift 7272250
  have htrace : WordTrace (prefixWord ++ tailWord_7272250) baseStart_7272250 baseEnd_7272250 := by
    simpa [prefixWord, tailWord_7272250, baseEnd_7272250] using wordTrace_append hprefix tailTrace_7272250
  have hstable : (prefixWord ++ tailWord_7272250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272250).length < 2 ^ (prefixWord ++ tailWord_7272250).sum := by decide
  have hdescent : baseEnd_7272250 < baseStart_7272250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272254 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_7272254 : Nat := 118140960795 + 7272254 * 2 ^ 59
def prefixEnd_7272254 : Nat := 4983230072969 + 3 ^ 40 * 7272254 * 2
def baseEnd_7272254 : Nat := 3734161743581895506480519

theorem tailTrace_7272254 : CollatzResearch.WordTrace tailWord_7272254 prefixEnd_7272254 3734161743581895506480519 := by
  unfold tailWord_7272254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33155111724484154368433977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176827262530582156631647877 33155111724484154368433977)
  ·
    refine ⟨24866333793363115776325483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33155111724484154368433977 24866333793363115776325483)
    ·
      refine ⟨37299500690044673664488225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24866333793363115776325483 37299500690044673664488225)
      ·
        refine ⟨27974625517533505248366169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37299500690044673664488225 27974625517533505248366169)
        ·
          refine ⟨20980969138150128936274627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27974625517533505248366169 20980969138150128936274627)
          ·
            refine ⟨31471453707225193404411941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20980969138150128936274627 31471453707225193404411941)
            ·
              refine ⟨5900897570104723763327239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31471453707225193404411941 5900897570104723763327239)
              ·
                refine ⟨8851346355157085644990859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5900897570104723763327239 8851346355157085644990859)
                ·
                  refine ⟨13277019532735628467486289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851346355157085644990859 13277019532735628467486289)
                  ·
                    refine ⟨9957764649551721350614717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13277019532735628467486289 9957764649551721350614717)
                    ·
                      refine ⟨3734161743581895506480519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957764649551721350614717 3734161743581895506480519)
                      ·
                        rfl

theorem cell23_7272254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_7272254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272254 prefixEnd_7272254 := by exact prefixLift 7272254
  have htrace : WordTrace (prefixWord ++ tailWord_7272254) baseStart_7272254 baseEnd_7272254 := by
    simpa [prefixWord, tailWord_7272254, baseEnd_7272254] using wordTrace_append hprefix tailTrace_7272254
  have hstable : (prefixWord ++ tailWord_7272254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272254).length < 2 ^ (prefixWord ++ tailWord_7272254).sum := by decide
  have hdescent : baseEnd_7272254 < baseStart_7272254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272284 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7272284 : Nat := 118140960795 + 7272284 * 2 ^ 59
def prefixEnd_7272284 : Nat := 4983230072969 + 3 ^ 40 * 7272284 * 2
def baseEnd_7272284 : Nat := 3734177148001530389105381

theorem tailTrace_7272284 : CollatzResearch.WordTrace tailWord_7272284 prefixEnd_7272284 3734177148001530389105381 := by
  unfold tailWord_7272284
  simp only [CollatzResearch.WordTrace]
  refine ⟨132620993992882275035531953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176827991990509700047375937 132620993992882275035531953)
  ·
    refine ⟨99465745494661706276648965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132620993992882275035531953 99465745494661706276648965)
    ·
      refine ⟨18649827280249069926871681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99465745494661706276648965 18649827280249069926871681)
      ·
        refine ⟨13987370460186802445153761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18649827280249069926871681 13987370460186802445153761)
        ·
          refine ⟨10490527845140101833865321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13987370460186802445153761 10490527845140101833865321)
          ·
            refine ⟨7867895883855076375398991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10490527845140101833865321 7867895883855076375398991)
            ·
              refine ⟨11801843825782614563098487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867895883855076375398991 11801843825782614563098487)
              ·
                refine ⟨17702765738673921844647731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801843825782614563098487 17702765738673921844647731)
                ·
                  refine ⟨26554148608010882766971597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17702765738673921844647731 26554148608010882766971597)
                  ·
                    refine ⟨9957805728004081037614349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26554148608010882766971597 9957805728004081037614349)
                    ·
                      refine ⟨3734177148001530389105381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957805728004081037614349 3734177148001530389105381)
                      ·
                        rfl

theorem cell23_7272284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7272284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272284 prefixEnd_7272284 := by exact prefixLift 7272284
  have htrace : WordTrace (prefixWord ++ tailWord_7272284) baseStart_7272284 baseEnd_7272284 := by
    simpa [prefixWord, tailWord_7272284, baseEnd_7272284] using wordTrace_append hprefix tailTrace_7272284
  have hstable : (prefixWord ++ tailWord_7272284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272284).length < 2 ^ (prefixWord ++ tailWord_7272284).sum := by decide
  have hdescent : baseEnd_7272284 < baseStart_7272284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272293 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7272293 : Nat := 118140960795 + 7272293 * 2 ^ 59
def prefixEnd_7272293 : Nat := 4983230072969 + 3 ^ 40 * 7272293 * 2
def baseEnd_7272293 : Nat := 3734181769327420853892839

theorem tailTrace_7272293 : CollatzResearch.WordTrace tailWord_7272293 prefixEnd_7272293 3734181769327420853892839 := by
  unfold tailWord_7272293
  simp only [CollatzResearch.WordTrace]
  refine ⟨265242316242731944608141533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176828210828487963072094355 265242316242731944608141533)
  ·
    refine ⟨99465868591024479228053075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265242316242731944608141533 99465868591024479228053075)
    ·
      refine ⟨149198802886536718842079613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99465868591024479228053075 149198802886536718842079613)
      ·
        refine ⟨55949551082451269565779855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149198802886536718842079613 55949551082451269565779855)
        ·
          refine ⟨83924326623676904348669783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55949551082451269565779855 83924326623676904348669783)
          ·
            refine ⟨125886489935515356523004675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83924326623676904348669783 125886489935515356523004675)
            ·
              refine ⟨188829734903273034784507013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125886489935515356523004675 188829734903273034784507013)
              ·
                refine ⟨35405575294363694022095065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188829734903273034784507013 35405575294363694022095065)
                ·
                  refine ⟨26554181470772770516571299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35405575294363694022095065 26554181470772770516571299)
                  ·
                    refine ⟨39831272206159155774856949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26554181470772770516571299 39831272206159155774856949)
                    ·
                      refine ⟨3734181769327420853892839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39831272206159155774856949 3734181769327420853892839)
                      ·
                        rfl

theorem cell23_7272293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7272293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272293 prefixEnd_7272293 := by exact prefixLift 7272293
  have htrace : WordTrace (prefixWord ++ tailWord_7272293) baseStart_7272293 baseEnd_7272293 := by
    simpa [prefixWord, tailWord_7272293, baseEnd_7272293] using wordTrace_append hprefix tailTrace_7272293
  have hstable : (prefixWord ++ tailWord_7272293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272293).length < 2 ^ (prefixWord ++ tailWord_7272293).sum := by decide
  have hdescent : baseEnd_7272293 < baseStart_7272293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272383 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_7272383 : Nat := 118140960795 + 7272383 * 2 ^ 59
def prefixEnd_7272383 : Nat := 4983230072969 + 3 ^ 40 * 7272383 * 2
def baseEnd_7272383 : Nat := 3734227982586325501767425

theorem tailTrace_7272383 : CollatzResearch.WordTrace tailWord_7272383 prefixEnd_7272383 3734227982586325501767425 := by
  unfold tailWord_7272383
  simp only [CollatzResearch.WordTrace]
  refine ⟨265245598812405889978917803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176830399208270593319278535 265245598812405889978917803)
  ·
    refine ⟨397868398218608834968376705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265245598812405889978917803 397868398218608834968376705)
    ·
      refine ⟨298401298663956626226282529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397868398218608834968376705 298401298663956626226282529)
      ·
        refine ⟨223800973997967469669711897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298401298663956626226282529 223800973997967469669711897)
        ·
          refine ⟨167850730498475602252283923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223800973997967469669711897 167850730498475602252283923)
          ·
            refine ⟨251776095747713403378425885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167850730498475602252283923 251776095747713403378425885)
            ·
              refine ⟨94416035905392526266909707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251776095747713403378425885 94416035905392526266909707)
              ·
                refine ⟨141624053858088789400364561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94416035905392526266909707 141624053858088789400364561)
                ·
                  refine ⟨106218040393566592050273421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141624053858088789400364561 106218040393566592050273421)
                  ·
                    refine ⟨39831765147587472018852533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106218040393566592050273421 39831765147587472018852533)
                    ·
                      refine ⟨3734227982586325501767425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39831765147587472018852533 3734227982586325501767425)
                      ·
                        rfl

theorem cell23_7272383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_7272383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272383 prefixEnd_7272383 := by exact prefixLift 7272383
  have htrace : WordTrace (prefixWord ++ tailWord_7272383) baseStart_7272383 baseEnd_7272383 := by
    simpa [prefixWord, tailWord_7272383, baseEnd_7272383] using wordTrace_append hprefix tailTrace_7272383
  have hstable : (prefixWord ++ tailWord_7272383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272383).length < 2 ^ (prefixWord ++ tailWord_7272383).sum := by decide
  have hdescent : baseEnd_7272383 < baseStart_7272383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272393 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_7272393 : Nat := 118140960795 + 7272393 * 2 ^ 59
def prefixEnd_7272393 : Nat := 4983230072969 + 3 ^ 40 * 7272393 * 2
def baseEnd_7272393 : Nat := 3734233117392870462642379

theorem tailTrace_7272393 : CollatzResearch.WordTrace tailWord_7272393 prefixEnd_7272393 3734233117392870462642379 := by
  unfold tailWord_7272393
  simp only [CollatzResearch.WordTrace]
  refine ⟨265245963542369661686781833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176830642361579774457854555 265245963542369661686781833)
  ·
    refine ⟨198934472656777246265086375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265245963542369661686781833 198934472656777246265086375)
    ·
      refine ⟨298401708985165869397629563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198934472656777246265086375 298401708985165869397629563)
      ·
        refine ⟨447602563477748804096444345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298401708985165869397629563 447602563477748804096444345)
        ·
          refine ⟨335701922608311603072333259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447602563477748804096444345 335701922608311603072333259)
          ·
            refine ⟨503552883912467404608499889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335701922608311603072333259 503552883912467404608499889)
            ·
              refine ⟨377664662934350553456374917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503552883912467404608499889 377664662934350553456374917)
              ·
                refine ⟨70812124300190728773070297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377664662934350553456374917 70812124300190728773070297)
                ·
                  refine ⟨53109093225143046579802723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70812124300190728773070297 53109093225143046579802723)
                  ·
                    refine ⟨79663639837714569869704085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53109093225143046579802723 79663639837714569869704085)
                    ·
                      refine ⟨3734233117392870462642379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79663639837714569869704085 3734233117392870462642379)
                      ·
                        rfl

theorem cell23_7272393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_7272393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272393 prefixEnd_7272393 := by exact prefixLift 7272393
  have htrace : WordTrace (prefixWord ++ tailWord_7272393) baseStart_7272393 baseEnd_7272393 := by
    simpa [prefixWord, tailWord_7272393, baseEnd_7272393] using wordTrace_append hprefix tailTrace_7272393
  have hstable : (prefixWord ++ tailWord_7272393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272393).length < 2 ^ (prefixWord ++ tailWord_7272393).sum := by decide
  have hdescent : baseEnd_7272393 < baseStart_7272393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272400 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_7272400 : Nat := 118140960795 + 7272400 * 2 ^ 59
def prefixEnd_7272400 : Nat := 4983230072969 + 3 ^ 40 * 7272400 * 2
def baseEnd_7272400 : Nat := 3734236711757451935254847

theorem tailTrace_7272400 : CollatzResearch.WordTrace tailWord_7272400 prefixEnd_7272400 3734236711757451935254847 := by
  unfold tailWord_7272400
  simp only [CollatzResearch.WordTrace]
  refine ⟨132623109426672150941143327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176830812568896201254857769 132623109426672150941143327)
  ·
    refine ⟨198934664140008226411714991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132623109426672150941143327 198934664140008226411714991)
    ·
      refine ⟨298401996210012339617572487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198934664140008226411714991 298401996210012339617572487)
      ·
        refine ⟨447602994315018509426358731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298401996210012339617572487 447602994315018509426358731)
        ·
          refine ⟨671404491472527764139538097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447602994315018509426358731 671404491472527764139538097)
          ·
            refine ⟨503553368604395823104653573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671404491472527764139538097 503553368604395823104653573)
            ·
              refine ⟨94416256613324216832122545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503553368604395823104653573 94416256613324216832122545)
              ·
                refine ⟨70812192459993162624091909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94416256613324216832122545 70812192459993162624091909)
                ·
                  refine ⟨13277286086248717992017233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70812192459993162624091909 13277286086248717992017233)
                  ·
                    refine ⟨9957964564686538494012925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13277286086248717992017233 9957964564686538494012925)
                    ·
                      refine ⟨3734236711757451935254847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957964564686538494012925 3734236711757451935254847)
                      ·
                        rfl

theorem cell23_7272400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_7272400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272400 prefixEnd_7272400 := by exact prefixLift 7272400
  have htrace : WordTrace (prefixWord ++ tailWord_7272400) baseStart_7272400 baseEnd_7272400 := by
    simpa [prefixWord, tailWord_7272400, baseEnd_7272400] using wordTrace_append hprefix tailTrace_7272400
  have hstable : (prefixWord ++ tailWord_7272400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272400).length < 2 ^ (prefixWord ++ tailWord_7272400).sum := by decide
  have hdescent : baseEnd_7272400 < baseStart_7272400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272417 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_7272417 : Nat := 118140960795 + 7272417 * 2 ^ 59
def prefixEnd_7272417 : Nat := 4983230072969 + 3 ^ 40 * 7272417 * 2
def baseEnd_7272417 : Nat := 3734245440928578368742269

theorem tailTrace_7272417 : CollatzResearch.WordTrace tailWord_7272417 prefixEnd_7272417 3734245440928578368742269 := by
  unfold tailWord_7272417
  simp only [CollatzResearch.WordTrace]
  refine ⟨265246838894282713785655505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176831225929521809190437003 265246838894282713785655505)
  ·
    refine ⟨198935129170712035339241629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265246838894282713785655505 198935129170712035339241629)
    ·
      refine ⟨74600673439017013252215611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198935129170712035339241629 74600673439017013252215611)
      ·
        refine ⟨111901010158525519878323417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74600673439017013252215611 111901010158525519878323417)
        ·
          refine ⟨83925757618894139908742563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111901010158525519878323417 83925757618894139908742563)
          ·
            refine ⟨125888636428341209863113845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83925757618894139908742563 125888636428341209863113845)
            ·
              refine ⟨11802059665156988424666923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125888636428341209863113845 11802059665156988424666923)
              ·
                refine ⟨17703089497735482637000385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802059665156988424666923 17703089497735482637000385)
                ·
                  refine ⟨13277317123301611977750289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17703089497735482637000385 13277317123301611977750289)
                  ·
                    refine ⟨9957987842476208983312717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13277317123301611977750289 9957987842476208983312717)
                    ·
                      refine ⟨3734245440928578368742269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9957987842476208983312717 3734245440928578368742269)
                      ·
                        rfl

theorem cell23_7272417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_7272417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272417 prefixEnd_7272417 := by exact prefixLift 7272417
  have htrace : WordTrace (prefixWord ++ tailWord_7272417) baseStart_7272417 baseEnd_7272417 := by
    simpa [prefixWord, tailWord_7272417, baseEnd_7272417] using wordTrace_append hprefix tailTrace_7272417
  have hstable : (prefixWord ++ tailWord_7272417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272417).length < 2 ^ (prefixWord ++ tailWord_7272417).sum := by decide
  have hdescent : baseEnd_7272417 < baseStart_7272417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272497 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_7272497 : Nat := 118140960795 + 7272497 * 2 ^ 59
def prefixEnd_7272497 : Nat := 4983230072969 + 3 ^ 40 * 7272497 * 2
def baseEnd_7272497 : Nat := 1244762173126979351913967

theorem tailTrace_7272497 : CollatzResearch.WordTrace tailWord_7272497 prefixEnd_7272497 1244762173126979351913967 := by
  unfold tailWord_7272497
  simp only [CollatzResearch.WordTrace]
  refine ⟨265249756733992887448567745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176833171155995258299045163 265249756733992887448567745)
  ·
    refine ⟨198937317550494665586425809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265249756733992887448567745 198937317550494665586425809)
    ·
      refine ⟨149202988162870999189819357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198937317550494665586425809 149202988162870999189819357)
      ·
        refine ⟨55951120561076624696182259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149202988162870999189819357 55951120561076624696182259)
        ·
          refine ⟨83926680841614937044273389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55951120561076624696182259 83926680841614937044273389)
          ·
            refine ⟨31472505315605601391602521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83926680841614937044273389 31472505315605601391602521)
            ·
              refine ⟨23604378986704201043701891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31472505315605601391602521 23604378986704201043701891)
              ·
                refine ⟨35406568480056301565552837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23604378986704201043701891 35406568480056301565552837)
                ·
                  refine ⟨6638731590010556543541157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35406568480056301565552837 6638731590010556543541157)
                  ·
                    refine ⟨1244762173126979351913967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6638731590010556543541157 1244762173126979351913967)
                    ·
                      rfl

theorem cell23_7272497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_7272497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272497 prefixEnd_7272497 := by exact prefixLift 7272497
  have htrace : WordTrace (prefixWord ++ tailWord_7272497) baseStart_7272497 baseEnd_7272497 := by
    simpa [prefixWord, tailWord_7272497, baseEnd_7272497] using wordTrace_append hprefix tailTrace_7272497
  have hstable : (prefixWord ++ tailWord_7272497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272497).length < 2 ^ (prefixWord ++ tailWord_7272497).sum := by decide
  have hdescent : baseEnd_7272497 < baseStart_7272497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272498 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_7272498 : Nat := 118140960795 + 7272498 * 2 ^ 59
def prefixEnd_7272498 : Nat := 4983230072969 + 3 ^ 40 * 7272498 * 2
def baseEnd_7272498 : Nat := 3734287032861592551829397

theorem tailTrace_7272498 : CollatzResearch.WordTrace tailWord_7272498 prefixEnd_7272498 3734287032861592551829397 := by
  unfold tailWord_7272498
  simp only [CollatzResearch.WordTrace]
  refine ⟨66312448301747316154838537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176833195471326176412902765 66312448301747316154838537)
  ·
    refine ⟨49734336226310487116128903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66312448301747316154838537 49734336226310487116128903)
    ·
      refine ⟨74601504339465730674193355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49734336226310487116128903 74601504339465730674193355)
      ·
        refine ⟨111902256509198596011290033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74601504339465730674193355 111902256509198596011290033)
        ·
          refine ⟨83926692381898947008467525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111902256509198596011290033 83926692381898947008467525)
          ·
            refine ⟨15736254821606052564087661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83926692381898947008467525 15736254821606052564087661)
            ·
              refine ⟨5901095558102269711532873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15736254821606052564087661 5901095558102269711532873)
              ·
                refine ⟨4425821668576702283649655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901095558102269711532873 4425821668576702283649655)
                ·
                  refine ⟨6638732502865053425474483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4425821668576702283649655 6638732502865053425474483)
                  ·
                    refine ⟨9958098754297580138211725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638732502865053425474483 9958098754297580138211725)
                    ·
                      refine ⟨3734287032861592551829397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958098754297580138211725 3734287032861592551829397)
                      ·
                        rfl

theorem cell23_7272498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_7272498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272498 prefixEnd_7272498 := by exact prefixLift 7272498
  have htrace : WordTrace (prefixWord ++ tailWord_7272498) baseStart_7272498 baseEnd_7272498 := by
    simpa [prefixWord, tailWord_7272498, baseEnd_7272498] using wordTrace_append hprefix tailTrace_7272498
  have hstable : (prefixWord ++ tailWord_7272498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272498).length < 2 ^ (prefixWord ++ tailWord_7272498).sum := by decide
  have hdescent : baseEnd_7272498 < baseStart_7272498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272524 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7272524 : Nat := 118140960795 + 7272524 * 2 ^ 59
def prefixEnd_7272524 : Nat := 4983230072969 + 3 ^ 40 * 7272524 * 2
def baseEnd_7272524 : Nat := 3734300383358609450104277

theorem tailTrace_7272524 : CollatzResearch.WordTrace tailWord_7272524 prefixEnd_7272524 3734300383358609450104277 := by
  unfold tailWord_7272524
  simp only [CollatzResearch.WordTrace]
  refine ⟨132625370752447535529900313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176833827669930047373200417 132625370752447535529900313)
  ·
    refine ⟨99469028064335651647425235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132625370752447535529900313 99469028064335651647425235)
    ·
      refine ⟨149203542096503477471137853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99469028064335651647425235 149203542096503477471137853)
      ·
        refine ⟨55951328286188804051676695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149203542096503477471137853 55951328286188804051676695)
        ·
          refine ⟨83926992429283206077515043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55951328286188804051676695 83926992429283206077515043)
          ·
            refine ⟨125890488643924809116272565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83926992429283206077515043 125890488643924809116272565)
            ·
              refine ⟨11802233310367950854650553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125890488643924809116272565 11802233310367950854650553)
              ·
                refine ⟨8851674982775963140987915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11802233310367950854650553 8851674982775963140987915)
                ·
                  refine ⟨13277512474163944711481873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851674982775963140987915 13277512474163944711481873)
                  ·
                    refine ⟨9958134355622958533611405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13277512474163944711481873 9958134355622958533611405)
                    ·
                      refine ⟨3734300383358609450104277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958134355622958533611405 3734300383358609450104277)
                      ·
                        rfl

theorem cell23_7272524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7272524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272524 prefixEnd_7272524 := by exact prefixLift 7272524
  have htrace : WordTrace (prefixWord ++ tailWord_7272524) baseStart_7272524 baseEnd_7272524 := by
    simpa [prefixWord, tailWord_7272524, baseEnd_7272524] using wordTrace_append hprefix tailTrace_7272524
  have hstable : (prefixWord ++ tailWord_7272524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272524).length < 2 ^ (prefixWord ++ tailWord_7272524).sum := by decide
  have hdescent : baseEnd_7272524 < baseStart_7272524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272537 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_7272537 : Nat := 118140960795 + 7272537 * 2 ^ 59
def prefixEnd_7272537 : Nat := 4983230072969 + 3 ^ 40 * 7272537 * 2
def baseEnd_7272537 : Nat := 3734307058607117899241717

theorem tailTrace_7272537 : CollatzResearch.WordTrace tailWord_7272537 prefixEnd_7272537 3734307058607117899241717 := by
  unfold tailWord_7272537
  simp only [CollatzResearch.WordTrace]
  refine ⟨265251215653847974280023865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176834143769231982853349243 265251215653847974280023865)
  ·
    refine ⟨198938411740385980710017899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265251215653847974280023865 198938411740385980710017899)
    ·
      refine ⟨298407617610578971065026849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198938411740385980710017899 298407617610578971065026849)
      ·
        refine ⟨223805713207934228298770137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298407617610578971065026849 223805713207934228298770137)
        ·
          refine ⟨167854284905950671224077603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223805713207934228298770137 167854284905950671224077603)
          ·
            refine ⟨251781427358926006836116405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167854284905950671224077603 251781427358926006836116405)
            ·
              refine ⟨23604508814899313140885913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251781427358926006836116405 23604508814899313140885913)
              ·
                refine ⟨17703381611174484855664435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23604508814899313140885913 17703381611174484855664435)
                ·
                  refine ⟨26555072416761727283496653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17703381611174484855664435 26555072416761727283496653)
                  ·
                    refine ⟨9958152156285647731311245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26555072416761727283496653 9958152156285647731311245)
                    ·
                      refine ⟨3734307058607117899241717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958152156285647731311245 3734307058607117899241717)
                      ·
                        rfl

theorem cell23_7272537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_7272537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272537 prefixEnd_7272537 := by exact prefixLift 7272537
  have htrace : WordTrace (prefixWord ++ tailWord_7272537) baseStart_7272537 baseEnd_7272537 := by
    simpa [prefixWord, tailWord_7272537, baseEnd_7272537] using wordTrace_append hprefix tailTrace_7272537
  have hstable : (prefixWord ++ tailWord_7272537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272537).length < 2 ^ (prefixWord ++ tailWord_7272537).sum := by decide
  have hdescent : baseEnd_7272537 < baseStart_7272537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272541 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7272541 : Nat := 118140960795 + 7272541 * 2 ^ 59
def prefixEnd_7272541 : Nat := 4983230072969 + 3 ^ 40 * 7272541 * 2
def baseEnd_7272541 : Nat := 3734309112529735883591699

theorem tailTrace_7272541 : CollatzResearch.WordTrace tailWord_7272541 prefixEnd_7272541 3734309112529735883591699 := by
  unfold tailWord_7272541
  simp only [CollatzResearch.WordTrace]
  refine ⟨265251361545833482963169477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176834241030555655308779651 265251361545833482963169477)
  ·
    refine ⟨49734630289843778055594277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265251361545833482963169477 49734630289843778055594277)
    ·
      refine ⟨9325243179345708385423927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49734630289843778055594277 9325243179345708385423927)
      ·
        refine ⟨13987864769018562578135891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9325243179345708385423927 13987864769018562578135891)
        ·
          refine ⟨20981797153527843867203837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13987864769018562578135891 20981797153527843867203837)
          ·
            refine ⟨7868173932572941450201439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20981797153527843867203837 7868173932572941450201439)
            ·
              refine ⟨11802260898859412175302159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868173932572941450201439 11802260898859412175302159)
              ·
                refine ⟨17703391348289118262953239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802260898859412175302159 17703391348289118262953239)
                ·
                  refine ⟨26555087022433677394429859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17703391348289118262953239 26555087022433677394429859)
                  ·
                    refine ⟨39832630533650516091644789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26555087022433677394429859 39832630533650516091644789)
                    ·
                      refine ⟨3734309112529735883591699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39832630533650516091644789 3734309112529735883591699)
                      ·
                        rfl

theorem cell23_7272541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7272541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272541 prefixEnd_7272541 := by exact prefixLift 7272541
  have htrace : WordTrace (prefixWord ++ tailWord_7272541) baseStart_7272541 baseEnd_7272541 := by
    simpa [prefixWord, tailWord_7272541, baseEnd_7272541] using wordTrace_append hprefix tailTrace_7272541
  have hstable : (prefixWord ++ tailWord_7272541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272541).length < 2 ^ (prefixWord ++ tailWord_7272541).sum := by decide
  have hdescent : baseEnd_7272541 < baseStart_7272541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272622 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7272622 : Nat := 118140960795 + 7272622 * 2 ^ 59
def prefixEnd_7272622 : Nat := 4983230072969 + 3 ^ 40 * 7272622 * 2
def baseEnd_7272622 : Nat := 3734350704462750066678827

theorem tailTrace_7272622 : CollatzResearch.WordTrace tailWord_7272622 prefixEnd_7272622 3734350704462750066678827 := by
  unfold tailWord_7272622
  simp only [CollatzResearch.WordTrace]
  refine ⟨33156789482317504224608515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176836210572360022531245413 33156789482317504224608515)
  ·
    refine ⟨49735184223476256336912773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33156789482317504224608515 49735184223476256336912773)
    ·
      refine ⟨9325347041901798063171145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49735184223476256336912773 9325347041901798063171145)
      ·
        refine ⟨6994010281426348547378359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325347041901798063171145 6994010281426348547378359)
        ·
          refine ⟨10491015422139522821067539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994010281426348547378359 10491015422139522821067539)
          ·
            refine ⟨15736523133209284231601309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491015422139522821067539 15736523133209284231601309)
            ·
              refine ⟨5901196174953481586850491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15736523133209284231601309 5901196174953481586850491)
              ·
                refine ⟨8851794262430222380275737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901196174953481586850491 8851794262430222380275737)
                ·
                  refine ⟨6638845696822666785206803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8851794262430222380275737 6638845696822666785206803)
                  ·
                    refine ⟨9958268545234000177810205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6638845696822666785206803 9958268545234000177810205)
                    ·
                      refine ⟨3734350704462750066678827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958268545234000177810205 3734350704462750066678827)
                      ·
                        rfl

theorem cell23_7272622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7272622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272622 prefixEnd_7272622 := by exact prefixLift 7272622
  have htrace : WordTrace (prefixWord ++ tailWord_7272622) baseStart_7272622 baseEnd_7272622 := by
    simpa [prefixWord, tailWord_7272622, baseEnd_7272622] using wordTrace_append hprefix tailTrace_7272622
  have hstable : (prefixWord ++ tailWord_7272622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272622).length < 2 ^ (prefixWord ++ tailWord_7272622).sum := by decide
  have hdescent : baseEnd_7272622 < baseStart_7272622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272664 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_7272664 : Nat := 118140960795 + 7272664 * 2 ^ 59
def prefixEnd_7272664 : Nat := 4983230072969 + 3 ^ 40 * 7272664 * 2
def baseEnd_7272664 : Nat := 1244790756883412967451211

theorem tailTrace_7272664 : CollatzResearch.WordTrace tailWord_7272664 prefixEnd_7272664 1244790756883412967451211 := by
  unfold tailWord_7272664
  simp only [CollatzResearch.WordTrace]
  refine ⟨132627923862193937484948523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176837231816258583313264697 132627923862193937484948523)
  ·
    refine ⟨198941885793290906227422785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132627923862193937484948523 198941885793290906227422785)
    ·
      refine ⟨149206414344968179670567089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198941885793290906227422785 149206414344968179670567089)
      ·
        refine ⟨111904810758726134752925317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149206414344968179670567089 111904810758726134752925317)
        ·
          refine ⟨20982152017261150266173497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111904810758726134752925317 20982152017261150266173497)
          ·
            refine ⟨15736614012945862699630123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20982152017261150266173497 15736614012945862699630123)
            ·
              refine ⟨23604921019418794049445185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15736614012945862699630123 23604921019418794049445185)
              ·
                refine ⟨17703690764564095537083889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23604921019418794049445185 17703690764564095537083889)
                ·
                  refine ⟨13277768073423071652812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17703690764564095537083889 13277768073423071652812917)
                  ·
                    refine ⟨1244790756883412967451211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13277768073423071652812917 1244790756883412967451211)
                    ·
                      rfl

theorem cell23_7272664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_7272664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272664 prefixEnd_7272664 := by exact prefixLift 7272664
  have htrace : WordTrace (prefixWord ++ tailWord_7272664) baseStart_7272664 baseEnd_7272664 := by
    simpa [prefixWord, tailWord_7272664, baseEnd_7272664] using wordTrace_append hprefix tailTrace_7272664
  have hstable : (prefixWord ++ tailWord_7272664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272664).length < 2 ^ (prefixWord ++ tailWord_7272664).sum := by decide
  have hdescent : baseEnd_7272664 < baseStart_7272664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272667 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4]
def baseStart_7272667 : Nat := 118140960795 + 7272667 * 2 ^ 59
def prefixEnd_7272667 : Nat := 4983230072969 + 3 ^ 40 * 7272667 * 2
def baseEnd_7272667 : Nat := 3734373811092202390616119

theorem tailTrace_7272667 : CollatzResearch.WordTrace tailWord_7272667 prefixEnd_7272667 3734373811092202390616119 := by
  unfold tailWord_7272667
  simp only [CollatzResearch.WordTrace]
  refine ⟨265255957143377006482256255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176837304762251337654837503 265255957143377006482256255)
  ·
    refine ⟨397883935715065509723384383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265255957143377006482256255 397883935715065509723384383)
    ·
      refine ⟨596825903572598264585076575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397883935715065509723384383 596825903572598264585076575)
      ·
        refine ⟨895238855358897396877614863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596825903572598264585076575 895238855358897396877614863)
        ·
          refine ⟨1342858283038346095316422295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895238855358897396877614863 1342858283038346095316422295)
          ·
            refine ⟨2014287424557519142974633443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342858283038346095316422295 2014287424557519142974633443)
            ·
              refine ⟨3021431136836278714461950165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014287424557519142974633443 3021431136836278714461950165)
              ·
                refine ⟨70814792269600282370201957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3021431136836278714461950165 70814792269600282370201957)
                ·
                  refine ⟨13277773550550052944412867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70814792269600282370201957 13277773550550052944412867)
                  ·
                    refine ⟨19916660325825079416619301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13277773550550052944412867 19916660325825079416619301)
                    ·
                      refine ⟨3734373811092202390616119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19916660325825079416619301 3734373811092202390616119)
                      ·
                        rfl

theorem cell23_7272667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 4].length) (baseStart_7272667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272667 prefixEnd_7272667 := by exact prefixLift 7272667
  have htrace : WordTrace (prefixWord ++ tailWord_7272667) baseStart_7272667 baseEnd_7272667 := by
    simpa [prefixWord, tailWord_7272667, baseEnd_7272667] using wordTrace_append hprefix tailTrace_7272667
  have hstable : (prefixWord ++ tailWord_7272667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272667).length < 2 ^ (prefixWord ++ tailWord_7272667).sum := by decide
  have hdescent : baseEnd_7272667 < baseStart_7272667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272668 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 7]
def baseStart_7272668 : Nat := 118140960795 + 7272668 * 2 ^ 59
def prefixEnd_7272668 : Nat := 4983230072969 + 3 ^ 40 * 7272668 * 2
def baseEnd_7272668 : Nat := 414930480508095209633735

theorem tailTrace_7272668 : CollatzResearch.WordTrace tailWord_7272668 prefixEnd_7272668 414930480508095209633735 := by
  unfold tailWord_7272668
  simp only [CollatzResearch.WordTrace]
  refine ⟨132627996808186691826521329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176837329077582255768695105 132627996808186691826521329)
  ·
    refine ⟨99470997606140018869890997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132627996808186691826521329 99470997606140018869890997)
    ·
      refine ⟨9325406025575626769052281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99470997606140018869890997 9325406025575626769052281)
      ·
        refine ⟨6994054519181720076789211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325406025575626769052281 6994054519181720076789211)
        ·
          refine ⟨10491081778772580115183817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994054519181720076789211 10491081778772580115183817)
          ·
            refine ⟨7868311334079435086387863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10491081778772580115183817 7868311334079435086387863)
            ·
              refine ⟨11802467001119152629581795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868311334079435086387863 11802467001119152629581795)
              ·
                refine ⟨17703700501678728944372693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802467001119152629581795 17703700501678728944372693)
                ·
                  refine ⟨414930480508095209633735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17703700501678728944372693 414930480508095209633735)
                  ·
                    rfl

theorem cell23_7272668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_7272668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272668 prefixEnd_7272668 := by exact prefixLift 7272668
  have htrace : WordTrace (prefixWord ++ tailWord_7272668) baseStart_7272668 baseEnd_7272668 := by
    simpa [prefixWord, tailWord_7272668, baseEnd_7272668] using wordTrace_append hprefix tailTrace_7272668
  have hstable : (prefixWord ++ tailWord_7272668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272668).length < 2 ^ (prefixWord ++ tailWord_7272668).sum := by decide
  have hdescent : baseEnd_7272668 < baseStart_7272668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272684 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_7272684 : Nat := 118140960795 + 7272684 * 2 ^ 59
def prefixEnd_7272684 : Nat := 4983230072969 + 3 ^ 40 * 7272684 * 2
def baseEnd_7272684 : Nat := 3734382540263328824103541

theorem tailTrace_7272684 : CollatzResearch.WordTrace tailWord_7272684 prefixEnd_7272684 3734382540263328824103541 := by
  unfold tailWord_7272684
  simp only [CollatzResearch.WordTrace]
  refine ⟨132628288592157709192812553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176837718122876945590416737 132628288592157709192812553)
  ·
    refine ⟨99471216444118281894609415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132628288592157709192812553 99471216444118281894609415)
    ·
      refine ⟨149206824666177422841914123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99471216444118281894609415 149206824666177422841914123)
      ·
        refine ⟨223810236999266134262871185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149206824666177422841914123 223810236999266134262871185)
        ·
          refine ⟨167857677749449600697153389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223810236999266134262871185 167857677749449600697153389)
          ·
            refine ⟨62946629156043600261432521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167857677749449600697153389 62946629156043600261432521)
            ·
              refine ⟨47209971867032700196074391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62946629156043600261432521 47209971867032700196074391)
              ·
                refine ⟨70814957800549050294111587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47209971867032700196074391 70814957800549050294111587)
                ·
                  refine ⟨106222436700823575441167381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70814957800549050294111587 106222436700823575441167381)
                  ·
                    refine ⟨4979176720351105098804721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106222436700823575441167381 4979176720351105098804721)
                    ·
                      refine ⟨3734382540263328824103541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979176720351105098804721 3734382540263328824103541)
                      ·
                        rfl

theorem cell23_7272684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_7272684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272684 prefixEnd_7272684 := by exact prefixLift 7272684
  have htrace : WordTrace (prefixWord ++ tailWord_7272684) baseStart_7272684 baseEnd_7272684 := by
    simpa [prefixWord, tailWord_7272684, baseEnd_7272684] using wordTrace_append hprefix tailTrace_7272684
  have hstable : (prefixWord ++ tailWord_7272684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272684).length < 2 ^ (prefixWord ++ tailWord_7272684).sum := by decide
  have hdescent : baseEnd_7272684 < baseStart_7272684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272704 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_7272704 : Nat := 118140960795 + 7272704 * 2 ^ 59
def prefixEnd_7272704 : Nat := 4983230072969 + 3 ^ 40 * 7272704 * 2
def baseEnd_7272704 : Nat := 3734392809876418745853449

theorem tailTrace_7272704 : CollatzResearch.WordTrace tailWord_7272704 prefixEnd_7272704 3734392809876418745853449 := by
  unfold tailWord_7272704
  simp only [CollatzResearch.WordTrace]
  refine ⟨132628653322121480900676583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176838204429495307867568777 132628653322121480900676583)
  ·
    refine ⟨198942979983182221351014875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132628653322121480900676583 198942979983182221351014875)
    ·
      refine ⟨298414469974773332026522313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198942979983182221351014875 298414469974773332026522313)
      ·
        refine ⟨223810852481079999019891735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298414469974773332026522313 223810852481079999019891735)
        ·
          refine ⟨335716278721619998529837603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223810852481079999019891735 335716278721619998529837603)
          ·
            refine ⟨503574418082429997794756405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335716278721619998529837603 503574418082429997794756405)
            ·
              refine ⟨47210101695227812293258413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 503574418082429997794756405 47210101695227812293258413)
              ·
                refine ⟨17703788135710429609971905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47210101695227812293258413 17703788135710429609971905)
                ·
                  refine ⟨13277841101782822207478929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17703788135710429609971905 13277841101782822207478929)
                  ·
                    refine ⟨9958380826337116655609197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13277841101782822207478929 9958380826337116655609197)
                    ·
                      refine ⟨3734392809876418745853449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958380826337116655609197 3734392809876418745853449)
                      ·
                        rfl

theorem cell23_7272704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_7272704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272704 prefixEnd_7272704 := by exact prefixLift 7272704
  have htrace : WordTrace (prefixWord ++ tailWord_7272704) baseStart_7272704 baseEnd_7272704 := by
    simpa [prefixWord, tailWord_7272704, baseEnd_7272704] using wordTrace_append hprefix tailTrace_7272704
  have hstable : (prefixWord ++ tailWord_7272704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272704).length < 2 ^ (prefixWord ++ tailWord_7272704).sum := by decide
  have hdescent : baseEnd_7272704 < baseStart_7272704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272771 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 1, 5]
def baseStart_7272771 : Nat := 118140960795 + 7272771 * 2 ^ 59
def prefixEnd_7272771 : Nat := 4983230072969 + 3 ^ 40 * 7272771 * 2
def baseEnd_7272771 : Nat := 1244809071026756661238547

theorem tailTrace_7272771 : CollatzResearch.WordTrace tailWord_7272771 prefixEnd_7272771 1244809071026756661238547 := by
  unfold tailWord_7272771
  simp only [CollatzResearch.WordTrace]
  refine ⟨265259750335000232244042167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176839833556666821496028111 265259750335000232244042167)
  ·
    refine ⟨397889625502500348366063251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265259750335000232244042167 397889625502500348366063251)
    ·
      refine ⟨596834438253750522549094877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397889625502500348366063251 596834438253750522549094877)
      ·
        refine ⟨223812914345156445955910579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596834438253750522549094877 223812914345156445955910579)
        ·
          refine ⟨335719371517734668933865869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223812914345156445955910579 335719371517734668933865869)
          ·
            refine ⟨125894764319150500850199701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335719371517734668933865869 125894764319150500850199701)
            ·
              refine ⟨5901317077460179727353111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125894764319150500850199701 5901317077460179727353111)
              ·
                refine ⟨8851975616190269591029667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901317077460179727353111 8851975616190269591029667)
                ·
                  refine ⟨13277963424285404386544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8851975616190269591029667 13277963424285404386544501)
                  ·
                    refine ⟨1244809071026756661238547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13277963424285404386544501 1244809071026756661238547)
                    ·
                      rfl

theorem cell23_7272771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 5].length) (baseStart_7272771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272771 prefixEnd_7272771 := by exact prefixLift 7272771
  have htrace : WordTrace (prefixWord ++ tailWord_7272771) baseStart_7272771 baseEnd_7272771 := by
    simpa [prefixWord, tailWord_7272771, baseEnd_7272771] using wordTrace_append hprefix tailTrace_7272771
  have hstable : (prefixWord ++ tailWord_7272771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272771).length < 2 ^ (prefixWord ++ tailWord_7272771).sum := by decide
  have hdescent : baseEnd_7272771 < baseStart_7272771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272804 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_7272804 : Nat := 118140960795 + 7272804 * 2 ^ 59
def prefixEnd_7272804 : Nat := 4983230072969 + 3 ^ 40 * 7272804 * 2
def baseEnd_7272804 : Nat := 3734444157941868354602989

theorem tailTrace_7272804 : CollatzResearch.WordTrace tailWord_7272804 prefixEnd_7272804 3734444157941868354602989 := by
  unfold tailWord_7272804
  simp only [CollatzResearch.WordTrace]
  refine ⟨132630476971940339439996733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176840635962587119253328977 132630476971940339439996733)
  ·
    refine ⟨49736428864477627289998775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132630476971940339439996733 49736428864477627289998775)
    ·
      refine ⟨74604643296716440934998163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49736428864477627289998775 74604643296716440934998163)
      ·
        refine ⟨111906964945074661402497245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74604643296716440934998163 111906964945074661402497245)
        ·
          refine ⟨41965111854402998025936467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111906964945074661402497245 41965111854402998025936467)
          ·
            refine ⟨62947667781604497038904701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41965111854402998025936467 62947667781604497038904701)
            ·
              refine ⟨23605375418101686389589263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62947667781604497038904701 23605375418101686389589263)
              ·
                refine ⟨35408063127152529584383895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23605375418101686389589263 35408063127152529584383895)
                ·
                  refine ⟨53112094690728794376575843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35408063127152529584383895 53112094690728794376575843)
                  ·
                    refine ⟨79668142036093191564863765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53112094690728794376575843 79668142036093191564863765)
                    ·
                      refine ⟨3734444157941868354602989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79668142036093191564863765 3734444157941868354602989)
                      ·
                        rfl

theorem cell23_7272804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_7272804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272804 prefixEnd_7272804 := by exact prefixLift 7272804
  have htrace : WordTrace (prefixWord ++ tailWord_7272804) baseStart_7272804 baseEnd_7272804 := by
    simpa [prefixWord, tailWord_7272804, baseEnd_7272804] using wordTrace_append hprefix tailTrace_7272804
  have hstable : (prefixWord ++ tailWord_7272804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272804).length < 2 ^ (prefixWord ++ tailWord_7272804).sum := by decide
  have hdescent : baseEnd_7272804 < baseStart_7272804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272808 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7272808 : Nat := 118140960795 + 7272808 * 2 ^ 59
def prefixEnd_7272808 : Nat := 4983230072969 + 3 ^ 40 * 7272808 * 2
def baseEnd_7272808 : Nat := 3734446211864486338952971

theorem tailTrace_7272808 : CollatzResearch.WordTrace tailWord_7272808 prefixEnd_7272808 3734446211864486338952971 := by
  unfold tailWord_7272808
  simp only [CollatzResearch.WordTrace]
  refine ⟨132630549917933093781569539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176840733223910791708759385 132630549917933093781569539)
  ·
    refine ⟨198945824876899640672354309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132630549917933093781569539 198945824876899640672354309)
    ·
      refine ⟨37302342164418682626066433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198945824876899640672354309 37302342164418682626066433)
      ·
        refine ⟨27976756623314011969549825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37302342164418682626066433 27976756623314011969549825)
        ·
          refine ⟨20982567467485508977162369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27976756623314011969549825 20982567467485508977162369)
          ·
            refine ⟨15736925600614131732871777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20982567467485508977162369 15736925600614131732871777)
            ·
              refine ⟨11802694200460598799653833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15736925600614131732871777 11802694200460598799653833)
              ·
                refine ⟨8852020650345449099740375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11802694200460598799653833 8852020650345449099740375)
                ·
                  refine ⟨13278030975518173649610563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8852020650345449099740375 13278030975518173649610563)
                  ·
                    refine ⟨19917046463277260474415845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13278030975518173649610563 19917046463277260474415845)
                    ·
                      refine ⟨3734446211864486338952971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19917046463277260474415845 3734446211864486338952971)
                      ·
                        rfl

theorem cell23_7272808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7272808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272808 prefixEnd_7272808 := by exact prefixLift 7272808
  have htrace : WordTrace (prefixWord ++ tailWord_7272808) baseStart_7272808 baseEnd_7272808 := by
    simpa [prefixWord, tailWord_7272808, baseEnd_7272808] using wordTrace_append hprefix tailTrace_7272808
  have hstable : (prefixWord ++ tailWord_7272808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272808).length < 2 ^ (prefixWord ++ tailWord_7272808).sum := by decide
  have hdescent : baseEnd_7272808 < baseStart_7272808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272852 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7272852 : Nat := 118140960795 + 7272852 * 2 ^ 59
def prefixEnd_7272852 : Nat := 4983230072969 + 3 ^ 40 * 7272852 * 2
def baseEnd_7272852 : Nat := 1244822935004428055600923

theorem tailTrace_7272852 : CollatzResearch.WordTrace tailWord_7272852 prefixEnd_7272852 1244822935004428055600923 := by
  unfold tailWord_7272852
  simp only [CollatzResearch.WordTrace]
  refine ⟨132631352323853391538870405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176841803098471188718493873 132631352323853391538870405)
  ·
    refine ⟨24868378560722510913538201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132631352323853391538870405 24868378560722510913538201)
    ·
      refine ⟨18651283920541883185153651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24868378560722510913538201 18651283920541883185153651)
      ·
        refine ⟨27976925880812824777730477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651283920541883185153651 27976925880812824777730477)
        ·
          refine ⟨10491347205304809291648929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27976925880812824777730477 10491347205304809291648929)
          ·
            refine ⟨7868510403978606968736697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10491347205304809291648929 7868510403978606968736697)
            ·
              refine ⟨5901382802983955226552523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7868510403978606968736697 5901382802983955226552523)
              ·
                refine ⟨8852074204475932839828785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5901382802983955226552523 8852074204475932839828785)
                ·
                  refine ⟨6639055653356949629871589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8852074204475932839828785 6639055653356949629871589)
                  ·
                    refine ⟨1244822935004428055600923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6639055653356949629871589 1244822935004428055600923)
                    ·
                      rfl

theorem cell23_7272852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7272852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272852 prefixEnd_7272852 := by exact prefixLift 7272852
  have htrace : WordTrace (prefixWord ++ tailWord_7272852) baseStart_7272852 baseEnd_7272852 := by
    simpa [prefixWord, tailWord_7272852, baseEnd_7272852] using wordTrace_append hprefix tailTrace_7272852
  have hstable : (prefixWord ++ tailWord_7272852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272852).length < 2 ^ (prefixWord ++ tailWord_7272852).sum := by decide
  have hdescent : baseEnd_7272852 < baseStart_7272852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272862 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7272862 : Nat := 118140960795 + 7272862 * 2 ^ 59
def prefixEnd_7272862 : Nat := 4983230072969 + 3 ^ 40 * 7272862 * 2
def baseEnd_7272862 : Nat := 3734473939819829127677723

theorem tailTrace_7272862 : CollatzResearch.WordTrace tailWord_7272862 prefixEnd_7272862 3734473939819829127677723 := by
  unfold tailWord_7272862
  simp only [CollatzResearch.WordTrace]
  refine ⟨33157883672208819348200605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176842046251780369857069893 33157883672208819348200605)
  ·
    refine ⟨12434206377078307255575227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33157883672208819348200605 12434206377078307255575227)
    ·
      refine ⟨18651309565617460883362841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434206377078307255575227 18651309565617460883362841)
      ·
        refine ⟨13988482174213095662522131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18651309565617460883362841 13988482174213095662522131)
        ·
          refine ⟨20982723261319643493783197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13988482174213095662522131 20982723261319643493783197)
          ·
            refine ⟨7868521222994866310168699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20982723261319643493783197 7868521222994866310168699)
            ·
              refine ⟨11802781834492299465253049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868521222994866310168699 11802781834492299465253049)
              ·
                refine ⟨8852086375869224598939787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11802781834492299465253049 8852086375869224598939787)
                ·
                  refine ⟨13278129563803836898409681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8852086375869224598939787 13278129563803836898409681)
                  ·
                    refine ⟨9958597172852877673807261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13278129563803836898409681 9958597172852877673807261)
                    ·
                      refine ⟨3734473939819829127677723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958597172852877673807261 3734473939819829127677723)
                      ·
                        rfl

theorem cell23_7272862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7272862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272862 prefixEnd_7272862 := by exact prefixLift 7272862
  have htrace : WordTrace (prefixWord ++ tailWord_7272862) baseStart_7272862 baseEnd_7272862 := by
    simpa [prefixWord, tailWord_7272862, baseEnd_7272862] using wordTrace_append hprefix tailTrace_7272862
  have hstable : (prefixWord ++ tailWord_7272862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272862).length < 2 ^ (prefixWord ++ tailWord_7272862).sum := by decide
  have hdescent : baseEnd_7272862 < baseStart_7272862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272918 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7272918 : Nat := 118140960795 + 7272918 * 2 ^ 59
def prefixEnd_7272918 : Nat := 4983230072969 + 3 ^ 40 * 7272918 * 2
def baseEnd_7272918 : Nat := 3734502694736480908577465

theorem tailTrace_7272918 : CollatzResearch.WordTrace tailWord_7272918 prefixEnd_7272918 3734502694736480908577465 := by
  unfold tailWord_7272918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579069491591729771852713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176843407910311784233095605 16579069491591729771852713)
  ·
    refine ⟨12434302118693797328889535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16579069491591729771852713 12434302118693797328889535)
    ·
      refine ⟨18651453178040695993334303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434302118693797328889535 18651453178040695993334303)
      ·
        refine ⟨27977179767061043990001455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651453178040695993334303 27977179767061043990001455)
        ·
          refine ⟨41965769650591565985002183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27977179767061043990001455 41965769650591565985002183)
          ·
            refine ⟨62948654475887348977503275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41965769650591565985002183 62948654475887348977503275)
            ·
              refine ⟨94422981713831023466254913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62948654475887348977503275 94422981713831023466254913)
              ·
                refine ⟨70817236285373267599691185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94422981713831023466254913 70817236285373267599691185)
                ·
                  refine ⟨53112927214029950699768389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70817236285373267599691185 53112927214029950699768389)
                  ·
                    refine ⟨9958673852630615756206573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53112927214029950699768389 9958673852630615756206573)
                    ·
                      refine ⟨3734502694736480908577465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9958673852630615756206573 3734502694736480908577465)
                      ·
                        rfl

theorem cell23_7272918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7272918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272918 prefixEnd_7272918 := by exact prefixLift 7272918
  have htrace : WordTrace (prefixWord ++ tailWord_7272918) baseStart_7272918 baseEnd_7272918 := by
    simpa [prefixWord, tailWord_7272918, baseEnd_7272918] using wordTrace_append hprefix tailTrace_7272918
  have hstable : (prefixWord ++ tailWord_7272918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272918).length < 2 ^ (prefixWord ++ tailWord_7272918).sum := by decide
  have hdescent : baseEnd_7272918 < baseStart_7272918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272938 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_7272938 : Nat := 118140960795 + 7272938 * 2 ^ 59
def prefixEnd_7272938 : Nat := 4983230072969 + 3 ^ 40 * 7272938 * 2
def baseEnd_7272938 : Nat := 414945884927730092258597

theorem tailTrace_7272938 : CollatzResearch.WordTrace tailWord_7272938 prefixEnd_7272938 414945884927730092258597 := by
  unfold tailWord_7272938
  simp only [CollatzResearch.WordTrace]
  refine ⟨66316460331348804941342867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176843894216930146510247645 66316460331348804941342867)
  ·
    refine ⟨99474690497023207412014301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66316460331348804941342867 99474690497023207412014301)
    ·
      refine ⟨37303008936383702779505363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99474690497023207412014301 37303008936383702779505363)
      ·
        refine ⟨55954513404575554169258045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37303008936383702779505363 55954513404575554169258045)
        ·
          refine ⟨20982942526715832813471767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55954513404575554169258045 20982942526715832813471767)
          ·
            refine ⟨31474413790073749220207651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20982942526715832813471767 31474413790073749220207651)
            ·
              refine ⟨47211620685110623830311477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31474413790073749220207651 47211620685110623830311477)
              ·
                refine ⟨4426089439229120984091701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47211620685110623830311477 4426089439229120984091701)
                ·
                  refine ⟨414945884927730092258597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426089439229120984091701 414945884927730092258597)
                  ·
                    rfl

theorem cell23_7272938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_7272938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272938 prefixEnd_7272938 := by exact prefixLift 7272938
  have htrace : WordTrace (prefixWord ++ tailWord_7272938) baseStart_7272938 baseEnd_7272938 := by
    simpa [prefixWord, tailWord_7272938, baseEnd_7272938] using wordTrace_append hprefix tailTrace_7272938
  have hstable : (prefixWord ++ tailWord_7272938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272938).length < 2 ^ (prefixWord ++ tailWord_7272938).sum := by decide
  have hdescent : baseEnd_7272938 < baseStart_7272938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272966 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7272966 : Nat := 118140960795 + 7272966 * 2 ^ 59
def prefixEnd_7272966 : Nat := 4983230072969 + 3 ^ 40 * 7272966 * 2
def baseEnd_7272966 : Nat := 3734527341807896720777245

theorem tailTrace_7272966 : CollatzResearch.WordTrace tailWord_7272966 prefixEnd_7272966 3734527341807896720777245 := by
  unfold tailWord_7272966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289589455290430642105961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176844575046195853698260501 8289589455290430642105961)
  ·
    refine ⟨6217192091467822981579471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8289589455290430642105961 6217192091467822981579471)
    ·
      refine ⟨9325788137201734472369207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217192091467822981579471 9325788137201734472369207)
      ·
        refine ⟨13988682205802601708553811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9325788137201734472369207 13988682205802601708553811)
        ·
          refine ⟨20983023308703902562830717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13988682205802601708553811 20983023308703902562830717)
          ·
            refine ⟨7868633740763963461061519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20983023308703902562830717 7868633740763963461061519)
            ·
              refine ⟨11802950611145945191592279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868633740763963461061519 11802950611145945191592279)
              ·
                refine ⟨17704425916718917787388419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802950611145945191592279 17704425916718917787388419)
                ·
                  refine ⟨26556638875078376681082629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17704425916718917787388419 26556638875078376681082629)
                  ·
                    refine ⟨4979369789077195627702993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26556638875078376681082629 4979369789077195627702993)
                    ·
                      refine ⟨3734527341807896720777245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979369789077195627702993 3734527341807896720777245)
                      ·
                        rfl

theorem cell23_7272966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7272966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272966 prefixEnd_7272966 := by exact prefixLift 7272966
  have htrace : WordTrace (prefixWord ++ tailWord_7272966) baseStart_7272966 baseEnd_7272966 := by
    simpa [prefixWord, tailWord_7272966, baseEnd_7272966] using wordTrace_append hprefix tailTrace_7272966
  have hstable : (prefixWord ++ tailWord_7272966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272966).length < 2 ^ (prefixWord ++ tailWord_7272966).sum := by decide
  have hdescent : baseEnd_7272966 < baseStart_7272966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7272971 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4]
def baseStart_7272971 : Nat := 118140960795 + 7272971 * 2 ^ 59
def prefixEnd_7272971 : Nat := 4983230072969 + 3 ^ 40 * 7272971 * 2
def baseEnd_7272971 : Nat := 3734529909211169201214721

theorem tailTrace_7272971 : CollatzResearch.WordTrace tailWord_7272971 prefixEnd_7272971 3734529909211169201214721 := by
  unfold tailWord_7272971
  simp only [CollatzResearch.WordTrace]
  refine ⟨265267044934275666401322767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176844696622850444267548511 265267044934275666401322767)
  ·
    refine ⟨397900567401413499601984151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265267044934275666401322767 397900567401413499601984151)
    ·
      refine ⟨596850851102120249402976227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397900567401413499601984151 596850851102120249402976227)
      ·
        refine ⟨895276276653180374104464341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596850851102120249402976227 895276276653180374104464341)
        ·
          refine ⟨20983037734058915018073383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 895276276653180374104464341 20983037734058915018073383)
          ·
            refine ⟨31474556601088372527110075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20983037734058915018073383 31474556601088372527110075)
            ·
              refine ⟨47211834901632558790665113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31474556601088372527110075 47211834901632558790665113)
              ·
                refine ⟨35408876176224419092998835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47211834901632558790665113 35408876176224419092998835)
                ·
                  refine ⟨53113314264336628639498253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35408876176224419092998835 53113314264336628639498253)
                  ·
                    refine ⟨19917492849126235739811845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53113314264336628639498253 19917492849126235739811845)
                    ·
                      refine ⟨3734529909211169201214721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19917492849126235739811845 3734529909211169201214721)
                      ·
                        rfl

theorem cell23_7272971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 4].length) (baseStart_7272971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7272971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7272971 prefixEnd_7272971 := by exact prefixLift 7272971
  have htrace : WordTrace (prefixWord ++ tailWord_7272971) baseStart_7272971 baseEnd_7272971 := by
    simpa [prefixWord, tailWord_7272971, baseEnd_7272971] using wordTrace_append hprefix tailTrace_7272971
  have hstable : (prefixWord ++ tailWord_7272971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7272971).length < 2 ^ (prefixWord ++ tailWord_7272971).sum := by decide
  have hdescent : baseEnd_7272971 < baseStart_7272971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7272971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273011 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 6]
def baseStart_7273011 : Nat := 118140960795 + 7273011 * 2 ^ 59
def prefixEnd_7273011 : Nat := 4983230072969 + 3 ^ 40 * 7273011 * 2
def baseEnd_7273011 : Nat := 414950049826372116079393

theorem tailTrace_7273011 : CollatzResearch.WordTrace tailWord_7273011 prefixEnd_7273011 414950049826372116079393 := by
  unfold tailWord_7273011
  simp only [CollatzResearch.WordTrace]
  refine ⟨265268503854130753232778887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176845669236087168821852591 265268503854130753232778887)
  ·
    refine ⟨397902755781196129849168331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265268503854130753232778887 397902755781196129849168331)
    ·
      refine ⟨596854133671794194773752497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397902755781196129849168331 596854133671794194773752497)
      ·
        refine ⟨447640600253845646080314373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596854133671794194773752497 447640600253845646080314373)
        ·
          refine ⟨83932612547596058640058945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 447640600253845646080314373 83932612547596058640058945)
          ·
            refine ⟨62949459410697043980044209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83932612547596058640058945 62949459410697043980044209)
            ·
              refine ⟨47212094558022782985033157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62949459410697043980044209 47212094558022782985033157)
              ·
                refine ⟨8852267729629271809693717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47212094558022782985033157 8852267729629271809693717)
                ·
                  refine ⟨414950049826372116079393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8852267729629271809693717 414950049826372116079393)
                  ·
                    rfl

theorem cell23_7273011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 6].length) (baseStart_7273011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273011 prefixEnd_7273011 := by exact prefixLift 7273011
  have htrace : WordTrace (prefixWord ++ tailWord_7273011) baseStart_7273011 baseEnd_7273011 := by
    simpa [prefixWord, tailWord_7273011, baseEnd_7273011] using wordTrace_append hprefix tailTrace_7273011
  have hstable : (prefixWord ++ tailWord_7273011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273011).length < 2 ^ (prefixWord ++ tailWord_7273011).sum := by decide
  have hdescent : baseEnd_7273011 < baseStart_7273011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273048 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_7273048 : Nat := 118140960795 + 7273048 * 2 ^ 59
def prefixEnd_7273048 : Nat := 4983230072969 + 3 ^ 40 * 7273048 * 2
def baseEnd_7273048 : Nat := 3734569447221565399951867

theorem tailTrace_7273048 : CollatzResearch.WordTrace tailWord_7273048 prefixEnd_7273048 3734569447221565399951867 := by
  unfold tailWord_7273048
  simp only [CollatzResearch.WordTrace]
  refine ⟨132634926677498354275937899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176846568903331139034583865 132634926677498354275937899)
  ·
    refine ⟨198952390016247531413906849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132634926677498354275937899 198952390016247531413906849)
    ·
      refine ⟨149214292512185648560430137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198952390016247531413906849 149214292512185648560430137)
      ·
        refine ⟨111910719384139236420322603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149214292512185648560430137 111910719384139236420322603)
        ·
          refine ⟨167866079076208854630483905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111910719384139236420322603 167866079076208854630483905)
          ·
            refine ⟨125899559307156640972862929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167866079076208854630483905 125899559307156640972862929)
            ·
              refine ⟨94424669480367480729647197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125899559307156640972862929 94424669480367480729647197)
              ·
                refine ⟨35409251055137805273617699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94424669480367480729647197 35409251055137805273617699)
                ·
                  refine ⟨53113876582706707910426549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35409251055137805273617699 53113876582706707910426549)
                  ·
                    refine ⟨4979425929628753866602489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53113876582706707910426549 4979425929628753866602489)
                    ·
                      refine ⟨3734569447221565399951867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979425929628753866602489 3734569447221565399951867)
                      ·
                        rfl

theorem cell23_7273048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_7273048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273048 prefixEnd_7273048 := by exact prefixLift 7273048
  have htrace : WordTrace (prefixWord ++ tailWord_7273048) baseStart_7273048 baseEnd_7273048 := by
    simpa [prefixWord, tailWord_7273048, baseEnd_7273048] using wordTrace_append hprefix tailTrace_7273048
  have hstable : (prefixWord ++ tailWord_7273048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273048).length < 2 ^ (prefixWord ++ tailWord_7273048).sum := by decide
  have hdescent : baseEnd_7273048 < baseStart_7273048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273088 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_7273088 : Nat := 118140960795 + 7273088 * 2 ^ 59
def prefixEnd_7273088 : Nat := 4983230072969 + 3 ^ 40 * 7273088 * 2
def baseEnd_7273088 : Nat := 1244863328815915081150561

theorem tailTrace_7273088 : CollatzResearch.WordTrace tailWord_7273088 prefixEnd_7273088 1244863328815915081150561 := by
  unfold tailWord_7273088
  simp only [CollatzResearch.WordTrace]
  refine ⟨132635656137425897691665959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176847541516567863588887945 132635656137425897691665959)
  ·
    refine ⟨198953484206138846537498939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132635656137425897691665959 198953484206138846537498939)
    ·
      refine ⟨298430226309208269806248409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198953484206138846537498939 298430226309208269806248409)
      ·
        refine ⟨223822669731906202354686307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298430226309208269806248409 223822669731906202354686307)
        ·
          refine ⟨335734004597859303532029461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223822669731906202354686307 335734004597859303532029461)
          ·
            refine ⟨15737531465524654853063881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335734004597859303532029461 15737531465524654853063881)
            ·
              refine ⟨11803148599143491139797911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15737531465524654853063881 11803148599143491139797911)
              ·
                refine ⟨17704722898715236709696867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803148599143491139797911 17704722898715236709696867)
                ·
                  refine ⟨26557084348072855064545301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17704722898715236709696867 26557084348072855064545301)
                  ·
                    refine ⟨1244863328815915081150561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26557084348072855064545301 1244863328815915081150561)
                    ·
                      rfl

theorem cell23_7273088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_7273088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273088 prefixEnd_7273088 := by exact prefixLift 7273088
  have htrace : WordTrace (prefixWord ++ tailWord_7273088) baseStart_7273088 baseEnd_7273088 := by
    simpa [prefixWord, tailWord_7273088, baseEnd_7273088] using wordTrace_append hprefix tailTrace_7273088
  have hstable : (prefixWord ++ tailWord_7273088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273088).length < 2 ^ (prefixWord ++ tailWord_7273088).sum := by decide
  have hdescent : baseEnd_7273088 < baseStart_7273088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273091 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6]
def baseStart_7273091 : Nat := 118140960795 + 7273091 * 2 ^ 59
def prefixEnd_7273091 : Nat := 4983230072969 + 3 ^ 40 * 7273091 * 2
def baseEnd_7273091 : Nat := 3734591526889708731714169

theorem tailTrace_7273091 : CollatzResearch.WordTrace tailWord_7273091 prefixEnd_7273091 3734591526889708731714169 := by
  unfold tailWord_7273091
  simp only [CollatzResearch.WordTrace]
  refine ⟨265271421693840926895691127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176847614462560617930460751 265271421693840926895691127)
  ·
    refine ⟨397907132540761390343536691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265271421693840926895691127 397907132540761390343536691)
    ·
      refine ⟨596860698811142085515305037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397907132540761390343536691 596860698811142085515305037)
      ·
        refine ⟨223822762054178282068239389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596860698811142085515305037 223822762054178282068239389)
        ·
          refine ⟨83933535770316855775589771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223822762054178282068239389 83933535770316855775589771)
          ·
            refine ⟨125900303655475283663384657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83933535770316855775589771 125900303655475283663384657)
            ·
              refine ⟨94425227741606462747538493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125900303655475283663384657 94425227741606462747538493)
              ·
                refine ⟨35409460403102423530326935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94425227741606462747538493 35409460403102423530326935)
                ·
                  refine ⟨53114190604653635295490403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35409460403102423530326935 53114190604653635295490403)
                  ·
                    refine ⟨79671285906980452943235605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53114190604653635295490403 79671285906980452943235605)
                    ·
                      refine ⟨3734591526889708731714169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79671285906980452943235605 3734591526889708731714169)
                      ·
                        rfl

theorem cell23_7273091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_7273091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273091 prefixEnd_7273091 := by exact prefixLift 7273091
  have htrace : WordTrace (prefixWord ++ tailWord_7273091) baseStart_7273091 baseEnd_7273091 := by
    simpa [prefixWord, tailWord_7273091, baseEnd_7273091] using wordTrace_append hprefix tailTrace_7273091
  have hstable : (prefixWord ++ tailWord_7273091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273091).length < 2 ^ (prefixWord ++ tailWord_7273091).sum := by decide
  have hdescent : baseEnd_7273091 < baseStart_7273091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273118 : List Nat := [4, 3, 1, 1, 1, 1, 12]
def baseStart_7273118 : Nat := 118140960795 + 7273118 * 2 ^ 59
def prefixEnd_7273118 : Nat := 4983230072969 + 3 ^ 40 * 7273118 * 2
def baseEnd_7273118 : Nat := 46106239393424446000945

theorem tailTrace_7273118 : CollatzResearch.WordTrace tailWord_7273118 prefixEnd_7273118 46106239393424446000945 := by
  unfold tailWord_7273118
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159050808092888813365501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176848270976495407004616005 33159050808092888813365501)
  ·
    refine ⟨12434644053034833305012063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33159050808092888813365501 12434644053034833305012063)
    ·
      refine ⟨18651966079552249957518095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434644053034833305012063 18651966079552249957518095)
      ·
        refine ⟨27977949119328374936277143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18651966079552249957518095 27977949119328374936277143)
        ·
          refine ⟨41966923678992562404415715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27977949119328374936277143 41966923678992562404415715)
          ·
            refine ⟨62950385518488843606623573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41966923678992562404415715 62950385518488843606623573)
            ·
              refine ⟨46106239393424446000945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62950385518488843606623573 46106239393424446000945)
              ·
                rfl

theorem cell23_7273118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 12].length) (baseStart_7273118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273118 prefixEnd_7273118 := by exact prefixLift 7273118
  have htrace : WordTrace (prefixWord ++ tailWord_7273118) baseStart_7273118 baseEnd_7273118 := by
    simpa [prefixWord, tailWord_7273118, baseEnd_7273118] using wordTrace_append hprefix tailTrace_7273118
  have hstable : (prefixWord ++ tailWord_7273118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273118).length < 2 ^ (prefixWord ++ tailWord_7273118).sum := by decide
  have hdescent : baseEnd_7273118 < baseStart_7273118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273142 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_7273142 : Nat := 118140960795 + 7273142 * 2 ^ 59
def prefixEnd_7273142 : Nat := 4983230072969 + 3 ^ 40 * 7273142 * 2
def baseEnd_7273142 : Nat := 3734617714403088032176435

theorem tailTrace_7273142 : CollatzResearch.WordTrace tailWord_7273142 prefixEnd_7273142 3734617714403088032176435 := by
  unfold tailWord_7273142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579580113541010162862355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176848854544437441737198453 16579580113541010162862355)
  ·
    refine ⟨24869370170311515244293533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16579580113541010162862355 24869370170311515244293533)
    ·
      refine ⟨9326013813866818216610075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24869370170311515244293533 9326013813866818216610075)
      ·
        refine ⟨13989020720800227324915113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9326013813866818216610075 13989020720800227324915113)
        ·
          refine ⟨10491765540600170493686335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13989020720800227324915113 10491765540600170493686335)
          ·
            refine ⟨15737648310900255740529503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491765540600170493686335 15737648310900255740529503)
            ·
              refine ⟨23606472466350383610794255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15737648310900255740529503 23606472466350383610794255)
              ·
                refine ⟨35409708699525575416191383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23606472466350383610794255 35409708699525575416191383)
                ·
                  refine ⟨53114563049288363124287075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35409708699525575416191383 53114563049288363124287075)
                  ·
                    refine ⟨79671844573932544686430613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53114563049288363124287075 79671844573932544686430613)
                    ·
                      refine ⟨3734617714403088032176435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79671844573932544686430613 3734617714403088032176435)
                      ·
                        rfl

theorem cell23_7273142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_7273142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273142 prefixEnd_7273142 := by exact prefixLift 7273142
  have htrace : WordTrace (prefixWord ++ tailWord_7273142) baseStart_7273142 baseEnd_7273142 := by
    simpa [prefixWord, tailWord_7273142, baseEnd_7273142] using wordTrace_append hprefix tailTrace_7273142
  have hstable : (prefixWord ++ tailWord_7273142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273142).length < 2 ^ (prefixWord ++ tailWord_7273142).sum := by decide
  have hdescent : baseEnd_7273142 < baseStart_7273142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273252 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_7273252 : Nat := 118140960795 + 7273252 * 2 ^ 59
def prefixEnd_7273252 : Nat := 4983230072969 + 3 ^ 40 * 7273252 * 2
def baseEnd_7273252 : Nat := 3734674197275082601800929

theorem tailTrace_7273252 : CollatzResearch.WordTrace tailWord_7273252 prefixEnd_7273252 3734674197275082601800929 := by
  unfold tailWord_7273252
  simp only [CollatzResearch.WordTrace]
  refine ⟨132638646923128825696151005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176851529230838434261534673 132638646923128825696151005)
  ·
    refine ⟨49739492596173309636056627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132638646923128825696151005 49739492596173309636056627)
    ·
      refine ⟨74609238894259964454084941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49739492596173309636056627 74609238894259964454084941)
      ·
        refine ⟨27978464585347486670281853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74609238894259964454084941 27978464585347486670281853)
        ·
          refine ⟨10491924219505307501355695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27978464585347486670281853 10491924219505307501355695)
          ·
            refine ⟨15737886329257961252033543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10491924219505307501355695 15737886329257961252033543)
            ·
              refine ⟨23606829493886941878050315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15737886329257961252033543 23606829493886941878050315)
              ·
                refine ⟨35410244240830412817075473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23606829493886941878050315 35410244240830412817075473)
                ·
                  refine ⟨26557683180622809612806605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35410244240830412817075473 26557683180622809612806605)
                  ·
                    refine ⟨9959131192733553604802477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26557683180622809612806605 9959131192733553604802477)
                    ·
                      refine ⟨3734674197275082601800929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9959131192733553604802477 3734674197275082601800929)
                      ·
                        rfl

theorem cell23_7273252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_7273252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273252 prefixEnd_7273252 := by exact prefixLift 7273252
  have htrace : WordTrace (prefixWord ++ tailWord_7273252) baseStart_7273252 baseEnd_7273252 := by
    simpa [prefixWord, tailWord_7273252, baseEnd_7273252] using wordTrace_append hprefix tailTrace_7273252
  have hstable : (prefixWord ++ tailWord_7273252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273252).length < 2 ^ (prefixWord ++ tailWord_7273252).sum := by decide
  have hdescent : baseEnd_7273252 < baseStart_7273252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273288 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_7273288 : Nat := 118140960795 + 7273288 * 2 ^ 59
def prefixEnd_7273288 : Nat := 4983230072969 + 3 ^ 40 * 7273288 * 2
def baseEnd_7273288 : Nat := 3734692682578644460950763

theorem tailTrace_7273288 : CollatzResearch.WordTrace tailWord_7273288 prefixEnd_7273288 3734692682578644460950763 := by
  unfold tailWord_7273288
  simp only [CollatzResearch.WordTrace]
  refine ⟨132639303437063614770306259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176852404582751486360408345 132639303437063614770306259)
  ·
    refine ⟨198958955155595422155459389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132639303437063614770306259 198958955155595422155459389)
    ·
      refine ⟨74609608183348283308297271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198958955155595422155459389 74609608183348283308297271)
      ·
        refine ⟨111914412275022424962445907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74609608183348283308297271 111914412275022424962445907)
        ·
          refine ⟨167871618412533637443668861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111914412275022424962445907 167871618412533637443668861)
          ·
            refine ⟨62951856904700114041375823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167871618412533637443668861 62951856904700114041375823)
            ·
              refine ⟨94427785357050171062063735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62951856904700114041375823 94427785357050171062063735)
              ·
                refine ⟨141641678035575256593095603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94427785357050171062063735 141641678035575256593095603)
                ·
                  refine ⟨212462517053362884889643405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141641678035575256593095603 212462517053362884889643405)
                  ·
                    refine ⟨79673443895011081833616277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212462517053362884889643405 79673443895011081833616277)
                    ·
                      refine ⟨3734692682578644460950763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79673443895011081833616277 3734692682578644460950763)
                      ·
                        rfl

theorem cell23_7273288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_7273288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273288 prefixEnd_7273288 := by exact prefixLift 7273288
  have htrace : WordTrace (prefixWord ++ tailWord_7273288) baseStart_7273288 baseEnd_7273288 := by
    simpa [prefixWord, tailWord_7273288, baseEnd_7273288] using wordTrace_append hprefix tailTrace_7273288
  have hstable : (prefixWord ++ tailWord_7273288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273288).length < 2 ^ (prefixWord ++ tailWord_7273288).sum := by decide
  have hdescent : baseEnd_7273288 < baseStart_7273288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273292 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7273292 : Nat := 118140960795 + 7273292 * 2 ^ 59
def prefixEnd_7273292 : Nat := 4983230072969 + 3 ^ 40 * 7273292 * 2
def baseEnd_7273292 : Nat := 3734694736501262445300745

theorem tailTrace_7273292 : CollatzResearch.WordTrace tailWord_7273292 prefixEnd_7273292 3734694736501262445300745 := by
  unfold tailWord_7273292
  simp only [CollatzResearch.WordTrace]
  refine ⟨132639376383056369111879065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176852501844075158815838753 132639376383056369111879065)
  ·
    refine ⟨99479532287292276833909299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132639376383056369111879065 99479532287292276833909299)
    ·
      refine ⟨149219298430938415250863949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99479532287292276833909299 149219298430938415250863949)
      ·
        refine ⟨55957236911601905719073981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149219298430938415250863949 55957236911601905719073981)
        ·
          refine ⟨20983963841850714644652743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55957236911601905719073981 20983963841850714644652743)
          ·
            refine ⟨31475945762776071966979115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20983963841850714644652743 31475945762776071966979115)
            ·
              refine ⟨47213918644164107950468673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31475945762776071966979115 47213918644164107950468673)
              ·
                refine ⟨35410438983123080962851505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47213918644164107950468673 35410438983123080962851505)
                ·
                  refine ⟨26557829237342310722138629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35410438983123080962851505 26557829237342310722138629)
                  ·
                    refine ⟨4979592982001683260400993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26557829237342310722138629 4979592982001683260400993)
                    ·
                      refine ⟨3734694736501262445300745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979592982001683260400993 3734694736501262445300745)
                      ·
                        rfl

theorem cell23_7273292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7273292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273292 prefixEnd_7273292 := by exact prefixLift 7273292
  have htrace : WordTrace (prefixWord ++ tailWord_7273292) baseStart_7273292 baseEnd_7273292 := by
    simpa [prefixWord, tailWord_7273292, baseEnd_7273292] using wordTrace_append hprefix tailTrace_7273292
  have hstable : (prefixWord ++ tailWord_7273292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273292).length < 2 ^ (prefixWord ++ tailWord_7273292).sum := by decide
  have hdescent : baseEnd_7273292 < baseStart_7273292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273325 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7273325 : Nat := 118140960795 + 7273325 * 2 ^ 59
def prefixEnd_7273325 : Nat := 4983230072969 + 3 ^ 40 * 7273325 * 2
def baseEnd_7273325 : Nat := 3734711681362860816188093

theorem tailTrace_7273325 : CollatzResearch.WordTrace tailWord_7273325 prefixEnd_7273325 3734711681362860816188093 := by
  unfold tailWord_7273325
  simp only [CollatzResearch.WordTrace]
  refine ⟨265279956374993184859709429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176853304249995456573139619 265279956374993184859709429)
  ·
    refine ⟨24869995910155611080597759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265279956374993184859709429 24869995910155611080597759)
    ·
      refine ⟨37304993865233416620896639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24869995910155611080597759 37304993865233416620896639)
      ·
        refine ⟨55957490797850124931344959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37304993865233416620896639 55957490797850124931344959)
        ·
          refine ⟨83936236196775187397017439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55957490797850124931344959 83936236196775187397017439)
          ·
            refine ⟨125904354295162781095526159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83936236196775187397017439 125904354295162781095526159)
            ·
              refine ⟨188856531442744171643289239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125904354295162781095526159 188856531442744171643289239)
              ·
                refine ⟨283284797164116257464933859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188856531442744171643289239 283284797164116257464933859)
                ·
                  refine ⟨424927195746174386197400789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283284797164116257464933859 424927195746174386197400789)
                  ·
                    refine ⟨9959231150300962176501581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 424927195746174386197400789 9959231150300962176501581)
                    ·
                      refine ⟨3734711681362860816188093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9959231150300962176501581 3734711681362860816188093)
                      ·
                        rfl

theorem cell23_7273325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7273325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273325 prefixEnd_7273325 := by exact prefixLift 7273325
  have htrace : WordTrace (prefixWord ++ tailWord_7273325) baseStart_7273325 baseEnd_7273325 := by
    simpa [prefixWord, tailWord_7273325, baseEnd_7273325] using wordTrace_append hprefix tailTrace_7273325
  have hstable : (prefixWord ++ tailWord_7273325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273325).length < 2 ^ (prefixWord ++ tailWord_7273325).sum := by decide
  have hdescent : baseEnd_7273325 < baseStart_7273325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273366 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_7273366 : Nat := 118140960795 + 7273366 * 2 ^ 59
def prefixEnd_7273366 : Nat := 4983230072969 + 3 ^ 40 * 7273366 * 2
def baseEnd_7273366 : Nat := 414970303785521683975045

theorem tailTrace_7273366 : CollatzResearch.WordTrace tailWord_7273366 prefixEnd_7273366 414970303785521683975045 := by
  unfold tailWord_7273366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580090735490290553871997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176854301178563099241301301 16580090735490290553871997)
  ·
    refine ⟨6217534025808858957701999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16580090735490290553871997 6217534025808858957701999)
    ·
      refine ⟨9326301038713288436552999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217534025808858957701999 9326301038713288436552999)
      ·
        refine ⟨13989451558069932654829499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9326301038713288436552999 13989451558069932654829499)
        ·
          refine ⟨20984177337104898982244249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13989451558069932654829499 20984177337104898982244249)
          ·
            refine ⟨15738133002828674236683187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20984177337104898982244249 15738133002828674236683187)
            ·
              refine ⟨23607199504243011355024781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738133002828674236683187 23607199504243011355024781)
              ·
                refine ⟨8852699814091129258134293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23607199504243011355024781 8852699814091129258134293)
                ·
                  refine ⟨414970303785521683975045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8852699814091129258134293 414970303785521683975045)
                  ·
                    rfl

theorem cell23_7273366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_7273366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273366 prefixEnd_7273366 := by exact prefixLift 7273366
  have htrace : WordTrace (prefixWord ++ tailWord_7273366) baseStart_7273366 baseEnd_7273366 := by
    simpa [prefixWord, tailWord_7273366, baseEnd_7273366] using wordTrace_append hprefix tailTrace_7273366
  have hstable : (prefixWord ++ tailWord_7273366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273366).length < 2 ^ (prefixWord ++ tailWord_7273366).sum := by decide
  have hdescent : baseEnd_7273366 < baseStart_7273366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273405 : List Nat := [1, 4, 1, 2, 4, 11]
def baseStart_7273405 : Nat := 118140960795 + 7273405 * 2 ^ 59
def prefixEnd_7273405 : Nat := 4983230072969 + 3 ^ 40 * 7273405 * 2
def baseEnd_7273405 : Nat := 15369352921050290136575

theorem tailTrace_7273405 : CollatzResearch.WordTrace tailWord_7273405 prefixEnd_7273405 15369352921050290136575 := by
  unfold tailWord_7273405
  simp only [CollatzResearch.WordTrace]
  refine ⟨265282874214703358522621669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176855249476468905681747779 265282874214703358522621669)
  ·
    refine ⟨49740538915256879722991563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265282874214703358522621669 49740538915256879722991563)
    ·
      refine ⟨74610808372885319584487345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49740538915256879722991563 74610808372885319584487345)
      ·
        refine ⟨55958106279663989688365509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74610808372885319584487345 55958106279663989688365509)
        ·
          refine ⟨10492144927436998066568533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55958106279663989688365509 10492144927436998066568533)
          ·
            refine ⟨15369352921050290136575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10492144927436998066568533 15369352921050290136575)
            ·
              rfl

theorem cell23_7273405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 11].length) (baseStart_7273405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273405 prefixEnd_7273405 := by exact prefixLift 7273405
  have htrace : WordTrace (prefixWord ++ tailWord_7273405) baseStart_7273405 baseEnd_7273405 := by
    simpa [prefixWord, tailWord_7273405, baseEnd_7273405] using wordTrace_append hprefix tailTrace_7273405
  have hstable : (prefixWord ++ tailWord_7273405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273405).length < 2 ^ (prefixWord ++ tailWord_7273405).sum := by decide
  have hdescent : baseEnd_7273405 < baseStart_7273405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273422 : List Nat := [4, 1, 1, 1, 2, 5, 1, 8]
def baseStart_7273422 : Nat := 118140960795 + 7273422 * 2 ^ 59
def prefixEnd_7273422 : Nat := 4983230072969 + 3 ^ 40 * 7273422 * 2
def baseEnd_7273422 : Nat := 138324499592086923580561

theorem tailTrace_7273422 : CollatzResearch.WordTrace tailWord_7273422 prefixEnd_7273422 138324499592086923580561 := by
  unfold tailWord_7273422
  simp only [CollatzResearch.WordTrace]
  refine ⟨33160436781955221303248815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176855662837094513617327013 33160436781955221303248815)
  ·
    refine ⟨49740655172932831954873223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33160436781955221303248815 49740655172932831954873223)
    ·
      refine ⟨74610982759399247932309835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49740655172932831954873223 74610982759399247932309835)
      ·
        refine ⟨111916474139098871898464753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74610982759399247932309835 111916474139098871898464753)
        ·
          refine ⟨83937355604324153923848565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111916474139098871898464753 83937355604324153923848565)
          ·
            refine ⟨7869127087905389430360803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83937355604324153923848565 7869127087905389430360803)
            ·
              refine ⟨11803690631858084145541205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869127087905389430360803 11803690631858084145541205)
              ·
                refine ⟨138324499592086923580561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11803690631858084145541205 138324499592086923580561)
                ·
                  rfl

theorem cell23_7273422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_7273422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273422 prefixEnd_7273422 := by exact prefixLift 7273422
  have htrace : WordTrace (prefixWord ++ tailWord_7273422) baseStart_7273422 baseEnd_7273422 := by
    simpa [prefixWord, tailWord_7273422, baseEnd_7273422] using wordTrace_append hprefix tailTrace_7273422
  have hstable : (prefixWord ++ tailWord_7273422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273422).length < 2 ^ (prefixWord ++ tailWord_7273422).sum := by decide
  have hdescent : baseEnd_7273422 < baseStart_7273422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273429 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7273429 : Nat := 118140960795 + 7273429 * 2 ^ 59
def prefixEnd_7273429 : Nat := 4983230072969 + 3 ^ 40 * 7273429 * 2
def baseEnd_7273429 : Nat := 3734765083350928409287615

theorem tailTrace_7273429 : CollatzResearch.WordTrace tailWord_7273429 prefixEnd_7273429 3734765083350928409287615 := by
  unfold tailWord_7273429
  simp only [CollatzResearch.WordTrace]
  refine ⟨265283749566616410621495341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176855833044410940414330227 265283749566616410621495341)
  ·
    refine ⟨99481406087481153983060753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265283749566616410621495341 99481406087481153983060753)
    ·
      refine ⟨74611054565610865487295565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99481406087481153983060753 74611054565610865487295565)
      ·
        refine ⟨27979145462104074557735837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74611054565610865487295565 27979145462104074557735837)
        ·
          refine ⟨10492179548289027959150939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27979145462104074557735837 10492179548289027959150939)
          ·
            refine ⟨15738269322433541938726409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492179548289027959150939 15738269322433541938726409)
            ·
              refine ⟨11803701991825156454044807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15738269322433541938726409 11803701991825156454044807)
              ·
                refine ⟨17705552987737734681067211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803701991825156454044807 17705552987737734681067211)
                ·
                  refine ⟨26558329481606602021600817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17705552987737734681067211 26558329481606602021600817)
                  ·
                    refine ⟨19918747111204951516200613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26558329481606602021600817 19918747111204951516200613)
                    ·
                      refine ⟨3734765083350928409287615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19918747111204951516200613 3734765083350928409287615)
                      ·
                        rfl

theorem cell23_7273429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7273429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273429 prefixEnd_7273429 := by exact prefixLift 7273429
  have htrace : WordTrace (prefixWord ++ tailWord_7273429) baseStart_7273429 baseEnd_7273429 := by
    simpa [prefixWord, tailWord_7273429, baseEnd_7273429] using wordTrace_append hprefix tailTrace_7273429
  have hstable : (prefixWord ++ tailWord_7273429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273429).length < 2 ^ (prefixWord ++ tailWord_7273429).sum := by decide
  have hdescent : baseEnd_7273429 < baseStart_7273429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273432 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_7273432 : Nat := 118140960795 + 7273432 * 2 ^ 59
def prefixEnd_7273432 : Nat := 4983230072969 + 3 ^ 40 * 7273432 * 2
def baseEnd_7273432 : Nat := 3734766623792891897550101

theorem tailTrace_7273432 : CollatzResearch.WordTrace tailWord_7273432 prefixEnd_7273432 3734766623792891897550101 := by
  unfold tailWord_7273432
  simp only [CollatzResearch.WordTrace]
  refine ⟨132641929492802771066927275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176855905990403694755903033 132641929492802771066927275)
  ·
    refine ⟨198962894239204156600390913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132641929492802771066927275 198962894239204156600390913)
    ·
      refine ⟨149222170679403117450293185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198962894239204156600390913 149222170679403117450293185)
      ·
        refine ⟨111916628009552338087719889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149222170679403117450293185 111916628009552338087719889)
        ·
          refine ⟨83937471007164253565789917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111916628009552338087719889 83937471007164253565789917)
          ·
            refine ⟨31476551627686595087171219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83937471007164253565789917 31476551627686595087171219)
            ·
              refine ⟨47214827441529892630756829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31476551627686595087171219 47214827441529892630756829)
              ·
                refine ⟨17705560290573709736533811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47214827441529892630756829 17705560290573709736533811)
                ·
                  refine ⟨26558340435860564604800717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17705560290573709736533811 26558340435860564604800717)
                  ·
                    refine ⟨9959377663447711726800269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26558340435860564604800717 9959377663447711726800269)
                    ·
                      refine ⟨3734766623792891897550101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9959377663447711726800269 3734766623792891897550101)
                      ·
                        rfl

theorem cell23_7273432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_7273432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273432 prefixEnd_7273432 := by exact prefixLift 7273432
  have htrace : WordTrace (prefixWord ++ tailWord_7273432) baseStart_7273432 baseEnd_7273432 := by
    simpa [prefixWord, tailWord_7273432, baseEnd_7273432] using wordTrace_append hprefix tailTrace_7273432
  have hstable : (prefixWord ++ tailWord_7273432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273432).length < 2 ^ (prefixWord ++ tailWord_7273432).sum := by decide
  have hdescent : baseEnd_7273432 < baseStart_7273432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273460 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7273460 : Nat := 118140960795 + 7273460 * 2 ^ 59
def prefixEnd_7273460 : Nat := 4983230072969 + 3 ^ 40 * 7273460 * 2
def baseEnd_7273460 : Nat := 1244927000417072595999991

theorem tailTrace_7273460 : CollatzResearch.WordTrace tailWord_7273460 prefixEnd_7273460 1244927000417072595999991 := by
  unfold tailWord_7273460
  simp only [CollatzResearch.WordTrace]
  refine ⟨132642440114752051457936917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176856586819669401943915889 132642440114752051457936917)
  ·
    refine ⟨6217614380379002412090793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132642440114752051457936917 6217614380379002412090793)
    ·
      refine ⟨4663210785284251809068095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6217614380379002412090793 4663210785284251809068095)
      ·
        refine ⟨6994816177926377713602143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663210785284251809068095 6994816177926377713602143)
        ·
          refine ⟨10492224266889566570403215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994816177926377713602143 10492224266889566570403215)
          ·
            refine ⟨15738336400334349855604823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492224266889566570403215 15738336400334349855604823)
            ·
              refine ⟨23607504600501524783407235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15738336400334349855604823 23607504600501524783407235)
              ·
                refine ⟨35411256900752287175110853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23607504600501524783407235 35411256900752287175110853)
                ·
                  refine ⟨6639610668891053845333285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35411256900752287175110853 6639610668891053845333285)
                  ·
                    refine ⟨1244927000417072595999991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6639610668891053845333285 1244927000417072595999991)
                    ·
                      rfl

theorem cell23_7273460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7273460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273460 prefixEnd_7273460 := by exact prefixLift 7273460
  have htrace : WordTrace (prefixWord ++ tailWord_7273460) baseStart_7273460 baseEnd_7273460 := by
    simpa [prefixWord, tailWord_7273460, baseEnd_7273460] using wordTrace_append hprefix tailTrace_7273460
  have hstable : (prefixWord ++ tailWord_7273460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273460).length < 2 ^ (prefixWord ++ tailWord_7273460).sum := by decide
  have hdescent : baseEnd_7273460 < baseStart_7273460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273465 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_7273465 : Nat := 118140960795 + 7273465 * 2 ^ 59
def prefixEnd_7273465 : Nat := 4983230072969 + 3 ^ 40 * 7273465 * 2
def baseEnd_7273465 : Nat := 1244927856218163422812483

theorem tailTrace_7273465 : CollatzResearch.WordTrace tailWord_7273465 prefixEnd_7273465 1244927856218163422812483 := by
  unfold tailWord_7273465
  simp only [CollatzResearch.WordTrace]
  refine ⟨265285062594485988769805849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176856708396323992513203899 265285062594485988769805849)
  ·
    refine ⟨198963796945864491577354387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265285062594485988769805849 198963796945864491577354387)
    ·
      refine ⟨298445695418796737366031581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198963796945864491577354387 298445695418796737366031581)
      ·
        refine ⟨111917135782048776512261843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298445695418796737366031581 111917135782048776512261843)
        ·
          refine ⟨167875703673073164768392765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111917135782048776512261843 167875703673073164768392765)
          ·
            refine ⟨62953388877402436788147287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167875703673073164768392765 62953388877402436788147287)
            ·
              refine ⟨94430083316103655182220931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62953388877402436788147287 94430083316103655182220931)
              ·
                refine ⟨141645124974155482773331397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94430083316103655182220931 141645124974155482773331397)
                ·
                  refine ⟨26558460932654153019999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141645124974155482773331397 26558460932654153019999637)
                  ·
                    refine ⟨1244927856218163422812483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26558460932654153019999637 1244927856218163422812483)
                    ·
                      rfl

theorem cell23_7273465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_7273465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273465 prefixEnd_7273465 := by exact prefixLift 7273465
  have htrace : WordTrace (prefixWord ++ tailWord_7273465) baseStart_7273465 baseEnd_7273465 := by
    simpa [prefixWord, tailWord_7273465, baseEnd_7273465] using wordTrace_append hprefix tailTrace_7273465
  have hstable : (prefixWord ++ tailWord_7273465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273465).length < 2 ^ (prefixWord ++ tailWord_7273465).sum := by decide
  have hdescent : baseEnd_7273465 < baseStart_7273465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273475 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5]
def baseStart_7273475 : Nat := 118140960795 + 7273475 * 2 ^ 59
def prefixEnd_7273475 : Nat := 4983230072969 + 3 ^ 40 * 7273475 * 2
def baseEnd_7273475 : Nat := 3734788703461035229312403

theorem tailTrace_7273475 : CollatzResearch.WordTrace tailWord_7273475 prefixEnd_7273475 3734788703461035229312403 := by
  unfold tailWord_7273475
  simp only [CollatzResearch.WordTrace]
  refine ⟨265285427324449760477669879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176856951549633173651779919 265285427324449760477669879)
  ·
    refine ⟨397928140986674640716504819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265285427324449760477669879 397928140986674640716504819)
    ·
      refine ⟨596892211480011961074757229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397928140986674640716504819 596892211480011961074757229)
      ·
        refine ⟨223834579305004485403033961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596892211480011961074757229 223834579305004485403033961)
        ·
          refine ⟨167875934478753364052275471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223834579305004485403033961 167875934478753364052275471)
          ·
            refine ⟨251813901718130046078413207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167875934478753364052275471 251813901718130046078413207)
            ·
              refine ⟨377720852577195069117619811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251813901718130046078413207 377720852577195069117619811)
              ·
                refine ⟨566581278865792603676429717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377720852577195069117619811 566581278865792603676429717)
                ·
                  refine ⟨26558497446834028297332643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 566581278865792603676429717 26558497446834028297332643)
                  ·
                    refine ⟨39837746170251042445998965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26558497446834028297332643 39837746170251042445998965)
                    ·
                      refine ⟨3734788703461035229312403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39837746170251042445998965 3734788703461035229312403)
                      ·
                        rfl

theorem cell23_7273475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_7273475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273475 prefixEnd_7273475 := by exact prefixLift 7273475
  have htrace : WordTrace (prefixWord ++ tailWord_7273475) baseStart_7273475 baseEnd_7273475 := by
    simpa [prefixWord, tailWord_7273475, baseEnd_7273475] using wordTrace_append hprefix tailTrace_7273475
  have hstable : (prefixWord ++ tailWord_7273475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273475).length < 2 ^ (prefixWord ++ tailWord_7273475).sum := by decide
  have hdescent : baseEnd_7273475 < baseStart_7273475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273482 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_7273482 : Nat := 118140960795 + 7273482 * 2 ^ 59
def prefixEnd_7273482 : Nat := 4983230072969 + 3 ^ 40 * 7273482 * 2
def baseEnd_7273482 : Nat := 1244930765941872233974957

theorem tailTrace_7273482 : CollatzResearch.WordTrace tailWord_7273482 prefixEnd_7273482 1244930765941872233974957 := by
  unfold tailWord_7273482
  simp only [CollatzResearch.WordTrace]
  refine ⟨66321420658856100168293675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176857121756949600448783133 66321420658856100168293675)
  ·
    refine ⟨99482130988284150252440513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66321420658856100168293675 99482130988284150252440513)
    ·
      refine ⟨74611598241213112689330385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99482130988284150252440513 74611598241213112689330385)
      ·
        refine ⟨55958698680909834516997789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74611598241213112689330385 55958698680909834516997789)
        ·
          refine ⟨20984512005341187943874171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55958698680909834516997789 20984512005341187943874171)
          ·
            refine ⟨31476768008011781915811257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20984512005341187943874171 31476768008011781915811257)
            ·
              refine ⟨23607576006008836436858443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31476768008011781915811257 23607576006008836436858443)
              ·
                refine ⟨35411364009013254655287665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23607576006008836436858443 35411364009013254655287665)
                ·
                  refine ⟨26558523006759940991465749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35411364009013254655287665 26558523006759940991465749)
                  ·
                    refine ⟨1244930765941872233974957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26558523006759940991465749 1244930765941872233974957)
                    ·
                      rfl

theorem cell23_7273482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_7273482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273482 prefixEnd_7273482 := by exact prefixLift 7273482
  have htrace : WordTrace (prefixWord ++ tailWord_7273482) baseStart_7273482 baseEnd_7273482 := by
    simpa [prefixWord, tailWord_7273482, baseEnd_7273482] using wordTrace_append hprefix tailTrace_7273482
  have hstable : (prefixWord ++ tailWord_7273482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273482).length < 2 ^ (prefixWord ++ tailWord_7273482).sum := by decide
  have hdescent : baseEnd_7273482 < baseStart_7273482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273490 : List Nat := [3, 2, 5, 1, 2, 1, 2, 7]
def baseStart_7273490 : Nat := 118140960795 + 7273490 * 2 ^ 59
def prefixEnd_7273490 : Nat := 4983230072969 + 3 ^ 40 * 7273490 * 2
def baseEnd_7273490 : Nat := 138325792802624172986105

theorem tailTrace_7273490 : CollatzResearch.WordTrace tailWord_7273490 prefixEnd_7273490 138325792802624172986105 := by
  unfold tailWord_7273490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66321493604848854509866481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176857316279596945359643949 66321493604848854509866481)
  ·
    refine ⟨49741120203636640882399861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66321493604848854509866481 49741120203636640882399861)
    ·
      refine ⟨4663230019090935082724987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49741120203636640882399861 4663230019090935082724987)
      ·
        refine ⟨6994845028636402624087481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663230019090935082724987 6994845028636402624087481)
        ·
          refine ⟨5246133771477301968065611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6994845028636402624087481 5246133771477301968065611)
          ·
            refine ⟨7869200657215952952098417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246133771477301968065611 7869200657215952952098417)
            ·
              refine ⟨5901900492911964714073813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7869200657215952952098417 5901900492911964714073813)
              ·
                refine ⟨138325792802624172986105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5901900492911964714073813 138325792802624172986105)
                ·
                  rfl

theorem cell23_7273490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_7273490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273490 prefixEnd_7273490 := by exact prefixLift 7273490
  have htrace : WordTrace (prefixWord ++ tailWord_7273490) baseStart_7273490 baseEnd_7273490 := by
    simpa [prefixWord, tailWord_7273490, baseEnd_7273490] using wordTrace_append hprefix tailTrace_7273490
  have hstable : (prefixWord ++ tailWord_7273490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273490).length < 2 ^ (prefixWord ++ tailWord_7273490).sum := by decide
  have hdescent : baseEnd_7273490 < baseStart_7273490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273506 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_7273506 : Nat := 118140960795 + 7273506 * 2 ^ 59
def prefixEnd_7273506 : Nat := 4983230072969 + 3 ^ 40 * 7273506 * 2
def baseEnd_7273506 : Nat := 3734804621361324608024761

theorem tailTrace_7273506 : CollatzResearch.WordTrace tailWord_7273506 prefixEnd_7273506 3734804621361324608024761 := by
  unfold tailWord_7273506
  simp only [CollatzResearch.WordTrace]
  refine ⟨66321639496834363193012093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176857705324891635181365581 66321639496834363193012093)
  ·
    refine ⟨24870614811312886197379535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66321639496834363193012093 24870614811312886197379535)
    ·
      refine ⟨37305922216969329296069303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24870614811312886197379535 37305922216969329296069303)
      ·
        refine ⟨55958883325453993944103955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37305922216969329296069303 55958883325453993944103955)
        ·
          refine ⟨83938324988180990916155933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55958883325453993944103955 83938324988180990916155933)
          ·
            refine ⟨31476871870567871593558475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83938324988180990916155933 31476871870567871593558475)
            ·
              refine ⟨47215307805851807390337713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31476871870567871593558475 47215307805851807390337713)
              ·
                refine ⟨35411480854388855542753285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47215307805851807390337713 35411480854388855542753285)
                ·
                  refine ⟨6639652660197910414266241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35411480854388855542753285 6639652660197910414266241)
                  ·
                    refine ⟨4979739495148432810699681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639652660197910414266241 4979739495148432810699681)
                    ·
                      refine ⟨3734804621361324608024761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979739495148432810699681 3734804621361324608024761)
                      ·
                        rfl

theorem cell23_7273506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_7273506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273506 prefixEnd_7273506 := by exact prefixLift 7273506
  have htrace : WordTrace (prefixWord ++ tailWord_7273506) baseStart_7273506 baseEnd_7273506 := by
    simpa [prefixWord, tailWord_7273506, baseEnd_7273506] using wordTrace_append hprefix tailTrace_7273506
  have hstable : (prefixWord ++ tailWord_7273506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273506).length < 2 ^ (prefixWord ++ tailWord_7273506).sum := by decide
  have hdescent : baseEnd_7273506 < baseStart_7273506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273529 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 7]
def baseStart_7273529 : Nat := 118140960795 + 7273529 * 2 ^ 59
def prefixEnd_7273529 : Nat := 4983230072969 + 3 ^ 40 * 7273529 * 2
def baseEnd_7273529 : Nat := 414979603490708668670795

theorem tailTrace_7273529 : CollatzResearch.WordTrace tailWord_7273529 prefixEnd_7273529 414979603490708668670795 := by
  unfold tailWord_7273529
  simp only [CollatzResearch.WordTrace]
  refine ⟨265287396866254127700135641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176858264577502751800090427 265287396866254127700135641)
  ·
    refine ⟨198965547649690595775101731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265287396866254127700135641 198965547649690595775101731)
    ·
      refine ⟨298448321474535893662652597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198965547649690595775101731 298448321474535893662652597)
      ·
        refine ⟨27979530138237740030873681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298448321474535893662652597 27979530138237740030873681)
        ·
          refine ⟨20984647603678305023155261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27979530138237740030873681 20984647603678305023155261)
          ·
            refine ⟨7869242851379364383683223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20984647603678305023155261 7869242851379364383683223)
            ·
              refine ⟨11803864277069046575524835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869242851379364383683223 11803864277069046575524835)
              ·
                refine ⟨17705796415603569863287253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803864277069046575524835 17705796415603569863287253)
                ·
                  refine ⟨414979603490708668670795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17705796415603569863287253 414979603490708668670795)
                  ·
                    rfl

theorem cell23_7273529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_7273529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273529 prefixEnd_7273529 := by exact prefixLift 7273529
  have htrace : WordTrace (prefixWord ++ tailWord_7273529) baseStart_7273529 baseEnd_7273529 := by
    simpa [prefixWord, tailWord_7273529, baseEnd_7273529] using wordTrace_append hprefix tailTrace_7273529
  have hstable : (prefixWord ++ tailWord_7273529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273529).length < 2 ^ (prefixWord ++ tailWord_7273529).sum := by decide
  have hdescent : baseEnd_7273529 < baseStart_7273529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273555 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 10]
def baseStart_7273555 : Nat := 118140960795 + 7273555 * 2 ^ 59
def prefixEnd_7273555 : Nat := 4983230072969 + 3 ^ 40 * 7273555 * 2
def baseEnd_7273555 : Nat := 1244943260637798305437345

theorem tailTrace_7273555 : CollatzResearch.WordTrace tailWord_7273555 prefixEnd_7273555 1244943260637798305437345 := by
  unfold tailWord_7273555
  simp only [CollatzResearch.WordTrace]
  refine ⟨265288345164159934140582119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176858896776106622760388079 265288345164159934140582119)
  ·
    refine ⟨397932517746239901210873179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265288345164159934140582119 397932517746239901210873179)
    ·
      refine ⟨596898776619359851816309769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397932517746239901210873179 596898776619359851816309769)
      ·
        refine ⟨447674082464519888862232327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596898776619359851816309769 447674082464519888862232327)
        ·
          refine ⟨671511123696779833293348491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447674082464519888862232327 671511123696779833293348491)
          ·
            refine ⟨1007266685545169749940022737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671511123696779833293348491 1007266685545169749940022737)
            ·
              refine ⟨755450014158877312455017053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007266685545169749940022737 755450014158877312455017053)
              ·
                refine ⟨283293755309578992170631395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755450014158877312455017053 283293755309578992170631395)
                ·
                  refine ⟨424940632964368488255947093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283293755309578992170631395 424940632964368488255947093)
                  ·
                    refine ⟨1244943260637798305437345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 424940632964368488255947093 1244943260637798305437345)
                    ·
                      rfl

theorem cell23_7273555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_7273555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273555 prefixEnd_7273555 := by exact prefixLift 7273555
  have htrace : WordTrace (prefixWord ++ tailWord_7273555) baseStart_7273555 baseEnd_7273555 := by
    simpa [prefixWord, tailWord_7273555, baseEnd_7273555] using wordTrace_append hprefix tailTrace_7273555
  have hstable : (prefixWord ++ tailWord_7273555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273555).length < 2 ^ (prefixWord ++ tailWord_7273555).sum := by decide
  have hdescent : baseEnd_7273555 < baseStart_7273555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273623 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 1, 4]
def baseStart_7273623 : Nat := 118140960795 + 7273623 * 2 ^ 59
def prefixEnd_7273623 : Nat := 4983230072969 + 3 ^ 40 * 7273623 * 2
def baseEnd_7273623 : Nat := 1244954899532633550087241

theorem tailTrace_7273623 : CollatzResearch.WordTrace tailWord_7273623 prefixEnd_7273623 1244954899532633550087241 := by
  unfold tailWord_7273623
  simp only [CollatzResearch.WordTrace]
  refine ⟨265290825327913581754057523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176860550218609054502705015 265290825327913581754057523)
  ·
    refine ⟨397936237991870372631086285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265290825327913581754057523 397936237991870372631086285)
    ·
      refine ⟨149226089246951389736657357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397936237991870372631086285 149226089246951389736657357)
      ·
        refine ⟨55959783467606771151246509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149226089246951389736657357 55959783467606771151246509)
        ·
          refine ⟨20984918800352539181717441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55959783467606771151246509 20984918800352539181717441)
          ·
            refine ⟨15738689100264404386288081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20984918800352539181717441 15738689100264404386288081)
            ·
              refine ⟨11804016825198303289716061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15738689100264404386288081 11804016825198303289716061)
              ·
                refine ⟨4426506309449363733643523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11804016825198303289716061 4426506309449363733643523)
                ·
                  refine ⟨6639759464174045600465285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426506309449363733643523 6639759464174045600465285)
                  ·
                    refine ⟨1244954899532633550087241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6639759464174045600465285 1244954899532633550087241)
                    ·
                      rfl

theorem cell23_7273623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_7273623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273623 prefixEnd_7273623 := by exact prefixLift 7273623
  have htrace : WordTrace (prefixWord ++ tailWord_7273623) baseStart_7273623 baseEnd_7273623 := by
    simpa [prefixWord, tailWord_7273623, baseEnd_7273623] using wordTrace_append hprefix tailTrace_7273623
  have hstable : (prefixWord ++ tailWord_7273623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273623).length < 2 ^ (prefixWord ++ tailWord_7273623).sum := by decide
  have hdescent : baseEnd_7273623 < baseStart_7273623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273636 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 6]
def baseStart_7273636 : Nat := 118140960795 + 7273636 * 2 ^ 59
def prefixEnd_7273636 : Nat := 4983230072969 + 3 ^ 40 * 7273636 * 2
def baseEnd_7273636 : Nat := 414985708205156566599907

theorem tailTrace_7273636 : CollatzResearch.WordTrace tailWord_7273636 prefixEnd_7273636 414985708205156566599907 := by
  unfold tailWord_7273636
  simp only [CollatzResearch.WordTrace]
  refine ⟨132645649738433242487140381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176860866317910989982853841 132645649738433242487140381)
  ·
    refine ⟨49742118651912465932677643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132645649738433242487140381 49742118651912465932677643)
    ·
      refine ⟨74613177977868698899016465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49742118651912465932677643 74613177977868698899016465)
      ·
        refine ⟨55959883483401524174262349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74613177977868698899016465 55959883483401524174262349)
        ·
          refine ⟨20984956306275571565348381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55959883483401524174262349 20984956306275571565348381)
          ·
            refine ⟨7869358614853339337005643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20984956306275571565348381 7869358614853339337005643)
            ·
              refine ⟨11804037922280009005508465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869358614853339337005643 11804037922280009005508465)
              ·
                refine ⟨8853028441710006754131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11804037922280009005508465 8853028441710006754131349)
                ·
                  refine ⟨414985708205156566599907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8853028441710006754131349 414985708205156566599907)
                  ·
                    rfl

theorem cell23_7273636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_7273636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273636 prefixEnd_7273636 := by exact prefixLift 7273636
  have htrace : WordTrace (prefixWord ++ tailWord_7273636) baseStart_7273636 baseEnd_7273636 := by
    simpa [prefixWord, tailWord_7273636, baseEnd_7273636] using wordTrace_append hprefix tailTrace_7273636
  have hstable : (prefixWord ++ tailWord_7273636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273636).length < 2 ^ (prefixWord ++ tailWord_7273636).sum := by decide
  have hdescent : baseEnd_7273636 < baseStart_7273636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273639 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7273639 : Nat := 118140960795 + 7273639 * 2 ^ 59
def prefixEnd_7273639 : Nat := 4983230072969 + 3 ^ 40 * 7273639 * 2
def baseEnd_7273639 : Nat := 3734872914288372587661649

theorem tailTrace_7273639 : CollatzResearch.WordTrace tailWord_7273639 prefixEnd_7273639 3734872914288372587661649 := by
  unfold tailWord_7273639
  simp only [CollatzResearch.WordTrace]
  refine ⟨265291408895855616486639971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176860939263903744324426647 265291408895855616486639971)
  ·
    refine ⟨397937113343783424729959957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265291408895855616486639971 397937113343783424729959957)
    ·
      refine ⟨18653302187989848034216873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 397937113343783424729959957 18653302187989848034216873)
      ·
        refine ⟨13989976640992386025662655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18653302187989848034216873 13989976640992386025662655)
        ·
          refine ⟨20984964961488579038493983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13989976640992386025662655 20984964961488579038493983)
          ·
            refine ⟨31477447442232868557740975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20984964961488579038493983 31477447442232868557740975)
            ·
              refine ⟨47216171163349302836611463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31477447442232868557740975 47216171163349302836611463)
              ·
                refine ⟨70824256745023954254917195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47216171163349302836611463 70824256745023954254917195)
                ·
                  refine ⟨106236385117535931382375793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70824256745023954254917195 106236385117535931382375793)
                  ·
                    refine ⟨79677288838151948536781845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106236385117535931382375793 79677288838151948536781845)
                    ·
                      refine ⟨3734872914288372587661649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79677288838151948536781845 3734872914288372587661649)
                      ·
                        rfl

theorem cell23_7273639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7273639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273639 prefixEnd_7273639 := by exact prefixLift 7273639
  have htrace : WordTrace (prefixWord ++ tailWord_7273639) baseStart_7273639 baseEnd_7273639 := by
    simpa [prefixWord, tailWord_7273639, baseEnd_7273639] using wordTrace_append hprefix tailTrace_7273639
  have hstable : (prefixWord ++ tailWord_7273639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273639).length < 2 ^ (prefixWord ++ tailWord_7273639).sum := by decide
  have hdescent : baseEnd_7273639 < baseStart_7273639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273669 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_7273669 : Nat := 118140960795 + 7273669 * 2 ^ 59
def prefixEnd_7273669 : Nat := 4983230072969 + 3 ^ 40 * 7273669 * 2
def baseEnd_7273669 : Nat := 3734888318708007470286511

theorem tailTrace_7273669 : CollatzResearch.WordTrace tailWord_7273669 prefixEnd_7273669 3734888318708007470286511 := by
  unfold tailWord_7273669
  simp only [CollatzResearch.WordTrace]
  refine ⟨265292503085746931610232061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176861668723831287740154707 265292503085746931610232061)
  ·
    refine ⟨99484688657155099353837023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265292503085746931610232061 99484688657155099353837023)
    ·
      refine ⟨149227032985732649030755535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99484688657155099353837023 149227032985732649030755535)
      ·
        refine ⟨223840549478598973546133303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149227032985732649030755535 223840549478598973546133303)
        ·
          refine ⟨335760824217898460319199955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223840549478598973546133303 335760824217898460319199955)
          ·
            refine ⟨503641236326847690478799933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335760824217898460319199955 503641236326847690478799933)
            ·
              refine ⟨188865463622567883929549975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503641236326847690478799933 188865463622567883929549975)
              ·
                refine ⟨283298195433851825894324963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188865463622567883929549975 283298195433851825894324963)
                ·
                  refine ⟨424947293150777738841487445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283298195433851825894324963 424947293150777738841487445)
                  ·
                    refine ⟨4979851091610676627048681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 424947293150777738841487445 4979851091610676627048681)
                    ·
                      refine ⟨3734888318708007470286511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979851091610676627048681 3734888318708007470286511)
                      ·
                        rfl

theorem cell23_7273669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_7273669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273669 prefixEnd_7273669 := by exact prefixLift 7273669
  have htrace : WordTrace (prefixWord ++ tailWord_7273669) baseStart_7273669 baseEnd_7273669 := by
    simpa [prefixWord, tailWord_7273669, baseEnd_7273669] using wordTrace_append hprefix tailTrace_7273669
  have hstable : (prefixWord ++ tailWord_7273669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273669).length < 2 ^ (prefixWord ++ tailWord_7273669).sum := by decide
  have hdescent : baseEnd_7273669 < baseStart_7273669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273689 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_7273689 : Nat := 118140960795 + 7273689 * 2 ^ 59
def prefixEnd_7273689 : Nat := 4983230072969 + 3 ^ 40 * 7273689 * 2
def baseEnd_7273689 : Nat := 3734898588321097392036419

theorem tailTrace_7273689 : CollatzResearch.WordTrace tailWord_7273689 prefixEnd_7273689 3734898588321097392036419 := by
  unfold tailWord_7273689
  simp only [CollatzResearch.WordTrace]
  refine ⟨265293232545674475025960121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176862155030449650017306747 265293232545674475025960121)
  ·
    refine ⟨198969924409255856269470091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265293232545674475025960121 198969924409255856269470091)
    ·
      refine ⟨298454886613883784404205137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198969924409255856269470091 298454886613883784404205137)
      ·
        refine ⟨223841164960412838303153853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298454886613883784404205137 223841164960412838303153853)
        ·
          refine ⟨83940436860154814363682695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223841164960412838303153853 83940436860154814363682695)
          ·
            refine ⟨125910655290232221545524043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83940436860154814363682695 125910655290232221545524043)
            ·
              refine ⟨188865982935348332318286065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125910655290232221545524043 188865982935348332318286065)
              ·
                refine ⟨141649487201511249238714549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188865982935348332318286065 141649487201511249238714549)
                ·
                  refine ⟨13279639425141679616129489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141649487201511249238714549 13279639425141679616129489)
                  ·
                    refine ⟨9959729568856259712097117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13279639425141679616129489 9959729568856259712097117)
                    ·
                      refine ⟨3734898588321097392036419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9959729568856259712097117 3734898588321097392036419)
                      ·
                        rfl

theorem cell23_7273689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_7273689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273689 prefixEnd_7273689 := by exact prefixLift 7273689
  have htrace : WordTrace (prefixWord ++ tailWord_7273689) baseStart_7273689 baseEnd_7273689 := by
    simpa [prefixWord, tailWord_7273689, baseEnd_7273689] using wordTrace_append hprefix tailTrace_7273689
  have hstable : (prefixWord ++ tailWord_7273689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273689).length < 2 ^ (prefixWord ++ tailWord_7273689).sum := by decide
  have hdescent : baseEnd_7273689 < baseStart_7273689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273709 : List Nat := [1, 5, 1, 2, 2, 1, 1, 10]
def baseStart_7273709 : Nat := 118140960795 + 7273709 * 2 ^ 59
def prefixEnd_7273709 : Nat := 4983230072969 + 3 ^ 40 * 7273709 * 2
def baseEnd_7273709 : Nat := 138329957701266196806901

theorem tailTrace_7273709 : CollatzResearch.WordTrace tailWord_7273709 prefixEnd_7273709 138329957701266196806901 := by
  unfold tailWord_7273709
  simp only [CollatzResearch.WordTrace]
  refine ⟨265293962005602018441688181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176862641337068012294458787 265293962005602018441688181)
  ·
    refine ⟨24871308938025189228908267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265293962005602018441688181 24871308938025189228908267)
    ·
      refine ⟨37306963407037783843362401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24871308938025189228908267 37306963407037783843362401)
      ·
        refine ⟨27980222555278337882521801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37306963407037783843362401 27980222555278337882521801)
        ·
          refine ⟨20985166916458753411891351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27980222555278337882521801 20985166916458753411891351)
          ·
            refine ⟨31477750374688130117837027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20985166916458753411891351 31477750374688130117837027)
            ·
              refine ⟨47216625562032195176755541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31477750374688130117837027 47216625562032195176755541)
              ·
                refine ⟨138329957701266196806901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47216625562032195176755541 138329957701266196806901)
                ·
                  rfl

theorem cell23_7273709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 10].length) (baseStart_7273709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273709 prefixEnd_7273709 := by exact prefixLift 7273709
  have htrace : WordTrace (prefixWord ++ tailWord_7273709) baseStart_7273709 baseEnd_7273709 := by
    simpa [prefixWord, tailWord_7273709, baseEnd_7273709] using wordTrace_append hprefix tailTrace_7273709
  have hstable : (prefixWord ++ tailWord_7273709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273709).length < 2 ^ (prefixWord ++ tailWord_7273709).sum := by decide
  have hdescent : baseEnd_7273709 < baseStart_7273709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273754 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2]
def baseStart_7273754 : Nat := 118140960795 + 7273754 * 2 ^ 59
def prefixEnd_7273754 : Nat := 4983230072969 + 3 ^ 40 * 7273754 * 2
def baseEnd_7273754 : Nat := 3734931964563639637723621

theorem tailTrace_7273754 : CollatzResearch.WordTrace tailWord_7273754 prefixEnd_7273754 3734931964563639637723621 := by
  unfold tailWord_7273754
  simp only [CollatzResearch.WordTrace]
  refine ⟨66323900822609747781769079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176863735526959327418050877 66323900822609747781769079)
  ·
    refine ⟨99485851233914621672653619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66323900822609747781769079 99485851233914621672653619)
    ·
      refine ⟨149228776850871932508980429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99485851233914621672653619 149228776850871932508980429)
      ·
        refine ⟨55960791319076974690867661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149228776850871932508980429 55960791319076974690867661)
        ·
          refine ⟨20985296744653865509075373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55960791319076974690867661 20985296744653865509075373)
          ·
            refine ⟨7869486279245199565903265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20985296744653865509075373 7869486279245199565903265)
            ·
              refine ⟨5902114709433899674427449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7869486279245199565903265 5902114709433899674427449)
              ·
                refine ⟨4426586032075424755820587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902114709433899674427449 4426586032075424755820587)
                ·
                  refine ⟨6639879048113137133730881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426586032075424755820587 6639879048113137133730881)
                  ·
                    refine ⟨4979909286084852850298161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639879048113137133730881 4979909286084852850298161)
                    ·
                      refine ⟨3734931964563639637723621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979909286084852850298161 3734931964563639637723621)
                      ·
                        rfl

theorem cell23_7273754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_7273754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273754 prefixEnd_7273754 := by exact prefixLift 7273754
  have htrace : WordTrace (prefixWord ++ tailWord_7273754) baseStart_7273754 baseEnd_7273754 := by
    simpa [prefixWord, tailWord_7273754, baseEnd_7273754] using wordTrace_append hprefix tailTrace_7273754
  have hstable : (prefixWord ++ tailWord_7273754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273754).length < 2 ^ (prefixWord ++ tailWord_7273754).sum := by decide
  have hdescent : baseEnd_7273754 < baseStart_7273754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273770 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7273770 : Nat := 118140960795 + 7273770 * 2 ^ 59
def prefixEnd_7273770 : Nat := 4983230072969 + 3 ^ 40 * 7273770 * 2
def baseEnd_7273770 : Nat := 3734940180254111575123547

theorem tailTrace_7273770 : CollatzResearch.WordTrace tailWord_7273770 prefixEnd_7273770 3734940180254111575123547 := by
  unfold tailWord_7273770
  simp only [CollatzResearch.WordTrace]
  refine ⟨66324046714595256464914691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176864124572254017239772509 66324046714595256464914691)
  ·
    refine ⟨99486070071892884697372037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66324046714595256464914691 99486070071892884697372037)
    ·
      refine ⟨18653638138479915880757257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99486070071892884697372037 18653638138479915880757257)
      ·
        refine ⟨13990228603859936910567943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18653638138479915880757257 13990228603859936910567943)
        ·
          refine ⟨20985342905789905365851915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13990228603859936910567943 20985342905789905365851915)
          ·
            refine ⟨31478014358684858048777873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20985342905789905365851915 31478014358684858048777873)
            ·
              refine ⟨23608510769013643536583405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31478014358684858048777873 23608510769013643536583405)
              ·
                refine ⟨8853191538380116326218777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23608510769013643536583405 8853191538380116326218777)
                ·
                  refine ⟨6639893653785087244664083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8853191538380116326218777 6639893653785087244664083)
                  ·
                    refine ⟨9959840480677630866996125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6639893653785087244664083 9959840480677630866996125)
                    ·
                      refine ⟨3734940180254111575123547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9959840480677630866996125 3734940180254111575123547)
                      ·
                        rfl

theorem cell23_7273770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7273770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273770 prefixEnd_7273770 := by exact prefixLift 7273770
  have htrace : WordTrace (prefixWord ++ tailWord_7273770) baseStart_7273770 baseEnd_7273770 := by
    simpa [prefixWord, tailWord_7273770, baseEnd_7273770] using wordTrace_append hprefix tailTrace_7273770
  have hstable : (prefixWord ++ tailWord_7273770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273770).length < 2 ^ (prefixWord ++ tailWord_7273770).sum := by decide
  have hdescent : baseEnd_7273770 < baseStart_7273770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273780 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7273780 : Nat := 118140960795 + 7273780 * 2 ^ 59
def prefixEnd_7273780 : Nat := 4983230072969 + 3 ^ 40 * 7273780 * 2
def baseEnd_7273780 : Nat := 3734945315060656535998501

theorem tailTrace_7273780 : CollatzResearch.WordTrace tailWord_7273780 prefixEnd_7273780 3734945315060656535998501 := by
  unfold tailWord_7273780
  simp only [CollatzResearch.WordTrace]
  refine ⟨132648275794172398783761397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176864367725563198378348529 132648275794172398783761397)
  ·
    refine ⟨12435775855703662385977631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132648275794172398783761397 12435775855703662385977631)
    ·
      refine ⟨18653663783555493578966447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12435775855703662385977631 18653663783555493578966447)
      ·
        refine ⟨27980495675333240368449671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18653663783555493578966447 27980495675333240368449671)
        ·
          refine ⟨41970743512999860552674507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27980495675333240368449671 41970743512999860552674507)
          ·
            refine ⟨62956115269499790829011761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41970743512999860552674507 62956115269499790829011761)
            ·
              refine ⟨47217086452124843121758821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62956115269499790829011761 47217086452124843121758821)
              ·
                refine ⟨8853203709773408085329779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47217086452124843121758821 8853203709773408085329779)
                ·
                  refine ⟨13279805564660112127994669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853203709773408085329779 13279805564660112127994669)
                  ·
                    refine ⟨4979927086747542047998001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13279805564660112127994669 4979927086747542047998001)
                    ·
                      refine ⟨3734945315060656535998501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979927086747542047998001 3734945315060656535998501)
                      ·
                        rfl

theorem cell23_7273780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7273780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273780 prefixEnd_7273780 := by exact prefixLift 7273780
  have htrace : WordTrace (prefixWord ++ tailWord_7273780) baseStart_7273780 baseEnd_7273780 := by
    simpa [prefixWord, tailWord_7273780, baseEnd_7273780] using wordTrace_append hprefix tailTrace_7273780
  have hstable : (prefixWord ++ tailWord_7273780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273780).length < 2 ^ (prefixWord ++ tailWord_7273780).sum := by decide
  have hdescent : baseEnd_7273780 < baseStart_7273780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273816 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 5]
def baseStart_7273816 : Nat := 118140960795 + 7273816 * 2 ^ 59
def prefixEnd_7273816 : Nat := 4983230072969 + 3 ^ 40 * 7273816 * 2
def baseEnd_7273816 : Nat := 414995977818246488349815

theorem tailTrace_7273816 : CollatzResearch.WordTrace tailWord_7273816 prefixEnd_7273816 414995977818246488349815 := by
  unfold tailWord_7273816
  simp only [CollatzResearch.WordTrace]
  refine ⟨132648932308107187857916651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176865243077476250477222201 132648932308107187857916651)
  ·
    refine ⟨198973398462160781786874977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132648932308107187857916651 198973398462160781786874977)
    ·
      refine ⟨149230048846620586340156233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198973398462160781786874977 149230048846620586340156233)
      ·
        refine ⟨111922536634965439755117175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149230048846620586340156233 111922536634965439755117175)
        ·
          refine ⟨167883804952448159632675763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111922536634965439755117175 167883804952448159632675763)
          ·
            refine ⟨251825707428672239449013645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167883804952448159632675763 251825707428672239449013645)
            ·
              refine ⟨94434640285752089793380117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251825707428672239449013645 94434640285752089793380117)
              ·
                refine ⟨4426623763394629209064693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94434640285752089793380117 4426623763394629209064693)
                ·
                  refine ⟨414995977818246488349815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426623763394629209064693 414995977818246488349815)
                  ·
                    rfl

theorem cell23_7273816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 5].length) (baseStart_7273816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273816 prefixEnd_7273816 := by exact prefixLift 7273816
  have htrace : WordTrace (prefixWord ++ tailWord_7273816) baseStart_7273816 baseEnd_7273816 := by
    simpa [prefixWord, tailWord_7273816, baseEnd_7273816] using wordTrace_append hprefix tailTrace_7273816
  have hstable : (prefixWord ++ tailWord_7273816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273816).length < 2 ^ (prefixWord ++ tailWord_7273816).sum := by decide
  have hdescent : baseEnd_7273816 < baseStart_7273816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273821 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7273821 : Nat := 118140960795 + 7273821 * 2 ^ 59
def prefixEnd_7273821 : Nat := 4983230072969 + 3 ^ 40 * 7273821 * 2
def baseEnd_7273821 : Nat := 3734966367767490875585813

theorem tailTrace_7273821 : CollatzResearch.WordTrace tailWord_7273821 prefixEnd_7273821 3734966367767490875585813 := by
  unfold tailWord_7273821
  simp only [CollatzResearch.WordTrace]
  refine ⟨265298046981196261569765317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176865364654130841046510211 265298046981196261569765317)
  ·
    refine ⟨49743383808974299044330997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265298046981196261569765317 49743383808974299044330997)
    ·
      refine ⟨4663442232091340535406031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49743383808974299044330997 4663442232091340535406031)
      ·
        refine ⟨6995163348137010803109047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663442232091340535406031 6995163348137010803109047)
        ·
          refine ⟨10492745022205516204663571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6995163348137010803109047 10492745022205516204663571)
          ·
            refine ⟨15739117533308274306995357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492745022205516204663571 15739117533308274306995357)
            ·
              refine ⟨5902169074990602865123259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15739117533308274306995357 5902169074990602865123259)
              ·
                refine ⟨8853253612485904297684889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902169074990602865123259 8853253612485904297684889)
                ·
                  refine ⟨6639940209364428223263667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8853253612485904297684889 6639940209364428223263667)
                  ·
                    refine ⟨9959910314046642334895501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6639940209364428223263667 9959910314046642334895501)
                    ·
                      refine ⟨3734966367767490875585813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9959910314046642334895501 3734966367767490875585813)
                      ·
                        rfl

theorem cell23_7273821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7273821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273821 prefixEnd_7273821 := by exact prefixLift 7273821
  have htrace : WordTrace (prefixWord ++ tailWord_7273821) baseStart_7273821 baseEnd_7273821 := by
    simpa [prefixWord, tailWord_7273821, baseEnd_7273821] using wordTrace_append hprefix tailTrace_7273821
  have hstable : (prefixWord ++ tailWord_7273821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273821).length < 2 ^ (prefixWord ++ tailWord_7273821).sum := by decide
  have hdescent : baseEnd_7273821 < baseStart_7273821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273827 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 2, 2, 2]
def baseStart_7273827 : Nat := 118140960795 + 7273827 * 2 ^ 59
def prefixEnd_7273827 : Nat := 4983230072969 + 3 ^ 40 * 7273827 * 2
def baseEnd_7273827 : Nat := 3734969448651417852110785

theorem tailTrace_7273827 : CollatzResearch.WordTrace tailWord_7273827 prefixEnd_7273827 3734969448651417852110785 := by
  unfold tailWord_7273827
  simp only [CollatzResearch.WordTrace]
  refine ⟨265298265819174524594483735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176865510546116349729655823 265298265819174524594483735)
  ·
    refine ⟨397947398728761786891725603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265298265819174524594483735 397947398728761786891725603)
    ·
      refine ⟨596921098093142680337588405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397947398728761786891725603 596921098093142680337588405)
      ·
        refine ⟨55961352946232126281648913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596921098093142680337588405 55961352946232126281648913)
        ·
          refine ⟨41971014709674094711236685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55961352946232126281648913 41971014709674094711236685)
          ·
            refine ⟨15739130516127785516713757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41971014709674094711236685 15739130516127785516713757)
            ·
              refine ⟨5902173943547919568767659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15739130516127785516713757 5902173943547919568767659)
              ·
                refine ⟨8853260915321879353151489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902173943547919568767659 8853260915321879353151489)
                ·
                  refine ⟨6639945686491409514863617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8853260915321879353151489 6639945686491409514863617)
                  ·
                    refine ⟨4979959264868557136147713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6639945686491409514863617 4979959264868557136147713)
                    ·
                      refine ⟨3734969448651417852110785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4979959264868557136147713 3734969448651417852110785)
                      ·
                        rfl

theorem cell23_7273827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_7273827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273827 prefixEnd_7273827 := by exact prefixLift 7273827
  have htrace : WordTrace (prefixWord ++ tailWord_7273827) baseStart_7273827 baseEnd_7273827 := by
    simpa [prefixWord, tailWord_7273827, baseEnd_7273827] using wordTrace_append hprefix tailTrace_7273827
  have hstable : (prefixWord ++ tailWord_7273827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273827).length < 2 ^ (prefixWord ++ tailWord_7273827).sum := by decide
  have hdescent : baseEnd_7273827 < baseStart_7273827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273829 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_7273829 : Nat := 118140960795 + 7273829 * 2 ^ 59
def prefixEnd_7273829 : Nat := 4983230072969 + 3 ^ 40 * 7273829 * 2
def baseEnd_7273829 : Nat := 1244990158537575614761925

theorem tailTrace_7273829 : CollatzResearch.WordTrace tailWord_7273829 prefixEnd_7273829 1244990158537575614761925 := by
  unfold tailWord_7273829
  simp only [CollatzResearch.WordTrace]
  refine ⟨265298338765167278936056541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176865559176778185957371027 265298338765167278936056541)
  ·
    refine ⟨99486877036937729601021203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265298338765167278936056541 99486877036937729601021203)
    ·
      refine ⟨149230315555406594401531805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99486877036937729601021203 149230315555406594401531805)
      ·
        refine ⟨55961368333277472900574427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149230315555406594401531805 55961368333277472900574427)
        ·
          refine ⟨83942052499916209350861641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55961368333277472900574427 83942052499916209350861641)
          ·
            refine ⟨62956539374937157013146231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83942052499916209350861641 62956539374937157013146231)
            ·
              refine ⟨94434809062405735519719347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62956539374937157013146231 94434809062405735519719347)
              ·
                refine ⟨141652213593608603279579021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94434809062405735519719347 141652213593608603279579021)
                ·
                  refine ⟨53119580097603226229842133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141652213593608603279579021 53119580097603226229842133)
                  ·
                    refine ⟨1244990158537575614761925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53119580097603226229842133 1244990158537575614761925)
                    ·
                      rfl

theorem cell23_7273829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_7273829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273829 prefixEnd_7273829 := by exact prefixLift 7273829
  have htrace : WordTrace (prefixWord ++ tailWord_7273829) baseStart_7273829 baseEnd_7273829 := by
    simpa [prefixWord, tailWord_7273829, baseEnd_7273829] using wordTrace_append hprefix tailTrace_7273829
  have hstable : (prefixWord ++ tailWord_7273829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273829).length < 2 ^ (prefixWord ++ tailWord_7273829).sum := by decide
  have hdescent : baseEnd_7273829 < baseStart_7273829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_7273943 : Nat := 118140960795 + 7273943 * 2 ^ 59
def prefixEnd_7273943 : Nat := 4983230072969 + 3 ^ 40 * 7273943 * 2
def baseEnd_7273943 : Nat := 3735029012407339398260251

theorem tailTrace_7273943 : CollatzResearch.WordTrace tailWord_7273943 prefixEnd_7273943 3735029012407339398260251 := by
  unfold tailWord_7273943
  simp only [CollatzResearch.WordTrace]
  refine ⟨265302496686754276405706483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176868331124502850937137655 265302496686754276405706483)
  ·
    refine ⟨397953745030131414608559725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265302496686754276405706483 397953745030131414608559725)
    ·
      refine ⟨149232654386299280478209897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397953745030131414608559725 149232654386299280478209897)
      ·
        refine ⟨111924490789724460358657423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149232654386299280478209897 111924490789724460358657423)
        ·
          refine ⟨167886736184586690537986135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111924490789724460358657423 167886736184586690537986135)
          ·
            refine ⟨251830104276880035806979203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167886736184586690537986135 251830104276880035806979203)
            ·
              refine ⟨377745156415320053710468805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251830104276880035806979203 377745156415320053710468805)
              ·
                refine ⟨70827216827872510070712901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377745156415320053710468805 70827216827872510070712901)
                ·
                  refine ⟨13280103155226095638258669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70827216827872510070712901 13280103155226095638258669)
                  ·
                    refine ⟨4980038683209785864347001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13280103155226095638258669 4980038683209785864347001)
                    ·
                      refine ⟨3735029012407339398260251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980038683209785864347001 3735029012407339398260251)
                      ·
                        rfl

theorem cell23_7273943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_7273943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273943 prefixEnd_7273943 := by exact prefixLift 7273943
  have htrace : WordTrace (prefixWord ++ tailWord_7273943) baseStart_7273943 baseEnd_7273943 := by
    simpa [prefixWord, tailWord_7273943, baseEnd_7273943] using wordTrace_append hprefix tailTrace_7273943
  have hstable : (prefixWord ++ tailWord_7273943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273943).length < 2 ^ (prefixWord ++ tailWord_7273943).sum := by decide
  have hdescent : baseEnd_7273943 < baseStart_7273943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273970 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_7273970 : Nat := 118140960795 + 7273970 * 2 ^ 59
def prefixEnd_7273970 : Nat := 4983230072969 + 3 ^ 40 * 7273970 * 2
def baseEnd_7273970 : Nat := 1245014292128336930874209

theorem tailTrace_7273970 : CollatzResearch.WordTrace tailWord_7273970 prefixEnd_7273970 1245014292128336930874209 := by
  unfold tailWord_7273970
  simp only [CollatzResearch.WordTrace]
  refine ⟨66325870364414115004234841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176868987638437640011292909 66325870364414115004234841)
  ·
    refine ⟨49744402773310586253176131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66325870364414115004234841 49744402773310586253176131)
    ·
      refine ⟨74616604159965879379764197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49744402773310586253176131 74616604159965879379764197)
      ·
        refine ⟨13990613279993602383705787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74616604159965879379764197 13990613279993602383705787)
        ·
          refine ⟨20985919919990403575558681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13990613279993602383705787 20985919919990403575558681)
          ·
            refine ⟨15739439939992802681669011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20985919919990403575558681 15739439939992802681669011)
            ·
              refine ⟨23609159909989204022503517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15739439939992802681669011 23609159909989204022503517)
              ·
                refine ⟨8853434966245951508438819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23609159909989204022503517 8853434966245951508438819)
                ·
                  refine ⟨13280152449368927262658229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853434966245951508438819 13280152449368927262658229)
                  ·
                    refine ⟨1245014292128336930874209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13280152449368927262658229 1245014292128336930874209)
                    ·
                      rfl

theorem cell23_7273970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_7273970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273970 prefixEnd_7273970 := by exact prefixLift 7273970
  have htrace : WordTrace (prefixWord ++ tailWord_7273970) baseStart_7273970 baseEnd_7273970 := by
    simpa [prefixWord, tailWord_7273970, baseEnd_7273970] using wordTrace_append hprefix tailTrace_7273970
  have hstable : (prefixWord ++ tailWord_7273970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273970).length < 2 ^ (prefixWord ++ tailWord_7273970).sum := by decide
  have hdescent : baseEnd_7273970 < baseStart_7273970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273983 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 2, 4]
def baseStart_7273983 : Nat := 118140960795 + 7273983 * 2 ^ 59
def prefixEnd_7273983 : Nat := 4983230072969 + 3 ^ 40 * 7273983 * 2
def baseEnd_7273983 : Nat := 1245016517211173080586689

theorem tailTrace_7273983 : CollatzResearch.WordTrace tailWord_7273983 prefixEnd_7273983 1245016517211173080586689 := by
  unfold tailWord_7273983
  simp only [CollatzResearch.WordTrace]
  refine ⟨265303955606609363237162603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176869303737739575491441735 265303955606609363237162603)
  ·
    refine ⟨397955933409914044855743905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265303955606609363237162603 397955933409914044855743905)
    ·
      refine ⟨298466950057435533641807929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397955933409914044855743905 298466950057435533641807929)
      ·
        refine ⟨223850212543076650231355947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298466950057435533641807929 223850212543076650231355947)
        ·
          refine ⟨335775318814614975347033921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223850212543076650231355947 335775318814614975347033921)
          ·
            refine ⟨251831489110961231510275441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335775318814614975347033921 251831489110961231510275441)
            ·
              refine ⟨188873616833220923632706581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251831489110961231510275441 188873616833220923632706581)
              ·
                refine ⟨8853450789057230795283121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188873616833220923632706581 8853450789057230795283121)
                ·
                  refine ⟨6640088091792923096462341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8853450789057230795283121 6640088091792923096462341)
                  ·
                    refine ⟨1245016517211173080586689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6640088091792923096462341 1245016517211173080586689)
                    ·
                      rfl

theorem cell23_7273983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_7273983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7273983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7273983 prefixEnd_7273983 := by exact prefixLift 7273983
  have htrace : WordTrace (prefixWord ++ tailWord_7273983) baseStart_7273983 baseEnd_7273983 := by
    simpa [prefixWord, tailWord_7273983, baseEnd_7273983] using wordTrace_append hprefix tailTrace_7273983
  have hstable : (prefixWord ++ tailWord_7273983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273983).length < 2 ^ (prefixWord ++ tailWord_7273983).sum := by decide
  have hdescent : baseEnd_7273983 < baseStart_7273983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274003 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4]
def baseStart_7274003 : Nat := 118140960795 + 7274003 * 2 ^ 59
def prefixEnd_7274003 : Nat := 4983230072969 + 3 ^ 40 * 7274003 * 2
def baseEnd_7274003 : Nat := 3735059821246609163509975

theorem tailTrace_7274003 : CollatzResearch.WordTrace tailWord_7274003 prefixEnd_7274003 3735059821246609163509975 := by
  unfold tailWord_7274003
  simp only [CollatzResearch.WordTrace]
  refine ⟨265304685066536906652890663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176869790044357937768593775 265304685066536906652890663)
  ·
    refine ⟨397957027599805359979335995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265304685066536906652890663 397957027599805359979335995)
    ·
      refine ⟨596935541399708039969003993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397957027599805359979335995 596935541399708039969003993)
      ·
        refine ⟨447701656049781029976752995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596935541399708039969003993 447701656049781029976752995)
        ·
          refine ⟨671552484074671544965129493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447701656049781029976752995 671552484074671544965129493)
          ·
            refine ⟨31479022691000228670240445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 671552484074671544965129493 31479022691000228670240445)
            ·
              refine ⟨11804633509125085751340167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31479022691000228670240445 11804633509125085751340167)
              ·
                refine ⟨17706950263687628627010251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11804633509125085751340167 17706950263687628627010251)
                ·
                  refine ⟨26560425395531442940515377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17706950263687628627010251 26560425395531442940515377)
                  ·
                    refine ⟨19920319046648582205386533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26560425395531442940515377 19920319046648582205386533)
                    ·
                      refine ⟨3735059821246609163509975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19920319046648582205386533 3735059821246609163509975)
                      ·
                        rfl

theorem cell23_7274003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_7274003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274003 prefixEnd_7274003 := by exact prefixLift 7274003
  have htrace : WordTrace (prefixWord ++ tailWord_7274003) baseStart_7274003 baseEnd_7274003 := by
    simpa [prefixWord, tailWord_7274003, baseEnd_7274003] using wordTrace_append hprefix tailTrace_7274003
  have hstable : (prefixWord ++ tailWord_7274003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274003).length < 2 ^ (prefixWord ++ tailWord_7274003).sum := by decide
  have hdescent : baseEnd_7274003 < baseStart_7274003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274040 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_7274040 : Nat := 118140960795 + 7274040 * 2 ^ 59
def prefixEnd_7274040 : Nat := 4983230072969 + 3 ^ 40 * 7274040 * 2
def baseEnd_7274040 : Nat := 3735078820030825518747305

theorem tailTrace_7274040 : CollatzResearch.WordTrace tailWord_7274040 prefixEnd_7274040 3735078820030825518747305 := by
  unfold tailWord_7274040
  simp only [CollatzResearch.WordTrace]
  refine ⟨132653017283701430985993787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176870689711601907981325049 132653017283701430985993787)
  ·
    refine ⟨198979525925552146478990681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132653017283701430985993787 198979525925552146478990681)
    ·
      refine ⟨149234644444164109859243011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198979525925552146478990681 149234644444164109859243011)
      ·
        refine ⟨223851966666246164788864517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149234644444164109859243011 223851966666246164788864517)
        ·
          refine ⟨41972243749921155897912097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223851966666246164788864517 41972243749921155897912097)
          ·
            refine ⟨31479182812440866923434073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41972243749921155897912097 31479182812440866923434073)
            ·
              refine ⟨23609387109330650192575555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31479182812440866923434073 23609387109330650192575555)
              ·
                refine ⟨35414080663995975288863333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23609387109330650192575555 35414080663995975288863333)
                ·
                  refine ⟨6640140124499245366661875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35414080663995975288863333 6640140124499245366661875)
                  ·
                    refine ⟨9960210186748868049992813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6640140124499245366661875 9960210186748868049992813)
                    ·
                      refine ⟨3735078820030825518747305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9960210186748868049992813 3735078820030825518747305)
                      ·
                        rfl

theorem cell23_7274040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_7274040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274040 prefixEnd_7274040 := by exact prefixLift 7274040
  have htrace : WordTrace (prefixWord ++ tailWord_7274040) baseStart_7274040 baseEnd_7274040 := by
    simpa [prefixWord, tailWord_7274040, baseEnd_7274040] using wordTrace_append hprefix tailTrace_7274040
  have hstable : (prefixWord ++ tailWord_7274040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274040).length < 2 ^ (prefixWord ++ tailWord_7274040).sum := by decide
  have hdescent : baseEnd_7274040 < baseStart_7274040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274041 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7274041 : Nat := 118140960795 + 7274041 * 2 ^ 59
def prefixEnd_7274041 : Nat := 4983230072969 + 3 ^ 40 * 7274041 * 2
def baseEnd_7274041 : Nat := 3735079333511480014834801

theorem tailTrace_7274041 : CollatzResearch.WordTrace tailWord_7274041 prefixEnd_7274041 3735079333511480014834801 := by
  unfold tailWord_7274041
  simp only [CollatzResearch.WordTrace]
  refine ⟨265306071040399239142773977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176870714026932826095182651 265306071040399239142773977)
  ·
    refine ⟨198979553280299429357080483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265306071040399239142773977 198979553280299429357080483)
    ·
      refine ⟨298469329920449144035620725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198979553280299429357080483 298469329920449144035620725)
      ·
        refine ⟨27981499680042107253339443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298469329920449144035620725 27981499680042107253339443)
        ·
          refine ⟨41972249520063160880009165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27981499680042107253339443 41972249520063160880009165)
          ·
            refine ⟨15739593570023685330003437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41972249520063160880009165 15739593570023685330003437)
            ·
              refine ⟨5902347588758881998751289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15739593570023685330003437 5902347588758881998751289)
              ·
                refine ⟨4426760691569161499063467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902347588758881998751289 4426760691569161499063467)
                ·
                  refine ⟨6640141037353742248595201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426760691569161499063467 6640141037353742248595201)
                  ·
                    refine ⟨4980105778015306686446401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6640141037353742248595201 4980105778015306686446401)
                    ·
                      refine ⟨3735079333511480014834801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980105778015306686446401 3735079333511480014834801)
                      ·
                        rfl

theorem cell23_7274041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7274041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274041 prefixEnd_7274041 := by exact prefixLift 7274041
  have htrace : WordTrace (prefixWord ++ tailWord_7274041) baseStart_7274041 baseEnd_7274041 := by
    simpa [prefixWord, tailWord_7274041, baseEnd_7274041] using wordTrace_append hprefix tailTrace_7274041
  have hstable : (prefixWord ++ tailWord_7274041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274041).length < 2 ^ (prefixWord ++ tailWord_7274041).sum := by decide
  have hdescent : baseEnd_7274041 < baseStart_7274041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274061 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7274061 : Nat := 118140960795 + 7274061 * 2 ^ 59
def prefixEnd_7274061 : Nat := 4983230072969 + 3 ^ 40 * 7274061 * 2
def baseEnd_7274061 : Nat := 3735089603124569936584709

theorem tailTrace_7274061 : CollatzResearch.WordTrace tailWord_7274061 prefixEnd_7274061 3735089603124569936584709 := by
  unfold tailWord_7274061
  simp only [CollatzResearch.WordTrace]
  refine ⟨265306800500326782558502037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176871200333551188372334691 265306800500326782558502037)
  ·
    refine ⟨12436256273452817932429783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265306800500326782558502037 12436256273452817932429783)
    ·
      refine ⟨18654384410179226898644675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12436256273452817932429783 18654384410179226898644675)
      ·
        refine ⟨27981576615268840347967013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18654384410179226898644675 27981576615268840347967013)
        ·
          refine ⟨5246545615362907565243815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27981576615268840347967013 5246545615362907565243815)
          ·
            refine ⟨7869818423044361347865723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246545615362907565243815 7869818423044361347865723)
            ·
              refine ⟨11804727634566542021798585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7869818423044361347865723 11804727634566542021798585)
              ·
                refine ⟨8853545725924906516348939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11804727634566542021798585 8853545725924906516348939)
                ·
                  refine ⟨13280318588887359774523409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853545725924906516348939 13280318588887359774523409)
                  ·
                    refine ⟨9960238941665519830892557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13280318588887359774523409 9960238941665519830892557)
                    ·
                      refine ⟨3735089603124569936584709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9960238941665519830892557 3735089603124569936584709)
                      ·
                        rfl

theorem cell23_7274061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7274061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274061 prefixEnd_7274061 := by exact prefixLift 7274061
  have htrace : WordTrace (prefixWord ++ tailWord_7274061) baseStart_7274061 baseEnd_7274061 := by
    simpa [prefixWord, tailWord_7274061, baseEnd_7274061] using wordTrace_append hprefix tailTrace_7274061
  have hstable : (prefixWord ++ tailWord_7274061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274061).length < 2 ^ (prefixWord ++ tailWord_7274061).sum := by decide
  have hdescent : baseEnd_7274061 < baseStart_7274061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274083 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_7274083 : Nat := 118140960795 + 7274083 * 2 ^ 59
def prefixEnd_7274083 : Nat := 4983230072969 + 3 ^ 40 * 7274083 * 2
def baseEnd_7274083 : Nat := 3735100899698968850509607

theorem tailTrace_7274083 : CollatzResearch.WordTrace tailWord_7274083 prefixEnd_7274083 3735100899698968850509607 := by
  unfold tailWord_7274083
  simp only [CollatzResearch.WordTrace]
  refine ⟨265307602906247080315802903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176871735270831386877201935 265307602906247080315802903)
  ·
    refine ⟨397961404359370620473704355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265307602906247080315802903 397961404359370620473704355)
    ·
      refine ⟨596942106539055930710556533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397961404359370620473704355 596942106539055930710556533)
      ·
        refine ⟨55963322488036493504114675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596942106539055930710556533 55963322488036493504114675)
        ·
          refine ⟨83944983732054740256172013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55963322488036493504114675 83944983732054740256172013)
          ·
            refine ⟨31479368899520527596064505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83944983732054740256172013 31479368899520527596064505)
            ·
              refine ⟨23609526674640395697048379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31479368899520527596064505 23609526674640395697048379)
              ·
                refine ⟨35414290011960593545572569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23609526674640395697048379 35414290011960593545572569)
                ·
                  refine ⟨26560717508970445159179427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35414290011960593545572569 26560717508970445159179427)
                  ·
                    refine ⟨39841076263455667738769141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26560717508970445159179427 39841076263455667738769141)
                    ·
                      refine ⟨3735100899698968850509607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39841076263455667738769141 3735100899698968850509607)
                      ·
                        rfl

theorem cell23_7274083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_7274083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274083 prefixEnd_7274083 := by exact prefixLift 7274083
  have htrace : WordTrace (prefixWord ++ tailWord_7274083) baseStart_7274083 baseEnd_7274083 := by
    simpa [prefixWord, tailWord_7274083, baseEnd_7274083] using wordTrace_append hprefix tailTrace_7274083
  have hstable : (prefixWord ++ tailWord_7274083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274083).length < 2 ^ (prefixWord ++ tailWord_7274083).sum := by decide
  have hdescent : baseEnd_7274083 < baseStart_7274083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274084 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_7274084 : Nat := 118140960795 + 7274084 * 2 ^ 59
def prefixEnd_7274084 : Nat := 4983230072969 + 3 ^ 40 * 7274084 * 2
def baseEnd_7274084 : Nat := 3735101413179623346597103

theorem tailTrace_7274084 : CollatzResearch.WordTrace tailWord_7274084 prefixEnd_7274084 3735101413179623346597103 := by
  unfold tailWord_7274084
  simp only [CollatzResearch.WordTrace]
  refine ⟨132653819689621728743294653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176871759586162304991059537 132653819689621728743294653)
  ·
    refine ⟨49745182383608148278735495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132653819689621728743294653 49745182383608148278735495)
    ·
      refine ⟨74617773575412222418103243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49745182383608148278735495 74617773575412222418103243)
      ·
        refine ⟨111926660363118333627154865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74617773575412222418103243 111926660363118333627154865)
        ·
          refine ⟨83944995272338750220366149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111926660363118333627154865 83944995272338750220366149)
          ·
            refine ⟨15739686613563515666318653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83944995272338750220366149 15739686613563515666318653)
            ·
              refine ⟨5902382480086318374869495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15739686613563515666318653 5902382480086318374869495)
              ·
                refine ⟨8853573720129477562304243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902382480086318374869495 8853573720129477562304243)
                ·
                  refine ⟨13280360580194216343456365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853573720129477562304243 13280360580194216343456365)
                  ·
                    refine ⟨4980135217572831128796137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13280360580194216343456365 4980135217572831128796137)
                    ·
                      refine ⟨3735101413179623346597103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980135217572831128796137 3735101413179623346597103)
                      ·
                        rfl

theorem cell23_7274084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_7274084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274084 prefixEnd_7274084 := by exact prefixLift 7274084
  have htrace : WordTrace (prefixWord ++ tailWord_7274084) baseStart_7274084 baseEnd_7274084 := by
    simpa [prefixWord, tailWord_7274084, baseEnd_7274084] using wordTrace_append hprefix tailTrace_7274084
  have hstable : (prefixWord ++ tailWord_7274084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274084).length < 2 ^ (prefixWord ++ tailWord_7274084).sum := by decide
  have hdescent : baseEnd_7274084 < baseStart_7274084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274183 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_7274183 : Nat := 118140960795 + 7274183 * 2 ^ 59
def prefixEnd_7274183 : Nat := 4983230072969 + 3 ^ 40 * 7274183 * 2
def baseEnd_7274183 : Nat := 3735152247764418459259147

theorem tailTrace_7274183 : CollatzResearch.WordTrace tailWord_7274183 prefixEnd_7274183 3735152247764418459259147 := by
  unfold tailWord_7274183
  simp only [CollatzResearch.WordTrace]
  refine ⟨265311250205884797394443203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176874166803923198262962135 265311250205884797394443203)
  ·
    refine ⟨397966875308827196091664805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265311250205884797394443203 397966875308827196091664805)
    ·
      refine ⟨74618789120405099267187151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397966875308827196091664805 74618789120405099267187151)
      ·
        refine ⟨111928183680607648900780727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74618789120405099267187151 111928183680607648900780727)
        ·
          refine ⟨167892275520911473351171091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111928183680607648900780727 167892275520911473351171091)
          ·
            refine ⟨251838413281367210026756637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167892275520911473351171091 251838413281367210026756637)
            ·
              refine ⟨94439404980512703760033739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251838413281367210026756637 94439404980512703760033739)
              ·
                refine ⟨141659107470769055640050609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94439404980512703760033739 141659107470769055640050609)
                ·
                  refine ⟨106244330603076791730037957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141659107470769055640050609 106244330603076791730037957)
                  ·
                    refine ⟨19920811988076898449382117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106244330603076791730037957 19920811988076898449382117)
                    ·
                      refine ⟨3735152247764418459259147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19920811988076898449382117 3735152247764418459259147)
                      ·
                        rfl

theorem cell23_7274183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_7274183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274183 prefixEnd_7274183 := by exact prefixLift 7274183
  have htrace : WordTrace (prefixWord ++ tailWord_7274183) baseStart_7274183 baseEnd_7274183 := by
    simpa [prefixWord, tailWord_7274183, baseEnd_7274183] using wordTrace_append hprefix tailTrace_7274183
  have hstable : (prefixWord ++ tailWord_7274183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274183).length < 2 ^ (prefixWord ++ tailWord_7274183).sum := by decide
  have hdescent : baseEnd_7274183 < baseStart_7274183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274190 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_7274190 : Nat := 118140960795 + 7274190 * 2 ^ 59
def prefixEnd_7274190 : Nat := 4983230072969 + 3 ^ 40 * 7274190 * 2
def baseEnd_7274190 : Nat := 3735155842128999931871615

theorem tailTrace_7274190 : CollatzResearch.WordTrace tailWord_7274190 prefixEnd_7274190 3735155842128999931871615 := by
  unfold tailWord_7274190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33163938189607429698743503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176874337011239625059965349 33163938189607429698743503)
  ·
    refine ⟨49745907284411144548115255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33163938189607429698743503 49745907284411144548115255)
    ·
      refine ⟨74618860926616716822172883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49745907284411144548115255 74618860926616716822172883)
      ·
        refine ⟨111928291389925075233259325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74618860926616716822172883 111928291389925075233259325)
        ·
          refine ⟨41973109271221903212472247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111928291389925075233259325 41973109271221903212472247)
          ·
            refine ⟨62959663906832854818708371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41973109271221903212472247 62959663906832854818708371)
            ·
              refine ⟨94439495860249282228062557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62959663906832854818708371 94439495860249282228062557)
              ·
                refine ⟨35414810947593480835523459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94439495860249282228062557 35414810947593480835523459)
                ·
                  refine ⟨53122216421390221253285189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35414810947593480835523459 53122216421390221253285189)
                  ·
                    refine ⟨9960415579010666484990973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53122216421390221253285189 9960415579010666484990973)
                    ·
                      refine ⟨3735155842128999931871615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9960415579010666484990973 3735155842128999931871615)
                      ·
                        rfl

theorem cell23_7274190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_7274190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274190 prefixEnd_7274190 := by exact prefixLift 7274190
  have htrace : WordTrace (prefixWord ++ tailWord_7274190) baseStart_7274190 baseEnd_7274190 := by
    simpa [prefixWord, tailWord_7274190, baseEnd_7274190] using wordTrace_append hprefix tailTrace_7274190
  have hstable : (prefixWord ++ tailWord_7274190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274190).length < 2 ^ (prefixWord ++ tailWord_7274190).sum := by decide
  have hdescent : baseEnd_7274190 < baseStart_7274190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274193 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 8]
def baseStart_7274193 : Nat := 118140960795 + 7274193 * 2 ^ 59
def prefixEnd_7274193 : Nat := 4983230072969 + 3 ^ 40 * 7274193 * 2
def baseEnd_7274193 : Nat := 415017486952329268903789

theorem tailTrace_7274193 : CollatzResearch.WordTrace tailWord_7274193 prefixEnd_7274193 415017486952329268903789 := by
  unfold tailWord_7274193
  simp only [CollatzResearch.WordTrace]
  refine ⟨265311614935848569102307233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176874409957232379401538155 265311614935848569102307233)
  ·
    refine ⟨198983711201886426826730425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265311614935848569102307233 198983711201886426826730425)
    ·
      refine ⟨149237783401414820120047819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198983711201886426826730425 149237783401414820120047819)
      ·
        refine ⟨223856675102122230180071729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149237783401414820120047819 223856675102122230180071729)
        ·
          refine ⟨167892506326591672635053797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223856675102122230180071729 167892506326591672635053797)
          ·
            refine ⟨31479844936235938619072587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167892506326591672635053797 31479844936235938619072587)
            ·
              refine ⟨47219767404353907928608881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31479844936235938619072587 47219767404353907928608881)
              ·
                refine ⟨35414825553265430946456661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47219767404353907928608881 35414825553265430946456661)
                ·
                  refine ⟨415017486952329268903789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35414825553265430946456661 415017486952329268903789)
                  ·
                    rfl

theorem cell23_7274193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_7274193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274193 prefixEnd_7274193 := by exact prefixLift 7274193
  have htrace : WordTrace (prefixWord ++ tailWord_7274193) baseStart_7274193 baseEnd_7274193 := by
    simpa [prefixWord, tailWord_7274193, baseEnd_7274193] using wordTrace_append hprefix tailTrace_7274193
  have hstable : (prefixWord ++ tailWord_7274193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274193).length < 2 ^ (prefixWord ++ tailWord_7274193).sum := by decide
  have hdescent : baseEnd_7274193 < baseStart_7274193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274204 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7274204 : Nat := 118140960795 + 7274204 * 2 ^ 59
def prefixEnd_7274204 : Nat := 4983230072969 + 3 ^ 40 * 7274204 * 2
def baseEnd_7274204 : Nat := 3735163030858162877096551

theorem tailTrace_7274204 : CollatzResearch.WordTrace tailWord_7274204 prefixEnd_7274204 3735163030858162877096551 := by
  unfold tailWord_7274204
  simp only [CollatzResearch.WordTrace]
  refine ⟨132656008069404358990478833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176874677425872478653971777 132656008069404358990478833)
  ·
    refine ⟨99492006052053269242859125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132656008069404358990478833 99492006052053269242859125)
    ·
      refine ⟨9327375567379993991518043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99492006052053269242859125 9327375567379993991518043)
      ·
        refine ⟨13991063351069990987277065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9327375567379993991518043 13991063351069990987277065)
        ·
          refine ⟨10493297513302493240457799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13991063351069990987277065 10493297513302493240457799)
          ·
            refine ⟨15739946269953739860686699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10493297513302493240457799 15739946269953739860686699)
            ·
              refine ⟨23609919404930609791030049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15739946269953739860686699 23609919404930609791030049)
              ·
                refine ⟨17707439553697957343272537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23609919404930609791030049 17707439553697957343272537)
                ·
                  refine ⟨13280579665273468007454403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17707439553697957343272537 13280579665273468007454403)
                  ·
                    refine ⟨19920869497910202011181605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13280579665273468007454403 19920869497910202011181605)
                    ·
                      refine ⟨3735163030858162877096551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19920869497910202011181605 3735163030858162877096551)
                      ·
                        rfl

theorem cell23_7274204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7274204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274204 prefixEnd_7274204 := by exact prefixLift 7274204
  have htrace : WordTrace (prefixWord ++ tailWord_7274204) baseStart_7274204 baseEnd_7274204 := by
    simpa [prefixWord, tailWord_7274204, baseEnd_7274204] using wordTrace_append hprefix tailTrace_7274204
  have hstable : (prefixWord ++ tailWord_7274204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274204).length < 2 ^ (prefixWord ++ tailWord_7274204).sum := by decide
  have hdescent : baseEnd_7274204 < baseStart_7274204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274294 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7274294 : Nat := 118140960795 + 7274294 * 2 ^ 59
def prefixEnd_7274294 : Nat := 4983230072969 + 3 ^ 40 * 7274294 * 2
def baseEnd_7274294 : Nat := 3735209244117067524971137

theorem tailTrace_7274294 : CollatzResearch.WordTrace tailWord_7274294 prefixEnd_7274294 3735209244117067524971137 := by
  unfold tailWord_7274294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16582206169280166459483371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176876865805655108901155957 16582206169280166459483371)
  ·
    refine ⟨24873309253920249689225057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16582206169280166459483371 24873309253920249689225057)
    ·
      refine ⟨18654981940440187266918793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24873309253920249689225057 18654981940440187266918793)
      ·
        refine ⟨13991236455330140450189095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18654981940440187266918793 13991236455330140450189095)
        ·
          refine ⟨20986854682995210675283643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13991236455330140450189095 20986854682995210675283643)
          ·
            refine ⟨31480282024492816012925465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20986854682995210675283643 31480282024492816012925465)
            ·
              refine ⟨23610211518369612009694099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31480282024492816012925465 23610211518369612009694099)
              ·
                refine ⟨35415317277554418014541149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23610211518369612009694099 35415317277554418014541149)
                ·
                  refine ⟨13280743979082906755452931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35415317277554418014541149 13280743979082906755452931)
                  ·
                    refine ⟨19921115968624360133179397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13280743979082906755452931 19921115968624360133179397)
                    ·
                      refine ⟨3735209244117067524971137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19921115968624360133179397 3735209244117067524971137)
                      ·
                        rfl

theorem cell23_7274294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7274294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274294 prefixEnd_7274294 := by exact prefixLift 7274294
  have htrace : WordTrace (prefixWord ++ tailWord_7274294) baseStart_7274294 baseEnd_7274294 := by
    simpa [prefixWord, tailWord_7274294, baseEnd_7274294] using wordTrace_append hprefix tailTrace_7274294
  have hstable : (prefixWord ++ tailWord_7274294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274294).length < 2 ^ (prefixWord ++ tailWord_7274294).sum := by decide
  have hdescent : baseEnd_7274294 < baseStart_7274294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274311 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_7274311 : Nat := 118140960795 + 7274311 * 2 ^ 59
def prefixEnd_7274311 : Nat := 4983230072969 + 3 ^ 40 * 7274311 * 2
def baseEnd_7274311 : Nat := 3735217973288193958458559

theorem tailTrace_7274311 : CollatzResearch.WordTrace tailWord_7274311 prefixEnd_7274311 3735217973288193958458559 := by
  unfold tailWord_7274311
  simp only [CollatzResearch.WordTrace]
  refine ⟨265315918749421075255102787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176877279166280716836735191 265315918749421075255102787)
  ·
    refine ⟨397973878124131612882654181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265315918749421075255102787 397973878124131612882654181)
    ·
      refine ⟨74620102148274677415497659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397973878124131612882654181 74620102148274677415497659)
      ·
        refine ⟨111930153222412016123246489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74620102148274677415497659 111930153222412016123246489)
        ·
          refine ⟨83947614916809012092434867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111930153222412016123246489 83947614916809012092434867)
          ·
            refine ⟨125921422375213518138652301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83947614916809012092434867 125921422375213518138652301)
            ·
              refine ⟨47220533390705069301994613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125921422375213518138652301 47220533390705069301994613)
              ·
                refine ⟨4426925005378600247061995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47220533390705069301994613 4426925005378600247061995)
                ·
                  refine ⟨6640387508067900370592993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426925005378600247061995 6640387508067900370592993)
                  ·
                    refine ⟨4980290631050925277944745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6640387508067900370592993 4980290631050925277944745)
                    ·
                      refine ⟨3735217973288193958458559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980290631050925277944745 3735217973288193958458559)
                      ·
                        rfl

theorem cell23_7274311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_7274311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274311 prefixEnd_7274311 := by exact prefixLift 7274311
  have htrace : WordTrace (prefixWord ++ tailWord_7274311) baseStart_7274311 baseEnd_7274311 := by
    simpa [prefixWord, tailWord_7274311, baseEnd_7274311] using wordTrace_append hprefix tailTrace_7274311
  have hstable : (prefixWord ++ tailWord_7274311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274311).length < 2 ^ (prefixWord ++ tailWord_7274311).sum := by decide
  have hdescent : baseEnd_7274311 < baseStart_7274311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274317 : List Nat := [1, 6, 1, 2, 1, 2, 10]
def baseStart_7274317 : Nat := 118140960795 + 7274317 * 2 ^ 59
def prefixEnd_7274317 : Nat := 4983230072969 + 3 ^ 40 * 7274317 * 2
def baseEnd_7274317 : Nat := 46113840174964455987451

theorem tailTrace_7274317 : CollatzResearch.WordTrace tailWord_7274317 prefixEnd_7274317 46113840174964455987451 := by
  unfold tailWord_7274317
  simp only [CollatzResearch.WordTrace]
  refine ⟨265316137587399338279821205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176877425058266225519880803 265316137587399338279821205)
  ·
    refine ⟨12436693949409343981866619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265316137587399338279821205 12436693949409343981866619)
    ·
      refine ⟨18655040924114015972799929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12436693949409343981866619 18655040924114015972799929)
      ·
        refine ⟨13991280693085511979599947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18655040924114015972799929 13991280693085511979599947)
        ·
          refine ⟨20986921039628267969399921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13991280693085511979599947 20986921039628267969399921)
          ·
            refine ⟨15740190779721200977049941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20986921039628267969399921 15740190779721200977049941)
            ·
              refine ⟨46113840174964455987451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15740190779721200977049941 46113840174964455987451)
              ·
                rfl

theorem cell23_7274317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 10].length) (baseStart_7274317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274317 prefixEnd_7274317 := by exact prefixLift 7274317
  have htrace : WordTrace (prefixWord ++ tailWord_7274317) baseStart_7274317 baseEnd_7274317 := by
    simpa [prefixWord, tailWord_7274317, baseEnd_7274317] using wordTrace_append hprefix tailTrace_7274317
  have hstable : (prefixWord ++ tailWord_7274317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274317).length < 2 ^ (prefixWord ++ tailWord_7274317).sum := by decide
  have hdescent : baseEnd_7274317 < baseStart_7274317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274367 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 3, 4, 2]
def baseStart_7274367 : Nat := 118140960795 + 7274367 * 2 ^ 59
def prefixEnd_7274367 : Nat := 4983230072969 + 3 ^ 40 * 7274367 * 2
def baseEnd_7274367 : Nat := 3735246728204845739358301

theorem tailTrace_7274367 : CollatzResearch.WordTrace tailWord_7274367 prefixEnd_7274367 3735246728204845739358301 := by
  unfold tailWord_7274367
  simp only [CollatzResearch.WordTrace]
  refine ⟨265317961237218196819141355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176878640824812131212760903 265317961237218196819141355)
  ·
    refine ⟨397976941855827295228712033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265317961237218196819141355 397976941855827295228712033)
    ·
      refine ⟨298482706391870471421534025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397976941855827295228712033 298482706391870471421534025)
      ·
        refine ⟨223862029793902853566150519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298482706391870471421534025 223862029793902853566150519)
        ·
          refine ⟨335793044690854280349225779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223862029793902853566150519 335793044690854280349225779)
          ·
            refine ⟨503689567036281420523838669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335793044690854280349225779 503689567036281420523838669)
            ·
              refine ⟨188883587638605532696439501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503689567036281420523838669 188883587638605532696439501)
              ·
                refine ⟨70831345364477074761164813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188883587638605532696439501 70831345364477074761164813)
                ·
                  refine ⟨26561754511678903035436805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70831345364477074761164813 26561754511678903035436805)
                  ·
                    refine ⟨4980328970939794319144401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26561754511678903035436805 4980328970939794319144401)
                    ·
                      refine ⟨3735246728204845739358301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980328970939794319144401 3735246728204845739358301)
                      ·
                        rfl

theorem cell23_7274367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_7274367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274367 prefixEnd_7274367 := by exact prefixLift 7274367
  have htrace : WordTrace (prefixWord ++ tailWord_7274367) baseStart_7274367 baseEnd_7274367 := by
    simpa [prefixWord, tailWord_7274367, baseEnd_7274367] using wordTrace_append hprefix tailTrace_7274367
  have hstable : (prefixWord ++ tailWord_7274367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274367).length < 2 ^ (prefixWord ++ tailWord_7274367).sum := by decide
  have hdescent : baseEnd_7274367 < baseStart_7274367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274427 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 7, 2]
def baseStart_7274427 : Nat := 118140960795 + 7274427 * 2 ^ 59
def prefixEnd_7274427 : Nat := 4983230072969 + 3 ^ 40 * 7274427 * 2
def baseEnd_7274427 : Nat := 3735277537044115504608025

theorem tailTrace_7274427 : CollatzResearch.WordTrace tailWord_7274427 prefixEnd_7274427 3735277537044115504608025 := by
  unfold tailWord_7274427
  simp only [CollatzResearch.WordTrace]
  refine ⟨265320149617000827066325535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176880099744667218044217023 265320149617000827066325535)
  ·
    refine ⟨397980224425501240599488303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265320149617000827066325535 397980224425501240599488303)
    ·
      refine ⟨596970336638251860899232455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397980224425501240599488303 596970336638251860899232455)
      ·
        refine ⟨895455504957377791348848683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596970336638251860899232455 895455504957377791348848683)
        ·
          refine ⟨1343183257436066687023273025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895455504957377791348848683 1343183257436066687023273025)
          ·
            refine ⟨1007387443077050015267454769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1343183257436066687023273025 1007387443077050015267454769)
            ·
              refine ⟨755540582307787511450591077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007387443077050015267454769 755540582307787511450591077)
              ·
                refine ⟨141663859182710158396985827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755540582307787511450591077 141663859182710158396985827)
                ·
                  refine ⟨212495788774065237595478741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141663859182710158396985827 212495788774065237595478741)
                  ·
                    refine ⟨4980370049392154006144033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 212495788774065237595478741 4980370049392154006144033)
                    ·
                      refine ⟨3735277537044115504608025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980370049392154006144033 3735277537044115504608025)
                      ·
                        rfl

theorem cell23_7274427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7, 2].length) (baseStart_7274427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274427 prefixEnd_7274427 := by exact prefixLift 7274427
  have htrace : WordTrace (prefixWord ++ tailWord_7274427) baseStart_7274427 baseEnd_7274427 := by
    simpa [prefixWord, tailWord_7274427, baseEnd_7274427] using wordTrace_append hprefix tailTrace_7274427
  have hstable : (prefixWord ++ tailWord_7274427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274427).length < 2 ^ (prefixWord ++ tailWord_7274427).sum := by decide
  have hdescent : baseEnd_7274427 < baseStart_7274427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274444 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7274444 : Nat := 118140960795 + 7274444 * 2 ^ 59
def prefixEnd_7274444 : Nat := 4983230072969 + 3 ^ 40 * 7274444 * 2
def baseEnd_7274444 : Nat := 3735286266215241938095447

theorem tailTrace_7274444 : CollatzResearch.WordTrace tailWord_7274444 prefixEnd_7274444 3735286266215241938095447 := by
  unfold tailWord_7274444
  simp only [CollatzResearch.WordTrace]
  refine ⟨132660384828969619484847193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176880513105292825979796257 132660384828969619484847193)
  ·
    refine ⟨99495288621727214613635395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132660384828969619484847193 99495288621727214613635395)
    ·
      refine ⟨149242932932590821920453093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99495288621727214613635395 149242932932590821920453093)
      ·
        refine ⟨27983049924860779110084955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149242932932590821920453093 27983049924860779110084955)
        ·
          refine ⟨41974574887291168665127433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27983049924860779110084955 41974574887291168665127433)
          ·
            refine ⟨31480931165468376498845575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41974574887291168665127433 31480931165468376498845575)
            ·
              refine ⟨47221396748202564748268363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31480931165468376498845575 47221396748202564748268363)
              ·
                refine ⟨70832095122303847122402545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47221396748202564748268363 70832095122303847122402545)
                ·
                  refine ⟨53124071341727885341801909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70832095122303847122402545 53124071341727885341801909)
                  ·
                    refine ⟨4980381688286989250793929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53124071341727885341801909 4980381688286989250793929)
                    ·
                      refine ⟨3735286266215241938095447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980381688286989250793929 3735286266215241938095447)
                      ·
                        rfl

theorem cell23_7274444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7274444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274444 prefixEnd_7274444 := by exact prefixLift 7274444
  have htrace : WordTrace (prefixWord ++ tailWord_7274444) baseStart_7274444 baseEnd_7274444 := by
    simpa [prefixWord, tailWord_7274444, baseEnd_7274444] using wordTrace_append hprefix tailTrace_7274444
  have hstable : (prefixWord ++ tailWord_7274444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274444).length < 2 ^ (prefixWord ++ tailWord_7274444).sum := by decide
  have hdescent : baseEnd_7274444 < baseStart_7274444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274471 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 2, 5]
def baseStart_7274471 : Nat := 118140960795 + 7274471 * 2 ^ 59
def prefixEnd_7274471 : Nat := 4983230072969 + 3 ^ 40 * 7274471 * 2
def baseEnd_7274471 : Nat := 1245100043397637777485941

theorem tailTrace_7274471 : CollatzResearch.WordTrace tailWord_7274471 prefixEnd_7274471 1245100043397637777485941 := by
  unfold tailWord_7274471
  simp only [CollatzResearch.WordTrace]
  refine ⟨265321754428841422580927267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176881169619227615053951511 265321754428841422580927267)
  ·
    refine ⟨397982631643262133871390901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265321754428841422580927267 397982631643262133871390901)
    ·
      refine ⟨37310871716555825050442897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397982631643262133871390901 37310871716555825050442897)
      ·
        refine ⟨27983153787416868787832173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37310871716555825050442897 27983153787416868787832173)
        ·
          refine ⟨10493682670281325795437065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27983153787416868787832173 10493682670281325795437065)
          ·
            refine ⟨7870262002710994346577799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10493682670281325795437065 7870262002710994346577799)
            ·
              refine ⟨11805393004066491519866699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7870262002710994346577799 11805393004066491519866699)
              ·
                refine ⟨17708089506099737279800049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11805393004066491519866699 17708089506099737279800049)
                ·
                  refine ⟨13281067129574802959850037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17708089506099737279800049 13281067129574802959850037)
                  ·
                    refine ⟨1245100043397637777485941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13281067129574802959850037 1245100043397637777485941)
                    ·
                      rfl

theorem cell23_7274471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_7274471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274471 prefixEnd_7274471 := by exact prefixLift 7274471
  have htrace : WordTrace (prefixWord ++ tailWord_7274471) baseStart_7274471 baseEnd_7274471 := by
    simpa [prefixWord, tailWord_7274471, baseEnd_7274471] using wordTrace_append hprefix tailTrace_7274471
  have hstable : (prefixWord ++ tailWord_7274471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274471).length < 2 ^ (prefixWord ++ tailWord_7274471).sum := by decide
  have hdescent : baseEnd_7274471 < baseStart_7274471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274474 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_7274474 : Nat := 118140960795 + 7274474 * 2 ^ 59
def prefixEnd_7274474 : Nat := 4983230072969 + 3 ^ 40 * 7274474 * 2
def baseEnd_7274474 : Nat := 3735301670634876820720309

theorem tailTrace_7274474 : CollatzResearch.WordTrace tailWord_7274474 prefixEnd_7274474 3735301670634876820720309 := by
  unfold tailWord_7274474
  simp only [CollatzResearch.WordTrace]
  refine ⟨66330465961957638523321619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176881242565220369395524317 66330465961957638523321619)
  ·
    refine ⟨99495698942936457784982429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66330465961957638523321619 99495698942936457784982429)
    ·
      refine ⟨37310887103601171669368411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99495698942936457784982429 37310887103601171669368411)
      ·
        refine ⟨55966330655401757504052617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37310887103601171669368411 55966330655401757504052617)
        ·
          refine ⟨41974747991551318128039463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55966330655401757504052617 41974747991551318128039463)
          ·
            refine ⟨62962121987326977192059195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41974747991551318128039463 62962121987326977192059195)
            ·
              refine ⟨94443182980990465788088793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62962121987326977192059195 94443182980990465788088793)
              ·
                refine ⟨70832387235742849341066595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94443182980990465788088793 70832387235742849341066595)
                ·
                  refine ⟨106248580853614274011599893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70832387235742849341066595 106248580853614274011599893)
                  ·
                    refine ⟨4980402227513169094293745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106248580853614274011599893 4980402227513169094293745)
                    ·
                      refine ⟨3735301670634876820720309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980402227513169094293745 3735301670634876820720309)
                      ·
                        rfl

theorem cell23_7274474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_7274474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274474 prefixEnd_7274474 := by exact prefixLift 7274474
  have htrace : WordTrace (prefixWord ++ tailWord_7274474) baseStart_7274474 baseEnd_7274474 := by
    simpa [prefixWord, tailWord_7274474, baseEnd_7274474] using wordTrace_append hprefix tailTrace_7274474
  have hstable : (prefixWord ++ tailWord_7274474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274474).length < 2 ^ (prefixWord ++ tailWord_7274474).sum := by decide
  have hdescent : baseEnd_7274474 < baseStart_7274474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274497 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 8]
def baseStart_7274497 : Nat := 118140960795 + 7274497 * 2 ^ 59
def prefixEnd_7274497 : Nat := 4983230072969 + 3 ^ 40 * 7274497 * 2
def baseEnd_7274497 : Nat := 415034831187770025636967

theorem tailTrace_7274497 : CollatzResearch.WordTrace tailWord_7274497 prefixEnd_7274497 415034831187770025636967 := by
  unfold tailWord_7274497
  simp only [CollatzResearch.WordTrace]
  refine ⟨265322702726747229021373745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176881801817831486014249163 265322702726747229021373745)
  ·
    refine ⟨198992027045060421766030309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265322702726747229021373745 198992027045060421766030309)
    ·
      refine ⟨37311005070948829081130683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198992027045060421766030309 37311005070948829081130683)
      ·
        refine ⟨55966507606423243621696025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37311005070948829081130683 55966507606423243621696025)
        ·
          refine ⟨41974880704817432716272019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55966507606423243621696025 41974880704817432716272019)
          ·
            refine ⟨62962321057226149074408029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41974880704817432716272019 62962321057226149074408029)
            ·
              refine ⟨23610870396459805902903011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62962321057226149074408029 23610870396459805902903011)
              ·
                refine ⟨35416305594689708854354517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23610870396459805902903011 35416305594689708854354517)
                ·
                  refine ⟨415034831187770025636967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35416305594689708854354517 415034831187770025636967)
                  ·
                    rfl

theorem cell23_7274497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_7274497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274497 prefixEnd_7274497 := by exact prefixLift 7274497
  have htrace : WordTrace (prefixWord ++ tailWord_7274497) baseStart_7274497 baseEnd_7274497 := by
    simpa [prefixWord, tailWord_7274497, baseEnd_7274497] using wordTrace_append hprefix tailTrace_7274497
  have hstable : (prefixWord ++ tailWord_7274497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274497).length < 2 ^ (prefixWord ++ tailWord_7274497).sum := by decide
  have hdescent : baseEnd_7274497 < baseStart_7274497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274501 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_7274501 : Nat := 118140960795 + 7274501 * 2 ^ 59
def prefixEnd_7274501 : Nat := 4983230072969 + 3 ^ 40 * 7274501 * 2
def baseEnd_7274501 : Nat := 1245105178204182738360895

theorem tailTrace_7274501 : CollatzResearch.WordTrace tailWord_7274501 prefixEnd_7274501 1245105178204182738360895 := by
  unfold tailWord_7274501
  simp only [CollatzResearch.WordTrace]
  refine ⟨265322848618732737704519357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176881899079155158469679571 265322848618732737704519357)
  ·
    refine ⟨99496068232024776639194759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265322848618732737704519357 99496068232024776639194759)
    ·
      refine ⟨149244102348037164958792139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99496068232024776639194759 149244102348037164958792139)
      ·
        refine ⟨223866153522055747438188209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149244102348037164958792139 223866153522055747438188209)
        ·
          refine ⟨167899615141541810578641157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223866153522055747438188209 167899615141541810578641157)
          ·
            refine ⟨31481177839039089483495217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167899615141541810578641157 31481177839039089483495217)
            ·
              refine ⟨23610883379279317112621413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31481177839039089483495217 23610883379279317112621413)
              ·
                refine ⟨4427040633614871958616515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23610883379279317112621413 4427040633614871958616515)
                ·
                  refine ⟨6640560950422307937924773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427040633614871958616515 6640560950422307937924773)
                  ·
                    refine ⟨1245105178204182738360895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6640560950422307937924773 1245105178204182738360895)
                    ·
                      rfl

theorem cell23_7274501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_7274501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274501 prefixEnd_7274501 := by exact prefixLift 7274501
  have htrace : WordTrace (prefixWord ++ tailWord_7274501) baseStart_7274501 baseEnd_7274501 := by
    simpa [prefixWord, tailWord_7274501, baseEnd_7274501] using wordTrace_append hprefix tailTrace_7274501
  have hstable : (prefixWord ++ tailWord_7274501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274501).length < 2 ^ (prefixWord ++ tailWord_7274501).sum := by decide
  have hdescent : baseEnd_7274501 < baseStart_7274501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274544 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_7274544 : Nat := 118140960795 + 7274544 * 2 ^ 59
def prefixEnd_7274544 : Nat := 4983230072969 + 3 ^ 40 * 7274544 * 2
def baseEnd_7274544 : Nat := 1245112538093563848948329

theorem tailTrace_7274544 : CollatzResearch.WordTrace tailWord_7274544 prefixEnd_7274544 1245112538093563848948329 := by
  unfold tailWord_7274544
  simp only [CollatzResearch.WordTrace]
  refine ⟨132662208478788478024167343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176882944638384637365556457 132662208478788478024167343)
  ·
    refine ⟨198993312718182717036251015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132662208478788478024167343 198993312718182717036251015)
    ·
      refine ⟨298489969077274075554376523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198993312718182717036251015 298489969077274075554376523)
      ·
        refine ⟨447734953615911113331564785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298489969077274075554376523 447734953615911113331564785)
        ·
          refine ⟨335801215211933334998673589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447734953615911113331564785 335801215211933334998673589)
          ·
            refine ⟨31481363926118750156125649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335801215211933334998673589 31481363926118750156125649)
            ·
              refine ⟨23611022944589062617094237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31481363926118750156125649 23611022944589062617094237)
              ·
                refine ⟨8854133604220898481410339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23611022944589062617094237 8854133604220898481410339)
                ·
                  refine ⟨13281200406331347722115509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854133604220898481410339 13281200406331347722115509)
                  ·
                    refine ⟨1245112538093563848948329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13281200406331347722115509 1245112538093563848948329)
                    ·
                      rfl

theorem cell23_7274544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_7274544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274544 prefixEnd_7274544 := by exact prefixLift 7274544
  have htrace : WordTrace (prefixWord ++ tailWord_7274544) baseStart_7274544 baseEnd_7274544 := by
    simpa [prefixWord, tailWord_7274544, baseEnd_7274544] using wordTrace_append hprefix tailTrace_7274544
  have hstable : (prefixWord ++ tailWord_7274544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274544).length < 2 ^ (prefixWord ++ tailWord_7274544).sum := by decide
  have hdescent : baseEnd_7274544 < baseStart_7274544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274578 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_7274578 : Nat := 118140960795 + 7274578 * 2 ^ 59
def prefixEnd_7274578 : Nat := 4983230072969 + 3 ^ 40 * 7274578 * 2
def baseEnd_7274578 : Nat := 1245118357540981471273277

theorem tailTrace_7274578 : CollatzResearch.WordTrace tailWord_7274578 prefixEnd_7274578 1245118357540981471273277 := by
  unfold tailWord_7274578
  simp only [CollatzResearch.WordTrace]
  refine ⟨66331414259863444963768097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176883771359635853236714925 66331414259863444963768097)
  ·
    refine ⟨49748560694897583722826073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66331414259863444963768097 49748560694897583722826073)
    ·
      refine ⟨37311420521173187792119555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49748560694897583722826073 37311420521173187792119555)
      ·
        refine ⟨55967130781759781688179333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37311420521173187792119555 55967130781759781688179333)
        ·
          refine ⟨10493837021579959066533625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55967130781759781688179333 10493837021579959066533625)
          ·
            refine ⟨7870377766184969299900219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10493837021579959066533625 7870377766184969299900219)
            ·
              refine ⟨11805566649277453949850329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7870377766184969299900219 11805566649277453949850329)
              ·
                refine ⟨8854174986958090462387747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11805566649277453949850329 8854174986958090462387747)
                ·
                  refine ⟨13281262480437135693581621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854174986958090462387747 13281262480437135693581621)
                  ·
                    refine ⟨1245118357540981471273277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13281262480437135693581621 1245118357540981471273277)
                    ·
                      rfl

theorem cell23_7274578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_7274578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274578 prefixEnd_7274578 := by exact prefixLift 7274578
  have htrace : WordTrace (prefixWord ++ tailWord_7274578) baseStart_7274578 baseEnd_7274578 := by
    simpa [prefixWord, tailWord_7274578, baseEnd_7274578] using wordTrace_append hprefix tailTrace_7274578
  have hstable : (prefixWord ++ tailWord_7274578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274578).length < 2 ^ (prefixWord ++ tailWord_7274578).sum := by decide
  have hdescent : baseEnd_7274578 < baseStart_7274578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274581 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7274581 : Nat := 118140960795 + 7274581 * 2 ^ 59
def prefixEnd_7274581 : Nat := 4983230072969 + 3 ^ 40 * 7274581 * 2
def baseEnd_7274581 : Nat := 3735356613064907902082317

theorem tailTrace_7274581 : CollatzResearch.WordTrace tailWord_7274581 prefixEnd_7274581 3735356613064907902082317 := by
  unfold tailWord_7274581
  simp only [CollatzResearch.WordTrace]
  refine ⟨265325766458442911367431597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176883844305628607578287731 265325766458442911367431597)
  ·
    refine ⟨99497162421916091762786849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265325766458442911367431597 99497162421916091762786849)
    ·
      refine ⟨74622871816437068822090137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99497162421916091762786849 74622871816437068822090137)
      ·
        refine ⟨55967153862327801616567603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74622871816437068822090137 55967153862327801616567603)
        ·
          refine ⟨83950730793491702424851405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55967153862327801616567603 83950730793491702424851405)
          ·
            refine ⟨31481524047559388409319277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83950730793491702424851405 31481524047559388409319277)
            ·
              refine ⟨11805571517834770653494729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31481524047559388409319277 11805571517834770653494729)
              ·
                refine ⟨8854178638376077990121047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11805571517834770653494729 8854178638376077990121047)
                ·
                  refine ⟨13281267957564116985181571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854178638376077990121047 13281267957564116985181571)
                  ·
                    refine ⟨19921901936346175477772357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13281267957564116985181571 19921901936346175477772357)
                    ·
                      refine ⟨3735356613064907902082317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19921901936346175477772357 3735356613064907902082317)
                      ·
                        rfl

theorem cell23_7274581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7274581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274581 prefixEnd_7274581 := by exact prefixLift 7274581
  have htrace : WordTrace (prefixWord ++ tailWord_7274581) baseStart_7274581 baseEnd_7274581 := by
    simpa [prefixWord, tailWord_7274581, baseEnd_7274581] using wordTrace_append hprefix tailTrace_7274581
  have hstable : (prefixWord ++ tailWord_7274581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274581).length < 2 ^ (prefixWord ++ tailWord_7274581).sum := by decide
  have hdescent : baseEnd_7274581 < baseStart_7274581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274615 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 1, 2, 2]
def baseStart_7274615 : Nat := 118140960795 + 7274615 * 2 ^ 59
def prefixEnd_7274615 : Nat := 4983230072969 + 3 ^ 40 * 7274615 * 2
def baseEnd_7274615 : Nat := 3735374071407160769057161

theorem tailTrace_7274615 : CollatzResearch.WordTrace tailWord_7274615 prefixEnd_7274615 3735374071407160769057161 := by
  unfold tailWord_7274615
  simp only [CollatzResearch.WordTrace]
  refine ⟨265327006540319735174169299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176884671026879823449446199 265327006540319735174169299)
  ·
    refine ⟨397990509810479602761253949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265327006540319735174169299 397990509810479602761253949)
    ·
      refine ⟨149246441178929851035470231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397990509810479602761253949 149246441178929851035470231)
      ·
        refine ⟨223869661768394776553205347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149246441178929851035470231 223869661768394776553205347)
        ·
          refine ⟨335804492652592164829808021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223869661768394776553205347 335804492652592164829808021)
          ·
            refine ⟨15740835593090257726397251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335804492652592164829808021 15740835593090257726397251)
            ·
              refine ⟨23611253389635386589595877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15740835593090257726397251 23611253389635386589595877)
              ·
                refine ⟨4427110010556634985549227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23611253389635386589595877 4427110010556634985549227)
                ·
                  refine ⟨6640665015834952478323841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427110010556634985549227 6640665015834952478323841)
                  ·
                    refine ⟨4980498761876214358742881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6640665015834952478323841 4980498761876214358742881)
                    ·
                      refine ⟨3735374071407160769057161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980498761876214358742881 3735374071407160769057161)
                      ·
                        rfl

theorem cell23_7274615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_7274615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274615 prefixEnd_7274615 := by exact prefixLift 7274615
  have htrace : WordTrace (prefixWord ++ tailWord_7274615) baseStart_7274615 baseEnd_7274615 := by
    simpa [prefixWord, tailWord_7274615, baseEnd_7274615] using wordTrace_append hprefix tailTrace_7274615
  have hstable : (prefixWord ++ tailWord_7274615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274615).length < 2 ^ (prefixWord ++ tailWord_7274615).sum := by decide
  have hdescent : baseEnd_7274615 < baseStart_7274615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274646 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7274646 : Nat := 118140960795 + 7274646 * 2 ^ 59
def prefixEnd_7274646 : Nat := 4983230072969 + 3 ^ 40 * 7274646 * 2
def baseEnd_7274646 : Nat := 1245129996435816715923173

theorem tailTrace_7274646 : CollatzResearch.WordTrace tailWord_7274646 prefixEnd_7274646 1245129996435816715923173 := by
  unfold tailWord_7274646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583008575200464216784237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176885424802138284979031861 16583008575200464216784237)
  ·
    refine ⟨6218628215700174081294089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16583008575200464216784237 6218628215700174081294089)
    ·
      refine ⟨4663971161775130560970567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6218628215700174081294089 4663971161775130560970567)
      ·
        refine ⟨6995956742662695841455851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663971161775130560970567 6995956742662695841455851)
        ·
          refine ⟨10493935113994043762183777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6995956742662695841455851 10493935113994043762183777)
          ·
            refine ⟨7870451335495532821637833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10493935113994043762183777 7870451335495532821637833)
            ·
              refine ⟨5902838501621649616228375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7870451335495532821637833 5902838501621649616228375)
              ·
                refine ⟨8854257752432474424342563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902838501621649616228375 8854257752432474424342563)
                ·
                  refine ⟨13281386628648711636513845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854257752432474424342563 13281386628648711636513845)
                  ·
                    refine ⟨1245129996435816715923173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13281386628648711636513845 1245129996435816715923173)
                    ·
                      rfl

theorem cell23_7274646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7274646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274646 prefixEnd_7274646 := by exact prefixLift 7274646
  have htrace : WordTrace (prefixWord ++ tailWord_7274646) baseStart_7274646 baseEnd_7274646 := by
    simpa [prefixWord, tailWord_7274646, baseEnd_7274646] using wordTrace_append hprefix tailTrace_7274646
  have hstable : (prefixWord ++ tailWord_7274646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274646).length < 2 ^ (prefixWord ++ tailWord_7274646).sum := by decide
  have hdescent : baseEnd_7274646 < baseStart_7274646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274688 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2]
def baseStart_7274688 : Nat := 118140960795 + 7274688 * 2 ^ 59
def prefixEnd_7274688 : Nat := 4983230072969 + 3 ^ 40 * 7274688 * 2
def baseEnd_7274688 : Nat := 3735411555494938983444325

theorem tailTrace_7274688 : CollatzResearch.WordTrace tailWord_7274688 prefixEnd_7274688 3735411555494938983444325 := by
  unfold tailWord_7274688
  simp only [CollatzResearch.WordTrace]
  refine ⟨132664834534527634320788359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176886446046036845761051145 132664834534527634320788359)
  ·
    refine ⟨198997251801791451481182539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132664834534527634320788359 198997251801791451481182539)
    ·
      refine ⟨298495877702687177221773809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198997251801791451481182539 298495877702687177221773809)
      ·
        refine ⟨223871908277015382916330357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298495877702687177221773809 223871908277015382916330357)
        ·
          refine ⟨20987991400970192148405971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223871908277015382916330357 20987991400970192148405971)
          ·
            refine ⟨31481987101455288222608957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20987991400970192148405971 31481987101455288222608957)
            ·
              refine ⟨11805745163045733083478359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31481987101455288222608957 11805745163045733083478359)
              ·
                refine ⟨17708617744568599625217539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11805745163045733083478359 17708617744568599625217539)
                ·
                  refine ⟨26562926616852899437826309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17708617744568599625217539 26562926616852899437826309)
                  ·
                    refine ⟨4980548740659918644592433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26562926616852899437826309 4980548740659918644592433)
                    ·
                      refine ⟨3735411555494938983444325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980548740659918644592433 3735411555494938983444325)
                      ·
                        rfl

theorem cell23_7274688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_7274688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274688 prefixEnd_7274688 := by exact prefixLift 7274688
  have htrace : WordTrace (prefixWord ++ tailWord_7274688) baseStart_7274688 baseEnd_7274688 := by
    simpa [prefixWord, tailWord_7274688, baseEnd_7274688] using wordTrace_append hprefix tailTrace_7274688
  have hstable : (prefixWord ++ tailWord_7274688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274688).length < 2 ^ (prefixWord ++ tailWord_7274688).sum := by decide
  have hdescent : baseEnd_7274688 < baseStart_7274688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274731 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 5, 2]
def baseStart_7274731 : Nat := 118140960795 + 7274731 * 2 ^ 59
def prefixEnd_7274731 : Nat := 4983230072969 + 3 ^ 40 * 7274731 * 2
def baseEnd_7274731 : Nat := 3735433635163082315206627

theorem tailTrace_7274731 : CollatzResearch.WordTrace tailWord_7274731 prefixEnd_7274731 3735433635163082315206627 := by
  unfold tailWord_7274731
  simp only [CollatzResearch.WordTrace]
  refine ⟨265331237407899486985392047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176887491605266324656928031 265331237407899486985392047)
  ·
    refine ⟨397996856111849230478088071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265331237407899486985392047 397996856111849230478088071)
    ·
      refine ⟨596995284167773845717132107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397996856111849230478088071 596995284167773845717132107)
      ·
        refine ⟨895492926251660768575698161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596995284167773845717132107 895492926251660768575698161)
        ·
          refine ⟨671619694688745576431773621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895492926251660768575698161 671619694688745576431773621)
          ·
            refine ⟨62964346377069897790478777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 671619694688745576431773621 62964346377069897790478777)
            ·
              refine ⟨47223259782802423342859083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62964346377069897790478777 47223259782802423342859083)
              ·
                refine ⟨70834889674203635014288625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47223259782802423342859083 70834889674203635014288625)
                ·
                  refine ⟨53126167255652726260716469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70834889674203635014288625 53126167255652726260716469)
                  ·
                    refine ⟨4980578180217443086942169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53126167255652726260716469 4980578180217443086942169)
                    ·
                      refine ⟨3735433635163082315206627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980578180217443086942169 3735433635163082315206627)
                      ·
                        rfl

theorem cell23_7274731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5, 2].length) (baseStart_7274731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274731 prefixEnd_7274731 := by exact prefixLift 7274731
  have htrace : WordTrace (prefixWord ++ tailWord_7274731) baseStart_7274731 baseEnd_7274731 := by
    simpa [prefixWord, tailWord_7274731, baseEnd_7274731] using wordTrace_append hprefix tailTrace_7274731
  have hstable : (prefixWord ++ tailWord_7274731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274731).length < 2 ^ (prefixWord ++ tailWord_7274731).sum := by decide
  have hdescent : baseEnd_7274731 < baseStart_7274731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274744 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_7274744 : Nat := 118140960795 + 7274744 * 2 ^ 59
def prefixEnd_7274744 : Nat := 4983230072969 + 3 ^ 40 * 7274744 * 2
def baseEnd_7274744 : Nat := 3735440310411590764344067

theorem tailTrace_7274744 : CollatzResearch.WordTrace tailWord_7274744 prefixEnd_7274744 3735440310411590764344067 := by
  unfold tailWord_7274744
  simp only [CollatzResearch.WordTrace]
  refine ⟨132665855778426195102807643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176887807704568260137076857 132665855778426195102807643)
  ·
    refine ⟨198998783667639292654211465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132665855778426195102807643 198998783667639292654211465)
    ·
      refine ⟨149249087750729469490658599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198998783667639292654211465 149249087750729469490658599)
      ·
        refine ⟨223873631626094204235987899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149249087750729469490658599 223873631626094204235987899)
        ·
          refine ⟨335810447439141306353981849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223873631626094204235987899 335810447439141306353981849)
          ·
            refine ⟨251857835579355979765486387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335810447439141306353981849 251857835579355979765486387)
            ·
              refine ⟨377786753369033969648229581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251857835579355979765486387 377786753369033969648229581)
              ·
                refine ⟨141670032513387738618086093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377786753369033969648229581 141670032513387738618086093)
                ·
                  refine ⟨53126262192520401981782285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141670032513387738618086093 53126262192520401981782285)
                  ·
                    refine ⟨19922348322195150743168357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53126262192520401981782285 19922348322195150743168357)
                    ·
                      refine ⟨3735440310411590764344067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19922348322195150743168357 3735440310411590764344067)
                      ·
                        rfl

theorem cell23_7274744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_7274744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274744 prefixEnd_7274744 := by exact prefixLift 7274744
  have htrace : WordTrace (prefixWord ++ tailWord_7274744) baseStart_7274744 baseEnd_7274744 := by
    simpa [prefixWord, tailWord_7274744, baseEnd_7274744] using wordTrace_append hprefix tailTrace_7274744
  have hstable : (prefixWord ++ tailWord_7274744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274744).length < 2 ^ (prefixWord ++ tailWord_7274744).sum := by decide
  have hdescent : baseEnd_7274744 < baseStart_7274744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274761 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_7274761 : Nat := 118140960795 + 7274761 * 2 ^ 59
def prefixEnd_7274761 : Nat := 4983230072969 + 3 ^ 40 * 7274761 * 2
def baseEnd_7274761 : Nat := 3735449039582717197831489

theorem tailTrace_7274761 : CollatzResearch.WordTrace tailWord_7274761 prefixEnd_7274761 3735449039582717197831489 := by
  unfold tailWord_7274761
  simp only [CollatzResearch.WordTrace]
  refine ⟨265332331597790802108984137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176888221065193868072656091 265332331597790802108984137)
  ·
    refine ⟨198999248698343101581738103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265332331597790802108984137 198999248698343101581738103)
    ·
      refine ⟨298498873047514652372607155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198999248698343101581738103 298498873047514652372607155)
      ·
        refine ⟨447748309571271978558910733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298498873047514652372607155 447748309571271978558910733)
        ·
          refine ⟨167905616089226991959591525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447748309571271978558910733 167905616089226991959591525)
          ·
            refine ⟨31482303016730060992423411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167905616089226991959591525 31482303016730060992423411)
            ·
              refine ⟨47223454525095091488635117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31482303016730060992423411 47223454525095091488635117)
              ·
                refine ⟨17708795446910659308238169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47223454525095091488635117 17708795446910659308238169)
                ·
                  refine ⟨13281596585182994481178627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17708795446910659308238169 13281596585182994481178627)
                  ·
                    refine ⟨19922394877774491721767941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13281596585182994481178627 19922394877774491721767941)
                    ·
                      refine ⟨3735449039582717197831489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19922394877774491721767941 3735449039582717197831489)
                      ·
                        rfl

theorem cell23_7274761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_7274761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274761 prefixEnd_7274761 := by exact prefixLift 7274761
  have htrace : WordTrace (prefixWord ++ tailWord_7274761) baseStart_7274761 baseEnd_7274761 := by
    simpa [prefixWord, tailWord_7274761, baseEnd_7274761] using wordTrace_append hprefix tailTrace_7274761
  have hstable : (prefixWord ++ tailWord_7274761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274761).length < 2 ^ (prefixWord ++ tailWord_7274761).sum := by decide
  have hdescent : baseEnd_7274761 < baseStart_7274761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274828 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7274828 : Nat := 118140960795 + 7274828 * 2 ^ 59
def prefixEnd_7274828 : Nat := 4983230072969 + 3 ^ 40 * 7274828 * 2
def baseEnd_7274828 : Nat := 3735483442786568435693681

theorem tailTrace_7274828 : CollatzResearch.WordTrace tailWord_7274828 prefixEnd_7274828 3735483442786568435693681 := by
  unfold tailWord_7274828
  simp only [CollatzResearch.WordTrace]
  refine ⟨132667387644274036275836569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176889850192365381701115425 132667387644274036275836569)
  ·
    refine ⟨99500540733205527206877427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132667387644274036275836569 99500540733205527206877427)
    ·
      refine ⟨149250811099808290810316141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99500540733205527206877427 149250811099808290810316141)
      ·
        refine ⟨55969054162428109053868553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149250811099808290810316141 55969054162428109053868553)
        ·
          refine ⟨41976790621821081790401415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55969054162428109053868553 41976790621821081790401415)
          ·
            refine ⟨62965185932731622685602123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41976790621821081790401415 62965185932731622685602123)
            ·
              refine ⟨94447778899097434028403185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62965185932731622685602123 94447778899097434028403185)
              ·
                refine ⟨70835834174323075521302389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94447778899097434028403185 70835834174323075521302389)
                ·
                  refine ⟨6640859453842788330122099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70835834174323075521302389 6640859453842788330122099)
                  ·
                    refine ⟨9961289180764182495183149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6640859453842788330122099 9961289180764182495183149)
                    ·
                      refine ⟨3735483442786568435693681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9961289180764182495183149 3735483442786568435693681)
                      ·
                        rfl

theorem cell23_7274828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7274828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274828 prefixEnd_7274828 := by exact prefixLift 7274828
  have htrace : WordTrace (prefixWord ++ tailWord_7274828) baseStart_7274828 baseEnd_7274828 := by
    simpa [prefixWord, tailWord_7274828, baseEnd_7274828] using wordTrace_append hprefix tailTrace_7274828
  have hstable : (prefixWord ++ tailWord_7274828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274828).length < 2 ^ (prefixWord ++ tailWord_7274828).sum := by decide
  have hdescent : baseEnd_7274828 < baseStart_7274828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274888 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_7274888 : Nat := 118140960795 + 7274888 * 2 ^ 59
def prefixEnd_7274888 : Nat := 4983230072969 + 3 ^ 40 * 7274888 * 2
def baseEnd_7274888 : Nat := 3735514251625838200943405

theorem tailTrace_7274888 : CollatzResearch.WordTrace tailWord_7274888 prefixEnd_7274888 3735514251625838200943405 := by
  unfold tailWord_7274888
  simp only [CollatzResearch.WordTrace]
  refine ⟨132668481834165351399428659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176891309112220468532571545 132668481834165351399428659)
  ·
    refine ⟨199002722751248027099142989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132668481834165351399428659 199002722751248027099142989)
    ·
      refine ⟨74626021031718010162178621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199002722751248027099142989 74626021031718010162178621)
      ·
        refine ⟨27984757886894253810816983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74626021031718010162178621 27984757886894253810816983)
        ·
          refine ⟨41977136830341380716225475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27984757886894253810816983 41977136830341380716225475)
          ·
            refine ⟨62965705245512071074338213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41977136830341380716225475 62965705245512071074338213)
            ·
              refine ⟨11806069733533513326438415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62965705245512071074338213 11806069733533513326438415)
              ·
                refine ⟨17709104600300269989657623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806069733533513326438415 17709104600300269989657623)
                ·
                  refine ⟨26563656900450404984486435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17709104600300269989657623 26563656900450404984486435)
                  ·
                    refine ⟨39845485350675607476729653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26563656900450404984486435 39845485350675607476729653)
                    ·
                      refine ⟨3735514251625838200943405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39845485350675607476729653 3735514251625838200943405)
                      ·
                        rfl

theorem cell23_7274888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_7274888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274888 prefixEnd_7274888 := by exact prefixLift 7274888
  have htrace : WordTrace (prefixWord ++ tailWord_7274888) baseStart_7274888 baseEnd_7274888 := by
    simpa [prefixWord, tailWord_7274888, baseEnd_7274888] using wordTrace_append hprefix tailTrace_7274888
  have hstable : (prefixWord ++ tailWord_7274888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274888).length < 2 ^ (prefixWord ++ tailWord_7274888).sum := by decide
  have hdescent : baseEnd_7274888 < baseStart_7274888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274891 : List Nat := [1, 1, 1, 1, 4, 6, 9]
def baseStart_7274891 : Nat := 118140960795 + 7274891 * 2 ^ 59
def prefixEnd_7274891 : Nat := 4983230072969 + 3 ^ 40 * 7274891 * 2
def baseEnd_7274891 : Nat := 46117478914417304805011

theorem tailTrace_7274891 : CollatzResearch.WordTrace tailWord_7274891 prefixEnd_7274891 46117478914417304805011 := by
  unfold tailWord_7274891
  simp only [CollatzResearch.WordTrace]
  refine ⟨265337073087319834311216527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176891382058213222874144351 265337073087319834311216527)
  ·
    refine ⟨398005609630979751466824791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265337073087319834311216527 398005609630979751466824791)
    ·
      refine ⟨597008414446469627200237187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398005609630979751466824791 597008414446469627200237187)
      ·
        refine ⟨895512621669704440800355781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597008414446469627200237187 895512621669704440800355781)
        ·
          refine ⟨167908616563069582650066709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 895512621669704440800355781 167908616563069582650066709)
          ·
            refine ⟨7870716401393886686721877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167908616563069582650066709 7870716401393886686721877)
            ·
              refine ⟨46117478914417304805011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7870716401393886686721877 46117478914417304805011)
              ·
                rfl

theorem cell23_7274891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 9].length) (baseStart_7274891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274891 prefixEnd_7274891 := by exact prefixLift 7274891
  have htrace : WordTrace (prefixWord ++ tailWord_7274891) baseStart_7274891 baseEnd_7274891 := by
    simpa [prefixWord, tailWord_7274891, baseEnd_7274891] using wordTrace_append hprefix tailTrace_7274891
  have hstable : (prefixWord ++ tailWord_7274891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274891).length < 2 ^ (prefixWord ++ tailWord_7274891).sum := by decide
  have hdescent : baseEnd_7274891 < baseStart_7274891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274911 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7274911 : Nat := 118140960795 + 7274911 * 2 ^ 59
def prefixEnd_7274911 : Nat := 4983230072969 + 3 ^ 40 * 7274911 * 2
def baseEnd_7274911 : Nat := 3735526061680891610955799

theorem tailTrace_7274911 : CollatzResearch.WordTrace tailWord_7274911 prefixEnd_7274911 3735526061680891610955799 := by
  unfold tailWord_7274911
  simp only [CollatzResearch.WordTrace]
  refine ⟨265337802547247377726944587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176891868364831585151296391 265337802547247377726944587)
  ·
    refine ⟨398006703820871066590416881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265337802547247377726944587 398006703820871066590416881)
    ·
      refine ⟨298505027865653299942812661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398006703820871066590416881 298505027865653299942812661)
      ·
        refine ⟨27984846362404996869638687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298505027865653299942812661 27984846362404996869638687)
        ·
          refine ⟨41977269543607495304458031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27984846362404996869638687 41977269543607495304458031)
          ·
            refine ⟨62965904315411242956687047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41977269543607495304458031 62965904315411242956687047)
            ·
              refine ⟨94448856473116864435030571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62965904315411242956687047 94448856473116864435030571)
              ·
                refine ⟨141673284709675296652545857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94448856473116864435030571 141673284709675296652545857)
                ·
                  refine ⟨106254963532256472489409393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141673284709675296652545857 106254963532256472489409393)
                  ·
                    refine ⟨79691222649192354367057045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106254963532256472489409393 79691222649192354367057045)
                    ·
                      refine ⟨3735526061680891610955799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79691222649192354367057045 3735526061680891610955799)
                      ·
                        rfl

theorem cell23_7274911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7274911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274911 prefixEnd_7274911 := by exact prefixLift 7274911
  have htrace : WordTrace (prefixWord ++ tailWord_7274911) baseStart_7274911 baseEnd_7274911 := by
    simpa [prefixWord, tailWord_7274911, baseEnd_7274911] using wordTrace_append hprefix tailTrace_7274911
  have hstable : (prefixWord ++ tailWord_7274911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274911).length < 2 ^ (prefixWord ++ tailWord_7274911).sum := by decide
  have hdescent : baseEnd_7274911 < baseStart_7274911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274912 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 2, 4]
def baseStart_7274912 : Nat := 118140960795 + 7274912 * 2 ^ 59
def prefixEnd_7274912 : Nat := 4983230072969 + 3 ^ 40 * 7274912 * 2
def baseEnd_7274912 : Nat := 1245175525053848702347765

theorem tailTrace_7274912 : CollatzResearch.WordTrace tailWord_7274912 prefixEnd_7274912 1245175525053848702347765 := by
  unfold tailWord_7274912
  simp only [CollatzResearch.WordTrace]
  refine ⟨132668919510121877448865495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176891892680162503265153993 132668919510121877448865495)
  ·
    refine ⟨199003379265182816173298243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132668919510121877448865495 199003379265182816173298243)
    ·
      refine ⟨298505068897774224259947365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199003379265182816173298243 298505068897774224259947365)
      ·
        refine ⟨55969700418332667048740131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298505068897774224259947365 55969700418332667048740131)
        ·
          refine ⟨83954550627499000573110197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55969700418332667048740131 83954550627499000573110197)
          ·
            refine ⟨7870739121328031303729081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83954550627499000573110197 7870739121328031303729081)
            ·
              refine ⟨5903054340996023477796811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7870739121328031303729081 5903054340996023477796811)
              ·
                refine ⟨8854581511494035216695217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903054340996023477796811 8854581511494035216695217)
                ·
                  refine ⟨6640936133620526412521413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8854581511494035216695217 6640936133620526412521413)
                  ·
                    refine ⟨1245175525053848702347765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6640936133620526412521413 1245175525053848702347765)
                    ·
                      rfl

theorem cell23_7274912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_7274912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274912 prefixEnd_7274912 := by exact prefixLift 7274912
  have htrace : WordTrace (prefixWord ++ tailWord_7274912) baseStart_7274912 baseEnd_7274912 := by
    simpa [prefixWord, tailWord_7274912, baseEnd_7274912] using wordTrace_append hprefix tailTrace_7274912
  have hstable : (prefixWord ++ tailWord_7274912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274912).length < 2 ^ (prefixWord ++ tailWord_7274912).sum := by decide
  have hdescent : baseEnd_7274912 < baseStart_7274912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274952 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_7274952 : Nat := 118140960795 + 7274952 * 2 ^ 59
def prefixEnd_7274952 : Nat := 4983230072969 + 3 ^ 40 * 7274952 * 2
def baseEnd_7274952 : Nat := 3735547114387725950543111

theorem tailTrace_7274952 : CollatzResearch.WordTrace tailWord_7274952 prefixEnd_7274952 3735547114387725950543111 := by
  unfold tailWord_7274952
  simp only [CollatzResearch.WordTrace]
  refine ⟨132669648970049420864593555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176892865293399227819458073 132669648970049420864593555)
  ·
    refine ⟨199004473455074131296890333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132669648970049420864593555 199004473455074131296890333)
    ·
      refine ⟨74626677545652799236333875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199004473455074131296890333 74626677545652799236333875)
      ·
        refine ⟨111940016318479198854500813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74626677545652799236333875 111940016318479198854500813)
        ·
          refine ⟨41977506119429699570437805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111940016318479198854500813 41977506119429699570437805)
          ·
            refine ⟨15741564794786137338914177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41977506119429699570437805 15741564794786137338914177)
            ·
              refine ⟨11806173596089603004185633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15741564794786137338914177 11806173596089603004185633)
              ·
                refine ⟨8854630197067202253139225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11806173596089603004185633 8854630197067202253139225)
                ·
                  refine ⟨6640972647800401689854419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8854630197067202253139225 6640972647800401689854419)
                  ·
                    refine ⟨9961458971700602534781629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6640972647800401689854419 9961458971700602534781629)
                    ·
                      refine ⟨3735547114387725950543111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9961458971700602534781629 3735547114387725950543111)
                      ·
                        rfl

theorem cell23_7274952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_7274952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274952 prefixEnd_7274952 := by exact prefixLift 7274952
  have htrace : WordTrace (prefixWord ++ tailWord_7274952) baseStart_7274952 baseEnd_7274952 := by
    simpa [prefixWord, tailWord_7274952, baseEnd_7274952] using wordTrace_append hprefix tailTrace_7274952
  have hstable : (prefixWord ++ tailWord_7274952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274952).length < 2 ^ (prefixWord ++ tailWord_7274952).sum := by decide
  have hdescent : baseEnd_7274952 < baseStart_7274952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274961 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_7274961 : Nat := 118140960795 + 7274961 * 2 ^ 59
def prefixEnd_7274961 : Nat := 4983230072969 + 3 ^ 40 * 7274961 * 2
def baseEnd_7274961 : Nat := 3735551735713616415330569

theorem tailTrace_7274961 : CollatzResearch.WordTrace tailWord_7274961 prefixEnd_7274961 3735551735713616415330569 := by
  unfold tailWord_7274961
  simp only [CollatzResearch.WordTrace]
  refine ⟨265339626197066236266264737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176893084131377490844176491 265339626197066236266264737)
  ·
    refine ⟨199004719647799677199698553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265339626197066236266264737 199004719647799677199698553)
    ·
      refine ⟨149253539735849757899773915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199004719647799677199698553 149253539735849757899773915)
      ·
        refine ⟨223880309603774636849660873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149253539735849757899773915 223880309603774636849660873)
        ·
          refine ⟨167910232202830977637245655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223880309603774636849660873 167910232202830977637245655)
          ·
            refine ⟨251865348304246466455868483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167910232202830977637245655 251865348304246466455868483)
            ·
              refine ⟨377798022456369699683802725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251865348304246466455868483 377798022456369699683802725)
              ·
                refine ⟨70837129210569318690713011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377798022456369699683802725 70837129210569318690713011)
                ·
                  refine ⟨106255693815853978036069517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70837129210569318690713011 106255693815853978036069517)
                  ·
                    refine ⟨39845885180945241763526069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106255693815853978036069517 39845885180945241763526069)
                    ·
                      refine ⟨3735551735713616415330569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39845885180945241763526069 3735551735713616415330569)
                      ·
                        rfl

theorem cell23_7274961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_7274961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274961 prefixEnd_7274961 := by exact prefixLift 7274961
  have htrace : WordTrace (prefixWord ++ tailWord_7274961) baseStart_7274961 baseEnd_7274961 := by
    simpa [prefixWord, tailWord_7274961, baseEnd_7274961] using wordTrace_append hprefix tailTrace_7274961
  have hstable : (prefixWord ++ tailWord_7274961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274961).length < 2 ^ (prefixWord ++ tailWord_7274961).sum := by decide
  have hdescent : baseEnd_7274961 < baseStart_7274961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274975 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 1, 4, 2]
def baseStart_7274975 : Nat := 118140960795 + 7274975 * 2 ^ 59
def prefixEnd_7274975 : Nat := 4983230072969 + 3 ^ 40 * 7274975 * 2
def baseEnd_7274975 : Nat := 3735558924442779360555505

theorem tailTrace_7274975 : CollatzResearch.WordTrace tailWord_7274975 prefixEnd_7274975 3735558924442779360555505 := by
  unfold tailWord_7274975
  simp only [CollatzResearch.WordTrace]
  refine ⟨265340136819015516657274379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176893424546010344438182919 265340136819015516657274379)
  ·
    refine ⟨398010205228523274985911569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265340136819015516657274379 398010205228523274985911569)
    ·
      refine ⟨298507653921392456239433677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398010205228523274985911569 298507653921392456239433677)
      ·
        refine ⟨111940370220522171089787629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298507653921392456239433677 111940370220522171089787629)
        ·
          refine ⟨41977638832695814158670361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111940370220522171089787629 41977638832695814158670361)
          ·
            refine ⟨31483229124521860619002771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41977638832695814158670361 31483229124521860619002771)
            ·
              refine ⟨47224843686782790928504157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31483229124521860619002771 47224843686782790928504157)
              ·
                refine ⟨17709316382543546598189059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47224843686782790928504157 17709316382543546598189059)
                ·
                  refine ⟨26563974573815319897283589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17709316382543546598189059 26563974573815319897283589)
                  ·
                    refine ⟨4980745232590372480740673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26563974573815319897283589 4980745232590372480740673)
                    ·
                      refine ⟨3735558924442779360555505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980745232590372480740673 3735558924442779360555505)
                      ·
                        rfl

theorem cell23_7274975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_7274975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274975 prefixEnd_7274975 := by exact prefixLift 7274975
  have htrace : WordTrace (prefixWord ++ tailWord_7274975) baseStart_7274975 baseEnd_7274975 := by
    simpa [prefixWord, tailWord_7274975, baseEnd_7274975] using wordTrace_append hprefix tailTrace_7274975
  have hstable : (prefixWord ++ tailWord_7274975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274975).length < 2 ^ (prefixWord ++ tailWord_7274975).sum := by decide
  have hdescent : baseEnd_7274975 < baseStart_7274975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274991 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_7274991 : Nat := 118140960795 + 7274991 * 2 ^ 59
def prefixEnd_7274991 : Nat := 4983230072969 + 3 ^ 40 * 7274991 * 2
def baseEnd_7274991 : Nat := 3735567140133251297955431

theorem tailTrace_7274991 : CollatzResearch.WordTrace tailWord_7274991 prefixEnd_7274991 3735567140133251297955431 := by
  unfold tailWord_7274991
  simp only [CollatzResearch.WordTrace]
  refine ⟨265340720386957551389856827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176893813591305034259904551 265340720386957551389856827)
  ·
    refine ⟨398011080580436327084785241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265340720386957551389856827 398011080580436327084785241)
    ·
      refine ⟨298508310435327245313588931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398011080580436327084785241 298508310435327245313588931)
      ·
        refine ⟨447762465652990867970383397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298508310435327245313588931 447762465652990867970383397)
        ·
          refine ⟨83955462309935787744446887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 447762465652990867970383397 83955462309935787744446887)
          ·
            refine ⟨125933193464903681616670331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83955462309935787744446887 125933193464903681616670331)
            ·
              refine ⟨188899790197355522425005497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125933193464903681616670331 188899790197355522425005497)
              ·
                refine ⟨141674842648016641818754123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188899790197355522425005497 141674842648016641818754123)
                ·
                  refine ⟨212512263972024962728131185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141674842648016641818754123 212512263972024962728131185)
                  ·
                    refine ⟨159384197979018722046098389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212512263972024962728131185 159384197979018722046098389)
                    ·
                      refine ⟨3735567140133251297955431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159384197979018722046098389 3735567140133251297955431)
                      ·
                        rfl

theorem cell23_7274991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_7274991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274991 prefixEnd_7274991 := by exact prefixLift 7274991
  have htrace : WordTrace (prefixWord ++ tailWord_7274991) baseStart_7274991 baseEnd_7274991 := by
    simpa [prefixWord, tailWord_7274991, baseEnd_7274991] using wordTrace_append hprefix tailTrace_7274991
  have hstable : (prefixWord ++ tailWord_7274991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274991).length < 2 ^ (prefixWord ++ tailWord_7274991).sum := by decide
  have hdescent : baseEnd_7274991 < baseStart_7274991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7274998 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_7274998 : Nat := 118140960795 + 7274998 * 2 ^ 59
def prefixEnd_7274998 : Nat := 4983230072969 + 3 ^ 40 * 7274998 * 2
def baseEnd_7274998 : Nat := 415063414944203641174211

theorem tailTrace_7274998 : CollatzResearch.WordTrace tailWord_7274998 prefixEnd_7274998 415063414944203641174211 := by
  unfold tailWord_7274998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583810981120761974085103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176893983798621461056907765 16583810981120761974085103)
  ·
    refine ⟨24875716471681142961127655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16583810981120761974085103 24875716471681142961127655)
    ·
      refine ⟨37313574707521714441691483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24875716471681142961127655 37313574707521714441691483)
      ·
        refine ⟨55970362061282571662537225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37313574707521714441691483 55970362061282571662537225)
        ·
          refine ⟨41977771545961928746902919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55970362061282571662537225 41977771545961928746902919)
          ·
            refine ⟨62966657318942893120354379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41977771545961928746902919 62966657318942893120354379)
            ·
              refine ⟨94449985978414339680531569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62966657318942893120354379 94449985978414339680531569)
              ·
                refine ⟨70837489483810754760398677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94449985978414339680531569 70837489483810754760398677)
                ·
                  refine ⟨415063414944203641174211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70837489483810754760398677 415063414944203641174211)
                  ·
                    rfl

theorem cell23_7274998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_7274998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7274998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7274998 prefixEnd_7274998 := by exact prefixLift 7274998
  have htrace : WordTrace (prefixWord ++ tailWord_7274998) baseStart_7274998 baseEnd_7274998 := by
    simpa [prefixWord, tailWord_7274998, baseEnd_7274998] using wordTrace_append hprefix tailTrace_7274998
  have hstable : (prefixWord ++ tailWord_7274998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7274998).length < 2 ^ (prefixWord ++ tailWord_7274998).sum := by decide
  have hdescent : baseEnd_7274998 < baseStart_7274998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7274998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275009 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_7275009 : Nat := 118140960795 + 7275009 * 2 ^ 59
def prefixEnd_7275009 : Nat := 4983230072969 + 3 ^ 40 * 7275009 * 2
def baseEnd_7275009 : Nat := 3735576382785032227530349

theorem tailTrace_7275009 : CollatzResearch.WordTrace tailWord_7275009 prefixEnd_7275009 3735576382785032227530349 := by
  unfold tailWord_7275009
  simp only [CollatzResearch.WordTrace]
  refine ⟨265341376900892340464012081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176894251267261560309341387 265341376900892340464012081)
  ·
    refine ⟨199006032675669255348009061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265341376900892340464012081 199006032675669255348009061)
    ·
      refine ⟨37313631126687985377751699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199006032675669255348009061 37313631126687985377751699)
      ·
        refine ⟨55970446690031978066627549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37313631126687985377751699 55970446690031978066627549)
        ·
          refine ⟨20988917508761991774985331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55970446690031978066627549 20988917508761991774985331)
          ·
            refine ⟨31483376263142987662477997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20988917508761991774985331 31483376263142987662477997)
            ·
              refine ⟨11806266098678620373429249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31483376263142987662477997 11806266098678620373429249)
              ·
                refine ⟨8854699574008965280071937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11806266098678620373429249 8854699574008965280071937)
                ·
                  refine ⟨6641024680506723960053953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8854699574008965280071937 6641024680506723960053953)
                  ·
                    refine ⟨4980768510380042970040465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641024680506723960053953 4980768510380042970040465)
                    ·
                      refine ⟨3735576382785032227530349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980768510380042970040465 3735576382785032227530349)
                      ·
                        rfl

theorem cell23_7275009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_7275009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275009 prefixEnd_7275009 := by exact prefixLift 7275009
  have htrace : WordTrace (prefixWord ++ tailWord_7275009) baseStart_7275009 baseEnd_7275009 := by
    simpa [prefixWord, tailWord_7275009, baseEnd_7275009] using wordTrace_append hprefix tailTrace_7275009
  have hstable : (prefixWord ++ tailWord_7275009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275009).length < 2 ^ (prefixWord ++ tailWord_7275009).sum := by decide
  have hdescent : baseEnd_7275009 < baseStart_7275009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275015 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 7]
def baseStart_7275015 : Nat := 118140960795 + 7275015 * 2 ^ 59
def prefixEnd_7275015 : Nat := 4983230072969 + 3 ^ 40 * 7275015 * 2
def baseEnd_7275015 : Nat := 415064384852106578228369

theorem tailTrace_7275015 : CollatzResearch.WordTrace tailWord_7275015 prefixEnd_7275015 415064384852106578228369 := by
  unfold tailWord_7275015
  simp only [CollatzResearch.WordTrace]
  refine ⟨265341595738870603488730499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176894397159247068992486999 265341595738870603488730499)
  ·
    refine ⟨398012393608305905233095749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265341595738870603488730499 398012393608305905233095749)
    ·
      refine ⟨74627323801557357231205453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398012393608305905233095749 74627323801557357231205453)
      ·
        refine ⟨27985246425584008961702045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74627323801557357231205453 27985246425584008961702045)
        ·
          refine ⟨10494467409594003360638267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27985246425584008961702045 10494467409594003360638267)
          ·
            refine ⟨15741701114391005040957401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494467409594003360638267 15741701114391005040957401)
            ·
              refine ⟨11806275835793253780718051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15741701114391005040957401 11806275835793253780718051)
              ·
                refine ⟨17709413753689880671077077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806275835793253780718051 17709413753689880671077077)
                ·
                  refine ⟨415064384852106578228369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17709413753689880671077077 415064384852106578228369)
                  ·
                    rfl

theorem cell23_7275015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 7].length) (baseStart_7275015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275015 prefixEnd_7275015 := by exact prefixLift 7275015
  have htrace : WordTrace (prefixWord ++ tailWord_7275015) baseStart_7275015 baseEnd_7275015 := by
    simpa [prefixWord, tailWord_7275015, baseEnd_7275015] using wordTrace_append hprefix tailTrace_7275015
  have hstable : (prefixWord ++ tailWord_7275015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275015).length < 2 ^ (prefixWord ++ tailWord_7275015).sum := by decide
  have hdescent : baseEnd_7275015 < baseStart_7275015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275062 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7275062 : Nat := 118140960795 + 7275062 * 2 ^ 59
def prefixEnd_7275062 : Nat := 4983230072969 + 3 ^ 40 * 7275062 * 2
def baseEnd_7275062 : Nat := 1245201199086573506722535

theorem tailTrace_7275062 : CollatzResearch.WordTrace tailWord_7275062 prefixEnd_7275062 1245201199086573506722535 := by
  unfold tailWord_7275062
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583956873106270657230715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176895539979800220343794293 16583956873106270657230715)
  ·
    refine ⟨24875935309659405985846073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16583956873106270657230715 24875935309659405985846073)
    ·
      refine ⟨18656951482244554489384555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24875935309659405985846073 18656951482244554489384555)
      ·
        refine ⟨27985427223366831734076833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18656951482244554489384555 27985427223366831734076833)
        ·
          refine ⟨20989070417525123800557625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27985427223366831734076833 20989070417525123800557625)
          ·
            refine ⟨15741802813143842850418219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20989070417525123800557625 15741802813143842850418219)
            ·
              refine ⟨23612704219715764275627329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15741802813143842850418219 23612704219715764275627329)
              ·
                refine ⟨17709528164786823206720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23612704219715764275627329 17709528164786823206720497)
                ·
                  refine ⟨13282146123590117405040373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17709528164786823206720497 13282146123590117405040373)
                  ·
                    refine ⟨1245201199086573506722535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13282146123590117405040373 1245201199086573506722535)
                    ·
                      rfl

theorem cell23_7275062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7275062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275062 prefixEnd_7275062 := by exact prefixLift 7275062
  have htrace : WordTrace (prefixWord ++ tailWord_7275062) baseStart_7275062 baseEnd_7275062 := by
    simpa [prefixWord, tailWord_7275062, baseEnd_7275062] using wordTrace_append hprefix tailTrace_7275062
  have hstable : (prefixWord ++ tailWord_7275062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275062).length < 2 ^ (prefixWord ++ tailWord_7275062).sum := by decide
  have hdescent : baseEnd_7275062 < baseStart_7275062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275065 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7275065 : Nat := 118140960795 + 7275065 * 2 ^ 59
def prefixEnd_7275065 : Nat := 4983230072969 + 3 ^ 40 * 7275065 * 2
def baseEnd_7275065 : Nat := 3735605137701684008430091

theorem tailTrace_7275065 : CollatzResearch.WordTrace tailWord_7275065 prefixEnd_7275065 3735605137701684008430091 := by
  unfold tailWord_7275065
  simp only [CollatzResearch.WordTrace]
  refine ⟨265343419388689462028050649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176895612925792974685367099 265343419388689462028050649)
  ·
    refine ⟨199007564541517096521037987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265343419388689462028050649 199007564541517096521037987)
    ·
      refine ⟨298511346812275644781556981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199007564541517096521037987 298511346812275644781556981)
      ·
        refine ⟨27985438763650841698270967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298511346812275644781556981 27985438763650841698270967)
        ·
          refine ⟨41978158145476262547406451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27985438763650841698270967 41978158145476262547406451)
          ·
            refine ⟨62967237218214393821109677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41978158145476262547406451 62967237218214393821109677)
            ·
              refine ⟨23612713956830397682916129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62967237218214393821109677 23612713956830397682916129)
              ·
                refine ⟨17709535467622798262187097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23612713956830397682916129 17709535467622798262187097)
                ·
                  refine ⟨13282151600717098696640323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17709535467622798262187097 13282151600717098696640323)
                  ·
                    refine ⟨19923227401075648044960485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13282151600717098696640323 19923227401075648044960485)
                    ·
                      refine ⟨3735605137701684008430091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19923227401075648044960485 3735605137701684008430091)
                      ·
                        rfl

theorem cell23_7275065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7275065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275065 prefixEnd_7275065 := by exact prefixLift 7275065
  have htrace : WordTrace (prefixWord ++ tailWord_7275065) baseStart_7275065 baseEnd_7275065 := by
    simpa [prefixWord, tailWord_7275065, baseEnd_7275065] using wordTrace_append hprefix tailTrace_7275065
  have hstable : (prefixWord ++ tailWord_7275065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275065).length < 2 ^ (prefixWord ++ tailWord_7275065).sum := by decide
  have hdescent : baseEnd_7275065 < baseStart_7275065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275115 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 3]
def baseStart_7275115 : Nat := 118140960795 + 7275115 * 2 ^ 59
def prefixEnd_7275115 : Nat := 4983230072969 + 3 ^ 40 * 7275115 * 2
def baseEnd_7275115 : Nat := 3735630811734408812804861

theorem tailTrace_7275115 : CollatzResearch.WordTrace tailWord_7275115 prefixEnd_7275115 3735630811734408812804861 := by
  unfold tailWord_7275115
  simp only [CollatzResearch.WordTrace]
  refine ⟨265345243038508320567370799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176896828692338880378247199 265345243038508320567370799)
  ·
    refine ⟨398017864557762480851056199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265345243038508320567370799 398017864557762480851056199)
    ·
      refine ⟨597026796836643721276584299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398017864557762480851056199 597026796836643721276584299)
      ·
        refine ⟨895540195254965581914876449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597026796836643721276584299 895540195254965581914876449)
        ·
          refine ⟨671655146441224186436157337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895540195254965581914876449 671655146441224186436157337)
          ·
            refine ⟨503741359830918139827118003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671655146441224186436157337 503741359830918139827118003)
            ·
              refine ⟨755612039746377209740677005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503741359830918139827118003 755612039746377209740677005)
              ·
                refine ⟨283354514904891453652753877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755612039746377209740677005 283354514904891453652753877)
                ·
                  refine ⟨6641121443083393444986419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 283354514904891453652753877 6641121443083393444986419)
                  ·
                    refine ⟨9961682164625090167479629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6641121443083393444986419 9961682164625090167479629)
                    ·
                      refine ⟨3735630811734408812804861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9961682164625090167479629 3735630811734408812804861)
                      ·
                        rfl

theorem cell23_7275115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 1, 3].length) (baseStart_7275115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275115 prefixEnd_7275115 := by exact prefixLift 7275115
  have htrace : WordTrace (prefixWord ++ tailWord_7275115) baseStart_7275115 baseEnd_7275115 := by
    simpa [prefixWord, tailWord_7275115, baseEnd_7275115] using wordTrace_append hprefix tailTrace_7275115
  have hstable : (prefixWord ++ tailWord_7275115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275115).length < 2 ^ (prefixWord ++ tailWord_7275115).sum := by decide
  have hdescent : baseEnd_7275115 < baseStart_7275115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275122 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_7275122 : Nat := 118140960795 + 7275122 * 2 ^ 59
def prefixEnd_7275122 : Nat := 4983230072969 + 3 ^ 40 * 7275122 * 2
def baseEnd_7275122 : Nat := 415070489566554476157481

theorem tailTrace_7275122 : CollatzResearch.WordTrace tailWord_7275122 prefixEnd_7275122 415070489566554476157481 := by
  unfold tailWord_7275122
  simp only [CollatzResearch.WordTrace]
  refine ⟨66336374587370740190718905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176896998899655307175250413 66336374587370740190718905)
  ·
    refine ⟨49752280940528055143039179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66336374587370740190718905 49752280940528055143039179)
    ·
      refine ⟨74628421410792082714558769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49752280940528055143039179 74628421410792082714558769)
      ·
        refine ⟨55971316058094062035919077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74628421410792082714558769 55971316058094062035919077)
        ·
          refine ⟨10494621760892636631734827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55971316058094062035919077 10494621760892636631734827)
          ·
            refine ⟨15741932641338954947602241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494621760892636631734827 15741932641338954947602241)
            ·
              refine ⟨11806449481004216210701681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15741932641338954947602241 11806449481004216210701681)
              ·
                refine ⟨8854837110753162158026261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11806449481004216210701681 8854837110753162158026261)
                ·
                  refine ⟨415070489566554476157481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8854837110753162158026261 415070489566554476157481)
                  ·
                    rfl

theorem cell23_7275122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_7275122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275122 prefixEnd_7275122 := by exact prefixLift 7275122
  have htrace : WordTrace (prefixWord ++ tailWord_7275122) baseStart_7275122 baseEnd_7275122 := by
    simpa [prefixWord, tailWord_7275122, baseEnd_7275122] using wordTrace_append hprefix tailTrace_7275122
  have hstable : (prefixWord ++ tailWord_7275122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275122).length < 2 ^ (prefixWord ++ tailWord_7275122).sum := by decide
  have hdescent : baseEnd_7275122 < baseStart_7275122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275126 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_7275126 : Nat := 118140960795 + 7275126 * 2 ^ 59
def prefixEnd_7275126 : Nat := 4983230072969 + 3 ^ 40 * 7275126 * 2
def baseEnd_7275126 : Nat := 1245212153340536089922437

theorem tailTrace_7275126 : CollatzResearch.WordTrace tailWord_7275126 prefixEnd_7275126 1245212153340536089922437 := by
  unfold tailWord_7275126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584102765091779340376327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176897096160978979630680821 16584102765091779340376327)
  ·
    refine ⟨24876154147637669010564491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584102765091779340376327 24876154147637669010564491)
    ·
      refine ⟨37314231221456503515846737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24876154147637669010564491 37314231221456503515846737)
      ·
        refine ⟨27985673416092377636885053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37314231221456503515846737 27985673416092377636885053)
        ·
          refine ⟨10494627531034641613831895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27985673416092377636885053 10494627531034641613831895)
          ·
            refine ⟨15741941296551962420747843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494627531034641613831895 15741941296551962420747843)
            ·
              refine ⟨23612911944827943631121765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15741941296551962420747843 23612911944827943631121765)
              ·
                refine ⟨4427420989655239430835331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23612911944827943631121765 4427420989655239430835331)
                ·
                  refine ⟨6641131484482859146252997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427420989655239430835331 6641131484482859146252997)
                  ·
                    refine ⟨1245212153340536089922437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641131484482859146252997 1245212153340536089922437)
                    ·
                      rfl

theorem cell23_7275126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_7275126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275126 prefixEnd_7275126 := by exact prefixLift 7275126
  have htrace : WordTrace (prefixWord ++ tailWord_7275126) baseStart_7275126 baseEnd_7275126 := by
    simpa [prefixWord, tailWord_7275126, baseEnd_7275126] using wordTrace_append hprefix tailTrace_7275126
  have hstable : (prefixWord ++ tailWord_7275126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275126).length < 2 ^ (prefixWord ++ tailWord_7275126).sum := by decide
  have hdescent : baseEnd_7275126 < baseStart_7275126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275155 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 6, 2]
def baseStart_7275155 : Nat := 118140960795 + 7275155 * 2 ^ 59
def prefixEnd_7275155 : Nat := 4983230072969 + 3 ^ 40 * 7275155 * 2
def baseEnd_7275155 : Nat := 3735651350960588656304677

theorem tailTrace_7275155 : CollatzResearch.WordTrace tailWord_7275155 prefixEnd_7275155 3735651350960588656304677 := by
  unfold tailWord_7275155
  simp only [CollatzResearch.WordTrace]
  refine ⟨265346701958363407398826919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176897801305575604932551279 265346701958363407398826919)
  ·
    refine ⟨398020052937545111098240379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265346701958363407398826919 398020052937545111098240379)
    ·
      refine ⟨597030079406317666647360569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398020052937545111098240379 597030079406317666647360569)
      ·
        refine ⟨447772559554738249985520427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597030079406317666647360569 447772559554738249985520427)
        ·
          refine ⟨671658839332107374978280641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447772559554738249985520427 671658839332107374978280641)
          ·
            refine ⟨503744129499080531233710481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671658839332107374978280641 503744129499080531233710481)
            ·
              refine ⟨377808097124310398425282861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503744129499080531233710481 377808097124310398425282861)
              ·
                refine ⟨141678036421616399409481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377808097124310398425282861 141678036421616399409481073)
                ·
                  refine ⟨106258527316212299557110805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141678036421616399409481073 106258527316212299557110805)
                  ·
                    refine ⟨4980868467947451541739569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106258527316212299557110805 4980868467947451541739569)
                    ·
                      refine ⟨3735651350960588656304677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980868467947451541739569 3735651350960588656304677)
                      ·
                        rfl

theorem cell23_7275155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6, 2].length) (baseStart_7275155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275155 prefixEnd_7275155 := by exact prefixLift 7275155
  have htrace : WordTrace (prefixWord ++ tailWord_7275155) baseStart_7275155 baseEnd_7275155 := by
    simpa [prefixWord, tailWord_7275155, baseEnd_7275155] using wordTrace_append hprefix tailTrace_7275155
  have hstable : (prefixWord ++ tailWord_7275155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275155).length < 2 ^ (prefixWord ++ tailWord_7275155).sum := by decide
  have hdescent : baseEnd_7275155 < baseStart_7275155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275165 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7275165 : Nat := 118140960795 + 7275165 * 2 ^ 59
def prefixEnd_7275165 : Nat := 4983230072969 + 3 ^ 40 * 7275165 * 2
def baseEnd_7275165 : Nat := 1245218828589044539059877

theorem tailTrace_7275165 : CollatzResearch.WordTrace tailWord_7275165 prefixEnd_7275165 1245218828589044539059877 := by
  unfold tailWord_7275165
  simp only [CollatzResearch.WordTrace]
  refine ⟨265347066688327179106690949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176898044458884786071127299 265347066688327179106690949)
  ·
    refine ⟨49752575004061346082504553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265347066688327179106690949 49752575004061346082504553)
    ·
      refine ⟨37314431253046009561878415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49752575004061346082504553 37314431253046009561878415)
      ·
        refine ⟨55971646879569014342817623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37314431253046009561878415 55971646879569014342817623)
        ·
          refine ⟨83957470319353521514226435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55971646879569014342817623 83957470319353521514226435)
          ·
            refine ⟨125936205479030282271339653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83957470319353521514226435 125936205479030282271339653)
            ·
              refine ⟨23613038527318177925876185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125936205479030282271339653 23613038527318177925876185)
              ·
                refine ⟨17709778895488633444407139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23613038527318177925876185 17709778895488633444407139)
                ·
                  refine ⟨26564668343232950166610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17709778895488633444407139 26564668343232950166610709)
                  ·
                    refine ⟨1245218828589044539059877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26564668343232950166610709 1245218828589044539059877)
                    ·
                      rfl

theorem cell23_7275165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7275165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275165 prefixEnd_7275165 := by exact prefixLift 7275165
  have htrace : WordTrace (prefixWord ++ tailWord_7275165) baseStart_7275165 baseEnd_7275165 := by
    simpa [prefixWord, tailWord_7275165, baseEnd_7275165] using wordTrace_append hprefix tailTrace_7275165
  have hstable : (prefixWord ++ tailWord_7275165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275165).length < 2 ^ (prefixWord ++ tailWord_7275165).sum := by decide
  have hdescent : baseEnd_7275165 < baseStart_7275165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275172 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_7275172 : Nat := 118140960795 + 7275172 * 2 ^ 59
def prefixEnd_7275172 : Nat := 4983230072969 + 3 ^ 40 * 7275172 * 2
def baseEnd_7275172 : Nat := 3735660080131715089792099

theorem tailTrace_7275172 : CollatzResearch.WordTrace tailWord_7275172 prefixEnd_7275172 3735660080131715089792099 := by
  unfold tailWord_7275172
  simp only [CollatzResearch.WordTrace]
  refine ⟨132673660999650909651097885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176898214666201212868130513 132673660999650909651097885)
  ·
    refine ⟨49752622874869091119161707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132673660999650909651097885 49752622874869091119161707)
    ·
      refine ⟨74628934312303636678742561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49752622874869091119161707 74628934312303636678742561)
      ·
        refine ⟨55971700734227727509056921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74628934312303636678742561 55971700734227727509056921)
        ·
          refine ⟨41978775550670795631792691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55971700734227727509056921 41978775550670795631792691)
          ·
            refine ⟨62968163326006193447689037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41978775550670795631792691 62968163326006193447689037)
            ·
              refine ⟨23613061247252322542883389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62968163326006193447689037 23613061247252322542883389)
              ·
                refine ⟨8854897967719620953581271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23613061247252322542883389 8854897967719620953581271)
                ·
                  refine ⟨13282346951579431430371907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8854897967719620953581271 13282346951579431430371907)
                  ·
                    refine ⟨19923520427369147145557861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13282346951579431430371907 19923520427369147145557861)
                    ·
                      refine ⟨3735660080131715089792099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19923520427369147145557861 3735660080131715089792099)
                      ·
                        rfl

theorem cell23_7275172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_7275172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275172 prefixEnd_7275172 := by exact prefixLift 7275172
  have htrace : WordTrace (prefixWord ++ tailWord_7275172) baseStart_7275172 baseEnd_7275172 := by
    simpa [prefixWord, tailWord_7275172, baseEnd_7275172] using wordTrace_append hprefix tailTrace_7275172
  have hstable : (prefixWord ++ tailWord_7275172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275172).length < 2 ^ (prefixWord ++ tailWord_7275172).sum := by decide
  have hdescent : baseEnd_7275172 < baseStart_7275172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275199 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 2, 4]
def baseStart_7275199 : Nat := 118140960795 + 7275199 * 2 ^ 59
def prefixEnd_7275199 : Nat := 4983230072969 + 3 ^ 40 * 7275199 * 2
def baseEnd_7275199 : Nat := 1245224648036462161384825

theorem tailTrace_7275199 : CollatzResearch.WordTrace tailWord_7275199 prefixEnd_7275199 1245224648036462161384825 := by
  unfold tailWord_7275199
  simp only [CollatzResearch.WordTrace]
  refine ⟨265348306770204002913428651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176898871180136001942285767 265348306770204002913428651)
  ·
    refine ⟨398022460155306004370142977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265348306770204002913428651 398022460155306004370142977)
    ·
      refine ⟨298516845116479503277607233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398022460155306004370142977 298516845116479503277607233)
      ·
        refine ⟨223887633837359627458205425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298516845116479503277607233 223887633837359627458205425)
        ·
          refine ⟨167915725378019720593654069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223887633837359627458205425 167915725378019720593654069)
          ·
            refine ⟨15742099254189348805655069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167915725378019720593654069 15742099254189348805655069)
            ·
              refine ⟨5903287220321005802120651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742099254189348805655069 5903287220321005802120651)
              ·
                refine ⟨8854930830481508703180977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903287220321005802120651 8854930830481508703180977)
                ·
                  refine ⟨6641198122861131527385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8854930830481508703180977 6641198122861131527385733)
                  ·
                    refine ⟨1245224648036462161384825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641198122861131527385733 1245224648036462161384825)
                    ·
                      rfl

theorem cell23_7275199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_7275199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275199 prefixEnd_7275199 := by exact prefixLift 7275199
  have htrace : WordTrace (prefixWord ++ tailWord_7275199) baseStart_7275199 baseEnd_7275199 := by
    simpa [prefixWord, tailWord_7275199, baseEnd_7275199] using wordTrace_append hprefix tailTrace_7275199
  have hstable : (prefixWord ++ tailWord_7275199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275199).length < 2 ^ (prefixWord ++ tailWord_7275199).sum := by decide
  have hdescent : baseEnd_7275199 < baseStart_7275199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275212 : List Nat := [2, 2, 1, 5, 1, 1, 4, 7]
def baseStart_7275212 : Nat := 118140960795 + 7275212 * 2 ^ 59
def prefixEnd_7275212 : Nat := 4983230072969 + 3 ^ 40 * 7275212 * 2
def baseEnd_7275212 : Nat := 138358541457699812344145

theorem tailTrace_7275212 : CollatzResearch.WordTrace tailWord_7275212 prefixEnd_7275212 138358541457699812344145 := by
  unfold tailWord_7275212
  simp only [CollatzResearch.WordTrace]
  refine ⟨132674390459578453066825945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176899187279437937422434593 132674390459578453066825945)
  ·
    refine ⟨99505792844683839800119459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132674390459578453066825945 99505792844683839800119459)
    ·
      refine ⟨149258689267025759700179189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99505792844683839800119459 149258689267025759700179189)
      ·
        refine ⟨13993002118783664971891799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149258689267025759700179189 13993002118783664971891799)
        ·
          refine ⟨20989503178175497457837699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993002118783664971891799 20989503178175497457837699)
          ·
            refine ⟨31484254767263246186756549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20989503178175497457837699 31484254767263246186756549)
            ·
              refine ⟨5903297768861858660016853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31484254767263246186756549 5903297768861858660016853)
              ·
                refine ⟨138358541457699812344145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5903297768861858660016853 138358541457699812344145)
                ·
                  rfl

theorem cell23_7275212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 7].length) (baseStart_7275212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275212 prefixEnd_7275212 := by exact prefixLift 7275212
  have htrace : WordTrace (prefixWord ++ tailWord_7275212) baseStart_7275212 baseEnd_7275212 := by
    simpa [prefixWord, tailWord_7275212, baseEnd_7275212] using wordTrace_append hprefix tailTrace_7275212
  have hstable : (prefixWord ++ tailWord_7275212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275212).length < 2 ^ (prefixWord ++ tailWord_7275212).sum := by decide
  have hdescent : baseEnd_7275212 < baseStart_7275212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275223 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 1, 2, 2]
def baseStart_7275223 : Nat := 118140960795 + 7275223 * 2 ^ 59
def prefixEnd_7275223 : Nat := 4983230072969 + 3 ^ 40 * 7275223 * 2
def baseEnd_7275223 : Nat := 3735686267645094390254365

theorem tailTrace_7275223 : CollatzResearch.WordTrace tailWord_7275223 prefixEnd_7275223 3735686267645094390254365 := by
  unfold tailWord_7275223
  simp only [CollatzResearch.WordTrace]
  refine ⟨265349182122117055012302323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176899454748078036674868215 265349182122117055012302323)
  ·
    refine ⟨398023773183175582518453485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265349182122117055012302323 398023773183175582518453485)
    ·
      refine ⟨149258914943690843444420057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398023773183175582518453485 149258914943690843444420057)
      ·
        refine ⟨111944186207768132583315043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149258914943690843444420057 111944186207768132583315043)
        ·
          refine ⟨167916279311652198874972565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111944186207768132583315043 167916279311652198874972565)
          ·
            refine ⟨7871075592733696822264339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167916279311652198874972565 7871075592733696822264339)
            ·
              refine ⟨11806613389100545233396509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871075592733696822264339 11806613389100545233396509)
              ·
                refine ⟨4427480020912704462523691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11806613389100545233396509 4427480020912704462523691)
                ·
                  refine ⟨6641220031369056693785537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427480020912704462523691 6641220031369056693785537)
                  ·
                    refine ⟨4980915023526792520339153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641220031369056693785537 4980915023526792520339153)
                    ·
                      refine ⟨3735686267645094390254365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980915023526792520339153 3735686267645094390254365)
                      ·
                        rfl

theorem cell23_7275223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_7275223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275223 prefixEnd_7275223 := by exact prefixLift 7275223
  have htrace : WordTrace (prefixWord ++ tailWord_7275223) baseStart_7275223 baseEnd_7275223 := by
    simpa [prefixWord, tailWord_7275223, baseEnd_7275223] using wordTrace_append hprefix tailTrace_7275223
  have hstable : (prefixWord ++ tailWord_7275223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275223).length < 2 ^ (prefixWord ++ tailWord_7275223).sum := by decide
  have hdescent : baseEnd_7275223 < baseStart_7275223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275232 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2]
def baseStart_7275232 : Nat := 118140960795 + 7275232 * 2 ^ 59
def prefixEnd_7275232 : Nat := 4983230072969 + 3 ^ 40 * 7275232 * 2
def baseEnd_7275232 : Nat := 3735690888970984855041823

theorem tailTrace_7275232 : CollatzResearch.WordTrace tailWord_7275232 prefixEnd_7275232 3735690888970984855041823 := by
  unfold tailWord_7275232
  simp only [CollatzResearch.WordTrace]
  refine ⟨132674755189542224774689975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176899673586056299699586633 132674755189542224774689975)
  ·
    refine ⟨199012132784313337162034963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132674755189542224774689975 199012132784313337162034963)
    ·
      refine ⟨298518199176470005743052445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199012132784313337162034963 298518199176470005743052445)
      ·
        refine ⟨111944324691176252153644667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298518199176470005743052445 111944324691176252153644667)
        ·
          refine ⟨167916487036764378230467001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111944324691176252153644667 167916487036764378230467001)
          ·
            refine ⟨125937365277573283672850251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167916487036764378230467001 125937365277573283672850251)
            ·
              refine ⟨188906047916359925509275377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125937365277573283672850251 188906047916359925509275377)
              ·
                refine ⟨141679535937269944131956533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188906047916359925509275377 141679535937269944131956533)
                ·
                  refine ⟨13282456494119057262370925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141679535937269944131956533 13282456494119057262370925)
                  ·
                    refine ⟨4980921185294646473389097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13282456494119057262370925 4980921185294646473389097)
                    ·
                      refine ⟨3735690888970984855041823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980921185294646473389097 3735690888970984855041823)
                      ·
                        rfl

theorem cell23_7275232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_7275232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275232 prefixEnd_7275232 := by exact prefixLift 7275232
  have htrace : WordTrace (prefixWord ++ tailWord_7275232) baseStart_7275232 baseEnd_7275232 := by
    simpa [prefixWord, tailWord_7275232, baseEnd_7275232] using wordTrace_append hprefix tailTrace_7275232
  have hstable : (prefixWord ++ tailWord_7275232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275232).length < 2 ^ (prefixWord ++ tailWord_7275232).sum := by decide
  have hdescent : baseEnd_7275232 < baseStart_7275232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275240 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_7275240 : Nat := 118140960795 + 7275240 * 2 ^ 59
def prefixEnd_7275240 : Nat := 4983230072969 + 3 ^ 40 * 7275240 * 2
def baseEnd_7275240 : Nat := 3735694996816220823741787

theorem tailTrace_7275240 : CollatzResearch.WordTrace tailWord_7275240 prefixEnd_7275240 3735694996816220823741787 := by
  unfold tailWord_7275240
  simp only [CollatzResearch.WordTrace]
  refine ⟨132674901081527733457835587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176899868108703644610447449 132674901081527733457835587)
  ·
    refine ⟨199012351622291600186753381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132674901081527733457835587 199012351622291600186753381)
    ·
      refine ⟨37314815929179675035016259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199012351622291600186753381 37314815929179675035016259)
      ·
        refine ⟨55972223893769512552524389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37314815929179675035016259 55972223893769512552524389)
        ·
          refine ⟨10494791980081783603598323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55972223893769512552524389 10494791980081783603598323)
          ·
            refine ⟨15742187970122675405397485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494791980081783603598323 15742187970122675405397485)
            ·
              refine ⟨5903320488796003277024057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742187970122675405397485 5903320488796003277024057)
              ·
                refine ⟨4427490366597002457768043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903320488796003277024057 4427490366597002457768043)
                ·
                  refine ⟨6641235549895503686652065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427490366597002457768043 6641235549895503686652065)
                  ·
                    refine ⟨4980926662421627764989049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641235549895503686652065 4980926662421627764989049)
                    ·
                      refine ⟨3735694996816220823741787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980926662421627764989049 3735694996816220823741787)
                      ·
                        rfl

theorem cell23_7275240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_7275240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275240 prefixEnd_7275240 := by exact prefixLift 7275240
  have htrace : WordTrace (prefixWord ++ tailWord_7275240) baseStart_7275240 baseEnd_7275240 := by
    simpa [prefixWord, tailWord_7275240, baseEnd_7275240] using wordTrace_append hprefix tailTrace_7275240
  have hstable : (prefixWord ++ tailWord_7275240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275240).length < 2 ^ (prefixWord ++ tailWord_7275240).sum := by decide
  have hdescent : baseEnd_7275240 < baseStart_7275240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275266 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_7275266 : Nat := 118140960795 + 7275266 * 2 ^ 59
def prefixEnd_7275266 : Nat := 4983230072969 + 3 ^ 40 * 7275266 * 2
def baseEnd_7275266 : Nat := 3735708347313237722016667

theorem tailTrace_7275266 : CollatzResearch.WordTrace tailWord_7275266 prefixEnd_7275266 3735708347313237722016667 := by
  unfold tailWord_7275266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66337687615240318339029413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176900500307307515570745101 66337687615240318339029413)
  ·
    refine ⟨12438316427857559688568015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66337687615240318339029413 12438316427857559688568015)
    ·
      refine ⟨18657474641786339532852023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12438316427857559688568015 18657474641786339532852023)
      ·
        refine ⟨27986211962679509299278035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18657474641786339532852023 27986211962679509299278035)
        ·
          refine ⟨41979317944019263948917053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27986211962679509299278035 41979317944019263948917053)
          ·
            refine ⟨15742244229007223980843895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41979317944019263948917053 15742244229007223980843895)
            ·
              refine ⟨23613366343510835971265843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15742244229007223980843895 23613366343510835971265843)
              ·
                refine ⟨35420049515266253956898765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23613366343510835971265843 35420049515266253956898765)
                ·
                  refine ⟨13282518568224845233837037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35420049515266253956898765 13282518568224845233837037)
                  ·
                    refine ⟨4980944463084316962688889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13282518568224845233837037 4980944463084316962688889)
                    ·
                      refine ⟨3735708347313237722016667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980944463084316962688889 3735708347313237722016667)
                      ·
                        rfl

theorem cell23_7275266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_7275266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275266 prefixEnd_7275266 := by exact prefixLift 7275266
  have htrace : WordTrace (prefixWord ++ tailWord_7275266) baseStart_7275266 baseEnd_7275266 := by
    simpa [prefixWord, tailWord_7275266, baseEnd_7275266] using wordTrace_append hprefix tailTrace_7275266
  have hstable : (prefixWord ++ tailWord_7275266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275266).length < 2 ^ (prefixWord ++ tailWord_7275266).sum := by decide
  have hdescent : baseEnd_7275266 < baseStart_7275266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275275 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_7275275 : Nat := 118140960795 + 7275275 * 2 ^ 59
def prefixEnd_7275275 : Nat := 4983230072969 + 3 ^ 40 * 7275275 * 2
def baseEnd_7275275 : Nat := 3735712968639128186804125

theorem tailTrace_7275275 : CollatzResearch.WordTrace tailWord_7275275 prefixEnd_7275275 3735712968639128186804125 := by
  unfold tailWord_7275275
  simp only [CollatzResearch.WordTrace]
  refine ⟨265351078717928667893195279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176900719145285778595463519 265351078717928667893195279)
  ·
    refine ⟨398026618076893001839792919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265351078717928667893195279 398026618076893001839792919)
    ·
      refine ⟨597039927115339502759689379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398026618076893001839792919 597039927115339502759689379)
      ·
        refine ⟨895559890673009254139534069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597039927115339502759689379 895559890673009254139534069)
        ·
          refine ⟨83958739750594617575581319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 895559890673009254139534069 83958739750594617575581319)
          ·
            refine ⟨125938109625891926363371979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83958739750594617575581319 125938109625891926363371979)
            ·
              refine ⟨188907164438837889545057969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125938109625891926363371979 188907164438837889545057969)
              ·
                refine ⟨141680373329128417158793477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188907164438837889545057969 141680373329128417158793477)
                ·
                  refine ⟨26565069999211578217273777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141680373329128417158793477 26565069999211578217273777)
                  ·
                    refine ⟨19923802499408683662955333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26565069999211578217273777 19923802499408683662955333)
                    ·
                      refine ⟨3735712968639128186804125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19923802499408683662955333 3735712968639128186804125)
                      ·
                        rfl

theorem cell23_7275275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_7275275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275275 prefixEnd_7275275 := by exact prefixLift 7275275
  have htrace : WordTrace (prefixWord ++ tailWord_7275275) baseStart_7275275 baseEnd_7275275 := by
    simpa [prefixWord, tailWord_7275275, baseEnd_7275275] using wordTrace_append hprefix tailTrace_7275275
  have hstable : (prefixWord ++ tailWord_7275275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275275).length < 2 ^ (prefixWord ++ tailWord_7275275).sum := by decide
  have hdescent : baseEnd_7275275 < baseStart_7275275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275296 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7275296 : Nat := 118140960795 + 7275296 * 2 ^ 59
def prefixEnd_7275296 : Nat := 4983230072969 + 3 ^ 40 * 7275296 * 2
def baseEnd_7275296 : Nat := 3735723751732872604641529

theorem tailTrace_7275296 : CollatzResearch.WordTrace tailWord_7275296 prefixEnd_7275296 3735723751732872604641529 := by
  unfold tailWord_7275296
  simp only [CollatzResearch.WordTrace]
  refine ⟨132675922325426294239854871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176901229767235058986473161 132675922325426294239854871)
  ·
    refine ⟨199013883488139441359782307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132675922325426294239854871 199013883488139441359782307)
    ·
      refine ⟨298520825232209162039673461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199013883488139441359782307 298520825232209162039673461)
      ·
        refine ⟨27986327365519608941219387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298520825232209162039673461 27986327365519608941219387)
        ·
          refine ⟨41979491048279413411829081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27986327365519608941219387 41979491048279413411829081)
          ·
            refine ⟨31484618286209560058871811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41979491048279413411829081 31484618286209560058871811)
            ·
              refine ⟨47226927429314340088307717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31484618286209560058871811 47226927429314340088307717)
              ·
                refine ⟨8855048892996438766557697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47226927429314340088307717 8855048892996438766557697)
                ·
                  refine ⟨6641286669747329074918273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8855048892996438766557697 6641286669747329074918273)
                  ·
                    refine ⟨4980965002310496806188705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641286669747329074918273 4980965002310496806188705)
                    ·
                      refine ⟨3735723751732872604641529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980965002310496806188705 3735723751732872604641529)
                      ·
                        rfl

theorem cell23_7275296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7275296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275296 prefixEnd_7275296 := by exact prefixLift 7275296
  have htrace : WordTrace (prefixWord ++ tailWord_7275296) baseStart_7275296 baseEnd_7275296 := by
    simpa [prefixWord, tailWord_7275296, baseEnd_7275296] using wordTrace_append hprefix tailTrace_7275296
  have hstable : (prefixWord ++ tailWord_7275296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275296).length < 2 ^ (prefixWord ++ tailWord_7275296).sum := by decide
  have hdescent : baseEnd_7275296 < baseStart_7275296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275334 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7275334 : Nat := 118140960795 + 7275334 * 2 ^ 59
def prefixEnd_7275334 : Nat := 4983230072969 + 3 ^ 40 * 7275334 * 2
def baseEnd_7275334 : Nat := 3735743263997743455966355

theorem tailTrace_7275334 : CollatzResearch.WordTrace tailWord_7275334 prefixEnd_7275334 3735743263997743455966355 := by
  unfold tailWord_7275334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292288457022341280299783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176902153749809947313062037 8292288457022341280299783)
  ·
    refine ⟨12438432685533511920449675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8292288457022341280299783 12438432685533511920449675)
    ·
      refine ⟨18657649028300267880674513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12438432685533511920449675 18657649028300267880674513)
      ·
        refine ⟨13993236771225200910505885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18657649028300267880674513 13993236771225200910505885)
        ·
          refine ⟨5247463789209450341439707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13993236771225200910505885 5247463789209450341439707)
          ·
            refine ⟨7871195683814175512159561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247463789209450341439707 7871195683814175512159561)
            ·
              refine ⟨5903396762860631634119671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871195683814175512159561 5903396762860631634119671)
              ·
                refine ⟨8855095144290947451179507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903396762860631634119671 8855095144290947451179507)
                ·
                  refine ⟨13282642716436421176769261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855095144290947451179507 13282642716436421176769261)
                  ·
                    refine ⟨4980991018663657941288473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13282642716436421176769261 4980991018663657941288473)
                    ·
                      refine ⟨3735743263997743455966355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4980991018663657941288473 3735743263997743455966355)
                      ·
                        rfl

theorem cell23_7275334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7275334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275334 prefixEnd_7275334 := by exact prefixLift 7275334
  have htrace : WordTrace (prefixWord ++ tailWord_7275334) baseStart_7275334 baseEnd_7275334 := by
    simpa [prefixWord, tailWord_7275334, baseEnd_7275334] using wordTrace_append hprefix tailTrace_7275334
  have hstable : (prefixWord ++ tailWord_7275334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275334).length < 2 ^ (prefixWord ++ tailWord_7275334).sum := by decide
  have hdescent : baseEnd_7275334 < baseStart_7275334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275352 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7275352 : Nat := 118140960795 + 7275352 * 2 ^ 59
def prefixEnd_7275352 : Nat := 4983230072969 + 3 ^ 40 * 7275352 * 2
def baseEnd_7275352 : Nat := 3735752506649524385541271

theorem tailTrace_7275352 : CollatzResearch.WordTrace tailWord_7275352 prefixEnd_7275352 3735752506649524385541271 := by
  unfold tailWord_7275352
  simp only [CollatzResearch.WordTrace]
  refine ⟨132676943569324855021874155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176902591425766473362498873 132676943569324855021874155)
  ·
    refine ⟨199015415353987282532811233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132676943569324855021874155 199015415353987282532811233)
    ·
      refine ⟨149261561515490461899608425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199015415353987282532811233 149261561515490461899608425)
      ·
        refine ⟨111946171136617846424706319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149261561515490461899608425 111946171136617846424706319)
        ·
          refine ⟨167919256704926769637059479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111946171136617846424706319 167919256704926769637059479)
          ·
            refine ⟨251878885057390154455589219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167919256704926769637059479 251878885057390154455589219)
            ·
              refine ⟨377818327586085231683383829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251878885057390154455589219 377818327586085231683383829)
              ·
                refine ⟨17710234105597745235158617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377818327586085231683383829 17710234105597745235158617)
                ·
                  refine ⟨13282675579198308926368963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17710234105597745235158617 13282675579198308926368963)
                  ·
                    refine ⟨19924013368797463389553445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13282675579198308926368963 19924013368797463389553445)
                    ·
                      refine ⟨3735752506649524385541271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19924013368797463389553445 3735752506649524385541271)
                      ·
                        rfl

theorem cell23_7275352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7275352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275352 prefixEnd_7275352 := by exact prefixLift 7275352
  have htrace : WordTrace (prefixWord ++ tailWord_7275352) baseStart_7275352 baseEnd_7275352 := by
    simpa [prefixWord, tailWord_7275352, baseEnd_7275352] using wordTrace_append hprefix tailTrace_7275352
  have hstable : (prefixWord ++ tailWord_7275352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275352).length < 2 ^ (prefixWord ++ tailWord_7275352).sum := by decide
  have hdescent : baseEnd_7275352 < baseStart_7275352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275372 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_7275372 : Nat := 118140960795 + 7275372 * 2 ^ 59
def prefixEnd_7275372 : Nat := 4983230072969 + 3 ^ 40 * 7275372 * 2
def baseEnd_7275372 : Nat := 3735762776262614307291179

theorem tailTrace_7275372 : CollatzResearch.WordTrace tailWord_7275372 prefixEnd_7275372 3735762776262614307291179 := by
  unfold tailWord_7275372
  simp only [CollatzResearch.WordTrace]
  refine ⟨132677308299288626729738185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176903077732384835639650913 132677308299288626729738185)
  ·
    refine ⟨99507981224466470047303639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132677308299288626729738185 99507981224466470047303639)
    ·
      refine ⟨149261971836699705070955459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99507981224466470047303639 149261971836699705070955459)
      ·
        refine ⟨223892957755049557606433189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149261971836699705070955459 223892957755049557606433189)
        ·
          refine ⟨41979929579071792051206223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223892957755049557606433189 41979929579071792051206223)
          ·
            refine ⟨62969894368607688076809335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41979929579071792051206223 62969894368607688076809335)
            ·
              refine ⟨94454841552911532115214003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62969894368607688076809335 94454841552911532115214003)
              ·
                refine ⟨141682262329367298172821005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94454841552911532115214003 141682262329367298172821005)
                ·
                  refine ⟨53130848373512736814807877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141682262329367298172821005 53130848373512736814807877)
                  ·
                    refine ⟨9962034070033638152776477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53130848373512736814807877 9962034070033638152776477)
                    ·
                      refine ⟨3735762776262614307291179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9962034070033638152776477 3735762776262614307291179)
                      ·
                        rfl

theorem cell23_7275372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_7275372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275372 prefixEnd_7275372 := by exact prefixLift 7275372
  have htrace : WordTrace (prefixWord ++ tailWord_7275372) baseStart_7275372 baseEnd_7275372 := by
    simpa [prefixWord, tailWord_7275372, baseEnd_7275372] using wordTrace_append hprefix tailTrace_7275372
  have hstable : (prefixWord ++ tailWord_7275372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275372).length < 2 ^ (prefixWord ++ tailWord_7275372).sum := by decide
  have hdescent : baseEnd_7275372 < baseStart_7275372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275413 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_7275413 : Nat := 118140960795 + 7275413 * 2 ^ 59
def prefixEnd_7275413 : Nat := 4983230072969 + 3 ^ 40 * 7275413 * 2
def baseEnd_7275413 : Nat := 1245261276323149548959497

theorem tailTrace_7275413 : CollatzResearch.WordTrace tailWord_7275413 prefixEnd_7275413 1245261276323149548959497 := by
  unfold tailWord_7275413
  simp only [CollatzResearch.WordTrace]
  refine ⟨265356111991428717461718893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176904074660952478307812595 265356111991428717461718893)
  ·
    refine ⟨99508541996785769048144585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265356111991428717461718893 99508541996785769048144585)
    ·
      refine ⟨74631406497589326786108439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99508541996785769048144585 74631406497589326786108439)
      ·
        refine ⟨111947109746383990179162659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74631406497589326786108439 111947109746383990179162659)
        ·
          refine ⟨167920664619575985268743989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111947109746383990179162659 167920664619575985268743989)
          ·
            refine ⟨15742562308085248618944749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167920664619575985268743989 15742562308085248618944749)
            ·
              refine ⟨5903460865531968232104281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742562308085248618944749 5903460865531968232104281)
              ·
                refine ⟨4427595649148976174078211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903460865531968232104281 4427595649148976174078211)
                ·
                  refine ⟨6641393473723464261117317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427595649148976174078211 6641393473723464261117317)
                  ·
                    refine ⟨1245261276323149548959497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641393473723464261117317 1245261276323149548959497)
                    ·
                      rfl

theorem cell23_7275413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_7275413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275413 prefixEnd_7275413 := by exact prefixLift 7275413
  have htrace : WordTrace (prefixWord ++ tailWord_7275413) baseStart_7275413 baseEnd_7275413 := by
    simpa [prefixWord, tailWord_7275413, baseEnd_7275413] using wordTrace_append hprefix tailTrace_7275413
  have hstable : (prefixWord ++ tailWord_7275413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275413).length < 2 ^ (prefixWord ++ tailWord_7275413).sum := by decide
  have hdescent : baseEnd_7275413 < baseStart_7275413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275426 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_7275426 : Nat := 118140960795 + 7275426 * 2 ^ 59
def prefixEnd_7275426 : Nat := 4983230072969 + 3 ^ 40 * 7275426 * 2
def baseEnd_7275426 : Nat := 415087833801995232890659

theorem tailTrace_7275426 : CollatzResearch.WordTrace tailWord_7275426 prefixEnd_7275426 415087833801995232890659 := by
  unfold tailWord_7275426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66339146535095405170485533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176904390760254413787961421 66339146535095405170485533)
  ·
    refine ⟨24877179950660776938932075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66339146535095405170485533 24877179950660776938932075)
    ·
      refine ⟨37315769925991165408398113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24877179950660776938932075 37315769925991165408398113)
      ·
        refine ⟨27986827444493374056298585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37315769925991165408398113 27986827444493374056298585)
        ·
          refine ⟨20990120583370030542223939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27986827444493374056298585 20990120583370030542223939)
          ·
            refine ⟨31485180875055045813335909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990120583370030542223939 31485180875055045813335909)
            ·
              refine ⟨5903471414072821090000483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31485180875055045813335909 5903471414072821090000483)
              ·
                refine ⟨8855207121109231635000725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903471414072821090000483 8855207121109231635000725)
                ·
                  refine ⟨415087833801995232890659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8855207121109231635000725 415087833801995232890659)
                  ·
                    rfl

theorem cell23_7275426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_7275426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275426 prefixEnd_7275426 := by exact prefixLift 7275426
  have htrace : WordTrace (prefixWord ++ tailWord_7275426) baseStart_7275426 baseEnd_7275426 := by
    simpa [prefixWord, tailWord_7275426, baseEnd_7275426] using wordTrace_append hprefix tailTrace_7275426
  have hstable : (prefixWord ++ tailWord_7275426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275426).length < 2 ^ (prefixWord ++ tailWord_7275426).sum := by decide
  have hdescent : baseEnd_7275426 < baseStart_7275426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275456 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 1, 5]
def baseStart_7275456 : Nat := 118140960795 + 7275456 * 2 ^ 59
def prefixEnd_7275456 : Nat := 4983230072969 + 3 ^ 40 * 7275456 * 2
def baseEnd_7275456 : Nat := 1245268636212530659546931

theorem tailTrace_7275456 : CollatzResearch.WordTrace tailWord_7275456 prefixEnd_7275456 1245268636212530659546931 := by
  unfold tailWord_7275456
  simp only [CollatzResearch.WordTrace]
  refine ⟨132678840165136467902767111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176905120220181957203689481 132678840165136467902767111)
  ·
    refine ⟨199018260247704701854150667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132678840165136467902767111 199018260247704701854150667)
    ·
      refine ⟨298527390371557052781226001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199018260247704701854150667 298527390371557052781226001)
      ·
        refine ⟨223895542778667789585919501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298527390371557052781226001 223895542778667789585919501)
        ·
          refine ⟨83960828542000421094719813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223895542778667789585919501 83960828542000421094719813)
          ·
            refine ⟨15742655351625078955259965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83960828542000421094719813 15742655351625078955259965)
            ·
              refine ⟨5903495756859404608222487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15742655351625078955259965 5903495756859404608222487)
              ·
                refine ⟨8855243635289106912333731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903495756859404608222487 8855243635289106912333731)
                ·
                  refine ⟨13282865452933660368500597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855243635289106912333731 13282865452933660368500597)
                  ·
                    refine ⟨1245268636212530659546931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13282865452933660368500597 1245268636212530659546931)
                    ·
                      rfl

theorem cell23_7275456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_7275456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275456 prefixEnd_7275456 := by exact prefixLift 7275456
  have htrace : WordTrace (prefixWord ++ tailWord_7275456) baseStart_7275456 baseEnd_7275456 := by
    simpa [prefixWord, tailWord_7275456, baseEnd_7275456] using wordTrace_append hprefix tailTrace_7275456
  have hstable : (prefixWord ++ tailWord_7275456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275456).length < 2 ^ (prefixWord ++ tailWord_7275456).sum := by decide
  have hdescent : baseEnd_7275456 < baseStart_7275456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275470 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_7275470 : Nat := 118140960795 + 7275470 * 2 ^ 59
def prefixEnd_7275470 : Nat := 4983230072969 + 3 ^ 40 * 7275470 * 2
def baseEnd_7275470 : Nat := 3735813097366754923865729

theorem tailTrace_7275470 : CollatzResearch.WordTrace tailWord_7275470 prefixEnd_7275470 3735813097366754923865729 := by
  unfold tailWord_7275470
  simp only [CollatzResearch.WordTrace]
  refine ⟨33169773869027777024567983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176905460634814810797695909 33169773869027777024567983)
  ·
    refine ⟨49754660803541665536851975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33169773869027777024567983 49754660803541665536851975)
    ·
      refine ⟨74631991205312498305277963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49754660803541665536851975 74631991205312498305277963)
      ·
        refine ⟨111947986807968747457916945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74631991205312498305277963 111947986807968747457916945)
        ·
          refine ⟨83960990105976560593437709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111947986807968747457916945 83960990105976560593437709)
          ·
            refine ⟨31485371289741210222539141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83960990105976560593437709 31485371289741210222539141)
            ·
              refine ⟨5903507116826476916726089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31485371289741210222539141 5903507116826476916726089)
              ·
                refine ⟨4427630337619857687544567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5903507116826476916726089 4427630337619857687544567)
                ·
                  refine ⟨6641445506429786531316851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427630337619857687544567 6641445506429786531316851)
                  ·
                    refine ⟨9962168259644679796975277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6641445506429786531316851 9962168259644679796975277)
                    ·
                      refine ⟨3735813097366754923865729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9962168259644679796975277 3735813097366754923865729)
                      ·
                        rfl

theorem cell23_7275470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_7275470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275470 prefixEnd_7275470 := by exact prefixLift 7275470
  have htrace : WordTrace (prefixWord ++ tailWord_7275470) baseStart_7275470 baseEnd_7275470 := by
    simpa [prefixWord, tailWord_7275470, baseEnd_7275470] using wordTrace_append hprefix tailTrace_7275470
  have hstable : (prefixWord ++ tailWord_7275470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275470).length < 2 ^ (prefixWord ++ tailWord_7275470).sum := by decide
  have hdescent : baseEnd_7275470 < baseStart_7275470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275472 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_7275472 : Nat := 118140960795 + 7275472 * 2 ^ 59
def prefixEnd_7275472 : Nat := 4983230072969 + 3 ^ 40 * 7275472 * 2
def baseEnd_7275472 : Nat := 3735814124328063916040719

theorem tailTrace_7275472 : CollatzResearch.WordTrace tailWord_7275472 prefixEnd_7275472 3735814124328063916040719 := by
  unfold tailWord_7275472
  simp only [CollatzResearch.WordTrace]
  refine ⟨132679131949107485269058335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176905509265476647025411113 132679131949107485269058335)
  ·
    refine ⟨199018697923661227903587503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132679131949107485269058335 199018697923661227903587503)
    ·
      refine ⟨298528046885491841855381255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199018697923661227903587503 298528046885491841855381255)
      ·
        refine ⟨447792070328237762783071883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298528046885491841855381255 447792070328237762783071883)
        ·
          refine ⟨671688105492356644174607825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447792070328237762783071883 671688105492356644174607825)
          ·
            refine ⟨503766079119267483130955869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671688105492356644174607825 503766079119267483130955869)
            ·
              refine ⟨188912279669725306174108451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503766079119267483130955869 188912279669725306174108451)
              ·
                refine ⟨283368419504587959261162677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188912279669725306174108451 283368419504587959261162677)
                ·
                  refine ⟨26565789328555121180734001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283368419504587959261162677 26565789328555121180734001)
                  ·
                    refine ⟨19924341996416340885550501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26565789328555121180734001 19924341996416340885550501)
                    ·
                      refine ⟨3735814124328063916040719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19924341996416340885550501 3735814124328063916040719)
                      ·
                        rfl

theorem cell23_7275472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_7275472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275472 prefixEnd_7275472 := by exact prefixLift 7275472
  have htrace : WordTrace (prefixWord ++ tailWord_7275472) baseStart_7275472 baseEnd_7275472 := by
    simpa [prefixWord, tailWord_7275472, baseEnd_7275472] using wordTrace_append hprefix tailTrace_7275472
  have hstable : (prefixWord ++ tailWord_7275472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275472).length < 2 ^ (prefixWord ++ tailWord_7275472).sum := by decide
  have hdescent : baseEnd_7275472 < baseStart_7275472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275510 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7275510 : Nat := 118140960795 + 7275510 * 2 ^ 59
def prefixEnd_7275510 : Nat := 4983230072969 + 3 ^ 40 * 7275510 * 2
def baseEnd_7275510 : Nat := 3735833636592934767365545

theorem tailTrace_7275510 : CollatzResearch.WordTrace tailWord_7275510 prefixEnd_7275510 3735833636592934767365545 := by
  unfold tailWord_7275510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584978117004831439249999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176906433248051535351999989 16584978117004831439249999)
  ·
    refine ⟨24877467175507247158874999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16584978117004831439249999 24877467175507247158874999)
    ·
      refine ⟨37316200763260870738312499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24877467175507247158874999 37316200763260870738312499)
      ·
        refine ⟨55974301144891306107468749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37316200763260870738312499 55974301144891306107468749)
        ·
          refine ⟨20990362929334239790300781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55974301144891306107468749 20990362929334239790300781)
          ·
            refine ⟨7871386098500339921362793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20990362929334239790300781 7871386098500339921362793)
            ·
              refine ⟨5903539573875254941022095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7871386098500339921362793 5903539573875254941022095)
              ·
                refine ⟨8855309360812882411533143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903539573875254941022095 8855309360812882411533143)
                ·
                  refine ⟨13282964041219323617299715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855309360812882411533143 13282964041219323617299715)
                  ·
                    refine ⟨19924446061828985425949573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13282964041219323617299715 19924446061828985425949573)
                    ·
                      refine ⟨3735833636592934767365545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19924446061828985425949573 3735833636592934767365545)
                      ·
                        rfl

theorem cell23_7275510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7275510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275510 prefixEnd_7275510 := by exact prefixLift 7275510
  have htrace : WordTrace (prefixWord ++ tailWord_7275510) baseStart_7275510 baseEnd_7275510 := by
    simpa [prefixWord, tailWord_7275510, baseEnd_7275510] using wordTrace_append hprefix tailTrace_7275510
  have hstable : (prefixWord ++ tailWord_7275510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275510).length < 2 ^ (prefixWord ++ tailWord_7275510).sum := by decide
  have hdescent : baseEnd_7275510 < baseStart_7275510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275543 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7275543 : Nat := 118140960795 + 7275543 * 2 ^ 59
def prefixEnd_7275543 : Nat := 4983230072969 + 3 ^ 40 * 7275543 * 2
def baseEnd_7275543 : Nat := 3735850581454533138252893

theorem tailTrace_7275543 : CollatzResearch.WordTrace tailWord_7275543 prefixEnd_7275543 3735850581454533138252893 := by
  unfold tailWord_7275543
  simp only [CollatzResearch.WordTrace]
  refine ⟨265360853480957749663951283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176907235653971833109300855 265360853480957749663951283)
  ·
    refine ⟨398041280221436624495926925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265360853480957749663951283 398041280221436624495926925)
    ·
      refine ⟨149265480083038734185972597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398041280221436624495926925 149265480083038734185972597)
      ·
        refine ⟨13993638757784881329934931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149265480083038734185972597 13993638757784881329934931)
        ·
          refine ⟨20990458136677321994902397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993638757784881329934931 20990458136677321994902397)
          ·
            refine ⟨7871421801253995748088399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20990458136677321994902397 7871421801253995748088399)
            ·
              refine ⟨11807132701880993622132599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871421801253995748088399 11807132701880993622132599)
              ·
                refine ⟨17710699052821490433198899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807132701880993622132599 17710699052821490433198899)
                ·
                  refine ⟨26566048579232235649798349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17710699052821490433198899 26566048579232235649798349)
                  ·
                    refine ⟨9962268217212088368674381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26566048579232235649798349 9962268217212088368674381)
                    ·
                      refine ⟨3735850581454533138252893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9962268217212088368674381 3735850581454533138252893)
                      ·
                        rfl

theorem cell23_7275543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7275543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275543 prefixEnd_7275543 := by exact prefixLift 7275543
  have htrace : WordTrace (prefixWord ++ tailWord_7275543) baseStart_7275543 baseEnd_7275543 := by
    simpa [prefixWord, tailWord_7275543, baseEnd_7275543] using wordTrace_append hprefix tailTrace_7275543
  have hstable : (prefixWord ++ tailWord_7275543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275543).length < 2 ^ (prefixWord ++ tailWord_7275543).sum := by decide
  have hdescent : baseEnd_7275543 < baseStart_7275543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275553 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_7275553 : Nat := 118140960795 + 7275553 * 2 ^ 59
def prefixEnd_7275553 : Nat := 4983230072969 + 3 ^ 40 * 7275553 * 2
def baseEnd_7275553 : Nat := 3735855716261078099127847

theorem tailTrace_7275553 : CollatzResearch.WordTrace tailWord_7275553 prefixEnd_7275553 3735855716261078099127847 := by
  unfold tailWord_7275553
  simp only [CollatzResearch.WordTrace]
  refine ⟨265361218210921521371815313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176907478807281014247876875 265361218210921521371815313)
  ·
    refine ⟨199020913658191141028861485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265361218210921521371815313 199020913658191141028861485)
    ·
      refine ⟨74632842621821677885823057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199020913658191141028861485 74632842621821677885823057)
      ·
        refine ⟨55974631966366258414367293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74632842621821677885823057 55974631966366258414367293)
        ·
          refine ⟨20990486987387346905387735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55974631966366258414367293 20990486987387346905387735)
          ·
            refine ⟨31485730481081020358081603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990486987387346905387735 31485730481081020358081603)
            ·
              refine ⟨47228595721621530537122405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31485730481081020358081603 47228595721621530537122405)
              ·
                refine ⟨8855361697804036975710451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47228595721621530537122405 8855361697804036975710451)
                ·
                  refine ⟨13283042546706055463565677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855361697804036975710451 13283042546706055463565677)
                  ·
                    refine ⟨4981140955014770798837129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13283042546706055463565677 4981140955014770798837129)
                    ·
                      refine ⟨3735855716261078099127847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981140955014770798837129 3735855716261078099127847)
                      ·
                        rfl

theorem cell23_7275553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_7275553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275553 prefixEnd_7275553 := by exact prefixLift 7275553
  have htrace : WordTrace (prefixWord ++ tailWord_7275553) baseStart_7275553 baseEnd_7275553 := by
    simpa [prefixWord, tailWord_7275553, baseEnd_7275553] using wordTrace_append hprefix tailTrace_7275553
  have hstable : (prefixWord ++ tailWord_7275553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275553).length < 2 ^ (prefixWord ++ tailWord_7275553).sum := by decide
  have hdescent : baseEnd_7275553 < baseStart_7275553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275569 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7275569 : Nat := 118140960795 + 7275569 * 2 ^ 59
def prefixEnd_7275569 : Nat := 4983230072969 + 3 ^ 40 * 7275569 * 2
def baseEnd_7275569 : Nat := 3735863931951550036527773

theorem tailTrace_7275569 : CollatzResearch.WordTrace tailWord_7275569 prefixEnd_7275569 3735863931951550036527773 := by
  unfold tailWord_7275569
  simp only [CollatzResearch.WordTrace]
  refine ⟨265361801778863556104397761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176907867852575704069598507 265361801778863556104397761)
  ·
    refine ⟨199021351334147667078298321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265361801778863556104397761 199021351334147667078298321)
    ·
      refine ⟨149266013500610750308723741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199021351334147667078298321 149266013500610750308723741)
      ·
        refine ⟨55974755062729031365771403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149266013500610750308723741 55974755062729031365771403)
        ·
          refine ⟨83962132594093547048657105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55974755062729031365771403 83962132594093547048657105)
          ·
            refine ⟨62971599445570160286492829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83962132594093547048657105 62971599445570160286492829)
            ·
              refine ⟨23614349792088810107434811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62971599445570160286492829 23614349792088810107434811)
              ·
                refine ⟨35421524688133215161152217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23614349792088810107434811 35421524688133215161152217)
                ·
                  refine ⟨26566143516099911370864163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35421524688133215161152217 26566143516099911370864163)
                  ·
                    refine ⟨39849215274149867056296245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26566143516099911370864163 39849215274149867056296245)
                    ·
                      refine ⟨3735863931951550036527773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39849215274149867056296245 3735863931951550036527773)
                      ·
                        rfl

theorem cell23_7275569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7275569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275569 prefixEnd_7275569 := by exact prefixLift 7275569
  have htrace : WordTrace (prefixWord ++ tailWord_7275569) baseStart_7275569 baseEnd_7275569 := by
    simpa [prefixWord, tailWord_7275569, baseEnd_7275569] using wordTrace_append hprefix tailTrace_7275569
  have hstable : (prefixWord ++ tailWord_7275569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275569).length < 2 ^ (prefixWord ++ tailWord_7275569).sum := by decide
  have hdescent : baseEnd_7275569 < baseStart_7275569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275583 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 2, 2, 2]
def baseStart_7275583 : Nat := 118140960795 + 7275583 * 2 ^ 59
def prefixEnd_7275583 : Nat := 4983230072969 + 3 ^ 40 * 7275583 * 2
def baseEnd_7275583 : Nat := 3735871120680712981752709

theorem tailTrace_7275583 : CollatzResearch.WordTrace tailWord_7275583 prefixEnd_7275583 3735871120680712981752709 := by
  unfold tailWord_7275583
  simp only [CollatzResearch.WordTrace]
  refine ⟨265362312400812836495407403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176908208267208557663604935 265362312400812836495407403)
  ·
    refine ⟨398043468601219254743111105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265362312400812836495407403 398043468601219254743111105)
    ·
      refine ⟨298532601450914441057333329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398043468601219254743111105 298532601450914441057333329)
      ·
        refine ⟨223899451088185830792999997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298532601450914441057333329 223899451088185830792999997)
        ·
          refine ⟨83962294158069686547374999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223899451088185830792999997 83962294158069686547374999)
          ·
            refine ⟨125943441237104529821062499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83962294158069686547374999 125943441237104529821062499)
            ·
              refine ⟨188915161855656794731593749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125943441237104529821062499 188915161855656794731593749)
              ·
                refine ⟨8855398211983912253043457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188915161855656794731593749 8855398211983912253043457)
                ·
                  refine ⟨6641548658987934189782593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8855398211983912253043457 6641548658987934189782593)
                  ·
                    refine ⟨4981161494240950642336945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641548658987934189782593 4981161494240950642336945)
                    ·
                      refine ⟨3735871120680712981752709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981161494240950642336945 3735871120680712981752709)
                      ·
                        rfl

theorem cell23_7275583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_7275583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275583 prefixEnd_7275583 := by exact prefixLift 7275583
  have htrace : WordTrace (prefixWord ++ tailWord_7275583) baseStart_7275583 baseEnd_7275583 := by
    simpa [prefixWord, tailWord_7275583, baseEnd_7275583] using wordTrace_append hprefix tailTrace_7275583
  have hstable : (prefixWord ++ tailWord_7275583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275583).length < 2 ^ (prefixWord ++ tailWord_7275583).sum := by decide
  have hdescent : baseEnd_7275583 < baseStart_7275583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275589 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 7]
def baseStart_7275589 : Nat := 118140960795 + 7275589 * 2 ^ 59
def prefixEnd_7275589 : Nat := 4983230072969 + 3 ^ 40 * 7275589 * 2
def baseEnd_7275589 : Nat := 415097133507182217586409

theorem tailTrace_7275589 : CollatzResearch.WordTrace tailWord_7275589 prefixEnd_7275589 415097133507182217586409 := by
  unfold tailWord_7275589
  simp only [CollatzResearch.WordTrace]
  refine ⟨265362531238791099520125821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176908354159194066346750547 265362531238791099520125821)
  ·
    refine ⟨99510949214546662320047183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265362531238791099520125821 99510949214546662320047183)
    ·
      refine ⟨149266423821819993480070775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99510949214546662320047183 149266423821819993480070775)
      ·
        refine ⟨223899635732729990220106163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149266423821819993480070775 223899635732729990220106163)
        ·
          refine ⟨335849453599094985330159245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223899635732729990220106163 335849453599094985330159245)
          ·
            refine ⟨125943545099660619498809717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335849453599094985330159245 125943545099660619498809717)
            ·
              refine ⟨11807207353093183078013411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125943545099660619498809717 11807207353093183078013411)
              ·
                refine ⟨17710811029639774617020117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807207353093183078013411 17710811029639774617020117)
                ·
                  refine ⟨415097133507182217586409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17710811029639774617020117 415097133507182217586409)
                  ·
                    rfl

theorem cell23_7275589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_7275589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275589 prefixEnd_7275589 := by exact prefixLift 7275589
  have htrace : WordTrace (prefixWord ++ tailWord_7275589) baseStart_7275589 baseEnd_7275589 := by
    simpa [prefixWord, tailWord_7275589, baseEnd_7275589] using wordTrace_append hprefix tailTrace_7275589
  have hstable : (prefixWord ++ tailWord_7275589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275589).length < 2 ^ (prefixWord ++ tailWord_7275589).sum := by decide
  have hdescent : baseEnd_7275589 < baseStart_7275589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275669 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7275669 : Nat := 118140960795 + 7275669 * 2 ^ 59
def prefixEnd_7275669 : Nat := 4983230072969 + 3 ^ 40 * 7275669 * 2
def baseEnd_7275669 : Nat := 3735915280016999645277313

theorem tailTrace_7275669 : CollatzResearch.WordTrace tailWord_7275669 prefixEnd_7275669 3735915280016999645277313 := by
  unfold tailWord_7275669
  simp only [CollatzResearch.WordTrace]
  refine ⟨265365449078501273183038061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176910299385667515455358707 265365449078501273183038061)
  ·
    refine ⟨99512043404437977443639273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265365449078501273183038061 99512043404437977443639273)
    ·
      refine ⟨74634032553328483082729455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99512043404437977443639273 74634032553328483082729455)
      ·
        refine ⟨111951048829992724624094183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74634032553328483082729455 111951048829992724624094183)
        ·
          refine ⟨167926573244989086936141275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111951048829992724624094183 167926573244989086936141275)
          ·
            refine ⟨251889859867483630404211913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167926573244989086936141275 251889859867483630404211913)
            ·
              refine ⟨188917394900612722803158935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251889859867483630404211913 188917394900612722803158935)
              ·
                refine ⟨283376092350919084204738403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188917394900612722803158935 283376092350919084204738403)
                ·
                  refine ⟨425064138526378626307107605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283376092350919084204738403 425064138526378626307107605)
                  ·
                    refine ⟨19924881493423998108145669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 425064138526378626307107605 19924881493423998108145669)
                    ·
                      refine ⟨3735915280016999645277313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19924881493423998108145669 3735915280016999645277313)
                      ·
                        rfl

theorem cell23_7275669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7275669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275669 prefixEnd_7275669 := by exact prefixLift 7275669
  have htrace : WordTrace (prefixWord ++ tailWord_7275669) baseStart_7275669 baseEnd_7275669 := by
    simpa [prefixWord, tailWord_7275669, baseEnd_7275669] using wordTrace_append hprefix tailTrace_7275669
  have hstable : (prefixWord ++ tailWord_7275669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275669).length < 2 ^ (prefixWord ++ tailWord_7275669).sum := by decide
  have hdescent : baseEnd_7275669 < baseStart_7275669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275690 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7275690 : Nat := 118140960795 + 7275690 * 2 ^ 59
def prefixEnd_7275690 : Nat := 4983230072969 + 3 ^ 40 * 7275690 * 2
def baseEnd_7275690 : Nat := 3735926063110744063114717

theorem tailTrace_7275690 : CollatzResearch.WordTrace tailWord_7275690 prefixEnd_7275690 3735926063110744063114717 := by
  unfold tailWord_7275690
  simp only [CollatzResearch.WordTrace]
  refine ⟨66341553752856298442388131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176910810007616795846368349 66341553752856298442388131)
  ·
    refine ⟨99512330629284447663582197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66341553752856298442388131 99512330629284447663582197)
    ·
      refine ⟨9329280996495416968460831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99512330629284447663582197 9329280996495416968460831)
      ·
        refine ⟨13993921494743125452691247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329280996495416968460831 13993921494743125452691247)
        ·
          refine ⟨20990882242114688179036871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13993921494743125452691247 20990882242114688179036871)
          ·
            refine ⟨31486323363172032268555307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990882242114688179036871 31486323363172032268555307)
            ·
              refine ⟨47229485044758048402832961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31486323363172032268555307 47229485044758048402832961)
              ·
                refine ⟨35422113783568536302124721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47229485044758048402832961 35422113783568536302124721)
                ·
                  refine ⟨26566585337676402226593541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35422113783568536302124721 26566585337676402226593541)
                  ·
                    refine ⟨4981234750814325417486289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26566585337676402226593541 4981234750814325417486289)
                    ·
                      refine ⟨3735926063110744063114717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981234750814325417486289 3735926063110744063114717)
                      ·
                        rfl

theorem cell23_7275690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7275690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275690 prefixEnd_7275690 := by exact prefixLift 7275690
  have htrace : WordTrace (prefixWord ++ tailWord_7275690) baseStart_7275690 baseEnd_7275690 := by
    simpa [prefixWord, tailWord_7275690, baseEnd_7275690] using wordTrace_append hprefix tailTrace_7275690
  have hstable : (prefixWord ++ tailWord_7275690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275690).length < 2 ^ (prefixWord ++ tailWord_7275690).sum := by decide
  have hdescent : baseEnd_7275690 < baseStart_7275690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275699 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_7275699 : Nat := 118140960795 + 7275699 * 2 ^ 59
def prefixEnd_7275699 : Nat := 4983230072969 + 3 ^ 40 * 7275699 * 2
def baseEnd_7275699 : Nat := 3735930684436634527902175

theorem tailTrace_7275699 : CollatzResearch.WordTrace tailWord_7275699 prefixEnd_7275699 3735930684436634527902175 := by
  unfold tailWord_7275699
  simp only [CollatzResearch.WordTrace]
  refine ⟨265366543268392588306630151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176911028845595058871086767 265366543268392588306630151)
  ·
    refine ⟨398049814902588882459945227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265366543268392588306630151 398049814902588882459945227)
    ·
      refine ⟨597074722353883323689917841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398049814902588882459945227 597074722353883323689917841)
      ·
        refine ⟨447806041765412492767438381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597074722353883323689917841 447806041765412492767438381)
        ·
          refine ⟨167927265662029684787789393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447806041765412492767438381 167927265662029684787789393)
          ·
            refine ⟨125945449246522263590842045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167927265662029684787789393 125945449246522263590842045)
            ·
              refine ⟨47229543467445848846565767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125945449246522263590842045 47229543467445848846565767)
              ·
                refine ⟨70844315201168773269848651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47229543467445848846565767 70844315201168773269848651)
                ·
                  refine ⟨106266472801753159904772977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70844315201168773269848651 106266472801753159904772977)
                  ·
                    refine ⟨79699854601314869928579733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106266472801753159904772977 79699854601314869928579733)
                    ·
                      refine ⟨3735930684436634527902175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79699854601314869928579733 3735930684436634527902175)
                      ·
                        rfl

theorem cell23_7275699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_7275699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275699 prefixEnd_7275699 := by exact prefixLift 7275699
  have htrace : WordTrace (prefixWord ++ tailWord_7275699) baseStart_7275699 baseEnd_7275699 := by
    simpa [prefixWord, tailWord_7275699, baseEnd_7275699] using wordTrace_append hprefix tailTrace_7275699
  have hstable : (prefixWord ++ tailWord_7275699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275699).length < 2 ^ (prefixWord ++ tailWord_7275699).sum := by decide
  have hdescent : baseEnd_7275699 < baseStart_7275699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275719 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_7275719 : Nat := 118140960795 + 7275719 * 2 ^ 59
def prefixEnd_7275719 : Nat := 4983230072969 + 3 ^ 40 * 7275719 * 2
def baseEnd_7275719 : Nat := 3735940954049724449652083

theorem tailTrace_7275719 : CollatzResearch.WordTrace tailWord_7275719 prefixEnd_7275719 3735940954049724449652083 := by
  unfold tailWord_7275719
  simp only [CollatzResearch.WordTrace]
  refine ⟨265367272728320131722358211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176911515152213421148238807 265367272728320131722358211)
  ·
    refine ⟨398050909092480197583537317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265367272728320131722358211 398050909092480197583537317)
    ·
      refine ⟨74634545454840037046913247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 398050909092480197583537317 74634545454840037046913247)
      ·
        refine ⟨111951818182260055570369871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74634545454840037046913247 111951818182260055570369871)
        ·
          refine ⟨167927727273390083355554807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111951818182260055570369871 167927727273390083355554807)
          ·
            refine ⟨251891590910085125033332211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167927727273390083355554807 251891590910085125033332211)
            ·
              refine ⟨377837386365127687549998317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251891590910085125033332211 377837386365127687549998317)
              ·
                refine ⟨141689019886922882831249369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377837386365127687549998317 141689019886922882831249369)
                ·
                  refine ⟨106266764915192162123437027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141689019886922882831249369 106266764915192162123437027)
                  ·
                    refine ⟨159400147372788243185155541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106266764915192162123437027 159400147372788243185155541)
                    ·
                      refine ⟨3735940954049724449652083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159400147372788243185155541 3735940954049724449652083)
                      ·
                        rfl

theorem cell23_7275719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_7275719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275719 prefixEnd_7275719 := by exact prefixLift 7275719
  have htrace : WordTrace (prefixWord ++ tailWord_7275719) baseStart_7275719 baseEnd_7275719 := by
    simpa [prefixWord, tailWord_7275719, baseEnd_7275719] using wordTrace_append hprefix tailTrace_7275719
  have hstable : (prefixWord ++ tailWord_7275719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275719).length < 2 ^ (prefixWord ++ tailWord_7275719).sum := by decide
  have hdescent : baseEnd_7275719 < baseStart_7275719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275757 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7275757 : Nat := 118140960795 + 7275757 * 2 ^ 59
def prefixEnd_7275757 : Nat := 4983230072969 + 3 ^ 40 * 7275757 * 2
def baseEnd_7275757 : Nat := 3735960466314595300976909

theorem tailTrace_7275757 : CollatzResearch.WordTrace tailWord_7275757 prefixEnd_7275757 3735960466314595300976909 := by
  unfold tailWord_7275757
  simp only [CollatzResearch.WordTrace]
  refine ⟨265368658702182464212241525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176912439134788309474827683 265368658702182464212241525)
  ·
    refine ⟨24878311753329606019897643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 265368658702182464212241525 24878311753329606019897643)
    ·
      refine ⟨37317467629994409029846465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24878311753329606019897643 37317467629994409029846465)
      ·
        refine ⟨27988100722495806772384849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37317467629994409029846465 27988100722495806772384849)
        ·
          refine ⟨20991075541871855079288637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27988100722495806772384849 20991075541871855079288637)
          ·
            refine ⟨7871653328201945654733239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20991075541871855079288637 7871653328201945654733239)
            ·
              refine ⟨11807479992302918482099859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871653328201945654733239 11807479992302918482099859)
              ·
                refine ⟨17711219988454377723149789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807479992302918482099859 17711219988454377723149789)
                ·
                  refine ⟨6641707495670391646181171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17711219988454377723149789 6641707495670391646181171)
                  ·
                    refine ⟨9962561243505587469271757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6641707495670391646181171 9962561243505587469271757)
                    ·
                      refine ⟨3735960466314595300976909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9962561243505587469271757 3735960466314595300976909)
                      ·
                        rfl

theorem cell23_7275757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7275757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275757 prefixEnd_7275757 := by exact prefixLift 7275757
  have htrace : WordTrace (prefixWord ++ tailWord_7275757) baseStart_7275757 baseEnd_7275757 := by
    simpa [prefixWord, tailWord_7275757, baseEnd_7275757] using wordTrace_append hprefix tailTrace_7275757
  have hstable : (prefixWord ++ tailWord_7275757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275757).length < 2 ^ (prefixWord ++ tailWord_7275757).sum := by decide
  have hdescent : baseEnd_7275757 < baseStart_7275757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275776 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_7275776 : Nat := 118140960795 + 7275776 * 2 ^ 59
def prefixEnd_7275776 : Nat := 4983230072969 + 3 ^ 40 * 7275776 * 2
def baseEnd_7275776 : Nat := 3735970222447030726639321

theorem tailTrace_7275776 : CollatzResearch.WordTrace tailWord_7275776 prefixEnd_7275776 3735970222447030726639321 := by
  unfold tailWord_7275776
  simp only [CollatzResearch.WordTrace]
  refine ⟨132684675844556815228591591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176912901126075753638122121 132684675844556815228591591)
  ·
    refine ⟨199027013766835222842887387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132684675844556815228591591 199027013766835222842887387)
    ·
      refine ⟨298540520650252834264331081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199027013766835222842887387 298540520650252834264331081)
      ·
        refine ⟨223905390487689625698248311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298540520650252834264331081 223905390487689625698248311)
        ·
          refine ⟨335858085731534438547372467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223905390487689625698248311 335858085731534438547372467)
          ·
            refine ⟨503787128597301657821058701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335858085731534438547372467 503787128597301657821058701)
            ·
              refine ⟨188920173223988121682897013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503787128597301657821058701 188920173223988121682897013)
              ·
                refine ⟨17711266239748886407771595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188920173223988121682897013 17711266239748886407771595)
                ·
                  refine ⟨26566899359623329611657393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17711266239748886407771595 26566899359623329611657393)
                  ·
                    refine ⟨19925174519717497208743045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26566899359623329611657393 19925174519717497208743045)
                    ·
                      refine ⟨3735970222447030726639321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19925174519717497208743045 3735970222447030726639321)
                      ·
                        rfl

theorem cell23_7275776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_7275776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275776 prefixEnd_7275776 := by exact prefixLift 7275776
  have htrace : WordTrace (prefixWord ++ tailWord_7275776) baseStart_7275776 baseEnd_7275776 := by
    simpa [prefixWord, tailWord_7275776, baseEnd_7275776] using wordTrace_append hprefix tailTrace_7275776
  have hstable : (prefixWord ++ tailWord_7275776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275776).length < 2 ^ (prefixWord ++ tailWord_7275776).sum := by decide
  have hdescent : baseEnd_7275776 < baseStart_7275776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275780 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_7275780 : Nat := 118140960795 + 7275780 * 2 ^ 59
def prefixEnd_7275780 : Nat := 4983230072969 + 3 ^ 40 * 7275780 * 2
def baseEnd_7275780 : Nat := 3735972276369648710989303

theorem tailTrace_7275780 : CollatzResearch.WordTrace tailWord_7275780 prefixEnd_7275780 3735972276369648710989303 := by
  unfold tailWord_7275780
  simp only [CollatzResearch.WordTrace]
  refine ⟨132684748790549569570164397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176912998387399426093552529 132684748790549569570164397)
  ·
    refine ⟨49756780796456088588811649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132684748790549569570164397 49756780796456088588811649)
    ·
      refine ⟨37317585597342066441608737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49756780796456088588811649 37317585597342066441608737)
      ·
        refine ⟨27988189198006549831206553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37317585597342066441608737 27988189198006549831206553)
        ·
          refine ⟨20991141898504912373404915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27988189198006549831206553 20991141898504912373404915)
          ·
            refine ⟨31486712847757368560107373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20991141898504912373404915 31486712847757368560107373)
            ·
              refine ⟨11807517317909013210040265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31486712847757368560107373 11807517317909013210040265)
              ·
                refine ⟨8855637988431759907530199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807517317909013210040265 8855637988431759907530199)
                ·
                  refine ⟨13283456982647639861295299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855637988431759907530199 13283456982647639861295299)
                  ·
                    refine ⟨19925185473971459791942949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13283456982647639861295299 19925185473971459791942949)
                    ·
                      refine ⟨3735972276369648710989303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19925185473971459791942949 3735972276369648710989303)
                      ·
                        rfl

theorem cell23_7275780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_7275780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275780 prefixEnd_7275780 := by exact prefixLift 7275780
  have htrace : WordTrace (prefixWord ++ tailWord_7275780) baseStart_7275780 baseEnd_7275780 := by
    simpa [prefixWord, tailWord_7275780, baseEnd_7275780] using wordTrace_append hprefix tailTrace_7275780
  have hstable : (prefixWord ++ tailWord_7275780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275780).length < 2 ^ (prefixWord ++ tailWord_7275780).sum := by decide
  have hdescent : baseEnd_7275780 < baseStart_7275780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275794 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7275794 : Nat := 118140960795 + 7275794 * 2 ^ 59
def prefixEnd_7275794 : Nat := 4983230072969 + 3 ^ 40 * 7275794 * 2
def baseEnd_7275794 : Nat := 1245326488366270552071413

theorem tailTrace_7275794 : CollatzResearch.WordTrace tailWord_7275794 prefixEnd_7275794 1245326488366270552071413 := by
  unfold tailWord_7275794
  simp only [CollatzResearch.WordTrace]
  refine ⟨66342502050762104882834609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176913338802032279687558957 66342502050762104882834609)
  ·
    refine ⟨49756876538071578662125957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66342502050762104882834609 49756876538071578662125957)
    ·
      refine ⟨9329414350888420999148617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49756876538071578662125957 9329414350888420999148617)
      ·
        refine ⟨6997060763166315749361463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9329414350888420999148617 6997060763166315749361463)
        ·
          refine ⟨10495591144749473624042195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997060763166315749361463 10495591144749473624042195)
          ·
            refine ⟨15743386717124210436063293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495591144749473624042195 15743386717124210436063293)
            ·
              refine ⟨5903770018921578913523735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15743386717124210436063293 5903770018921578913523735)
              ·
                refine ⟨8855655028382368370285603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5903770018921578913523735 8855655028382368370285603)
                ·
                  refine ⟨13283482542573552555428405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855655028382368370285603 13283482542573552555428405)
                  ·
                    refine ⟨1245326488366270552071413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13283482542573552555428405 1245326488366270552071413)
                    ·
                      rfl

theorem cell23_7275794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7275794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275794 prefixEnd_7275794 := by exact prefixLift 7275794
  have htrace : WordTrace (prefixWord ++ tailWord_7275794) baseStart_7275794 baseEnd_7275794 := by
    simpa [prefixWord, tailWord_7275794, baseEnd_7275794] using wordTrace_append hprefix tailTrace_7275794
  have hstable : (prefixWord ++ tailWord_7275794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275794).length < 2 ^ (prefixWord ++ tailWord_7275794).sum := by decide
  have hdescent : baseEnd_7275794 < baseStart_7275794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275797 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_7275797 : Nat := 118140960795 + 7275797 * 2 ^ 59
def prefixEnd_7275797 : Nat := 4983230072969 + 3 ^ 40 * 7275797 * 2
def baseEnd_7275797 : Nat := 3735981005540775144476725

theorem tailTrace_7275797 : CollatzResearch.WordTrace tailWord_7275797 prefixEnd_7275797 3735981005540775144476725 := by
  unfold tailWord_7275797
  simp only [CollatzResearch.WordTrace]
  refine ⟨265370117622037551043697645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176913411748025034029131763 265370117622037551043697645)
  ·
    refine ⟨99513794108264081641386617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265370117622037551043697645 99513794108264081641386617)
    ·
      refine ⟨74635345581198061231039963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99513794108264081641386617 74635345581198061231039963)
      ·
        refine ⟨111953018371797091846559945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74635345581198061231039963 111953018371797091846559945)
        ·
          refine ⟨83964763778847818884919959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111953018371797091846559945 83964763778847818884919959)
          ·
            refine ⟨125947145668271728327379939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83964763778847818884919959 125947145668271728327379939)
            ·
              refine ⟨188920718502407592491069909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125947145668271728327379939 188920718502407592491069909)
              ·
                refine ⟨4427829339900177949009451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188920718502407592491069909 4427829339900177949009451)
                ·
                  refine ⟨6641744009850266923514177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427829339900177949009451 6641744009850266923514177)
                  ·
                    refine ⟨4981308007387700192635633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641744009850266923514177 4981308007387700192635633)
                    ·
                      refine ⟨3735981005540775144476725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981308007387700192635633 3735981005540775144476725)
                      ·
                        rfl

theorem cell23_7275797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_7275797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275797 prefixEnd_7275797 := by exact prefixLift 7275797
  have htrace : WordTrace (prefixWord ++ tailWord_7275797) baseStart_7275797 baseEnd_7275797 := by
    simpa [prefixWord, tailWord_7275797, baseEnd_7275797] using wordTrace_append hprefix tailTrace_7275797
  have hstable : (prefixWord ++ tailWord_7275797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275797).length < 2 ^ (prefixWord ++ tailWord_7275797).sum := by decide
  have hdescent : baseEnd_7275797 < baseStart_7275797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275840 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2]
def baseStart_7275840 : Nat := 118140960795 + 7275840 * 2 ^ 59
def prefixEnd_7275840 : Nat := 4983230072969 + 3 ^ 40 * 7275840 * 2
def baseEnd_7275840 : Nat := 3736003085208918476239027

theorem tailTrace_7275840 : CollatzResearch.WordTrace tailWord_7275840 prefixEnd_7275840 3736003085208918476239027 := by
  unfold tailWord_7275840
  simp only [CollatzResearch.WordTrace]
  refine ⟨132685842980440884693756487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176914457307254512925008649 132685842980440884693756487)
  ·
    refine ⟨199028764470661327040634731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132685842980440884693756487 199028764470661327040634731)
    ·
      refine ⟨298543146705991990560952097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199028764470661327040634731 298543146705991990560952097)
      ·
        refine ⟨223907360029493992920714073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298543146705991990560952097 223907360029493992920714073)
        ·
          refine ⟨167930520022120494690535555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223907360029493992920714073 167930520022120494690535555)
          ·
            refine ⟨251895780033180742035803333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167930520022120494690535555 251895780033180742035803333)
            ·
              refine ⟨47230458756221389131713125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251895780033180742035803333 47230458756221389131713125)
              ·
                refine ⟨8855711016791510462196211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47230458756221389131713125 8855711016791510462196211)
                ·
                  refine ⟨13283566525187265693294317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8855711016791510462196211 13283566525187265693294317)
                  ·
                    refine ⟨4981337446945224634985369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13283566525187265693294317 4981337446945224634985369)
                    ·
                      refine ⟨3736003085208918476239027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981337446945224634985369 3736003085208918476239027)
                      ·
                        rfl

theorem cell23_7275840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_7275840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275840 prefixEnd_7275840 := by exact prefixLift 7275840
  have htrace : WordTrace (prefixWord ++ tailWord_7275840) baseStart_7275840 baseEnd_7275840 := by
    simpa [prefixWord, tailWord_7275840, baseEnd_7275840] using wordTrace_append hprefix tailTrace_7275840
  have hstable : (prefixWord ++ tailWord_7275840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275840).length < 2 ^ (prefixWord ++ tailWord_7275840).sum := by decide
  have hdescent : baseEnd_7275840 < baseStart_7275840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275856 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_7275856 : Nat := 118140960795 + 7275856 * 2 ^ 59
def prefixEnd_7275856 : Nat := 4983230072969 + 3 ^ 40 * 7275856 * 2
def baseEnd_7275856 : Nat := 3736011300899390413638953

theorem tailTrace_7275856 : CollatzResearch.WordTrace tailWord_7275856 prefixEnd_7275856 3736011300899390413638953 := by
  unfold tailWord_7275856
  simp only [CollatzResearch.WordTrace]
  refine ⟨132686134764411902060047711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176914846352549202746730281 132686134764411902060047711)
  ·
    refine ⟨199029202146617853090071567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132686134764411902060047711 199029202146617853090071567)
    ·
      refine ⟨298543803219926779635107351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199029202146617853090071567 298543803219926779635107351)
      ·
        refine ⟨447815704829890169452661027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298543803219926779635107351 447815704829890169452661027)
        ·
          refine ⟨671723557244835254178991541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447815704829890169452661027 671723557244835254178991541)
          ·
            refine ⟨62974083491703305079280457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 671723557244835254178991541 62974083491703305079280457)
            ·
              refine ⟨47230562618777478809460343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62974083491703305079280457 47230562618777478809460343)
              ·
                refine ⟨70845843928166218214190515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47230562618777478809460343 70845843928166218214190515)
                ·
                  refine ⟨106268765892249327321285773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70845843928166218214190515 106268765892249327321285773)
                  ·
                    refine ⟨39850787209593497745482165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106268765892249327321285773 39850787209593497745482165)
                    ·
                      refine ⟨3736011300899390413638953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39850787209593497745482165 3736011300899390413638953)
                      ·
                        rfl

theorem cell23_7275856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_7275856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275856 prefixEnd_7275856 := by exact prefixLift 7275856
  have htrace : WordTrace (prefixWord ++ tailWord_7275856) baseStart_7275856 baseEnd_7275856 := by
    simpa [prefixWord, tailWord_7275856, baseEnd_7275856] using wordTrace_append hprefix tailTrace_7275856
  have hstable : (prefixWord ++ tailWord_7275856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275856).length < 2 ^ (prefixWord ++ tailWord_7275856).sum := by decide
  have hdescent : baseEnd_7275856 < baseStart_7275856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275930 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_7275930 : Nat := 118140960795 + 7275930 * 2 ^ 59
def prefixEnd_7275930 : Nat := 4983230072969 + 3 ^ 40 * 7275930 * 2
def baseEnd_7275930 : Nat := 3736049298467823124113613

theorem tailTrace_7275930 : CollatzResearch.WordTrace tailWord_7275930 prefixEnd_7275930 3736049298467823124113613 := by
  unfold tailWord_7275930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66343742132638928689572311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176916645687037143172192829 66343742132638928689572311)
  ·
    refine ⟨99515613198958393034358467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66343742132638928689572311 99515613198958393034358467)
    ·
      refine ⟨149273419798437589551537701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99515613198958393034358467 149273419798437589551537701)
      ·
        refine ⟨27988766212207048040913319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149273419798437589551537701 27988766212207048040913319)
        ·
          refine ⟨41983149318310572061369979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27988766212207048040913319 41983149318310572061369979)
          ·
            refine ⟨62974723977465858092054969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41983149318310572061369979 62974723977465858092054969)
            ·
              refine ⟨47231042983099393569041227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62974723977465858092054969 47231042983099393569041227)
              ·
                refine ⟨70846564474649090353561841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47231042983099393569041227 70846564474649090353561841)
                ·
                  refine ⟨53134923355986817765171381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70846564474649090353561841 53134923355986817765171381)
                  ·
                    refine ⟨4981399064623764165484817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53134923355986817765171381 4981399064623764165484817)
                    ·
                      refine ⟨3736049298467823124113613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981399064623764165484817 3736049298467823124113613)
                      ·
                        rfl

theorem cell23_7275930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_7275930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275930 prefixEnd_7275930 := by exact prefixLift 7275930
  have htrace : WordTrace (prefixWord ++ tailWord_7275930) baseStart_7275930 baseEnd_7275930 := by
    simpa [prefixWord, tailWord_7275930, baseEnd_7275930] using wordTrace_append hprefix tailTrace_7275930
  have hstable : (prefixWord ++ tailWord_7275930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275930).length < 2 ^ (prefixWord ++ tailWord_7275930).sum := by decide
  have hdescent : baseEnd_7275930 < baseStart_7275930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275933 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_7275933 : Nat := 118140960795 + 7275933 * 2 ^ 59
def prefixEnd_7275933 : Nat := 4983230072969 + 3 ^ 40 * 7275933 * 2
def baseEnd_7275933 : Nat := 3736050838909786612376099

theorem tailTrace_7275933 : CollatzResearch.WordTrace tailWord_7275933 prefixEnd_7275933 3736050838909786612376099 := by
  unfold tailWord_7275933
  simp only [CollatzResearch.WordTrace]
  refine ⟨265375077949544846270648453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176916718633029897513765635 265375077949544846270648453)
  ·
    refine ⟨49757827115539658675746585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 265375077949544846270648453 49757827115539658675746585)
    ·
      refine ⟨37318370336654744006809939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49757827115539658675746585 37318370336654744006809939)
      ·
        refine ⟨55977555504982116010214909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37318370336654744006809939 55977555504982116010214909)
        ·
          refine ⟨20991583314368293503830591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55977555504982116010214909 20991583314368293503830591)
          ·
            refine ⟨31487374971552440255745887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20991583314368293503830591 31487374971552440255745887)
            ·
              refine ⟨47231062457328660383618831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31487374971552440255745887 47231062457328660383618831)
              ·
                refine ⟨70846593685992990575428247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47231062457328660383618831 70846593685992990575428247)
                ·
                  refine ⟨106269890528989485863142371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70846593685992990575428247 106269890528989485863142371)
                  ·
                    refine ⟨159404835793484228794713557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106269890528989485863142371 159404835793484228794713557)
                    ·
                      refine ⟨3736050838909786612376099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159404835793484228794713557 3736050838909786612376099)
                      ·
                        rfl

theorem cell23_7275933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_7275933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275933 prefixEnd_7275933 := by exact prefixLift 7275933
  have htrace : WordTrace (prefixWord ++ tailWord_7275933) baseStart_7275933 baseEnd_7275933 := by
    simpa [prefixWord, tailWord_7275933, baseEnd_7275933] using wordTrace_append hprefix tailTrace_7275933
  have hstable : (prefixWord ++ tailWord_7275933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275933).length < 2 ^ (prefixWord ++ tailWord_7275933).sum := by decide
  have hdescent : baseEnd_7275933 < baseStart_7275933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7275983 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 6]
def baseStart_7275983 : Nat := 118140960795 + 7275983 * 2 ^ 59
def prefixEnd_7275983 : Nat := 4983230072969 + 3 ^ 40 * 7275983 * 2
def baseEnd_7275983 : Nat := 415119612549167935194541

theorem tailTrace_7275983 : CollatzResearch.WordTrace tailWord_7275983 prefixEnd_7275983 415119612549167935194541 := by
  unfold tailWord_7275983
  simp only [CollatzResearch.WordTrace]
  refine ⟨265376901599363704809968603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176917934399575803206645735 265376901599363704809968603)
  ·
    refine ⟨398065352399045557214952905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265376901599363704809968603 398065352399045557214952905)
    ·
      refine ⟨298549014299284167911214679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398065352399045557214952905 298549014299284167911214679)
      ·
        refine ⟨447823521448926251866822019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298549014299284167911214679 447823521448926251866822019)
        ·
          refine ⟨671735282173389377800233029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447823521448926251866822019 671735282173389377800233029)
          ·
            refine ⟨125950365407510508337543693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 671735282173389377800233029 125950365407510508337543693)
            ·
              refine ⟨47231387027816440626578885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125950365407510508337543693 47231387027816440626578885)
              ·
                refine ⟨8855885067715582617483541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47231387027816440626578885 8855885067715582617483541)
                ·
                  refine ⟨415119612549167935194541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8855885067715582617483541 415119612549167935194541)
                  ·
                    rfl

theorem cell23_7275983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 6].length) (baseStart_7275983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7275983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7275983 prefixEnd_7275983 := by exact prefixLift 7275983
  have htrace : WordTrace (prefixWord ++ tailWord_7275983) baseStart_7275983 baseEnd_7275983 := by
    simpa [prefixWord, tailWord_7275983, baseEnd_7275983] using wordTrace_append hprefix tailTrace_7275983
  have hstable : (prefixWord ++ tailWord_7275983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7275983).length < 2 ^ (prefixWord ++ tailWord_7275983).sum := by decide
  have hdescent : baseEnd_7275983 < baseStart_7275983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7275983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276021 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7276021 : Nat := 118140960795 + 7276021 * 2 ^ 59
def prefixEnd_7276021 : Nat := 4983230072969 + 3 ^ 40 * 7276021 * 2
def baseEnd_7276021 : Nat := 1245365341735794089358565

theorem tailTrace_7276021 : CollatzResearch.WordTrace tailWord_7276021 prefixEnd_7276021 1245365341735794089358565 := by
  unfold tailWord_7276021
  simp only [CollatzResearch.WordTrace]
  refine ⟨265378287573226037299851917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176918858382150691533234611 265378287573226037299851917)
  ·
    refine ⟨99516857839959763987444469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265378287573226037299851917 99516857839959763987444469)
    ·
      refine ⟨9329705422496227873822919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99516857839959763987444469 9329705422496227873822919)
      ·
        refine ⟨13994558133744341810734379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329705422496227873822919 13994558133744341810734379)
        ·
          refine ⟨20991837200616512716101569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13994558133744341810734379 20991837200616512716101569)
          ·
            refine ⟨15743877900462384537076177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20991837200616512716101569 15743877900462384537076177)
            ·
              refine ⟨11807908425346788402807133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743877900462384537076177 11807908425346788402807133)
              ·
                refine ⟨4427965659505045651052675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11807908425346788402807133 4427965659505045651052675)
                ·
                  refine ⟨6641948489257568476579013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427965659505045651052675 6641948489257568476579013)
                  ·
                    refine ⟨1245365341735794089358565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641948489257568476579013 1245365341735794089358565)
                    ·
                      rfl

theorem cell23_7276021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7276021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276021 prefixEnd_7276021 := by exact prefixLift 7276021
  have htrace : WordTrace (prefixWord ++ tailWord_7276021) baseStart_7276021 baseEnd_7276021 := by
    simpa [prefixWord, tailWord_7276021, baseEnd_7276021] using wordTrace_append hprefix tailTrace_7276021
  have hstable : (prefixWord ++ tailWord_7276021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276021).length < 2 ^ (prefixWord ++ tailWord_7276021).sum := by decide
  have hdescent : baseEnd_7276021 < baseStart_7276021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276034 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7276034 : Nat := 118140960795 + 7276034 * 2 ^ 59
def prefixEnd_7276034 : Nat := 4983230072969 + 3 ^ 40 * 7276034 * 2
def baseEnd_7276034 : Nat := 415122522272876746357015

theorem tailTrace_7276034 : CollatzResearch.WordTrace tailWord_7276034 prefixEnd_7276034 415122522272876746357015 := by
  unfold tailWord_7276034
  simp only [CollatzResearch.WordTrace]
  refine ⟨66344690430544735130018789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176919174481452627013383437 66344690430544735130018789)
  ·
    refine ⟨12439629455727137836878523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66344690430544735130018789 12439629455727137836878523)
    ·
      refine ⟨18659444183590706755317785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12439629455727137836878523 18659444183590706755317785)
      ·
        refine ⟨13994583137693030066488339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18659444183590706755317785 13994583137693030066488339)
        ·
          refine ⟨20991874706539545099732509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13994583137693030066488339 20991874706539545099732509)
          ·
            refine ⟨7871953014952329412399691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20991874706539545099732509 7871953014952329412399691)
            ·
              refine ⟨11807929522428494118599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871953014952329412399691 11807929522428494118599537)
              ·
                refine ⟨8855947141821370588949653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807929522428494118599537 8855947141821370588949653)
                ·
                  refine ⟨415122522272876746357015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8855947141821370588949653 415122522272876746357015)
                  ·
                    rfl

theorem cell23_7276034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7276034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276034 prefixEnd_7276034 := by exact prefixLift 7276034
  have htrace : WordTrace (prefixWord ++ tailWord_7276034) baseStart_7276034 baseEnd_7276034 := by
    simpa [prefixWord, tailWord_7276034, baseEnd_7276034] using wordTrace_append hprefix tailTrace_7276034
  have hstable : (prefixWord ++ tailWord_7276034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276034).length < 2 ^ (prefixWord ++ tailWord_7276034).sum := by decide
  have hdescent : baseEnd_7276034 < baseStart_7276034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276038 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7276038 : Nat := 118140960795 + 7276038 * 2 ^ 59
def prefixEnd_7276038 : Nat := 4983230072969 + 3 ^ 40 * 7276038 * 2
def baseEnd_7276038 : Nat := 1245368251459502900521039

theorem tailTrace_7276038 : CollatzResearch.WordTrace tailWord_7276038 prefixEnd_7276038 1245368251459502900521039 := by
  unfold tailWord_7276038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293090862942639037600649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176919271742776299468813845 8293090862942639037600649)
  ·
    refine ⟨6219818147206979278200487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8293090862942639037600649 6219818147206979278200487)
    ·
      refine ⟨9329727220810468917300731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6219818147206979278200487 9329727220810468917300731)
      ·
        refine ⟨13994590831215703375951097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329727220810468917300731 13994590831215703375951097)
        ·
          refine ⟨10495943123411777531963323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13994590831215703375951097 10495943123411777531963323)
          ·
            refine ⟨15743914685117666297944985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495943123411777531963323 15743914685117666297944985)
            ·
              refine ⟨11807936013838249723458739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743914685117666297944985 11807936013838249723458739)
              ·
                refine ⟨17711904020757374585188109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807936013838249723458739 17711904020757374585188109)
                ·
                  refine ⟨6641964007784015469445541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17711904020757374585188109 6641964007784015469445541)
                  ·
                    refine ⟨1245368251459502900521039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6641964007784015469445541 1245368251459502900521039)
                    ·
                      rfl

theorem cell23_7276038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7276038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276038 prefixEnd_7276038 := by exact prefixLift 7276038
  have htrace : WordTrace (prefixWord ++ tailWord_7276038) baseStart_7276038 baseEnd_7276038 := by
    simpa [prefixWord, tailWord_7276038, baseEnd_7276038] using wordTrace_append hprefix tailTrace_7276038
  have hstable : (prefixWord ++ tailWord_7276038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276038).length < 2 ^ (prefixWord ++ tailWord_7276038).sum := by decide
  have hdescent : baseEnd_7276038 < baseStart_7276038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276044 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_7276044 : Nat := 118140960795 + 7276044 * 2 ^ 59
def prefixEnd_7276044 : Nat := 4983230072969 + 3 ^ 40 * 7276044 * 2
def baseEnd_7276044 : Nat := 3736107835262435678088089

theorem tailTrace_7276044 : CollatzResearch.WordTrace tailWord_7276044 prefixEnd_7276044 3736107835262435678088089 := by
  unfold tailWord_7276044
  simp only [CollatzResearch.WordTrace]
  refine ⟨132689563226071356113969593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176919417634761808151959457 132689563226071356113969593)
  ·
    refine ⟨99517172419553517085477195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132689563226071356113969593 99517172419553517085477195)
    ·
      refine ⟨149275758629330275628215793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99517172419553517085477195 149275758629330275628215793)
      ·
        refine ⟨111956818971997706721161845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149275758629330275628215793 111956818971997706721161845)
        ·
          refine ⟨10495951778624785005108923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111956818971997706721161845 10495951778624785005108923)
          ·
            refine ⟨15743927667937177507663385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495951778624785005108923 15743927667937177507663385)
            ·
              refine ⟨11807945750952883130747539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743927667937177507663385 11807945750952883130747539)
              ·
                refine ⟨17711918626429324696121309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807945750952883130747539 17711918626429324696121309)
                ·
                  refine ⟨6641969484910996761045491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17711918626429324696121309 6641969484910996761045491)
                  ·
                    refine ⟨9962954227366495141568237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6641969484910996761045491 9962954227366495141568237)
                    ·
                      refine ⟨3736107835262435678088089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9962954227366495141568237 3736107835262435678088089)
                      ·
                        rfl

theorem cell23_7276044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_7276044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276044 prefixEnd_7276044 := by exact prefixLift 7276044
  have htrace : WordTrace (prefixWord ++ tailWord_7276044) baseStart_7276044 baseEnd_7276044 := by
    simpa [prefixWord, tailWord_7276044, baseEnd_7276044] using wordTrace_append hprefix tailTrace_7276044
  have hstable : (prefixWord ++ tailWord_7276044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276044).length < 2 ^ (prefixWord ++ tailWord_7276044).sum := by decide
  have hdescent : baseEnd_7276044 < baseStart_7276044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276078 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_7276078 : Nat := 118140960795 + 7276078 * 2 ^ 59
def prefixEnd_7276078 : Nat := 4983230072969 + 3 ^ 40 * 7276078 * 2
def baseEnd_7276078 : Nat := 3736125293604688545062933

theorem tailTrace_7276078 : CollatzResearch.WordTrace tailWord_7276078 prefixEnd_7276078 3736125293604688545062933 := by
  unfold tailWord_7276078
  simp only [CollatzResearch.WordTrace]
  refine ⟨33172545816752442004334611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176920244356013024023117925 33172545816752442004334611)
  ·
    refine ⟨49758818725128663006501917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33172545816752442004334611 49758818725128663006501917)
    ·
      refine ⟨18659557021923248627438219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49758818725128663006501917 18659557021923248627438219)
      ·
        refine ⟨27989335532884872941157329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18659557021923248627438219 27989335532884872941157329)
        ·
          refine ⟨20992001649663654705867997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27989335532884872941157329 20992001649663654705867997)
          ·
            refine ⟨7872000618623870514700499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20992001649663654705867997 7872000618623870514700499)
            ·
              refine ⟨11808000927935805772050749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872000618623870514700499 11808000927935805772050749)
              ·
                refine ⟨4428000347975927164519031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11808000927935805772050749 4428000347975927164519031)
                ·
                  refine ⟨6642000521963890746778547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428000347975927164519031 6642000521963890746778547)
                  ·
                    refine ⟨9963000782945836120167821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642000521963890746778547 9963000782945836120167821)
                    ·
                      refine ⟨3736125293604688545062933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963000782945836120167821 3736125293604688545062933)
                      ·
                        rfl

theorem cell23_7276078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_7276078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276078 prefixEnd_7276078 := by exact prefixLift 7276078
  have htrace : WordTrace (prefixWord ++ tailWord_7276078) baseStart_7276078 baseEnd_7276078 := by
    simpa [prefixWord, tailWord_7276078, baseEnd_7276078] using wordTrace_append hprefix tailTrace_7276078
  have hstable : (prefixWord ++ tailWord_7276078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276078).length < 2 ^ (prefixWord ++ tailWord_7276078).sum := by decide
  have hdescent : baseEnd_7276078 < baseStart_7276078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276087 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_7276087 : Nat := 118140960795 + 7276087 * 2 ^ 59
def prefixEnd_7276087 : Nat := 4983230072969 + 3 ^ 40 * 7276087 * 2
def baseEnd_7276087 : Nat := 3736129914930579009850391

theorem tailTrace_7276087 : CollatzResearch.WordTrace tailWord_7276087 prefixEnd_7276087 3736129914930579009850391 := by
  unfold tailWord_7276087
  simp only [CollatzResearch.WordTrace]
  refine ⟨265380694790986930571754515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176920463193991287047836343 265380694790986930571754515)
  ·
    refine ⟨398071042186480395857631773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265380694790986930571754515 398071042186480395857631773)
    ·
      refine ⟨149276640819930148446611915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398071042186480395857631773 149276640819930148446611915)
      ·
        refine ⟨223914961229895222669917873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149276640819930148446611915 223914961229895222669917873)
        ·
          refine ⟨167936220922421417002438405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223914961229895222669917873 167936220922421417002438405)
          ·
            refine ⟨31488041422954015687957201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167936220922421417002438405 31488041422954015687957201)
            ·
              refine ⟨23616031067215511765967901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31488041422954015687957201 23616031067215511765967901)
              ·
                refine ⟨8856011650205816912237963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23616031067215511765967901 8856011650205816912237963)
                ·
                  refine ⟨13284017475308725368356945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856011650205816912237963 13284017475308725368356945)
                  ·
                    refine ⟨9963013106481544026267709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13284017475308725368356945 9963013106481544026267709)
                    ·
                      refine ⟨3736129914930579009850391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963013106481544026267709 3736129914930579009850391)
                      ·
                        rfl

theorem cell23_7276087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_7276087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276087 prefixEnd_7276087 := by exact prefixLift 7276087
  have htrace : WordTrace (prefixWord ++ tailWord_7276087) baseStart_7276087 baseEnd_7276087 := by
    simpa [prefixWord, tailWord_7276087, baseEnd_7276087] using wordTrace_append hprefix tailTrace_7276087
  have hstable : (prefixWord ++ tailWord_7276087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276087).length < 2 ^ (prefixWord ++ tailWord_7276087).sum := by decide
  have hdescent : baseEnd_7276087 < baseStart_7276087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276160 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_7276160 : Nat := 118140960795 + 7276160 * 2 ^ 59
def prefixEnd_7276160 : Nat := 4983230072969 + 3 ^ 40 * 7276160 * 2
def baseEnd_7276160 : Nat := 3736167399018357224237555

theorem tailTrace_7276160 : CollatzResearch.WordTrace tailWord_7276160 prefixEnd_7276160 3736167399018357224237555 := by
  unfold tailWord_7276160
  simp only [CollatzResearch.WordTrace]
  refine ⟨132691678659861232019580967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176922238213148309359441289 132691678659861232019580967)
  ·
    refine ⟨199037517989791848029371451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132691678659861232019580967 199037517989791848029371451)
    ·
      refine ⟨298556276984687772044057177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199037517989791848029371451 298556276984687772044057177)
      ·
        refine ⟨223917207738515829033042883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298556276984687772044057177 223917207738515829033042883)
        ·
          refine ⟨335875811607773743549564325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223917207738515829033042883 335875811607773743549564325)
          ·
            refine ⟨62976714676457576915543311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335875811607773743549564325 62976714676457576915543311)
            ·
              refine ⟨94465072014686365373314967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62976714676457576915543311 94465072014686365373314967)
              ·
                refine ⟨141697608022029548059972451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94465072014686365373314967 141697608022029548059972451)
                ·
                  refine ⟨212546412033044322089958677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141697608022029548059972451 212546412033044322089958677)
                  ·
                    refine ⟨9963113064048952597966813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212546412033044322089958677 9963113064048952597966813)
                    ·
                      refine ⟨3736167399018357224237555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963113064048952597966813 3736167399018357224237555)
                      ·
                        rfl

theorem cell23_7276160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_7276160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276160 prefixEnd_7276160 := by exact prefixLift 7276160
  have htrace : WordTrace (prefixWord ++ tailWord_7276160) baseStart_7276160 baseEnd_7276160 := by
    simpa [prefixWord, tailWord_7276160, baseEnd_7276160] using wordTrace_append hprefix tailTrace_7276160
  have hstable : (prefixWord ++ tailWord_7276160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276160).length < 2 ^ (prefixWord ++ tailWord_7276160).sum := by decide
  have hdescent : baseEnd_7276160 < baseStart_7276160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276174 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7276174 : Nat := 118140960795 + 7276174 * 2 ^ 59
def prefixEnd_7276174 : Nat := 4983230072969 + 3 ^ 40 * 7276174 * 2
def baseEnd_7276174 : Nat := 3736174587747520169462491

theorem tailTrace_7276174 : CollatzResearch.WordTrace tailWord_7276174 prefixEnd_7276174 3736174587747520169462491 := by
  unfold tailWord_7276174
  simp only [CollatzResearch.WordTrace]
  refine ⟨33172983492708968053771447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176922578627781162953447717 33172983492708968053771447)
  ·
    refine ⟨49759475239063452080657171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33172983492708968053771447 49759475239063452080657171)
    ·
      refine ⟨74639212858595178120985757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49759475239063452080657171 74639212858595178120985757)
      ·
        refine ⟨27989704821973191795369659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74639212858595178120985757 27989704821973191795369659)
        ·
          refine ⟨41984557232959787693054489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27989704821973191795369659 41984557232959787693054489)
          ·
            refine ⟨31488417924719840769790867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41984557232959787693054489 31488417924719840769790867)
            ·
              refine ⟨47232626887079761154686301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31488417924719840769790867 47232626887079761154686301)
              ·
                refine ⟨17712235082654910433007363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47232626887079761154686301 17712235082654910433007363)
                ·
                  refine ⟨26568352623982365649511045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17712235082654910433007363 26568352623982365649511045)
                  ·
                    refine ⟨4981566116996693559283321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26568352623982365649511045 4981566116996693559283321)
                    ·
                      refine ⟨3736174587747520169462491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981566116996693559283321 3736174587747520169462491)
                      ·
                        rfl

theorem cell23_7276174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7276174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276174 prefixEnd_7276174 := by exact prefixLift 7276174
  have htrace : WordTrace (prefixWord ++ tailWord_7276174) baseStart_7276174 baseEnd_7276174 := by
    simpa [prefixWord, tailWord_7276174, baseEnd_7276174] using wordTrace_append hprefix tailTrace_7276174
  have hstable : (prefixWord ++ tailWord_7276174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276174).length < 2 ^ (prefixWord ++ tailWord_7276174).sum := by decide
  have hdescent : baseEnd_7276174 < baseStart_7276174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276197 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 5]
def baseStart_7276197 : Nat := 118140960795 + 7276197 * 2 ^ 59
def prefixEnd_7276197 : Nat := 4983230072969 + 3 ^ 40 * 7276197 * 2
def baseEnd_7276197 : Nat := 415131821978063731052765

theorem tailTrace_7276197 : CollatzResearch.WordTrace tailWord_7276197 prefixEnd_7276197 415131821978063731052765 := by
  unfold tailWord_7276197
  simp only [CollatzResearch.WordTrace]
  refine ⟨265384706820588419358258845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176923137880392279572172563 265384706820588419358258845)
  ·
    refine ⟨99519265057720657259347067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 265384706820588419358258845 99519265057720657259347067)
    ·
      refine ⟨149278897586580985889020601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99519265057720657259347067 149278897586580985889020601)
      ·
        refine ⟨111959173189935739416765451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149278897586580985889020601 111959173189935739416765451)
        ·
          refine ⟨167938759784903609125148177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111959173189935739416765451 167938759784903609125148177)
          ·
            refine ⟨125954069838677706843861133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167938759784903609125148177 125954069838677706843861133)
            ·
              refine ⟨47232776189504140066447925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125954069838677706843861133 47232776189504140066447925)
              ·
                refine ⟨4428072767766013131229493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47232776189504140066447925 4428072767766013131229493)
                ·
                  refine ⟨415131821978063731052765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428072767766013131229493 415131821978063731052765)
                  ·
                    rfl

theorem cell23_7276197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_7276197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276197 prefixEnd_7276197 := by exact prefixLift 7276197
  have htrace : WordTrace (prefixWord ++ tailWord_7276197) baseStart_7276197 baseEnd_7276197 := by
    simpa [prefixWord, tailWord_7276197, baseEnd_7276197] using wordTrace_append hprefix tailTrace_7276197
  have hstable : (prefixWord ++ tailWord_7276197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276197).length < 2 ^ (prefixWord ++ tailWord_7276197).sum := by decide
  have hdescent : baseEnd_7276197 < baseStart_7276197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276214 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_7276214 : Nat := 118140960795 + 7276214 * 2 ^ 59
def prefixEnd_7276214 : Nat := 4983230072969 + 3 ^ 40 * 7276214 * 2
def baseEnd_7276214 : Nat := 415132791885966668106923

theorem tailTrace_7276214 : CollatzResearch.WordTrace tailWord_7276214 prefixEnd_7276214 415132791885966668106923 := by
  unfold tailWord_7276214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16586582928845426953851731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176923551241017887507751797 16586582928845426953851731)
  ·
    refine ⟨24879874393268140430777597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16586582928845426953851731 24879874393268140430777597)
    ·
      refine ⟨9329952897475552661541599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24879874393268140430777597 9329952897475552661541599)
      ·
        refine ⟨13994929346213328992312399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329952897475552661541599 13994929346213328992312399)
        ·
          refine ⟨20992394019319993488468599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13994929346213328992312399 20992394019319993488468599)
          ·
            refine ⟨31488591028979990232702899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992394019319993488468599 31488591028979990232702899)
            ·
              refine ⟨47232886543469985349054349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31488591028979990232702899 47232886543469985349054349)
              ·
                refine ⟨17712332453801244505895381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47232886543469985349054349 17712332453801244505895381)
                ·
                  refine ⟨415132791885966668106923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17712332453801244505895381 415132791885966668106923)
                  ·
                    rfl

theorem cell23_7276214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_7276214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276214 prefixEnd_7276214 := by exact prefixLift 7276214
  have htrace : WordTrace (prefixWord ++ tailWord_7276214) baseStart_7276214 baseEnd_7276214 := by
    simpa [prefixWord, tailWord_7276214, baseEnd_7276214] using wordTrace_append hprefix tailTrace_7276214
  have hstable : (prefixWord ++ tailWord_7276214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276214).length < 2 ^ (prefixWord ++ tailWord_7276214).sum := by decide
  have hdescent : baseEnd_7276214 < baseStart_7276214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276217 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7276217 : Nat := 118140960795 + 7276217 * 2 ^ 59
def prefixEnd_7276217 : Nat := 4983230072969 + 3 ^ 40 * 7276217 * 2
def baseEnd_7276217 : Nat := 3736196667415663501224793

theorem tailTrace_7276217 : CollatzResearch.WordTrace tailWord_7276217 prefixEnd_7276217 3736196667415663501224793 := by
  unfold tailWord_7276217
  simp only [CollatzResearch.WordTrace]
  refine ⟨265385436280515962773986905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176923624187010641849324603 265385436280515962773986905)
  ·
    refine ⟨199039077210386972080490179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265385436280515962773986905 199039077210386972080490179)
    ·
      refine ⟨298558615815580458120735269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199039077210386972080490179 298558615815580458120735269)
      ·
        refine ⟨55979740465421335897637863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298558615815580458120735269 55979740465421335897637863)
        ·
          refine ⟨83969610698132003846456795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55979740465421335897637863 83969610698132003846456795)
          ·
            refine ⟨125954416047198005769685193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83969610698132003846456795 125954416047198005769685193)
            ·
              refine ⟨94465812035398504327263895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125954416047198005769685193 94465812035398504327263895)
              ·
                refine ⟨141698718053097756490895843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94465812035398504327263895 141698718053097756490895843)
                ·
                  refine ⟨212548077079646634736343765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141698718053097756490895843 212548077079646634736343765)
                  ·
                    refine ⟨4981595556554218001633057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 212548077079646634736343765 4981595556554218001633057)
                    ·
                      refine ⟨3736196667415663501224793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981595556554218001633057 3736196667415663501224793)
                      ·
                        rfl

theorem cell23_7276217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7276217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276217 prefixEnd_7276217 := by exact prefixLift 7276217
  have htrace : WordTrace (prefixWord ++ tailWord_7276217) baseStart_7276217 baseEnd_7276217 := by
    simpa [prefixWord, tailWord_7276217, baseEnd_7276217] using wordTrace_append hprefix tailTrace_7276217
  have hstable : (prefixWord ++ tailWord_7276217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276217).length < 2 ^ (prefixWord ++ tailWord_7276217).sum := by decide
  have hdescent : baseEnd_7276217 < baseStart_7276217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276247 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_7276247 : Nat := 118140960795 + 7276247 * 2 ^ 59
def prefixEnd_7276247 : Nat := 4983230072969 + 3 ^ 40 * 7276247 * 2
def baseEnd_7276247 : Nat := 3736212071835298383849655

theorem tailTrace_7276247 : CollatzResearch.WordTrace tailWord_7276247 prefixEnd_7276247 3736212071835298383849655 := by
  unfold tailWord_7276247
  simp only [CollatzResearch.WordTrace]
  refine ⟨265386530470407277897578995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176924353646938185265052663 265386530470407277897578995)
  ·
    refine ⟨398079795705610916846368493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265386530470407277897578995 398079795705610916846368493)
    ·
      refine ⟨149279923389604093817388185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398079795705610916846368493 149279923389604093817388185)
      ·
        refine ⟨111959942542203070363041139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149279923389604093817388185 111959942542203070363041139)
        ·
          refine ⟨167939913813304605544561709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111959942542203070363041139 167939913813304605544561709)
          ·
            refine ⟨62977467679989227079210641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167939913813304605544561709 62977467679989227079210641)
            ·
              refine ⟨47233100759991920309407981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62977467679989227079210641 47233100759991920309407981)
              ·
                refine ⟨17712412784996970116027993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47233100759991920309407981 17712412784996970116027993)
                ·
                  refine ⟨13284309588747727587020995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17712412784996970116027993 13284309588747727587020995)
                  ·
                    refine ⟨19926464383121591380531493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13284309588747727587020995 19926464383121591380531493)
                    ·
                      refine ⟨3736212071835298383849655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19926464383121591380531493 3736212071835298383849655)
                      ·
                        rfl

theorem cell23_7276247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_7276247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276247 prefixEnd_7276247 := by exact prefixLift 7276247
  have htrace : WordTrace (prefixWord ++ tailWord_7276247) baseStart_7276247 baseEnd_7276247 := by
    simpa [prefixWord, tailWord_7276247, baseEnd_7276247] using wordTrace_append hprefix tailTrace_7276247
  have hstable : (prefixWord ++ tailWord_7276247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276247).length < 2 ^ (prefixWord ++ tailWord_7276247).sum := by decide
  have hdescent : baseEnd_7276247 < baseStart_7276247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276264 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7276264 : Nat := 118140960795 + 7276264 * 2 ^ 59
def prefixEnd_7276264 : Nat := 4983230072969 + 3 ^ 40 * 7276264 * 2
def baseEnd_7276264 : Nat := 3736220801006424817337077

theorem tailTrace_7276264 : CollatzResearch.WordTrace tailWord_7276264 prefixEnd_7276264 3736220801006424817337077 := by
  unfold tailWord_7276264
  simp only [CollatzResearch.WordTrace]
  refine ⟨132693575255672844900473923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176924767007563793200631897 132693575255672844900473923)
  ·
    refine ⟨199040362883509267350710885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132693575255672844900473923 199040362883509267350710885)
    ·
      refine ⟨37320068040657987628258291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199040362883509267350710885 37320068040657987628258291)
      ·
        refine ⟨55980102060986981442387437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37320068040657987628258291 55980102060986981442387437)
        ·
          refine ⟨20992538272870118040895289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55980102060986981442387437 20992538272870118040895289)
          ·
            refine ⟨15744403704652588530671467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20992538272870118040895289 15744403704652588530671467)
            ·
              refine ⟨23616605556978882796007201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15744403704652588530671467 23616605556978882796007201)
              ·
                refine ⟨17712454167734162097005401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23616605556978882796007201 17712454167734162097005401)
                ·
                  refine ⟨13284340625800621572754051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17712454167734162097005401 13284340625800621572754051)
                  ·
                    refine ⟨19926510938700932359131077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13284340625800621572754051 19926510938700932359131077)
                    ·
                      refine ⟨3736220801006424817337077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19926510938700932359131077 3736220801006424817337077)
                      ·
                        rfl

theorem cell23_7276264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7276264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276264 prefixEnd_7276264 := by exact prefixLift 7276264
  have htrace : WordTrace (prefixWord ++ tailWord_7276264) baseStart_7276264 baseEnd_7276264 := by
    simpa [prefixWord, tailWord_7276264, baseEnd_7276264] using wordTrace_append hprefix tailTrace_7276264
  have hstable : (prefixWord ++ tailWord_7276264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276264).length < 2 ^ (prefixWord ++ tailWord_7276264).sum := by decide
  have hdescent : baseEnd_7276264 < baseStart_7276264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276267 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3]
def baseStart_7276267 : Nat := 118140960795 + 7276267 * 2 ^ 59
def prefixEnd_7276267 : Nat := 4983230072969 + 3 ^ 40 * 7276267 * 2
def baseEnd_7276267 : Nat := 3736222341448388305599563

theorem tailTrace_7276267 : CollatzResearch.WordTrace tailWord_7276267 prefixEnd_7276267 3736222341448388305599563 := by
  unfold tailWord_7276267
  simp only [CollatzResearch.WordTrace]
  refine ⟨265387259930334821313307055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176924839953556547542204703 265387259930334821313307055)
  ·
    refine ⟨398080889895502231969960583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265387259930334821313307055 398080889895502231969960583)
    ·
      refine ⟨597121334843253347954940875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398080889895502231969960583 597121334843253347954940875)
      ·
        refine ⟨895682002264880021932411313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597121334843253347954940875 895682002264880021932411313)
        ·
          refine ⟨671761501698660016449308485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895682002264880021932411313 671761501698660016449308485)
          ·
            refine ⟨125955281568498753084245341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 671761501698660016449308485 125955281568498753084245341)
            ·
              refine ⟨47233230588187032406592003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125955281568498753084245341 47233230588187032406592003)
              ·
                refine ⟨70849845882280548609888005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47233230588187032406592003 70849845882280548609888005)
                ·
                  refine ⟨13284346102927602864354001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70849845882280548609888005 13284346102927602864354001)
                  ·
                    refine ⟨9963259577195702148265501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13284346102927602864354001 9963259577195702148265501)
                    ·
                      refine ⟨3736222341448388305599563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963259577195702148265501 3736222341448388305599563)
                      ·
                        rfl

theorem cell23_7276267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3].length) (baseStart_7276267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276267 prefixEnd_7276267 := by exact prefixLift 7276267
  have htrace : WordTrace (prefixWord ++ tailWord_7276267) baseStart_7276267 baseEnd_7276267 := by
    simpa [prefixWord, tailWord_7276267, baseEnd_7276267] using wordTrace_append hprefix tailTrace_7276267
  have hstable : (prefixWord ++ tailWord_7276267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276267).length < 2 ^ (prefixWord ++ tailWord_7276267).sum := by decide
  have hdescent : baseEnd_7276267 < baseStart_7276267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276365 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_7276365 : Nat := 118140960795 + 7276365 * 2 ^ 59
def prefixEnd_7276365 : Nat := 4983230072969 + 3 ^ 40 * 7276365 * 2
def baseEnd_7276365 : Nat := 3736272662552528922174113

theorem tailTrace_7276365 : CollatzResearch.WordTrace tailWord_7276365 prefixEnd_7276365 3736272662552528922174113 := by
  unfold tailWord_7276365
  simp only [CollatzResearch.WordTrace]
  refine ⟨265390834283979784050374549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176927222855986522700249699 265390834283979784050374549)
  ·
    refine ⟨12440195357061552377361307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 265390834283979784050374549 12440195357061552377361307)
    ·
      refine ⟨18660293035592328566041961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440195357061552377361307 18660293035592328566041961)
      ·
        refine ⟨13995219776694246424531471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18660293035592328566041961 13995219776694246424531471)
        ·
          refine ⟨20992829665041369636797207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13995219776694246424531471 20992829665041369636797207)
          ·
            refine ⟨31489244497562054455195811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992829665041369636797207 31489244497562054455195811)
            ·
              refine ⟨47233866746343081682793717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31489244497562054455195811 47233866746343081682793717)
              ·
                refine ⟨4428175007469663907761911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47233866746343081682793717 4428175007469663907761911)
                ·
                  refine ⟨6642262511204495861642867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428175007469663907761911 6642262511204495861642867)
                  ·
                    refine ⟨9963393766806743792464301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642262511204495861642867 9963393766806743792464301)
                    ·
                      refine ⟨3736272662552528922174113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963393766806743792464301 3736272662552528922174113)
                      ·
                        rfl

theorem cell23_7276365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_7276365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276365 prefixEnd_7276365 := by exact prefixLift 7276365
  have htrace : WordTrace (prefixWord ++ tailWord_7276365) baseStart_7276365 baseEnd_7276365 := by
    simpa [prefixWord, tailWord_7276365, baseEnd_7276365] using wordTrace_append hprefix tailTrace_7276365
  have hstable : (prefixWord ++ tailWord_7276365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276365).length < 2 ^ (prefixWord ++ tailWord_7276365).sum := by decide
  have hdescent : baseEnd_7276365 < baseStart_7276365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276427 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_7276427 : Nat := 118140960795 + 7276427 * 2 ^ 59
def prefixEnd_7276427 : Nat := 4983230072969 + 3 ^ 40 * 7276427 * 2
def baseEnd_7276427 : Nat := 3736304498353107679598827

theorem tailTrace_7276427 : CollatzResearch.WordTrace tailWord_7276427 prefixEnd_7276427 3736304498353107679598827 := by
  unfold tailWord_7276427
  simp only [CollatzResearch.WordTrace]
  refine ⟨265393095609755168639131535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176928730406503445759421023 265393095609755168639131535)
  ·
    refine ⟨398089643414632752958697303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265393095609755168639131535 398089643414632752958697303)
    ·
      refine ⟨597134465121949129438045955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398089643414632752958697303 597134465121949129438045955)
      ·
        refine ⟨895701697682923694157068933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597134465121949129438045955 895701697682923694157068933)
        ·
          refine ⟨167944068315548192654450425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 895701697682923694157068933 167944068315548192654450425)
          ·
            refine ⟨125958051236661144490837819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167944068315548192654450425 125958051236661144490837819)
            ·
              refine ⟨188937076854991716736256729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125958051236661144490837819 188937076854991716736256729)
              ·
                refine ⟨141702807641243787552192547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188937076854991716736256729 141702807641243787552192547)
                ·
                  refine ⟨212554211461865681328288821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141702807641243787552192547 212554211461865681328288821)
                  ·
                    refine ⟨19926957324549907624527077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212554211461865681328288821 19926957324549907624527077)
                    ·
                      refine ⟨3736304498353107679598827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19926957324549907624527077 3736304498353107679598827)
                      ·
                        rfl

theorem cell23_7276427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_7276427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276427 prefixEnd_7276427 := by exact prefixLift 7276427
  have htrace : WordTrace (prefixWord ++ tailWord_7276427) baseStart_7276427 baseEnd_7276427 := by
    simpa [prefixWord, tailWord_7276427, baseEnd_7276427] using wordTrace_append hprefix tailTrace_7276427
  have hstable : (prefixWord ++ tailWord_7276427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276427).length < 2 ^ (prefixWord ++ tailWord_7276427).sum := by decide
  have hdescent : baseEnd_7276427 < baseStart_7276427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276455 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_7276455 : Nat := 118140960795 + 7276455 * 2 ^ 59
def prefixEnd_7276455 : Nat := 4983230072969 + 3 ^ 40 * 7276455 * 2
def baseEnd_7276455 : Nat := 3736318875811433570048699

theorem tailTrace_7276455 : CollatzResearch.WordTrace tailWord_7276455 prefixEnd_7276455 3736318875811433570048699 := by
  unfold tailWord_7276455
  simp only [CollatzResearch.WordTrace]
  refine ⟨265394116853653729421150819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176929411235769152947433879 265394116853653729421150819)
  ·
    refine ⟨398091175280480594131726229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265394116853653729421150819 398091175280480594131726229)
    ·
      refine ⟨18660523841272527849924667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 398091175280480594131726229 18660523841272527849924667)
      ·
        refine ⟨27990785761908791774887001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18660523841272527849924667 27990785761908791774887001)
        ·
          refine ⟨20993089321431593831165251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27990785761908791774887001 20993089321431593831165251)
          ·
            refine ⟨31489633982147390746747877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20993089321431593831165251 31489633982147390746747877)
            ·
              refine ⟨5904306371652635765015227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31489633982147390746747877 5904306371652635765015227)
              ·
                refine ⟨8856459557478953647522841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904306371652635765015227 8856459557478953647522841)
                ·
                  refine ⟨6642344668109215235642131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8856459557478953647522841 6642344668109215235642131)
                  ·
                    refine ⟨9963517002163822853463197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642344668109215235642131 9963517002163822853463197)
                    ·
                      refine ⟨3736318875811433570048699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963517002163822853463197 3736318875811433570048699)
                      ·
                        rfl

theorem cell23_7276455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_7276455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276455 prefixEnd_7276455 := by exact prefixLift 7276455
  have htrace : WordTrace (prefixWord ++ tailWord_7276455) baseStart_7276455 baseEnd_7276455 := by
    simpa [prefixWord, tailWord_7276455, baseEnd_7276455] using wordTrace_append hprefix tailTrace_7276455
  have hstable : (prefixWord ++ tailWord_7276455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276455).length < 2 ^ (prefixWord ++ tailWord_7276455).sum := by decide
  have hdescent : baseEnd_7276455 < baseStart_7276455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276465 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7276465 : Nat := 118140960795 + 7276465 * 2 ^ 59
def prefixEnd_7276465 : Nat := 4983230072969 + 3 ^ 40 * 7276465 * 2
def baseEnd_7276465 : Nat := 3736324010617978530923653

theorem tailTrace_7276465 : CollatzResearch.WordTrace tailWord_7276465 prefixEnd_7276465 3736324010617978530923653 := by
  unfold tailWord_7276465
  simp only [CollatzResearch.WordTrace]
  refine ⟨265394481583617501129014849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176929654389078334086009899 265394481583617501129014849)
  ·
    refine ⟨199045861187713125846761137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265394481583617501129014849 199045861187713125846761137)
    ·
      refine ⟨149284395890784844385070853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199045861187713125846761137 149284395890784844385070853)
      ·
        refine ⟨27990824229522158322200785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149284395890784844385070853 27990824229522158322200785)
        ·
          refine ⟨20993118172141618741650589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27990824229522158322200785 20993118172141618741650589)
          ·
            refine ⟨7872419314553107028118971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20993118172141618741650589 7872419314553107028118971)
            ·
              refine ⟨11808628971829660542178457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872419314553107028118971 11808628971829660542178457)
              ·
                refine ⟨8856471728872245406633843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11808628971829660542178457 8856471728872245406633843)
                ·
                  refine ⟨13284707593308368109950765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856471728872245406633843 13284707593308368109950765)
                  ·
                    refine ⟨4981765347490638041231537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13284707593308368109950765 4981765347490638041231537)
                    ·
                      refine ⟨3736324010617978530923653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981765347490638041231537 3736324010617978530923653)
                      ·
                        rfl

theorem cell23_7276465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7276465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276465 prefixEnd_7276465 := by exact prefixLift 7276465
  have htrace : WordTrace (prefixWord ++ tailWord_7276465) baseStart_7276465 baseEnd_7276465 := by
    simpa [prefixWord, tailWord_7276465, baseEnd_7276465] using wordTrace_append hprefix tailTrace_7276465
  have hstable : (prefixWord ++ tailWord_7276465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276465).length < 2 ^ (prefixWord ++ tailWord_7276465).sum := by decide
  have hdescent : baseEnd_7276465 < baseStart_7276465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276467 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 9]
def baseStart_7276467 : Nat := 118140960795 + 7276467 * 2 ^ 59
def prefixEnd_7276467 : Nat := 4983230072969 + 3 ^ 40 * 7276467 * 2
def baseEnd_7276467 : Nat := 415147226397698613677627

theorem tailTrace_7276467 : CollatzResearch.WordTrace tailWord_7276467 prefixEnd_7276467 415147226397698613677627 := by
  unfold tailWord_7276467
  simp only [CollatzResearch.WordTrace]
  refine ⟨265394554529610255470587655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176929703019740170313725103 265394554529610255470587655)
  ·
    refine ⟨398091831794415383205881483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265394554529610255470587655 398091831794415383205881483)
    ·
      refine ⟨597137747691623074808822225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398091831794415383205881483 597137747691623074808822225)
      ·
        refine ⟨447853310768717306106616669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597137747691623074808822225 447853310768717306106616669)
        ·
          refine ⟨167944991538268989789981251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447853310768717306106616669 167944991538268989789981251)
          ·
            refine ⟨251917487307403484684971877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167944991538268989789981251 251917487307403484684971877)
            ·
              refine ⟨47234528870138153378432227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251917487307403484684971877 47234528870138153378432227)
              ·
                refine ⟨70851793305207230067648341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47234528870138153378432227 70851793305207230067648341)
                ·
                  refine ⟨415147226397698613677627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70851793305207230067648341 415147226397698613677627)
                  ·
                    rfl

theorem cell23_7276467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 9].length) (baseStart_7276467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276467 prefixEnd_7276467 := by exact prefixLift 7276467
  have htrace : WordTrace (prefixWord ++ tailWord_7276467) baseStart_7276467 baseEnd_7276467 := by
    simpa [prefixWord, tailWord_7276467, baseEnd_7276467] using wordTrace_append hprefix tailTrace_7276467
  have hstable : (prefixWord ++ tailWord_7276467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276467).length < 2 ^ (prefixWord ++ tailWord_7276467).sum := by decide
  have hdescent : baseEnd_7276467 < baseStart_7276467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276478 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_7276478 : Nat := 118140960795 + 7276478 * 2 ^ 59
def prefixEnd_7276478 : Nat := 4983230072969 + 3 ^ 40 * 7276478 * 2
def baseEnd_7276478 : Nat := 3736330685866486980061093

theorem tailTrace_7276478 : CollatzResearch.WordTrace tailWord_7276478 prefixEnd_7276478 3736330685866486980061093 := by
  unfold tailWord_7276478
  simp only [CollatzResearch.WordTrace]
  refine ⟨33174369466571300543654761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176929970488380269566158725 33174369466571300543654761)
  ·
    refine ⟨24880777099928475407741071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33174369466571300543654761 24880777099928475407741071)
    ·
      refine ⟨37321165649892713111611607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24880777099928475407741071 37321165649892713111611607)
      ·
        refine ⟨55981748474839069667417411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37321165649892713111611607 55981748474839069667417411)
        ·
          refine ⟨83972622712258604501126117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55981748474839069667417411 83972622712258604501126117)
          ·
            refine ⟨15744866758548488343961147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83972622712258604501126117 15744866758548488343961147)
            ·
              refine ⟨23617300137822732515941721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15744866758548488343961147 23617300137822732515941721)
              ·
                refine ⟨17712975103367049386956291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23617300137822732515941721 17712975103367049386956291)
                ·
                  refine ⟨26569462655050574080434437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17712975103367049386956291 26569462655050574080434437)
                  ·
                    refine ⟨4981774247821982640081457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26569462655050574080434437 4981774247821982640081457)
                    ·
                      refine ⟨3736330685866486980061093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4981774247821982640081457 3736330685866486980061093)
                      ·
                        rfl

theorem cell23_7276478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_7276478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276478 prefixEnd_7276478 := by exact prefixLift 7276478
  have htrace : WordTrace (prefixWord ++ tailWord_7276478) baseStart_7276478 baseEnd_7276478 := by
    simpa [prefixWord, tailWord_7276478, baseEnd_7276478] using wordTrace_append hprefix tailTrace_7276478
  have hstable : (prefixWord ++ tailWord_7276478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276478).length < 2 ^ (prefixWord ++ tailWord_7276478).sum := by decide
  have hdescent : baseEnd_7276478 < baseStart_7276478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7276511 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_7276511 : Nat := 118140960795 + 7276511 * 2 ^ 59
def prefixEnd_7276511 : Nat := 4983230072969 + 3 ^ 40 * 7276511 * 2
def baseEnd_7276511 : Nat := 3736347630728085350948441

theorem tailTrace_7276511 : CollatzResearch.WordTrace tailWord_7276511 prefixEnd_7276511 3736347630728085350948441 := by
  unfold tailWord_7276511
  simp only [CollatzResearch.WordTrace]
  refine ⟨265396159341450850985189387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176930772894300567323459591 265396159341450850985189387)
  ·
    refine ⟨398094239012176276477784081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265396159341450850985189387 398094239012176276477784081)
    ·
      refine ⟨298570679259132207358338061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398094239012176276477784081 298570679259132207358338061)
      ·
        refine ⟨111964004722174577759376773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298570679259132207358338061 111964004722174577759376773)
        ·
          refine ⟨20993250885407733329883145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111964004722174577759376773 20993250885407733329883145)
          ·
            refine ⟨15744938164055799997412359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20993250885407733329883145 15744938164055799997412359)
            ·
              refine ⟨23617407246083699996118539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15744938164055799997412359 23617407246083699996118539)
              ·
                refine ⟨35426110869125549994177809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23617407246083699996118539 35426110869125549994177809)
                ·
                  refine ⟨26569583151844162495633357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35426110869125549994177809 26569583151844162495633357)
                  ·
                    refine ⟨9963593681941560935862509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26569583151844162495633357 9963593681941560935862509)
                    ·
                      refine ⟨3736347630728085350948441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9963593681941560935862509 3736347630728085350948441)
                      ·
                        rfl

theorem cell23_7276511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_7276511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7276511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7276511 prefixEnd_7276511 := by exact prefixLift 7276511
  have htrace : WordTrace (prefixWord ++ tailWord_7276511) baseStart_7276511 baseEnd_7276511 := by
    simpa [prefixWord, tailWord_7276511, baseEnd_7276511] using wordTrace_append hprefix tailTrace_7276511
  have hstable : (prefixWord ++ tailWord_7276511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7276511).length < 2 ^ (prefixWord ++ tailWord_7276511).sum := by decide
  have hdescent : baseEnd_7276511 < baseStart_7276511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7276511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
