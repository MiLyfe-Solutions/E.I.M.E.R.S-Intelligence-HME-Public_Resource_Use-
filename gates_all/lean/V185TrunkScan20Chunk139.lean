import V185TrunkScan20Chunk138

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_845029 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 4]
def baseStart_845029 : Nat := 118140960795 + 845029 * 2 ^ 59
def prefixEnd_845029 : Nat := 4983230072969 + 3 ^ 40 * 845029 * 2
def baseEnd_845029 : Nat := 385694261322915158978923

theorem tailTrace_845029 : CollatzResearch.WordTrace tailWord_845029 prefixEnd_845029 385694261322915158978923 := by
  unfold tailWord_845029
  simp only [CollatzResearch.WordTrace]
  refine ⟨30820739655611727308450141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20547159770407818205633427 30820739655611727308450141)
  ·
    refine ⟨11557777370854397740668803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30820739655611727308450141 11557777370854397740668803)
    ·
      refine ⟨17336666056281596611003205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11557777370854397740668803 17336666056281596611003205)
      ·
        refine ⟨3250624885552799364563101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17336666056281596611003205 3250624885552799364563101)
        ·
          refine ⟨1218984332082299761711163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3250624885552799364563101 1218984332082299761711163)
          ·
            refine ⟨1828476498123449642566745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218984332082299761711163 1828476498123449642566745)
            ·
              refine ⟨1371357373592587231925059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828476498123449642566745 1371357373592587231925059)
              ·
                refine ⟨2057036060388880847887589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371357373592587231925059 2057036060388880847887589)
                ·
                  refine ⟨385694261322915158978923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057036060388880847887589 385694261322915158978923)
                  ·
                    rfl

theorem cell20_845029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_845029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845029 prefixEnd_845029 := by exact prefixLift 845029
  have htrace : WordTrace (prefixWord ++ tailWord_845029) baseStart_845029 baseEnd_845029 := by
    simpa [prefixWord, tailWord_845029, baseEnd_845029] using wordTrace_append hprefix tailTrace_845029
  have hstable : (prefixWord ++ tailWord_845029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845029).length < 2 ^ (prefixWord ++ tailWord_845029).sum := by decide
  have hdescent : baseEnd_845029 < baseStart_845029 := by decide
  rcases family_descends (prefixWord ++ tailWord_845029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845057 : List Nat := [1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_845057 : Nat := 118140960795 + 845057 * 2 ^ 59
def prefixEnd_845057 : Nat := 4983230072969 + 3 ^ 40 * 845057 * 2
def baseEnd_845057 : Nat := 128569013761957168681825

theorem tailTrace_845057 : CollatzResearch.WordTrace tailWord_845057 prefixEnd_845057 128569013761957168681825 := by
  unfold tailWord_845057
  simp only [CollatzResearch.WordTrace]
  refine ⟨30821760899510288090469425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20547840599673525393646283 30821760899510288090469425)
  ·
    refine ⟨23116320674632716067852069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30821760899510288090469425 23116320674632716067852069)
    ·
      refine ⟨4334310126493634262722263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23116320674632716067852069 4334310126493634262722263)
      ·
        refine ⟨6501465189740451394083395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334310126493634262722263 6501465189740451394083395)
        ·
          refine ⟨9752197784610677091125093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501465189740451394083395 9752197784610677091125093)
          ·
            refine ⟨1828537084614501954585955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9752197784610677091125093 1828537084614501954585955)
            ·
              refine ⟨2742805626921752931878933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828537084614501954585955 2742805626921752931878933)
              ·
                refine ⟨128569013761957168681825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2742805626921752931878933 128569013761957168681825)
                ·
                  rfl

theorem cell20_845057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_845057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845057 prefixEnd_845057 := by exact prefixLift 845057
  have htrace : WordTrace (prefixWord ++ tailWord_845057) baseStart_845057 baseEnd_845057 := by
    simpa [prefixWord, tailWord_845057, baseEnd_845057] using wordTrace_append hprefix tailTrace_845057
  have hstable : (prefixWord ++ tailWord_845057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845057).length < 2 ^ (prefixWord ++ tailWord_845057).sum := by decide
  have hdescent : baseEnd_845057 < baseStart_845057 := by decide
  rcases family_descends (prefixWord ++ tailWord_845057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845067 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 2]
def baseStart_845067 : Nat := 118140960795 + 845067 * 2 ^ 59
def prefixEnd_845067 : Nat := 4983230072969 + 3 ^ 40 * 845067 * 2
def baseEnd_845067 : Nat := 385711605558355915712101

theorem tailTrace_845067 : CollatzResearch.WordTrace tailWord_845067 prefixEnd_845067 385711605558355915712101 := by
  unfold tailWord_845067
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822125629474059798333455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20548083752982706532222303 30822125629474059798333455)
  ·
    refine ⟨46233188444211089697500183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30822125629474059798333455 46233188444211089697500183)
    ·
      refine ⟨69349782666316634546250275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46233188444211089697500183 69349782666316634546250275)
      ·
        refine ⟨104024673999474951819375413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69349782666316634546250275 104024673999474951819375413)
        ·
          refine ⟨9752313187450776733066445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104024673999474951819375413 9752313187450776733066445)
          ·
            refine ⟨3657117445294041274899917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9752313187450776733066445 3657117445294041274899917)
            ·
              refine ⟨1371419041985265478087469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3657117445294041274899917 1371419041985265478087469)
              ·
                refine ⟨514282140744474554282801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371419041985265478087469 514282140744474554282801)
                ·
                  refine ⟨385711605558355915712101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514282140744474554282801 385711605558355915712101)
                  ·
                    rfl

theorem cell20_845067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 2].length) (baseStart_845067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845067 prefixEnd_845067 := by exact prefixLift 845067
  have htrace : WordTrace (prefixWord ++ tailWord_845067) baseStart_845067 baseEnd_845067 := by
    simpa [prefixWord, tailWord_845067, baseEnd_845067] using wordTrace_append hprefix tailTrace_845067
  have hstable : (prefixWord ++ tailWord_845067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845067).length < 2 ^ (prefixWord ++ tailWord_845067).sum := by decide
  have hdescent : baseEnd_845067 < baseStart_845067 := by decide
  rcases family_descends (prefixWord ++ tailWord_845067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845098 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_845098 : Nat := 118140960795 + 845098 * 2 ^ 59
def prefixEnd_845098 : Nat := 4983230072969 + 3 ^ 40 * 845098 * 2
def baseEnd_845098 : Nat := 385725754803057585678641

theorem tailTrace_845098 : CollatzResearch.WordTrace tailWord_845098 prefixEnd_845098 385725754803057585678641 := by
  unfold tailWord_845098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7705814073090438023177987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20548837528241168061807965 7705814073090438023177987)
  ·
    refine ⟨11558721109635657034766981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7705814073090438023177987 11558721109635657034766981)
    ·
      refine ⟨2167260208056685694018809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11558721109635657034766981 2167260208056685694018809)
      ·
        refine ⟨1625445156042514270514107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2167260208056685694018809 1625445156042514270514107)
        ·
          refine ⟨2438167734063771405771161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625445156042514270514107 2438167734063771405771161)
          ·
            refine ⟨1828625800547828554328371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438167734063771405771161 1828625800547828554328371)
            ·
              refine ⟨2742938700821742831492557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828625800547828554328371 2742938700821742831492557)
              ·
                refine ⟨1028602012808153561809709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2742938700821742831492557 1028602012808153561809709)
                ·
                  refine ⟨385725754803057585678641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028602012808153561809709 385725754803057585678641)
                  ·
                    rfl

theorem cell20_845098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_845098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845098 prefixEnd_845098 := by exact prefixLift 845098
  have htrace : WordTrace (prefixWord ++ tailWord_845098) baseStart_845098 baseEnd_845098 := by
    simpa [prefixWord, tailWord_845098, baseEnd_845098] using wordTrace_append hprefix tailTrace_845098
  have hstable : (prefixWord ++ tailWord_845098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845098).length < 2 ^ (prefixWord ++ tailWord_845098).sum := by decide
  have hdescent : baseEnd_845098 < baseStart_845098 := by decide
  rcases family_descends (prefixWord ++ tailWord_845098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845142 : List Nat := [5, 2, 3, 1, 2, 1, 1, 5]
def baseStart_845142 : Nat := 118140960795 + 845142 * 2 ^ 59
def prefixEnd_845142 : Nat := 4983230072969 + 3 ^ 40 * 845142 * 2
def baseEnd_845142 : Nat := 128581945867329662737265

theorem tailTrace_845142 : CollatzResearch.WordTrace tailWord_845142 prefixEnd_845142 128581945867329662737265 := by
  unfold tailWord_845142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926553819012646725457105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20549907402801565071542453 1926553819012646725457105)
  ·
    refine ⟨1444915364259485044092829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1926553819012646725457105 1444915364259485044092829)
    ·
      refine ⟨541843261597306891534811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1444915364259485044092829 541843261597306891534811)
      ·
        refine ⟨812764892395960337302217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541843261597306891534811 812764892395960337302217)
        ·
          refine ⟨609573669296970252976663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812764892395960337302217 609573669296970252976663)
          ·
            refine ⟨914360503945455379464995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609573669296970252976663 914360503945455379464995)
            ·
              refine ⟨1371540755918183069197493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914360503945455379464995 1371540755918183069197493)
              ·
                refine ⟨128581945867329662737265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1371540755918183069197493 128581945867329662737265)
                ·
                  rfl

theorem cell20_845142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_845142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845142 prefixEnd_845142 := by exact prefixLift 845142
  have htrace : WordTrace (prefixWord ++ tailWord_845142) baseStart_845142 baseEnd_845142 := by
    simpa [prefixWord, tailWord_845142, baseEnd_845142] using wordTrace_append hprefix tailTrace_845142
  have hstable : (prefixWord ++ tailWord_845142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845142).length < 2 ^ (prefixWord ++ tailWord_845142).sum := by decide
  have hdescent : baseEnd_845142 < baseStart_845142 := by decide
  rcases family_descends (prefixWord ++ tailWord_845142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845143 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 2]
def baseStart_845143 : Nat := 118140960795 + 845143 * 2 ^ 59
def prefixEnd_845143 : Nat := 4983230072969 + 3 ^ 40 * 845143 * 2
def baseEnd_845143 : Nat := 385746294029237429178457

theorem tailTrace_845143 : CollatzResearch.WordTrace tailWord_845143 prefixEnd_845143 385746294029237429178457 := by
  unfold tailWord_845143
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824897577198724778100083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20549931718132483185400055 30824897577198724778100083)
  ·
    refine ⟨46237346365798087167150125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30824897577198724778100083 46237346365798087167150125)
    ·
      refine ⟨17339004887174282687681297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46237346365798087167150125 17339004887174282687681297)
      ·
        refine ⟨13004253665380712015760973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17339004887174282687681297 13004253665380712015760973)
        ·
          refine ⟨4876595124517767005910365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13004253665380712015760973 4876595124517767005910365)
          ·
            refine ⟨1828723171694162627216387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4876595124517767005910365 1828723171694162627216387)
            ·
              refine ⟨2743084757541243940824581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828723171694162627216387 2743084757541243940824581)
              ·
                refine ⟨514328392038983238904609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2743084757541243940824581 514328392038983238904609)
                ·
                  refine ⟨385746294029237429178457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514328392038983238904609 385746294029237429178457)
                  ·
                    rfl

theorem cell20_845143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 2].length) (baseStart_845143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845143 prefixEnd_845143 := by exact prefixLift 845143
  have htrace : WordTrace (prefixWord ++ tailWord_845143) baseStart_845143 baseEnd_845143 := by
    simpa [prefixWord, tailWord_845143, baseEnd_845143] using wordTrace_append hprefix tailTrace_845143
  have hstable : (prefixWord ++ tailWord_845143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845143).length < 2 ^ (prefixWord ++ tailWord_845143).sum := by decide
  have hdescent : baseEnd_845143 < baseStart_845143 := by decide
  rcases family_descends (prefixWord ++ tailWord_845143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845164 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_845164 : Nat := 118140960795 + 845164 * 2 ^ 59
def prefixEnd_845164 : Nat := 4983230072969 + 3 ^ 40 * 845164 * 2
def baseEnd_845164 : Nat := 385755879001454689478371

theorem tailTrace_845164 : CollatzResearch.WordTrace tailWord_845164 prefixEnd_845164 385755879001454689478371 := by
  unfold tailWord_845164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412831755061322682307273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20550442340081763576409697 15412831755061322682307273)
  ·
    refine ⟨11559623816295992011730455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15412831755061322682307273 11559623816295992011730455)
    ·
      refine ⟨17339435724443988017595683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559623816295992011730455 17339435724443988017595683)
      ·
        refine ⟨26009153586665982026393525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17339435724443988017595683 26009153586665982026393525)
        ·
          refine ⟨2438358148749935814974393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26009153586665982026393525 2438358148749935814974393)
          ·
            refine ⟨1828768611562451861230795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438358148749935814974393 1828768611562451861230795)
            ·
              refine ⟨2743152917343677791846193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828768611562451861230795 2743152917343677791846193)
              ·
                refine ⟨2057364688007758343884645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743152917343677791846193 2057364688007758343884645)
                ·
                  refine ⟨385755879001454689478371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057364688007758343884645 385755879001454689478371)
                  ·
                    rfl

theorem cell20_845164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_845164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845164 prefixEnd_845164 := by exact prefixLift 845164
  have htrace : WordTrace (prefixWord ++ tailWord_845164) baseStart_845164 baseEnd_845164 := by
    simpa [prefixWord, tailWord_845164, baseEnd_845164] using wordTrace_append hprefix tailTrace_845164
  have hstable : (prefixWord ++ tailWord_845164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845164).length < 2 ^ (prefixWord ++ tailWord_845164).sum := by decide
  have hdescent : baseEnd_845164 < baseStart_845164 := by decide
  rcases family_descends (prefixWord ++ tailWord_845164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845181 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 2]
def baseStart_845181 : Nat := 118140960795 + 845181 * 2 ^ 59
def prefixEnd_845181 : Nat := 4983230072969 + 3 ^ 40 * 845181 * 2
def baseEnd_845181 : Nat := 385763638264678185911635

theorem tailTrace_845181 : CollatzResearch.WordTrace tailWord_845181 prefixEnd_845181 385763638264678185911635 := by
  unfold tailWord_845181
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826283551061057267983397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20550855700707371511988931 30826283551061057267983397)
  ·
    refine ⟨5779928165823948237746887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30826283551061057267983397 5779928165823948237746887)
    ·
      refine ⟨8669892248735922356620331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779928165823948237746887 8669892248735922356620331)
      ·
        refine ⟨13004838373103883534930497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8669892248735922356620331 13004838373103883534930497)
        ·
          refine ⟨9753628779827912651197873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13004838373103883534930497 9753628779827912651197873)
          ·
            refine ⟨7315221584870934488398405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9753628779827912651197873 7315221584870934488398405)
            ·
              refine ⟨1371604047163300216574701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7315221584870934488398405 1371604047163300216574701)
              ·
                refine ⟨514351517686237581215513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1371604047163300216574701 514351517686237581215513)
                ·
                  refine ⟨385763638264678185911635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514351517686237581215513 385763638264678185911635)
                  ·
                    rfl

theorem cell20_845181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_845181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845181 prefixEnd_845181 := by exact prefixLift 845181
  have htrace : WordTrace (prefixWord ++ tailWord_845181) baseStart_845181 baseEnd_845181 := by
    simpa [prefixWord, tailWord_845181, baseEnd_845181] using wordTrace_append hprefix tailTrace_845181
  have hstable : (prefixWord ++ tailWord_845181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845181).length < 2 ^ (prefixWord ++ tailWord_845181).sum := by decide
  have hdescent : baseEnd_845181 < baseStart_845181 := by decide
  rcases family_descends (prefixWord ++ tailWord_845181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845285 : List Nat := [1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_845285 : Nat := 118140960795 + 845285 * 2 ^ 59
def prefixEnd_845285 : Nat := 4983230072969 + 3 ^ 40 * 845285 * 2
def baseEnd_845285 : Nat := 128603702232838682148181

theorem tailTrace_845285 : CollatzResearch.WordTrace tailWord_845285 prefixEnd_845285 128603702232838682148181 := by
  unfold tailWord_845285
  simp only [CollatzResearch.WordTrace]
  refine ⟨30830076742684283029769309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20553384495122855353179539 30830076742684283029769309)
  ·
    refine ⟨11561278778506606136163491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30830076742684283029769309 11561278778506606136163491)
    ·
      refine ⟨17341918167759909204245237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11561278778506606136163491 17341918167759909204245237)
      ·
        refine ⟨1625804828227491487897991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17341918167759909204245237 1625804828227491487897991)
        ·
          refine ⟨2438707242341237231846987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625804828227491487897991 2438707242341237231846987)
          ·
            refine ⟨3658060863511855847770481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438707242341237231846987 3658060863511855847770481)
            ·
              refine ⟨2743545647633891885827861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3658060863511855847770481 2743545647633891885827861)
              ·
                refine ⟨128603702232838682148181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2743545647633891885827861 128603702232838682148181)
                ·
                  rfl

theorem cell20_845285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_845285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845285 prefixEnd_845285 := by exact prefixLift 845285
  have htrace : WordTrace (prefixWord ++ tailWord_845285) baseStart_845285 baseEnd_845285 := by
    simpa [prefixWord, tailWord_845285, baseEnd_845285] using wordTrace_append hprefix tailTrace_845285
  have hstable : (prefixWord ++ tailWord_845285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845285).length < 2 ^ (prefixWord ++ tailWord_845285).sum := by decide
  have hdescent : baseEnd_845285 < baseStart_845285 := by decide
  rcases family_descends (prefixWord ++ tailWord_845285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845309 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 3]
def baseStart_845309 : Nat := 118140960795 + 845309 * 2 ^ 59
def prefixEnd_845309 : Nat := 4983230072969 + 3 ^ 40 * 845309 * 2
def baseEnd_845309 : Nat := 385822060952478629644445

theorem tailTrace_845309 : CollatzResearch.WordTrace tailWord_845309 prefixEnd_845309 385822060952478629644445 := by
  unfold tailWord_845309
  simp only [CollatzResearch.WordTrace]
  refine ⟨30830952094597335128642981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20553968063064890085761987 30830952094597335128642981)
  ·
    refine ⟨5780803517737000336620559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30830952094597335128642981 5780803517737000336620559)
    ·
      refine ⟨8671205276605500504930839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780803517737000336620559 8671205276605500504930839)
      ·
        refine ⟨13006807914908250757396259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8671205276605500504930839 13006807914908250757396259)
        ·
          refine ⟨19510211872362376136094389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006807914908250757396259 19510211872362376136094389)
          ·
            refine ⟨1829082363033972762758849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19510211872362376136094389 1829082363033972762758849)
            ·
              refine ⟨1371811772275479572069137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829082363033972762758849 1371811772275479572069137)
              ·
                refine ⟨1028858829206609679051853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371811772275479572069137 1028858829206609679051853)
                ·
                  refine ⟨385822060952478629644445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028858829206609679051853 385822060952478629644445)
                  ·
                    rfl

theorem cell20_845309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_845309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845309 prefixEnd_845309 := by exact prefixLift 845309
  have htrace : WordTrace (prefixWord ++ tailWord_845309) baseStart_845309 baseEnd_845309 := by
    simpa [prefixWord, tailWord_845309, baseEnd_845309] using wordTrace_append hprefix tailTrace_845309
  have hstable : (prefixWord ++ tailWord_845309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845309).length < 2 ^ (prefixWord ++ tailWord_845309).sum := by decide
  have hdescent : baseEnd_845309 < baseStart_845309 := by decide
  rcases family_descends (prefixWord ++ tailWord_845309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845368 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_845368 : Nat := 118140960795 + 845368 * 2 ^ 59
def prefixEnd_845368 : Nat := 4983230072969 + 3 ^ 40 * 845368 * 2
def baseEnd_845368 : Nat := 385848990160136646677537

theorem tailTrace_845368 : CollatzResearch.WordTrace tailWord_845368 prefixEnd_845368 385848990160136646677537 := by
  unfold tailWord_845368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15416552000691794102520379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20555402667589058803360505 15416552000691794102520379)
  ·
    refine ⟨23124828001037691153780569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15416552000691794102520379 23124828001037691153780569)
    ·
      refine ⟨17343621000778268365335427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23124828001037691153780569 17343621000778268365335427)
      ·
        refine ⟨26015431501167402548003141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17343621000778268365335427 26015431501167402548003141)
        ·
          refine ⟨4877893406468887977750589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26015431501167402548003141 4877893406468887977750589)
          ·
            refine ⟨1829210027425832991656471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4877893406468887977750589 1829210027425832991656471)
            ·
              refine ⟨2743815041138749487484707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829210027425832991656471 2743815041138749487484707)
              ·
                refine ⟨4115722561708124231227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743815041138749487484707 4115722561708124231227061)
                ·
                  refine ⟨385848990160136646677537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4115722561708124231227061 385848990160136646677537)
                  ·
                    rfl

theorem cell20_845368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_845368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845368 prefixEnd_845368 := by exact prefixLift 845368
  have htrace : WordTrace (prefixWord ++ tailWord_845368) baseStart_845368 baseEnd_845368 := by
    simpa [prefixWord, tailWord_845368, baseEnd_845368] using wordTrace_append hprefix tailTrace_845368
  have hstable : (prefixWord ++ tailWord_845368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845368).length < 2 ^ (prefixWord ++ tailWord_845368).sum := by decide
  have hdescent : baseEnd_845368 < baseStart_845368 := by decide
  rcases family_descends (prefixWord ++ tailWord_845368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845375 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_845375 : Nat := 118140960795 + 845375 * 2 ^ 59
def prefixEnd_845375 : Nat := 4983230072969 + 3 ^ 40 * 845375 * 2
def baseEnd_845375 : Nat := 385852185150875733444175

theorem tailTrace_845375 : CollatzResearch.WordTrace tailWord_845375 prefixEnd_845375 385852185150875733444175 := by
  unfold tailWord_845375
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833359312358228400545579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20555572874905485600363719 30833359312358228400545579)
  ·
    refine ⟨46250038968537342600818369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30833359312358228400545579 46250038968537342600818369)
    ·
      refine ⟨34687529226403006950613777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46250038968537342600818369 34687529226403006950613777)
      ·
        refine ⟨26015646919802255212960333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34687529226403006950613777 26015646919802255212960333)
        ·
          refine ⟨9755867594925845704860125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26015646919802255212960333 9755867594925845704860125)
          ·
            refine ⟨3658450348097192139322547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9755867594925845704860125 3658450348097192139322547)
            ·
              refine ⟨5487675522145788208983821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658450348097192139322547 5487675522145788208983821)
              ·
                refine ⟨2057878320804670578368933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5487675522145788208983821 2057878320804670578368933)
                ·
                  refine ⟨385852185150875733444175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057878320804670578368933 385852185150875733444175)
                  ·
                    rfl

theorem cell20_845375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_845375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845375 prefixEnd_845375 := by exact prefixLift 845375
  have htrace : WordTrace (prefixWord ++ tailWord_845375) baseStart_845375 baseEnd_845375 := by
    simpa [prefixWord, tailWord_845375, baseEnd_845375] using wordTrace_append hprefix tailTrace_845375
  have hstable : (prefixWord ++ tailWord_845375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845375).length < 2 ^ (prefixWord ++ tailWord_845375).sum := by decide
  have hdescent : baseEnd_845375 < baseStart_845375 := by decide
  rcases family_descends (prefixWord ++ tailWord_845375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845399 : List Nat := [1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_845399 : Nat := 118140960795 + 845399 * 2 ^ 59
def prefixEnd_845399 : Nat := 4983230072969 + 3 ^ 40 * 845399 * 2
def baseEnd_845399 : Nat := 128621046468279438881359

theorem tailTrace_845399 : CollatzResearch.WordTrace tailWord_845399 prefixEnd_845399 128621046468279438881359 := by
  unfold tailWord_845399
  simp only [CollatzResearch.WordTrace]
  refine ⟨30834234664271280499419251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20556156442847520332946167 30834234664271280499419251)
  ·
    refine ⟨46251351996406920749128877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30834234664271280499419251 46251351996406920749128877)
    ·
      refine ⟨17344256998652595280923329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46251351996406920749128877 17344256998652595280923329)
      ·
        refine ⟨13008192748989446460692497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17344256998652595280923329 13008192748989446460692497)
        ·
          refine ⟨9756144561742084845519373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13008192748989446460692497 9756144561742084845519373)
          ·
            refine ⟨3658554210653281817069765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9756144561742084845519373 3658554210653281817069765)
            ·
              refine ⟨685978914497490340700581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3658554210653281817069765 685978914497490340700581)
              ·
                refine ⟨128621046468279438881359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685978914497490340700581 128621046468279438881359)
                ·
                  rfl

theorem cell20_845399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_845399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845399 prefixEnd_845399 := by exact prefixLift 845399
  have htrace : WordTrace (prefixWord ++ tailWord_845399) baseStart_845399 baseEnd_845399 := by
    simpa [prefixWord, tailWord_845399, baseEnd_845399] using wordTrace_append hprefix tailTrace_845399
  have hstable : (prefixWord ++ tailWord_845399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845399).length < 2 ^ (prefixWord ++ tailWord_845399).sum := by decide
  have hdescent : baseEnd_845399 < baseStart_845399 := by decide
  rcases family_descends (prefixWord ++ tailWord_845399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845426 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_845426 : Nat := 118140960795 + 845426 * 2 ^ 59
def prefixEnd_845426 : Nat := 4983230072969 + 3 ^ 40 * 845426 * 2
def baseEnd_845426 : Nat := 385875462940546222743967

theorem tailTrace_845426 : CollatzResearch.WordTrace tailWord_845426 prefixEnd_845426 385875462940546222743967 := by
  unfold tailWord_845426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708804858793366027663033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20556812956782309407101421 7708804858793366027663033)
  ·
    refine ⟨5781603644095024520747275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7708804858793366027663033 5781603644095024520747275)
    ·
      refine ⟨8672405466142536781120913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5781603644095024520747275 8672405466142536781120913)
      ·
        refine ⟨6504304099606902585840685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8672405466142536781120913 6504304099606902585840685)
        ·
          refine ⟨2439114037352588469690257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6504304099606902585840685 2439114037352588469690257)
          ·
            refine ⟨1829335528014441352267693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439114037352588469690257 1829335528014441352267693)
            ·
              refine ⟨686000823005415507100385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1829335528014441352267693 686000823005415507100385)
              ·
                refine ⟨514500617254061630325289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686000823005415507100385 514500617254061630325289)
                ·
                  refine ⟨385875462940546222743967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514500617254061630325289 385875462940546222743967)
                  ·
                    rfl

theorem cell20_845426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_845426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845426 prefixEnd_845426 := by exact prefixLift 845426
  have htrace : WordTrace (prefixWord ++ tailWord_845426) baseStart_845426 baseEnd_845426 := by
    simpa [prefixWord, tailWord_845426, baseEnd_845426] using wordTrace_append hprefix tailTrace_845426
  have hstable : (prefixWord ++ tailWord_845426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845426).length < 2 ^ (prefixWord ++ tailWord_845426).sum := by decide
  have hdescent : baseEnd_845426 < baseStart_845426 := by decide
  rcases family_descends (prefixWord ++ tailWord_845426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845437 : List Nat := [1, 4, 1, 1, 4, 2, 2, 5]
def baseStart_845437 : Nat := 118140960795 + 845437 * 2 ^ 59
def prefixEnd_845437 : Nat := 4983230072969 + 3 ^ 40 * 845437 * 2
def baseEnd_845437 : Nat := 128626827880093024459085

theorem tailTrace_845437 : CollatzResearch.WordTrace tailWord_845437 prefixEnd_845437 128626827880093024459085 := by
  unfold tailWord_845437
  simp only [CollatzResearch.WordTrace]
  refine ⟨30835620638133612989302565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20557080425422408659535043 30835620638133612989302565)
  ·
    refine ⟨5781678869650052435494231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30835620638133612989302565 5781678869650052435494231)
    ·
      refine ⟨8672518304475078653241347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5781678869650052435494231 8672518304475078653241347)
      ·
        refine ⟨13008777456712617979862021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8672518304475078653241347 13008777456712617979862021)
        ·
          refine ⟨2439145773133615871224129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13008777456712617979862021 2439145773133615871224129)
          ·
            refine ⟨1829359329850211903418097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439145773133615871224129 1829359329850211903418097)
            ·
              refine ⟨1372019497387658927563573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829359329850211903418097 1372019497387658927563573)
              ·
                refine ⟨128626827880093024459085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1372019497387658927563573 128626827880093024459085)
                ·
                  rfl

theorem cell20_845437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_845437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845437 prefixEnd_845437 := by exact prefixLift 845437
  have htrace : WordTrace (prefixWord ++ tailWord_845437) baseStart_845437 baseEnd_845437 := by
    simpa [prefixWord, tailWord_845437, baseEnd_845437] using wordTrace_append hprefix tailTrace_845437
  have hstable : (prefixWord ++ tailWord_845437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845437).length < 2 ^ (prefixWord ++ tailWord_845437).sum := by decide
  have hdescent : baseEnd_845437 < baseStart_845437 := by decide
  rcases family_descends (prefixWord ++ tailWord_845437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845465 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_845465 : Nat := 118140960795 + 845465 * 2 ^ 59
def prefixEnd_845465 : Nat := 4983230072969 + 3 ^ 40 * 845465 * 2
def baseEnd_845465 : Nat := 385893263603235420443807

theorem tailTrace_845465 : CollatzResearch.WordTrace tailWord_845465 prefixEnd_845465 385893263603235420443807 := by
  unfold tailWord_845465
  simp only [CollatzResearch.WordTrace]
  refine ⟨30836641882032173771321849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20557761254688115847547899 30836641882032173771321849)
  ·
    refine ⟨23127481411524130328491387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30836641882032173771321849 23127481411524130328491387)
    ·
      refine ⟨34691222117286195492737081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23127481411524130328491387 34691222117286195492737081)
      ·
        refine ⟨26018416587964646619552811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34691222117286195492737081 26018416587964646619552811)
        ·
          refine ⟨39027624881946969929329217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26018416587964646619552811 39027624881946969929329217)
          ·
            refine ⟨29270718661460227446996913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39027624881946969929329217 29270718661460227446996913)
            ·
              refine ⟨21953038996095170585247685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29270718661460227446996913 21953038996095170585247685)
              ·
                refine ⟨4116194811767844484733941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21953038996095170585247685 4116194811767844484733941)
                ·
                  refine ⟨385893263603235420443807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116194811767844484733941 385893263603235420443807)
                  ·
                    rfl

theorem cell20_845465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_845465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845465 prefixEnd_845465 := by exact prefixLift 845465
  have htrace : WordTrace (prefixWord ++ tailWord_845465) baseStart_845465 baseEnd_845465 := by
    simpa [prefixWord, tailWord_845465, baseEnd_845465] using wordTrace_append hprefix tailTrace_845465
  have hstable : (prefixWord ++ tailWord_845465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845465).length < 2 ^ (prefixWord ++ tailWord_845465).sum := by decide
  have hdescent : baseEnd_845465 < baseStart_845465 := by decide
  rcases family_descends (prefixWord ++ tailWord_845465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845485 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 2]
def baseStart_845485 : Nat := 118140960795 + 845485 * 2 ^ 59
def prefixEnd_845485 : Nat := 4983230072969 + 3 ^ 40 * 845485 * 2
def baseEnd_845485 : Nat := 385902392148204239777059

theorem tailTrace_845485 : CollatzResearch.WordTrace tailWord_845485 prefixEnd_845485 385902392148204239777059 := by
  unfold tailWord_845485
  simp only [CollatzResearch.WordTrace]
  refine ⟨30837371341959717187049909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20558247561306478124699939 30837371341959717187049909)
  ·
    refine ⟨2891003563308723486285929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30837371341959717187049909 2891003563308723486285929)
    ·
      refine ⟨2168252672481542614714447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2891003563308723486285929 2168252672481542614714447)
      ·
        refine ⟨3252379008722313922071671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168252672481542614714447 3252379008722313922071671)
        ·
          refine ⟨4878568513083470883107507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252379008722313922071671 4878568513083470883107507)
          ·
            refine ⟨7317852769625206324661261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878568513083470883107507 7317852769625206324661261)
            ·
              refine ⟨2744194788609452371747973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7317852769625206324661261 2744194788609452371747973)
              ·
                refine ⟨514536522864272319702745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2744194788609452371747973 514536522864272319702745)
                ·
                  refine ⟨385902392148204239777059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514536522864272319702745 385902392148204239777059)
                  ·
                    rfl

theorem cell20_845485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_845485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845485 prefixEnd_845485 := by exact prefixLift 845485
  have htrace : WordTrace (prefixWord ++ tailWord_845485) baseStart_845485 baseEnd_845485 := by
    simpa [prefixWord, tailWord_845485, baseEnd_845485] using wordTrace_append hprefix tailTrace_845485
  have hstable : (prefixWord ++ tailWord_845485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845485).length < 2 ^ (prefixWord ++ tailWord_845485).sum := by decide
  have hdescent : baseEnd_845485 < baseStart_845485 := by decide
  rcases family_descends (prefixWord ++ tailWord_845485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845533 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_845533 : Nat := 118140960795 + 845533 * 2 ^ 59
def prefixEnd_845533 : Nat := 4983230072969 + 3 ^ 40 * 845533 * 2
def baseEnd_845533 : Nat := 385924300656129406176863

theorem tailTrace_845533 : CollatzResearch.WordTrace tailWord_845533 prefixEnd_845533 385924300656129406176863 := by
  unfold tailWord_845533
  simp only [CollatzResearch.WordTrace]
  refine ⟨30839122045785821384797253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20559414697190547589864835 30839122045785821384797253)
  ·
    refine ⟨5782335383584841509649485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30839122045785821384797253 5782335383584841509649485)
    ·
      refine ⟨2168375768844315566118557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5782335383584841509649485 2168375768844315566118557)
      ·
        refine ⟨813140913316618337294459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2168375768844315566118557 813140913316618337294459)
        ·
          refine ⟨1219711369974927505941689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813140913316618337294459 1219711369974927505941689)
          ·
            refine ⟨914783527481195629456267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219711369974927505941689 914783527481195629456267)
            ·
              refine ⟨1372175291221793444184401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914783527481195629456267 1372175291221793444184401)
              ·
                refine ⟨1029131468416345083138301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372175291221793444184401 1029131468416345083138301)
                ·
                  refine ⟨385924300656129406176863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029131468416345083138301 385924300656129406176863)
                  ·
                    rfl

theorem cell20_845533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_845533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845533 prefixEnd_845533 := by exact prefixLift 845533
  have htrace : WordTrace (prefixWord ++ tailWord_845533) baseStart_845533 baseEnd_845533 := by
    simpa [prefixWord, tailWord_845533, baseEnd_845533] using wordTrace_append hprefix tailTrace_845533
  have hstable : (prefixWord ++ tailWord_845533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845533).length < 2 ^ (prefixWord ++ tailWord_845533).sum := by decide
  have hdescent : baseEnd_845533 < baseStart_845533 := by decide
  rcases family_descends (prefixWord ++ tailWord_845533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845544 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_845544 : Nat := 118140960795 + 845544 * 2 ^ 59
def prefixEnd_845544 : Nat := 4983230072969 + 3 ^ 40 * 845544 * 2
def baseEnd_845544 : Nat := 385929321355862256810151

theorem tailTrace_845544 : CollatzResearch.WordTrace tailWord_845544 prefixEnd_845544 385929321355862256810151 := by
  unfold tailWord_845544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419761624372985131723843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20559682165830646842298457 15419761624372985131723843)
  ·
    refine ⟨23129642436559477697585765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15419761624372985131723843 23129642436559477697585765)
    ·
      refine ⟨4336807956854902068297331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23129642436559477697585765 4336807956854902068297331)
      ·
        refine ⟨6505211935282353102445997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336807956854902068297331 6505211935282353102445997)
        ·
          refine ⟨2439454475730882413417249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6505211935282353102445997 2439454475730882413417249)
          ·
            refine ⟨1829590856798161810062937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439454475730882413417249 1829590856798161810062937)
            ·
              refine ⟨1372193142598621357547203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829590856798161810062937 1372193142598621357547203)
              ·
                refine ⟨2058289713897932036320805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372193142598621357547203 2058289713897932036320805)
                ·
                  refine ⟨385929321355862256810151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058289713897932036320805 385929321355862256810151)
                  ·
                    rfl

theorem cell20_845544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_845544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845544 prefixEnd_845544 := by exact prefixLift 845544
  have htrace : WordTrace (prefixWord ++ tailWord_845544) baseStart_845544 baseEnd_845544 := by
    simpa [prefixWord, tailWord_845544, baseEnd_845544] using wordTrace_append hprefix tailTrace_845544
  have hstable : (prefixWord ++ tailWord_845544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845544).length < 2 ^ (prefixWord ++ tailWord_845544).sum := by decide
  have hdescent : baseEnd_845544 < baseStart_845544 := by decide
  rcases family_descends (prefixWord ++ tailWord_845544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845579 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_845579 : Nat := 118140960795 + 845579 * 2 ^ 59
def prefixEnd_845579 : Nat := 4983230072969 + 3 ^ 40 * 845579 * 2
def baseEnd_845579 : Nat := 385945296309557690643341

theorem tailTrace_845579 : CollatzResearch.WordTrace tailWord_845579 prefixEnd_845579 385945296309557690643341 := by
  unfold tailWord_845579
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840799803619171240971791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20560533202412780827314527 30840799803619171240971791)
  ·
    refine ⟨46261199705428756861457687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30840799803619171240971791 46261199705428756861457687)
    ·
      refine ⟨69391799558143135292186531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46261199705428756861457687 69391799558143135292186531)
      ·
        refine ⟨104087699337214702938279797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69391799558143135292186531 104087699337214702938279797)
        ·
          refine ⟨9758221812863878400463731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104087699337214702938279797 9758221812863878400463731)
          ·
            refine ⟨14637332719295817600695597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758221812863878400463731 14637332719295817600695597)
            ·
              refine ⟨5488999769735931600260849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14637332719295817600695597 5488999769735931600260849)
              ·
                refine ⟨4116749827301948700195637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488999769735931600260849 4116749827301948700195637)
                ·
                  refine ⟨385945296309557690643341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116749827301948700195637 385945296309557690643341)
                  ·
                    rfl

theorem cell20_845579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_845579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845579 prefixEnd_845579 := by exact prefixLift 845579
  have htrace : WordTrace (prefixWord ++ tailWord_845579) baseStart_845579 baseEnd_845579 := by
    simpa [prefixWord, tailWord_845579, baseEnd_845579] using wordTrace_append hprefix tailTrace_845579
  have hstable : (prefixWord ++ tailWord_845579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845579).length < 2 ^ (prefixWord ++ tailWord_845579).sum := by decide
  have hdescent : baseEnd_845579 < baseStart_845579 := by decide
  rcases family_descends (prefixWord ++ tailWord_845579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845581 : List Nat := [1, 7, 2, 1, 2, 1, 6]
def baseStart_845581 : Nat := 118140960795 + 845581 * 2 ^ 59
def prefixEnd_845581 : Nat := 4983230072969 + 3 ^ 40 * 845581 * 2
def baseEnd_845581 : Nat := 42882912129339396952963

theorem tailTrace_845581 : CollatzResearch.WordTrace tailWord_845581 prefixEnd_845581 42882912129339396952963 := by
  unfold tailWord_845581
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840872749611925582544597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20560581833074617055029731 30840872749611925582544597)
  ·
    refine ⟨722832955069029505840889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30840872749611925582544597 722832955069029505840889)
    ·
      refine ⟨542124716301772129380667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722832955069029505840889 542124716301772129380667)
      ·
        refine ⟨813187074452658194071001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542124716301772129380667 813187074452658194071001)
        ·
          refine ⟨609890305839493645553251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813187074452658194071001 609890305839493645553251)
          ·
            refine ⟨914835458759240468329877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609890305839493645553251 914835458759240468329877)
            ·
              refine ⟨42882912129339396952963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 914835458759240468329877 42882912129339396952963)
              ·
                rfl

theorem cell20_845581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 6].length) (baseStart_845581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845581 prefixEnd_845581 := by exact prefixLift 845581
  have htrace : WordTrace (prefixWord ++ tailWord_845581) baseStart_845581 baseEnd_845581 := by
    simpa [prefixWord, tailWord_845581, baseEnd_845581] using wordTrace_append hprefix tailTrace_845581
  have hstable : (prefixWord ++ tailWord_845581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845581).length < 2 ^ (prefixWord ++ tailWord_845581).sum := by decide
  have hdescent : baseEnd_845581 < baseStart_845581 := by decide
  rcases family_descends (prefixWord ++ tailWord_845581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845596 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 3]
def baseStart_845596 : Nat := 118140960795 + 845596 * 2 ^ 59
def prefixEnd_845596 : Nat := 4983230072969 + 3 ^ 40 * 845596 * 2
def baseEnd_845596 : Nat := 385953055572781187076605

theorem tailTrace_845596 : CollatzResearch.WordTrace tailWord_845596 prefixEnd_845596 385953055572781187076605 := by
  unfold tailWord_845596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420709922278791572170321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20560946563038388762893761 15420709922278791572170321)
  ·
    refine ⟨11565532441709093679127741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15420709922278791572170321 11565532441709093679127741)
    ·
      refine ⟨4337074665640910129672903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11565532441709093679127741 4337074665640910129672903)
      ·
        refine ⟨6505611998461365194509355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337074665640910129672903 6505611998461365194509355)
        ·
          refine ⟨9758417997692047791764033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505611998461365194509355 9758417997692047791764033)
          ·
            refine ⟨7318813498269035843823025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758417997692047791764033 7318813498269035843823025)
            ·
              refine ⟨5489110123701776882867269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318813498269035843823025 5489110123701776882867269)
              ·
                refine ⟨1029208148194083165537613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5489110123701776882867269 1029208148194083165537613)
                ·
                  refine ⟨385953055572781187076605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029208148194083165537613 385953055572781187076605)
                  ·
                    rfl

theorem cell20_845596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_845596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845596 prefixEnd_845596 := by exact prefixLift 845596
  have htrace : WordTrace (prefixWord ++ tailWord_845596) baseStart_845596 baseEnd_845596 := by
    simpa [prefixWord, tailWord_845596, baseEnd_845596] using wordTrace_append hprefix tailTrace_845596
  have hstable : (prefixWord ++ tailWord_845596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845596).length < 2 ^ (prefixWord ++ tailWord_845596).sum := by decide
  have hdescent : baseEnd_845596 < baseStart_845596 := by decide
  rcases family_descends (prefixWord ++ tailWord_845596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845599 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 2]
def baseStart_845599 : Nat := 118140960795 + 845599 * 2 ^ 59
def prefixEnd_845599 : Nat := 4983230072969 + 3 ^ 40 * 845599 * 2
def baseEnd_845599 : Nat := 385954424854526509976593

theorem tailTrace_845599 : CollatzResearch.WordTrace tailWord_845599 prefixEnd_845599 385954424854526509976593 := by
  unfold tailWord_845599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841529263546714656699851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20561019509031143104466567 30841529263546714656699851)
  ·
    refine ⟨46262293895320071985049777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841529263546714656699851 46262293895320071985049777)
    ·
      refine ⟨34696720421490053988787333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46262293895320071985049777 34696720421490053988787333)
      ·
        refine ⟨6505635079029385122897625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34696720421490053988787333 6505635079029385122897625)
        ·
          refine ⟨4879226309272038842173219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505635079029385122897625 4879226309272038842173219)
          ·
            refine ⟨7318839463908058263259829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879226309272038842173219 7318839463908058263259829)
            ·
              refine ⟨686141199741380462180609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7318839463908058263259829 686141199741380462180609)
              ·
                refine ⟨514605899806035346635457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686141199741380462180609 514605899806035346635457)
                ·
                  refine ⟨385954424854526509976593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514605899806035346635457 385954424854526509976593)
                  ·
                    rfl

theorem cell20_845599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 2].length) (baseStart_845599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845599 prefixEnd_845599 := by exact prefixLift 845599
  have htrace : WordTrace (prefixWord ++ tailWord_845599) baseStart_845599 baseEnd_845599 := by
    simpa [prefixWord, tailWord_845599, baseEnd_845599] using wordTrace_append hprefix tailTrace_845599
  have hstable : (prefixWord ++ tailWord_845599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845599).length < 2 ^ (prefixWord ++ tailWord_845599).sum := by decide
  have hdescent : baseEnd_845599 < baseStart_845599 := by decide
  rcases family_descends (prefixWord ++ tailWord_845599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845603 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_845603 : Nat := 118140960795 + 845603 * 2 ^ 59
def prefixEnd_845603 : Nat := 4983230072969 + 3 ^ 40 * 845603 * 2
def baseEnd_845603 : Nat := 385956250563520273843243

theorem tailTrace_845603 : CollatzResearch.WordTrace tailWord_845603 prefixEnd_845603 385956250563520273843243 := by
  unfold tailWord_845603
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841675155532223339845463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20561116770354815559896975 30841675155532223339845463)
  ·
    refine ⟨46262512733298335009768195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30841675155532223339845463 46262512733298335009768195)
    ·
      refine ⟨69393769099947502514652293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46262512733298335009768195 69393769099947502514652293)
      ·
        refine ⟨13011331706240156721497305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69393769099947502514652293 13011331706240156721497305)
        ·
          refine ⟨9758498779680117541122979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13011331706240156721497305 9758498779680117541122979)
          ·
            refine ⟨14637748169520176311684469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758498779680117541122979 14637748169520176311684469)
            ·
              refine ⟨1372288890892516529220419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14637748169520176311684469 1372288890892516529220419)
              ·
                refine ⟨2058433336338774793830629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372288890892516529220419 2058433336338774793830629)
                ·
                  refine ⟨385956250563520273843243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058433336338774793830629 385956250563520273843243)
                  ·
                    rfl

theorem cell20_845603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_845603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845603 prefixEnd_845603 := by exact prefixLift 845603
  have htrace : WordTrace (prefixWord ++ tailWord_845603) baseStart_845603 baseEnd_845603 := by
    simpa [prefixWord, tailWord_845603, baseEnd_845603] using wordTrace_append hprefix tailTrace_845603
  have hstable : (prefixWord ++ tailWord_845603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845603).length < 2 ^ (prefixWord ++ tailWord_845603).sum := by decide
  have hdescent : baseEnd_845603 < baseStart_845603 := by decide
  rcases family_descends (prefixWord ++ tailWord_845603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845658 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_845658 : Nat := 118140960795 + 845658 * 2 ^ 59
def prefixEnd_845658 : Nat := 4983230072969 + 3 ^ 40 * 845658 * 2
def baseEnd_845658 : Nat := 385981354062184527009685

theorem tailTrace_845658 : CollatzResearch.WordTrace tailWord_845658 prefixEnd_845658 385981354062184527009685 := by
  unfold tailWord_845658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710920292583241933274407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20562454113555311822065085 7710920292583241933274407)
  ·
    refine ⟨11566380438874862899911611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7710920292583241933274407 11566380438874862899911611)
    ·
      refine ⟨17349570658312294349867417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566380438874862899911611 17349570658312294349867417)
      ·
        refine ⟨13012177993734220762400563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17349570658312294349867417 13012177993734220762400563)
        ·
          refine ⟨19518266990601331143600845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13012177993734220762400563 19518266990601331143600845)
          ·
            refine ⟨7319350121475499178850317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19518266990601331143600845 7319350121475499178850317)
            ·
              refine ⟨2744756295553312192068869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7319350121475499178850317 2744756295553312192068869)
              ·
                refine ⟨514641805416246036012913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2744756295553312192068869 514641805416246036012913)
                ·
                  refine ⟨385981354062184527009685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514641805416246036012913 385981354062184527009685)
                  ·
                    rfl

theorem cell20_845658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_845658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845658 prefixEnd_845658 := by exact prefixLift 845658
  have htrace : WordTrace (prefixWord ++ tailWord_845658) baseStart_845658 baseEnd_845658 := by
    simpa [prefixWord, tailWord_845658, baseEnd_845658] using wordTrace_append hprefix tailTrace_845658
  have hstable : (prefixWord ++ tailWord_845658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845658).length < 2 ^ (prefixWord ++ tailWord_845658).sum := by decide
  have hdescent : baseEnd_845658 < baseStart_845658 := by decide
  rcases family_descends (prefixWord ++ tailWord_845658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845672 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_845672 : Nat := 118140960795 + 845672 * 2 ^ 59
def prefixEnd_845672 : Nat := 4983230072969 + 3 ^ 40 * 845672 * 2
def baseEnd_845672 : Nat := 385987744043662700542961

theorem tailTrace_845672 : CollatzResearch.WordTrace tailWord_845672 prefixEnd_845672 385987744043662700542961 := by
  unfold tailWord_845672
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422095896141124062053635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20562794528188165416071513 15422095896141124062053635)
  ·
    refine ⟨23133143844211686093080453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15422095896141124062053635 23133143844211686093080453)
    ·
      refine ⟨4337464470789691142452585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23133143844211686093080453 4337464470789691142452585)
      ·
        refine ⟨3253098353092268356839439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4337464470789691142452585 3253098353092268356839439)
        ·
          refine ⟨4879647529638402535259159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253098353092268356839439 4879647529638402535259159)
          ·
            refine ⟨7319471294457603802888739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879647529638402535259159 7319471294457603802888739)
            ·
              refine ⟨10979206941686405704333109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319471294457603802888739 10979206941686405704333109)
              ·
                refine ⟨1029300650783100534781229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10979206941686405704333109 1029300650783100534781229)
                ·
                  refine ⟨385987744043662700542961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029300650783100534781229 385987744043662700542961)
                  ·
                    rfl

theorem cell20_845672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_845672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845672 prefixEnd_845672 := by exact prefixLift 845672
  have htrace : WordTrace (prefixWord ++ tailWord_845672) baseStart_845672 baseEnd_845672 := by
    simpa [prefixWord, tailWord_845672, baseEnd_845672] using wordTrace_append hprefix tailTrace_845672
  have hstable : (prefixWord ++ tailWord_845672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845672).length < 2 ^ (prefixWord ++ tailWord_845672).sum := by decide
  have hdescent : baseEnd_845672 < baseStart_845672 := by decide
  rcases family_descends (prefixWord ++ tailWord_845672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845693 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_845693 : Nat := 118140960795 + 845693 * 2 ^ 59
def prefixEnd_845693 : Nat := 4983230072969 + 3 ^ 40 * 845693 * 2
def baseEnd_845693 : Nat := 385997329015879960842875

theorem tailTrace_845693 : CollatzResearch.WordTrace tailWord_845693 prefixEnd_845693 385997329015879960842875 := by
  unfold tailWord_845693
  simp only [CollatzResearch.WordTrace]
  refine ⟨30844957725206168710621733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20563305150137445807081155 30844957725206168710621733)
  ·
    refine ⟨5783429573476156633241575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30844957725206168710621733 5783429573476156633241575)
    ·
      refine ⟨8675144360214234949862363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783429573476156633241575 8675144360214234949862363)
      ·
        refine ⟨13012716540321352424793545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675144360214234949862363 13012716540321352424793545)
        ·
          refine ⟨9759537405241014318595159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13012716540321352424793545 9759537405241014318595159)
          ·
            refine ⟨14639306107861521477892739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9759537405241014318595159 14639306107861521477892739)
            ·
              refine ⟨21958959161792282216839109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14639306107861521477892739 21958959161792282216839109)
              ·
                refine ⟨4117304842836052915657333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21958959161792282216839109 4117304842836052915657333)
                ·
                  refine ⟨385997329015879960842875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4117304842836052915657333 385997329015879960842875)
                  ·
                    rfl

theorem cell20_845693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_845693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845693 prefixEnd_845693 := by exact prefixLift 845693
  have htrace : WordTrace (prefixWord ++ tailWord_845693) baseStart_845693 baseEnd_845693 := by
    simpa [prefixWord, tailWord_845693, baseEnd_845693] using wordTrace_append hprefix tailTrace_845693
  have hstable : (prefixWord ++ tailWord_845693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845693).length < 2 ^ (prefixWord ++ tailWord_845693).sum := by decide
  have hdescent : baseEnd_845693 < baseStart_845693 := by decide
  rcases family_descends (prefixWord ++ tailWord_845693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845696 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_845696 : Nat := 118140960795 + 845696 * 2 ^ 59
def prefixEnd_845696 : Nat := 4983230072969 + 3 ^ 40 * 845696 * 2
def baseEnd_845696 : Nat := 385998698297625283742863

theorem tailTrace_845696 : CollatzResearch.WordTrace tailWord_845696 prefixEnd_845696 385998698297625283742863 := by
  unfold tailWord_845696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422533572097650111490471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20563378096130200148653961 15422533572097650111490471)
  ·
    refine ⟨23133800358146475167235707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15422533572097650111490471 23133800358146475167235707)
    ·
      refine ⟨34700700537219712750853561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23133800358146475167235707 34700700537219712750853561)
      ·
        refine ⟨26025525402914784563140171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34700700537219712750853561 26025525402914784563140171)
        ·
          refine ⟨39038288104372176844710257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26025525402914784563140171 39038288104372176844710257)
          ·
            refine ⟨29278716078279132633532693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39038288104372176844710257 29278716078279132633532693)
            ·
              refine ⟨1372439816169334342196845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29278716078279132633532693 1372439816169334342196845)
              ·
                refine ⟨514664931063500378323817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372439816169334342196845 514664931063500378323817)
                ·
                  refine ⟨385998698297625283742863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514664931063500378323817 385998698297625283742863)
                  ·
                    rfl

theorem cell20_845696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_845696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845696 prefixEnd_845696 := by exact prefixLift 845696
  have htrace : WordTrace (prefixWord ++ tailWord_845696) baseStart_845696 baseEnd_845696 := by
    simpa [prefixWord, tailWord_845696, baseEnd_845696] using wordTrace_append hprefix tailTrace_845696
  have hstable : (prefixWord ++ tailWord_845696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845696).length < 2 ^ (prefixWord ++ tailWord_845696).sum := by decide
  have hdescent : baseEnd_845696 < baseStart_845696 := by decide
  rcases family_descends (prefixWord ++ tailWord_845696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845706 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_845706 : Nat := 118140960795 + 845706 * 2 ^ 59
def prefixEnd_845706 : Nat := 4983230072969 + 3 ^ 40 * 845706 * 2
def baseEnd_845706 : Nat := 386003262570109693409489

theorem tailTrace_845706 : CollatzResearch.WordTrace tailWord_845706 prefixEnd_845706 386003262570109693409489 := by
  unfold tailWord_845706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711357968539767982711243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20563621249439381287229981 7711357968539767982711243)
  ·
    refine ⟨11567036952809651974066865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711357968539767982711243 11567036952809651974066865)
    ·
      refine ⟨8675277714607238980550149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11567036952809651974066865 8675277714607238980550149)
      ·
        refine ⟨1626614571488857308853153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8675277714607238980550149 1626614571488857308853153)
        ·
          refine ⟨1219960928616642981639865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1626614571488857308853153 1219960928616642981639865)
          ·
            refine ⟨914970696462482236229899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1219960928616642981639865 914970696462482236229899)
            ·
              refine ⟨1372456044693723354344849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914970696462482236229899 1372456044693723354344849)
              ·
                refine ⟨1029342033520292515758637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372456044693723354344849 1029342033520292515758637)
                ·
                  refine ⟨386003262570109693409489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029342033520292515758637 386003262570109693409489)
                  ·
                    rfl

theorem cell20_845706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_845706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845706 prefixEnd_845706 := by exact prefixLift 845706
  have htrace : WordTrace (prefixWord ++ tailWord_845706) baseStart_845706 baseEnd_845706 := by
    simpa [prefixWord, tailWord_845706, baseEnd_845706] using wordTrace_append hprefix tailTrace_845706
  have hstable : (prefixWord ++ tailWord_845706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845706).length < 2 ^ (prefixWord ++ tailWord_845706).sum := by decide
  have hdescent : baseEnd_845706 < baseStart_845706 := by decide
  rcases family_descends (prefixWord ++ tailWord_845706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845717 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_845717 : Nat := 118140960795 + 845717 * 2 ^ 59
def prefixEnd_845717 : Nat := 4983230072969 + 3 ^ 40 * 845717 * 2
def baseEnd_845717 : Nat := 386008283269842544042777

theorem tailTrace_845717 : CollatzResearch.WordTrace tailWord_845717 prefixEnd_845717 386008283269842544042777 := by
  unfold tailWord_845717
  simp only [CollatzResearch.WordTrace]
  refine ⟨30845833077119220809495405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20563888718079480539663603 30845833077119220809495405)
  ·
    refine ⟨11567187403919707803560777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30845833077119220809495405 11567187403919707803560777)
    ·
      refine ⟨8675390552939780852670583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11567187403919707803560777 8675390552939780852670583)
      ·
        refine ⟨13013085829409671279005875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675390552939780852670583 13013085829409671279005875)
        ·
          refine ⟨19519628744114506918508813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013085829409671279005875 19519628744114506918508813)
          ·
            refine ⟨7319860779042940094440805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19519628744114506918508813 7319860779042940094440805)
            ·
              refine ⟨1372473896070551267707651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7319860779042940094440805 1372473896070551267707651)
              ·
                refine ⟨2058710844105826901561477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372473896070551267707651 2058710844105826901561477)
                ·
                  refine ⟨386008283269842544042777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058710844105826901561477 386008283269842544042777)
                  ·
                    rfl

theorem cell20_845717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_845717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845717 prefixEnd_845717 := by exact prefixLift 845717
  have htrace : WordTrace (prefixWord ++ tailWord_845717) baseStart_845717 baseEnd_845717 := by
    simpa [prefixWord, tailWord_845717, baseEnd_845717] using wordTrace_append hprefix tailTrace_845717
  have hstable : (prefixWord ++ tailWord_845717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845717).length < 2 ^ (prefixWord ++ tailWord_845717).sum := by decide
  have hdescent : baseEnd_845717 < baseStart_845717 := by decide
  rcases family_descends (prefixWord ++ tailWord_845717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845772 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_845772 : Nat := 118140960795 + 845772 * 2 ^ 59
def prefixEnd_845772 : Nat := 4983230072969 + 3 ^ 40 * 845772 * 2
def baseEnd_845772 : Nat := 386033386768506797209219

theorem tailTrace_845772 : CollatzResearch.WordTrace tailWord_845772 prefixEnd_845772 386033386768506797209219 := by
  unfold tailWord_845772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15423919545959982601373785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20565226061279976801831713 15423919545959982601373785)
  ·
    refine ⟨11567939659469986951030339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15423919545959982601373785 11567939659469986951030339)
    ·
      refine ⟨17351909489204980426545509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11567939659469986951030339 17351909489204980426545509)
      ·
        refine ⟨3253483029225933829977283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17351909489204980426545509 3253483029225933829977283)
        ·
          refine ⟨4880224543838900744965925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253483029225933829977283 4880224543838900744965925)
          ·
            refine ⟨915042101969793889681111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4880224543838900744965925 915042101969793889681111)
            ·
              refine ⟨1372563152954690834521667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915042101969793889681111 1372563152954690834521667)
              ·
                refine ⟨2058844729432036251782501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372563152954690834521667 2058844729432036251782501)
                ·
                  refine ⟨386033386768506797209219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058844729432036251782501 386033386768506797209219)
                  ·
                    rfl

theorem cell20_845772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_845772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845772 prefixEnd_845772 := by exact prefixLift 845772
  have htrace : WordTrace (prefixWord ++ tailWord_845772) baseStart_845772 baseEnd_845772 := by
    simpa [prefixWord, tailWord_845772, baseEnd_845772] using wordTrace_append hprefix tailTrace_845772
  have hstable : (prefixWord ++ tailWord_845772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845772).length < 2 ^ (prefixWord ++ tailWord_845772).sum := by decide
  have hdescent : baseEnd_845772 < baseStart_845772 := by decide
  rcases family_descends (prefixWord ++ tailWord_845772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845782 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_845782 : Nat := 118140960795 + 845782 * 2 ^ 59
def prefixEnd_845782 : Nat := 4983230072969 + 3 ^ 40 * 845782 * 2
def baseEnd_845782 : Nat := 386037951040991206875845

theorem tailTrace_845782 : CollatzResearch.WordTrace tailWord_845782 prefixEnd_845782 386037951040991206875845 := by
  unfold tailWord_845782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928012738867733556913225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20565469214589157940407733 1928012738867733556913225)
  ·
    refine ⟨1446009554150800167684919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928012738867733556913225 1446009554150800167684919)
    ·
      refine ⟨2169014331226200251527379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446009554150800167684919 2169014331226200251527379)
      ·
        refine ⟨3253521496839300377291069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2169014331226200251527379 3253521496839300377291069)
        ·
          refine ⟨1220070561314737641484151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3253521496839300377291069 1220070561314737641484151)
          ·
            refine ⟨1830105841972106462226227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220070561314737641484151 1830105841972106462226227)
            ·
              refine ⟨2745158762958159693339341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830105841972106462226227 2745158762958159693339341)
              ·
                refine ⟨1029434536109309885002253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745158762958159693339341 1029434536109309885002253)
                ·
                  refine ⟨386037951040991206875845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029434536109309885002253 386037951040991206875845)
                  ·
                    rfl

theorem cell20_845782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_845782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845782 prefixEnd_845782 := by exact prefixLift 845782
  have htrace : WordTrace (prefixWord ++ tailWord_845782) baseStart_845782 baseEnd_845782 := by
    simpa [prefixWord, tailWord_845782, baseEnd_845782] using wordTrace_append hprefix tailTrace_845782
  have hstable : (prefixWord ++ tailWord_845782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845782).length < 2 ^ (prefixWord ++ tailWord_845782).sum := by decide
  have hdescent : baseEnd_845782 < baseStart_845782 := by decide
  rcases family_descends (prefixWord ++ tailWord_845782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845834 : List Nat := [3, 1, 2, 2, 5, 1, 1, 5]
def baseStart_845834 : Nat := 118140960795 + 845834 * 2 ^ 59
def prefixEnd_845834 : Nat := 4983230072969 + 3 ^ 40 * 845834 * 2
def baseEnd_845834 : Nat := 128687228419303379047433

theorem tailTrace_845834 : CollatzResearch.WordTrace tailWord_845834 prefixEnd_845834 128687228419303379047433 := by
  unfold tailWord_845834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7712525104423837447876139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20566733611796899861003037 7712525104423837447876139)
  ·
    refine ⟨11568787656635756171814209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7712525104423837447876139 11568787656635756171814209)
    ·
      refine ⟨8676590742476817128860657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11568787656635756171814209 8676590742476817128860657)
      ·
        refine ⟨6507443056857612846645493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8676590742476817128860657 6507443056857612846645493)
        ·
          refine ⟨610072786580401204373015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6507443056857612846645493 610072786580401204373015)
          ·
            refine ⟨915109179870601806559523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610072786580401204373015 915109179870601806559523)
            ·
              refine ⟨1372663769805902709839285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915109179870601806559523 1372663769805902709839285)
              ·
                refine ⟨128687228419303379047433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1372663769805902709839285 128687228419303379047433)
                ·
                  rfl

theorem cell20_845834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_845834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845834 prefixEnd_845834 := by exact prefixLift 845834
  have htrace : WordTrace (prefixWord ++ tailWord_845834) baseStart_845834 baseEnd_845834 := by
    simpa [prefixWord, tailWord_845834, baseEnd_845834] using wordTrace_append hprefix tailTrace_845834
  have hstable : (prefixWord ++ tailWord_845834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845834).length < 2 ^ (prefixWord ++ tailWord_845834).sum := by decide
  have hdescent : baseEnd_845834 < baseStart_845834 := by decide
  rcases family_descends (prefixWord ++ tailWord_845834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845897 : List Nat := [1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_845897 : Nat := 118140960795 + 845897 * 2 ^ 59
def prefixEnd_845897 : Nat := 4983230072969 + 3 ^ 40 * 845897 * 2
def baseEnd_845897 : Nat := 128696813391520639347347

theorem tailTrace_845897 : CollatzResearch.WordTrace tailWord_845897 prefixEnd_845897 128696813391520639347347 := by
  unfold tailWord_845897
  simp only [CollatzResearch.WordTrace]
  refine ⟨30852398216467111551047945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20568265477644741034031963 30852398216467111551047945)
  ·
    refine ⟨23139298662350333663285959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30852398216467111551047945 23139298662350333663285959)
    ·
      refine ⟨34708947993525500494928939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23139298662350333663285959 34708947993525500494928939)
      ·
        refine ⟨52063421990288250742393409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34708947993525500494928939 52063421990288250742393409)
        ·
          refine ⟨39047566492716188056795057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52063421990288250742393409 39047566492716188056795057)
          ·
            refine ⟨29285674869537141042596293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39047566492716188056795057 29285674869537141042596293)
            ·
              refine ⟨5491064038038213945486805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29285674869537141042596293 5491064038038213945486805)
              ·
                refine ⟨128696813391520639347347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5491064038038213945486805 128696813391520639347347)
                ·
                  rfl

theorem cell20_845897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_845897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845897 prefixEnd_845897 := by exact prefixLift 845897
  have htrace : WordTrace (prefixWord ++ tailWord_845897) baseStart_845897 baseEnd_845897 := by
    simpa [prefixWord, tailWord_845897, baseEnd_845897] using wordTrace_append hprefix tailTrace_845897
  have hstable : (prefixWord ++ tailWord_845897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845897).length < 2 ^ (prefixWord ++ tailWord_845897).sum := by decide
  have hdescent : baseEnd_845897 < baseStart_845897 := by decide
  rcases family_descends (prefixWord ++ tailWord_845897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845910 : List Nat := [5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_845910 : Nat := 118140960795 + 845910 * 2 ^ 59
def prefixEnd_845910 : Nat := 4983230072969 + 3 ^ 40 * 845910 * 2
def baseEnd_845910 : Nat := 128698791242930550202885

theorem tailTrace_845910 : CollatzResearch.WordTrace tailWord_845910 prefixEnd_845910 128698791242930550202885 := by
  unfold tailWord_845910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928304522838750923204449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20568581576946676514180789 1928304522838750923204449)
  ·
    refine ⟨1446228392129063192403337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928304522838750923204449 1446228392129063192403337)
    ·
      refine ⟨1084671294096797394302503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446228392129063192403337 1084671294096797394302503)
      ·
        refine ⟨1627006941145196091453755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084671294096797394302503 1627006941145196091453755)
        ·
          refine ⟨2440510411717794137180633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627006941145196091453755 2440510411717794137180633)
          ·
            refine ⟨1830382808788345602885475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2440510411717794137180633 1830382808788345602885475)
            ·
              refine ⟨2745574213182518404328213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830382808788345602885475 2745574213182518404328213)
              ·
                refine ⟨128698791242930550202885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2745574213182518404328213 128698791242930550202885)
                ·
                  rfl

theorem cell20_845910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_845910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845910 prefixEnd_845910 := by exact prefixLift 845910
  have htrace : WordTrace (prefixWord ++ tailWord_845910) baseStart_845910 baseEnd_845910 := by
    simpa [prefixWord, tailWord_845910, baseEnd_845910] using wordTrace_append hprefix tailTrace_845910
  have hstable : (prefixWord ++ tailWord_845910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845910).length < 2 ^ (prefixWord ++ tailWord_845910).sum := by decide
  have hdescent : baseEnd_845910 < baseStart_845910 := by decide
  rcases family_descends (prefixWord ++ tailWord_845910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845924 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 2]
def baseStart_845924 : Nat := 118140960795 + 845924 * 2 ^ 59
def prefixEnd_845924 : Nat := 4983230072969 + 3 ^ 40 * 845924 * 2
def baseEnd_845924 : Nat := 386102763710269824141931

theorem tailTrace_845924 : CollatzResearch.WordTrace tailWord_845924 prefixEnd_845924 386102763710269824141931 := by
  unfold tailWord_845924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426691493684647581140413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20568921991579530108187217 15426691493684647581140413)
  ·
    refine ⟨5785009310131742842927655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15426691493684647581140413 5785009310131742842927655)
    ·
      refine ⟨8677513965197614264391483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785009310131742842927655 8677513965197614264391483)
      ·
        refine ⟨13016270947796421396587225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677513965197614264391483 13016270947796421396587225)
        ·
          refine ⟨9762203210847316047440419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13016270947796421396587225 9762203210847316047440419)
          ·
            refine ⟨14643304816270974071160629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762203210847316047440419 14643304816270974071160629)
            ·
              refine ⟨1372809826525403819171309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14643304816270974071160629 1372809826525403819171309)
              ·
                refine ⟨514803684947026432189241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372809826525403819171309 514803684947026432189241)
                ·
                  refine ⟨386102763710269824141931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514803684947026432189241 386102763710269824141931)
                  ·
                    rfl

theorem cell20_845924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_845924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845924 prefixEnd_845924 := by exact prefixLift 845924
  have htrace : WordTrace (prefixWord ++ tailWord_845924) baseStart_845924 baseEnd_845924 := by
    simpa [prefixWord, tailWord_845924, baseEnd_845924] using wordTrace_append hprefix tailTrace_845924
  have hstable : (prefixWord ++ tailWord_845924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845924).length < 2 ^ (prefixWord ++ tailWord_845924).sum := by decide
  have hdescent : baseEnd_845924 < baseStart_845924 := by decide
  rcases family_descends (prefixWord ++ tailWord_845924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845935 : List Nat := [1, 1, 2, 1, 3, 4, 8]
def baseStart_845935 : Nat := 118140960795 + 845935 * 2 ^ 59
def prefixEnd_845935 : Nat := 4983230072969 + 3 ^ 40 * 845935 * 2
def baseEnd_845935 : Nat := 42900864934444741641691

theorem tailTrace_845935 : CollatzResearch.WordTrace tailWord_845935 prefixEnd_845935 42900864934444741641691 := by
  unfold tailWord_845935
  simp only [CollatzResearch.WordTrace]
  refine ⟨30853784190329444040931259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20569189460219629360620839 30853784190329444040931259)
  ·
    refine ⟨46280676285494166061396889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30853784190329444040931259 46280676285494166061396889)
    ·
      refine ⟨34710507214120624546047667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46280676285494166061396889 34710507214120624546047667)
      ·
        refine ⟨52065760821180936819071501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34710507214120624546047667 52065760821180936819071501)
        ·
          refine ⟨19524660307942851307151813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52065760821180936819071501 19524660307942851307151813)
          ·
            refine ⟨3660873807739284620090965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19524660307942851307151813 3660873807739284620090965)
            ·
              refine ⟨42900864934444741641691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3660873807739284620090965 42900864934444741641691)
              ·
                rfl

theorem cell20_845935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_845935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845935 prefixEnd_845935 := by exact prefixLift 845935
  have htrace : WordTrace (prefixWord ++ tailWord_845935) baseStart_845935 baseEnd_845935 := by
    simpa [prefixWord, tailWord_845935, baseEnd_845935] using wordTrace_append hprefix tailTrace_845935
  have hstable : (prefixWord ++ tailWord_845935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845935).length < 2 ^ (prefixWord ++ tailWord_845935).sum := by decide
  have hdescent : baseEnd_845935 < baseStart_845935 := by decide
  rcases family_descends (prefixWord ++ tailWord_845935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845945 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_845945 : Nat := 118140960795 + 845945 * 2 ^ 59
def prefixEnd_845945 : Nat := 4983230072969 + 3 ^ 40 * 845945 * 2
def baseEnd_845945 : Nat := 386112348682487084441845

theorem tailTrace_845945 : CollatzResearch.WordTrace tailWord_845945 prefixEnd_845945 386112348682487084441845 := by
  unfold tailWord_845945
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854148920293215748795289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20569432613528810499196859 30854148920293215748795289)
  ·
    refine ⟨23140611690219911811596467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30854148920293215748795289 23140611690219911811596467)
    ·
      refine ⟨34710917535329867717394701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23140611690219911811596467 34710917535329867717394701)
      ·
        refine ⟨13016594075748700394023013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34710917535329867717394701 13016594075748700394023013)
        ·
          refine ⟨2440611389202881323879315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13016594075748700394023013 2440611389202881323879315)
          ·
            refine ⟨3660917083804321985818973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440611389202881323879315 3660917083804321985818973)
            ·
              refine ⟨1372843906426620744682115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3660917083804321985818973 1372843906426620744682115)
              ·
                refine ⟨2059265859639931117023173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372843906426620744682115 2059265859639931117023173)
                ·
                  refine ⟨386112348682487084441845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059265859639931117023173 386112348682487084441845)
                  ·
                    rfl

theorem cell20_845945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_845945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845945 prefixEnd_845945 := by exact prefixLift 845945
  have htrace : WordTrace (prefixWord ++ tailWord_845945) baseStart_845945 baseEnd_845945 := by
    simpa [prefixWord, tailWord_845945, baseEnd_845945] using wordTrace_append hprefix tailTrace_845945
  have hstable : (prefixWord ++ tailWord_845945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845945).length < 2 ^ (prefixWord ++ tailWord_845945).sum := by decide
  have hdescent : baseEnd_845945 < baseStart_845945 := by decide
  rcases family_descends (prefixWord ++ tailWord_845945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845955 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 3]
def baseStart_845955 : Nat := 118140960795 + 845955 * 2 ^ 59
def prefixEnd_845955 : Nat := 4983230072969 + 3 ^ 40 * 845955 * 2
def baseEnd_845955 : Nat := 386116912954971494108471

theorem tailTrace_845955 : CollatzResearch.WordTrace tailWord_845955 prefixEnd_845955 386116912954971494108471 := by
  unfold tailWord_845955
  simp only [CollatzResearch.WordTrace]
  refine ⟨30854513650256987456659319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20569675766837991637772879 30854513650256987456659319)
  ·
    refine ⟨46281770475385481184988979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30854513650256987456659319 46281770475385481184988979)
    ·
      refine ⟨69422655713078221777483469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46281770475385481184988979 69422655713078221777483469)
      ·
        refine ⟨26033495892404333166556301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69422655713078221777483469 26033495892404333166556301)
        ·
          refine ⟨9762560959651624937458613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26033495892404333166556301 9762560959651624937458613)
          ·
            refine ⟨915240089967339837886745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9762560959651624937458613 915240089967339837886745)
            ·
              refine ⟨686430067475504878415059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915240089967339837886745 686430067475504878415059)
              ·
                refine ⟨1029645101213257317622589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686430067475504878415059 1029645101213257317622589)
                ·
                  refine ⟨386116912954971494108471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029645101213257317622589 386116912954971494108471)
                  ·
                    rfl

theorem cell20_845955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_845955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845955 prefixEnd_845955 := by exact prefixLift 845955
  have htrace : WordTrace (prefixWord ++ tailWord_845955) baseStart_845955 baseEnd_845955 := by
    simpa [prefixWord, tailWord_845955, baseEnd_845955] using wordTrace_append hprefix tailTrace_845955
  have hstable : (prefixWord ++ tailWord_845955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845955).length < 2 ^ (prefixWord ++ tailWord_845955).sum := by decide
  have hdescent : baseEnd_845955 < baseStart_845955 := by decide
  rcases family_descends (prefixWord ++ tailWord_845955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_845973 : List Nat := [1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_845973 : Nat := 118140960795 + 845973 * 2 ^ 59
def prefixEnd_845973 : Nat := 4983230072969 + 3 ^ 40 * 845973 * 2
def baseEnd_845973 : Nat := 128708376215147810502799

theorem tailTrace_845973 : CollatzResearch.WordTrace tailWord_845973 prefixEnd_845973 128708376215147810502799 := by
  unfold tailWord_845973
  simp only [CollatzResearch.WordTrace]
  refine ⟨30855170164191776530814573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20570113442794517687209715 30855170164191776530814573)
  ·
    refine ⟨11570688811571916199055465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30855170164191776530814573 11570688811571916199055465)
    ·
      refine ⟨8678016608678937149291599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11570688811571916199055465 8678016608678937149291599)
      ·
        refine ⟨13017024913018405723937399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678016608678937149291599 13017024913018405723937399)
        ·
          refine ⟨19525537369527608585906099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13017024913018405723937399 19525537369527608585906099)
          ·
            refine ⟨29288306054291412878859149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19525537369527608585906099 29288306054291412878859149)
            ·
              refine ⟨10983114770359279829572181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29288306054291412878859149 10983114770359279829572181)
              ·
                refine ⟨128708376215147810502799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10983114770359279829572181 128708376215147810502799)
                ·
                  rfl

theorem cell20_845973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_845973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_845973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_845973 prefixEnd_845973 := by exact prefixLift 845973
  have htrace : WordTrace (prefixWord ++ tailWord_845973) baseStart_845973 baseEnd_845973 := by
    simpa [prefixWord, tailWord_845973, baseEnd_845973] using wordTrace_append hprefix tailTrace_845973
  have hstable : (prefixWord ++ tailWord_845973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_845973).length < 2 ^ (prefixWord ++ tailWord_845973).sum := by decide
  have hdescent : baseEnd_845973 < baseStart_845973 := by decide
  rcases family_descends (prefixWord ++ tailWord_845973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846049 : List Nat := [1, 2, 3, 1, 3, 1, 9]
def baseStart_846049 : Nat := 118140960795 + 846049 * 2 ^ 59
def prefixEnd_846049 : Nat := 4983230072969 + 3 ^ 40 * 846049 * 2
def baseEnd_846049 : Nat := 42906646346258327219417

theorem tailTrace_846049 : CollatzResearch.WordTrace tailWord_846049 prefixEnd_846049 42906646346258327219417 := by
  unfold tailWord_846049
  simp only [CollatzResearch.WordTrace]
  refine ⟨30857942111916441510581201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20571961407944294340387467 30857942111916441510581201)
  ·
    refine ⟨23143456583937331132935901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30857942111916441510581201 23143456583937331132935901)
    ·
      refine ⟨8678796218976499174850963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23143456583937331132935901 8678796218976499174850963)
      ·
        refine ⟨13018194328464748762276445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8678796218976499174850963 13018194328464748762276445)
        ·
          refine ⟨4881822873174280785853667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13018194328464748762276445 4881822873174280785853667)
          ·
            refine ⟨7322734309761421178780501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881822873174280785853667 7322734309761421178780501)
            ·
              refine ⟨42906646346258327219417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7322734309761421178780501 42906646346258327219417)
              ·
                rfl

theorem cell20_846049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_846049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846049 prefixEnd_846049 := by exact prefixLift 846049
  have htrace : WordTrace (prefixWord ++ tailWord_846049) baseStart_846049 baseEnd_846049 := by
    simpa [prefixWord, tailWord_846049, baseEnd_846049] using wordTrace_append hprefix tailTrace_846049
  have hstable : (prefixWord ++ tailWord_846049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846049).length < 2 ^ (prefixWord ++ tailWord_846049).sum := by decide
  have hdescent : baseEnd_846049 < baseStart_846049 := by decide
  rcases family_descends (prefixWord ++ tailWord_846049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846059 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 2]
def baseStart_846059 : Nat := 118140960795 + 846059 * 2 ^ 59
def prefixEnd_846059 : Nat := 4983230072969 + 3 ^ 40 * 846059 * 2
def baseEnd_846059 : Nat := 386164381388809354641379

theorem tailTrace_846059 : CollatzResearch.WordTrace tailWord_846059 prefixEnd_846059 386164381388809354641379 := by
  unfold tailWord_846059
  simp only [CollatzResearch.WordTrace]
  refine ⟨30858306841880213218445231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20572204561253475478963487 30858306841880213218445231)
  ·
    refine ⟨46287460262820319827667847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30858306841880213218445231 46287460262820319827667847)
    ·
      refine ⟨69431190394230479741501771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46287460262820319827667847 69431190394230479741501771)
      ·
        refine ⟨104146785591345719612252657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69431190394230479741501771 104146785591345719612252657)
        ·
          refine ⟨78110089193509289709189493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104146785591345719612252657 78110089193509289709189493)
          ·
            refine ⟨7322820861891495910236515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78110089193509289709189493 7322820861891495910236515)
            ·
              refine ⟨10984231292837243865354773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322820861891495910236515 10984231292837243865354773)
              ·
                refine ⟨514885841851745806188505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10984231292837243865354773 514885841851745806188505)
                ·
                  refine ⟨386164381388809354641379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514885841851745806188505 386164381388809354641379)
                  ·
                    rfl

theorem cell20_846059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 2].length) (baseStart_846059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846059 prefixEnd_846059 := by exact prefixLift 846059
  have htrace : WordTrace (prefixWord ++ tailWord_846059) baseStart_846059 baseEnd_846059 := by
    simpa [prefixWord, tailWord_846059, baseEnd_846059] using wordTrace_append hprefix tailTrace_846059
  have hstable : (prefixWord ++ tailWord_846059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846059).length < 2 ^ (prefixWord ++ tailWord_846059).sum := by decide
  have hdescent : baseEnd_846059 < baseStart_846059 := by decide
  rcases family_descends (prefixWord ++ tailWord_846059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846080 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_846080 : Nat := 118140960795 + 846080 * 2 ^ 59
def prefixEnd_846080 : Nat := 4983230072969 + 3 ^ 40 * 846080 * 2
def baseEnd_846080 : Nat := 386173966361026614941293

theorem tailTrace_846080 : CollatzResearch.WordTrace tailWord_846080 prefixEnd_846080 386173966361026614941293 := by
  unfold tailWord_846080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429536387402066902479847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20572715183202755869973129 15429536387402066902479847)
  ·
    refine ⟨23144304581103100353719771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15429536387402066902479847 23144304581103100353719771)
    ·
      refine ⟨34716456871654650530579657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23144304581103100353719771 34716456871654650530579657)
      ·
        refine ⟨26037342653740987897934743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34716456871654650530579657 26037342653740987897934743)
        ·
          refine ⟨39056013980611481846902115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26037342653740987897934743 39056013980611481846902115)
          ·
            refine ⟨58584020970917222770353173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39056013980611481846902115 58584020970917222770353173)
            ·
              refine ⟨2746125983011744817360305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58584020970917222770353173 2746125983011744817360305)
              ·
                refine ⟨2059594487258808613020229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746125983011744817360305 2059594487258808613020229)
                ·
                  refine ⟨386173966361026614941293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059594487258808613020229 386173966361026614941293)
                  ·
                    rfl

theorem cell20_846080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_846080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846080 prefixEnd_846080 := by exact prefixLift 846080
  have htrace : WordTrace (prefixWord ++ tailWord_846080) baseStart_846080 baseEnd_846080 := by
    simpa [prefixWord, tailWord_846080, baseEnd_846080] using wordTrace_append hprefix tailTrace_846080
  have hstable : (prefixWord ++ tailWord_846080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846080).length < 2 ^ (prefixWord ++ tailWord_846080).sum := by decide
  have hdescent : baseEnd_846080 < baseStart_846080 := by decide
  rcases family_descends (prefixWord ++ tailWord_846080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846111 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_846111 : Nat := 118140960795 + 846111 * 2 ^ 59
def prefixEnd_846111 : Nat := 4983230072969 + 3 ^ 40 * 846111 * 2
def baseEnd_846111 : Nat := 386188115605728284907833

theorem tailTrace_846111 : CollatzResearch.WordTrace tailWord_846111 prefixEnd_846111 386188115605728284907833 := by
  unfold tailWord_846111
  simp only [CollatzResearch.WordTrace]
  refine ⟨30860203437691826099338187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20573468958461217399558791 30860203437691826099338187)
  ·
    refine ⟨46290305156537739149007281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30860203437691826099338187 46290305156537739149007281)
    ·
      refine ⟨34717728867403304361755461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46290305156537739149007281 34717728867403304361755461)
      ·
        refine ⟨6509574162638119567829149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34717728867403304361755461 6509574162638119567829149)
        ·
          refine ⟨2441090310989294837935931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6509574162638119567829149 2441090310989294837935931)
          ·
            refine ⟨3661635466483942256903897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2441090310989294837935931 3661635466483942256903897)
            ·
              refine ⟨2746226599862956692677923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3661635466483942256903897 2746226599862956692677923)
              ·
                refine ⟨4119339899794435039016885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746226599862956692677923 4119339899794435039016885)
                ·
                  refine ⟨386188115605728284907833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4119339899794435039016885 386188115605728284907833)
                  ·
                    rfl

theorem cell20_846111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_846111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846111 prefixEnd_846111 := by exact prefixLift 846111
  have htrace : WordTrace (prefixWord ++ tailWord_846111) baseStart_846111 baseEnd_846111 := by
    simpa [prefixWord, tailWord_846111, baseEnd_846111] using wordTrace_append hprefix tailTrace_846111
  have hstable : (prefixWord ++ tailWord_846111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846111).length < 2 ^ (prefixWord ++ tailWord_846111).sum := by decide
  have hdescent : baseEnd_846111 < baseStart_846111 := by decide
  rcases family_descends (prefixWord ++ tailWord_846111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846114 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_846114 : Nat := 118140960795 + 846114 * 2 ^ 59
def prefixEnd_846114 : Nat := 4983230072969 + 3 ^ 40 * 846114 * 2
def baseEnd_846114 : Nat := 386189484887473607807821

theorem tailTrace_846114 : CollatzResearch.WordTrace tailWord_846114 prefixEnd_846114 386189484887473607807821 := by
  unfold tailWord_846114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715078214170239402924349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20573541904453971741131597 7715078214170239402924349)
  ·
    refine ⟨2893154330313839776096631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7715078214170239402924349 2893154330313839776096631)
    ·
      refine ⟨4339731495470759664144947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893154330313839776096631 4339731495470759664144947)
      ·
        refine ⟨6509597243206139496217421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339731495470759664144947 6509597243206139496217421)
        ·
          refine ⟨2441098966202302311081533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6509597243206139496217421 2441098966202302311081533)
          ·
            refine ⟨915412112325863366655575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2441098966202302311081533 915412112325863366655575)
            ·
              refine ⟨1373118168488795049983363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915412112325863366655575 1373118168488795049983363)
              ·
                refine ⟨2059677252733192574975045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373118168488795049983363 2059677252733192574975045)
                ·
                  refine ⟨386189484887473607807821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059677252733192574975045 386189484887473607807821)
                  ·
                    rfl

theorem cell20_846114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_846114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846114 prefixEnd_846114 := by exact prefixLift 846114
  have htrace : WordTrace (prefixWord ++ tailWord_846114) baseStart_846114 baseEnd_846114 := by
    simpa [prefixWord, tailWord_846114, baseEnd_846114] using wordTrace_append hprefix tailTrace_846114
  have hstable : (prefixWord ++ tailWord_846114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846114).length < 2 ^ (prefixWord ++ tailWord_846114).sum := by decide
  have hdescent : baseEnd_846114 < baseStart_846114 := by decide
  rcases family_descends (prefixWord ++ tailWord_846114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846142 : List Nat := [4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_846142 : Nat := 118140960795 + 846142 * 2 ^ 59
def prefixEnd_846142 : Nat := 4983230072969 + 3 ^ 40 * 846142 * 2
def baseEnd_846142 : Nat := 128734088283476651624791

theorem tailTrace_846142 : CollatzResearch.WordTrace tailWord_846142 prefixEnd_846142 128734088283476651624791 := by
  unfold tailWord_846142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857666762572439799214585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20574222733719678929144453 3857666762572439799214585)
  ·
    refine ⟨2893250071929329849410939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3857666762572439799214585 2893250071929329849410939)
    ·
      refine ⟨4339875107893994774116409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893250071929329849410939 4339875107893994774116409)
      ·
        refine ⟨3254906330920496080587307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4339875107893994774116409 3254906330920496080587307)
        ·
          refine ⟨4882359496380744120880961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254906330920496080587307 4882359496380744120880961)
          ·
            refine ⟨3661769622285558090660721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4882359496380744120880961 3661769622285558090660721)
            ·
              refine ⟨2746327216714168567995541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3661769622285558090660721 2746327216714168567995541)
              ·
                refine ⟨128734088283476651624791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2746327216714168567995541 128734088283476651624791)
                ·
                  rfl

theorem cell20_846142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_846142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846142 prefixEnd_846142 := by exact prefixLift 846142
  have htrace : WordTrace (prefixWord ++ tailWord_846142) baseStart_846142 baseEnd_846142 := by
    simpa [prefixWord, tailWord_846142, baseEnd_846142] using wordTrace_append hprefix tailTrace_846142
  have hstable : (prefixWord ++ tailWord_846142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846142).length < 2 ^ (prefixWord ++ tailWord_846142).sum := by decide
  have hdescent : baseEnd_846142 < baseStart_846142 := by decide
  rcases family_descends (prefixWord ++ tailWord_846142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846194 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_846194 : Nat := 118140960795 + 846194 * 2 ^ 59
def prefixEnd_846194 : Nat := 4983230072969 + 3 ^ 40 * 846194 * 2
def baseEnd_846194 : Nat := 386225999067348885140827

theorem tailTrace_846194 : CollatzResearch.WordTrace tailWord_846194 prefixEnd_846194 386225999067348885140827 := by
  unfold tailWord_846194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7715807674097782818652409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20575487130927420849739757 7715807674097782818652409)
  ·
    refine ⟨5786855755573337113989307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7715807674097782818652409 5786855755573337113989307)
    ·
      refine ⟨8680283633360005670983961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786855755573337113989307 8680283633360005670983961)
      ·
        refine ⟨6510212725020004253237971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8680283633360005670983961 6510212725020004253237971)
        ·
          refine ⟨9765319087530006379856957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510212725020004253237971 9765319087530006379856957)
          ·
            refine ⟨3661994657823752392446359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9765319087530006379856957 3661994657823752392446359)
            ·
              refine ⟨5492991986735628588669539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661994657823752392446359 5492991986735628588669539)
              ·
                refine ⟨8239487980103442883004309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492991986735628588669539 8239487980103442883004309)
                ·
                  refine ⟨386225999067348885140827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8239487980103442883004309 386225999067348885140827)
                  ·
                    rfl

theorem cell20_846194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_846194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846194 prefixEnd_846194 := by exact prefixLift 846194
  have htrace : WordTrace (prefixWord ++ tailWord_846194) baseStart_846194 baseEnd_846194 := by
    simpa [prefixWord, tailWord_846194, baseEnd_846194] using wordTrace_append hprefix tailTrace_846194
  have hstable : (prefixWord ++ tailWord_846194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846194).length < 2 ^ (prefixWord ++ tailWord_846194).sum := by decide
  have hdescent : baseEnd_846194 < baseStart_846194 := by decide
  rcases family_descends (prefixWord ++ tailWord_846194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846197 : List Nat := [1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_846197 : Nat := 118140960795 + 846197 * 2 ^ 59
def prefixEnd_846197 : Nat := 4983230072969 + 3 ^ 40 * 846197 * 2
def baseEnd_846197 : Nat := 128742456116364736013605

theorem tailTrace_846197 : CollatzResearch.WordTrace tailWord_846197 prefixEnd_846197 128742456116364736013605 := by
  unfold tailWord_846197
  simp only [CollatzResearch.WordTrace]
  refine ⟨30863340115380262786968845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20575560076920175191312563 30863340115380262786968845)
  ·
    refine ⟨11573752543267598545113317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30863340115380262786968845 11573752543267598545113317)
    ·
      refine ⟨2170078601862674727208747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11573752543267598545113317 2170078601862674727208747)
      ·
        refine ⟨3255117902794012090813121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170078601862674727208747 3255117902794012090813121)
        ·
          refine ⟨2441338427095509068109841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3255117902794012090813121 2441338427095509068109841)
          ·
            refine ⟨1831003820321631801082381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2441338427095509068109841 1831003820321631801082381)
            ·
              refine ⟨686626432620611925405893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1831003820321631801082381 686626432620611925405893)
              ·
                refine ⟨128742456116364736013605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686626432620611925405893 128742456116364736013605)
                ·
                  rfl

theorem cell20_846197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_846197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846197 prefixEnd_846197 := by exact prefixLift 846197
  have htrace : WordTrace (prefixWord ++ tailWord_846197) baseStart_846197 baseEnd_846197 := by
    simpa [prefixWord, tailWord_846197, baseEnd_846197] using wordTrace_append hprefix tailTrace_846197
  have hstable : (prefixWord ++ tailWord_846197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846197).length < 2 ^ (prefixWord ++ tailWord_846197).sum := by decide
  have hdescent : baseEnd_846197 < baseStart_846197 := by decide
  rcases family_descends (prefixWord ++ tailWord_846197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846228 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_846228 : Nat := 118140960795 + 846228 * 2 ^ 59
def prefixEnd_846228 : Nat := 4983230072969 + 3 ^ 40 * 846228 * 2
def baseEnd_846228 : Nat := 386241517593795878007355

theorem tailTrace_846228 : CollatzResearch.WordTrace tailWord_846228 prefixEnd_846228 386241517593795878007355 := by
  unfold tailWord_846228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15432235389133977540673669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20576313852178636720898225 15432235389133977540673669)
  ·
    refine ⟨2893544135462620788876313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15432235389133977540673669 2893544135462620788876313)
    ·
      refine ⟨2170158101596965591657235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2893544135462620788876313 2170158101596965591657235)
      ·
        refine ⟨3255237152395448387485853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170158101596965591657235 3255237152395448387485853)
        ·
          refine ⟨1220713932148293145307195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3255237152395448387485853 1220713932148293145307195)
          ·
            refine ⟨1831070898222439717960793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220713932148293145307195 1831070898222439717960793)
            ·
              refine ⟨1373303173666829788470595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831070898222439717960793 1373303173666829788470595)
              ·
                refine ⟨2059954760500244682705893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373303173666829788470595 2059954760500244682705893)
                ·
                  refine ⟨386241517593795878007355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059954760500244682705893 386241517593795878007355)
                  ·
                    rfl

theorem cell20_846228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_846228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846228 prefixEnd_846228 := by exact prefixLift 846228
  have htrace : WordTrace (prefixWord ++ tailWord_846228) baseStart_846228 baseEnd_846228 := by
    simpa [prefixWord, tailWord_846228, baseEnd_846228] using wordTrace_append hprefix tailTrace_846228
  have hstable : (prefixWord ++ tailWord_846228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846228).length < 2 ^ (prefixWord ++ tailWord_846228).sum := by decide
  have hdescent : baseEnd_846228 < baseStart_846228 := by decide
  rcases family_descends (prefixWord ++ tailWord_846228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846238 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_846238 : Nat := 118140960795 + 846238 * 2 ^ 59
def prefixEnd_846238 : Nat := 4983230072969 + 3 ^ 40 * 846238 * 2
def baseEnd_846238 : Nat := 386246081866280287673981

theorem tailTrace_846238 : CollatzResearch.WordTrace tailWord_846238 prefixEnd_846238 386246081866280287673981 := by
  unfold tailWord_846238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858104438528965848651421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20576557005487817859474245 3858104438528965848651421)
  ·
    refine ⟨1446789164448362193244283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3858104438528965848651421 1446789164448362193244283)
    ·
      refine ⟨2170183746672543289866425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446789164448362193244283 2170183746672543289866425)
      ·
        refine ⟨1627637810004407467399819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170183746672543289866425 1627637810004407467399819)
        ·
          refine ⟨2441456715006611201099729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1627637810004407467399819 2441456715006611201099729)
          ·
            refine ⟨1831092536254958400824797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2441456715006611201099729 1831092536254958400824797)
            ·
              refine ⟨686659701095609400309299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1831092536254958400824797 686659701095609400309299)
              ·
                refine ⟨1029989551643414100463949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686659701095609400309299 1029989551643414100463949)
                ·
                  refine ⟨386246081866280287673981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1029989551643414100463949 386246081866280287673981)
                  ·
                    rfl

theorem cell20_846238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_846238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846238 prefixEnd_846238 := by exact prefixLift 846238
  have htrace : WordTrace (prefixWord ++ tailWord_846238) baseStart_846238 baseEnd_846238 := by
    simpa [prefixWord, tailWord_846238, baseEnd_846238] using wordTrace_append hprefix tailTrace_846238
  have hstable : (prefixWord ++ tailWord_846238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846238).length < 2 ^ (prefixWord ++ tailWord_846238).sum := by decide
  have hdescent : baseEnd_846238 < baseStart_846238 := by decide
  rcases family_descends (prefixWord ++ tailWord_846238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846239 : List Nat := [1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_846239 : Nat := 118140960795 + 846239 * 2 ^ 59
def prefixEnd_846239 : Nat := 4983230072969 + 3 ^ 40 * 846239 * 2
def baseEnd_846239 : Nat := 128748846097842909546881

theorem tailTrace_846239 : CollatzResearch.WordTrace tailWord_846239 prefixEnd_846239 128748846097842909546881 := by
  unfold tailWord_846239
  simp only [CollatzResearch.WordTrace]
  refine ⟨30864871981228103959997771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20576581320818735973331847 30864871981228103959997771)
  ·
    refine ⟨46297307971842155939996657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30864871981228103959997771 46297307971842155939996657)
    ·
      refine ⟨34722980978881616954997493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46297307971842155939996657 34722980978881616954997493)
      ·
        refine ⟨3255279466770151589531015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34722980978881616954997493 3255279466770151589531015)
        ·
          refine ⟨4882919200155227384296523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255279466770151589531015 4882919200155227384296523)
          ·
            refine ⟨7324378800232841076444785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882919200155227384296523 7324378800232841076444785)
            ·
              refine ⟨5493284100174630807333589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7324378800232841076444785 5493284100174630807333589)
              ·
                refine ⟨128748846097842909546881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5493284100174630807333589 128748846097842909546881)
                ·
                  rfl

theorem cell20_846239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_846239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846239 prefixEnd_846239 := by exact prefixLift 846239
  have htrace : WordTrace (prefixWord ++ tailWord_846239) baseStart_846239 baseEnd_846239 := by
    simpa [prefixWord, tailWord_846239, baseEnd_846239] using wordTrace_append hprefix tailTrace_846239
  have hstable : (prefixWord ++ tailWord_846239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846239).length < 2 ^ (prefixWord ++ tailWord_846239).sum := by decide
  have hdescent : baseEnd_846239 < baseStart_846239 := by decide
  rcases family_descends (prefixWord ++ tailWord_846239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846270 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_846270 : Nat := 118140960795 + 846270 * 2 ^ 59
def prefixEnd_846270 : Nat := 4983230072969 + 3 ^ 40 * 846270 * 2
def baseEnd_846270 : Nat := 386260687538230398607183

theorem tailTrace_846270 : CollatzResearch.WordTrace tailWord_846270 prefixEnd_846270 386260687538230398607183 := by
  unfold tailWord_846270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858250330514474531797033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20577335096077197502917509 3858250330514474531797033)
  ·
    refine ⟨2893687747885855898847775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3858250330514474531797033 2893687747885855898847775)
    ·
      refine ⟨4340531621828783848271663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893687747885855898847775 4340531621828783848271663)
      ·
        refine ⟨6510797432743175772407495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340531621828783848271663 6510797432743175772407495)
        ·
          refine ⟨9766196149114763658611243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510797432743175772407495 9766196149114763658611243)
          ·
            refine ⟨14649294223672145487916865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766196149114763658611243 14649294223672145487916865)
            ·
              refine ⟨10986970667754109115937649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14649294223672145487916865 10986970667754109115937649)
              ·
                refine ⟨8240228000815581836953237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10986970667754109115937649 8240228000815581836953237)
                ·
                  refine ⟨386260687538230398607183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8240228000815581836953237 386260687538230398607183)
                  ·
                    rfl

theorem cell20_846270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_846270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846270 prefixEnd_846270 := by exact prefixLift 846270
  have htrace : WordTrace (prefixWord ++ tailWord_846270) baseStart_846270 baseEnd_846270 := by
    simpa [prefixWord, tailWord_846270, baseEnd_846270] using wordTrace_append hprefix tailTrace_846270
  have hstable : (prefixWord ++ tailWord_846270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846270).length < 2 ^ (prefixWord ++ tailWord_846270).sum := by decide
  have hdescent : baseEnd_846270 < baseStart_846270 := by decide
  rcases family_descends (prefixWord ++ tailWord_846270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846339 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_846339 : Nat := 118140960795 + 846339 * 2 ^ 59
def prefixEnd_846339 : Nat := 4983230072969 + 3 ^ 40 * 846339 * 2
def baseEnd_846339 : Nat := 386292181018372825306901

theorem tailTrace_846339 : CollatzResearch.WordTrace tailWord_846339 prefixEnd_846339 386292181018372825306901 := by
  unfold tailWord_846339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30868519280865821038638071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20579012853910547359092047 30868519280865821038638071)
  ·
    refine ⟨46302778921298731557957107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30868519280865821038638071 46302778921298731557957107)
    ·
      refine ⟨69454168381948097336935661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46302778921298731557957107 69454168381948097336935661)
      ·
        refine ⟨26045313143230536501350873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69454168381948097336935661 26045313143230536501350873)
        ·
          refine ⟨19533984857422902376013155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26045313143230536501350873 19533984857422902376013155)
          ·
            refine ⟨29300977286134353564019733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19533984857422902376013155 29300977286134353564019733)
            ·
              refine ⟨1373483310287547823313425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29300977286134353564019733 1373483310287547823313425)
              ·
                refine ⟨1030112482715660867485069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373483310287547823313425 1030112482715660867485069)
                ·
                  refine ⟨386292181018372825306901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030112482715660867485069 386292181018372825306901)
                  ·
                    rfl

theorem cell20_846339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_846339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846339 prefixEnd_846339 := by exact prefixLift 846339
  have htrace : WordTrace (prefixWord ++ tailWord_846339) baseStart_846339 baseEnd_846339 := by
    simpa [prefixWord, tailWord_846339, baseEnd_846339] using wordTrace_append hprefix tailTrace_846339
  have hstable : (prefixWord ++ tailWord_846339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846339).length < 2 ^ (prefixWord ++ tailWord_846339).sum := by decide
  have hdescent : baseEnd_846339 < baseStart_846339 := by decide
  rcases family_descends (prefixWord ++ tailWord_846339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846346 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_846346 : Nat := 118140960795 + 846346 * 2 ^ 59
def prefixEnd_846346 : Nat := 4983230072969 + 3 ^ 40 * 846346 * 2
def baseEnd_846346 : Nat := 386295376009111912073539

theorem tailTrace_846346 : CollatzResearch.WordTrace tailWord_846346 prefixEnd_846346 386295376009111912073539 := by
  unfold tailWord_846346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717193647960115308535723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20579183061226974156095261 7717193647960115308535723)
  ·
    refine ⟨11575790471940172962803585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7717193647960115308535723 11575790471940172962803585)
    ·
      refine ⟨8681842853955129722102689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11575790471940172962803585 8681842853955129722102689)
      ·
        refine ⟨6511382140466347291577017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8681842853955129722102689 6511382140466347291577017)
        ·
          refine ⟨4883536605349760468682763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511382140466347291577017 4883536605349760468682763)
          ·
            refine ⟨7325304908024640703024145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883536605349760468682763 7325304908024640703024145)
            ·
              refine ⟨5493978681018480527268109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7325304908024640703024145 5493978681018480527268109)
              ·
                refine ⟨2060242005381930197725541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5493978681018480527268109 2060242005381930197725541)
                ·
                  refine ⟨386295376009111912073539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060242005381930197725541 386295376009111912073539)
                  ·
                    rfl

theorem cell20_846346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_846346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846346 prefixEnd_846346 := by exact prefixLift 846346
  have htrace : WordTrace (prefixWord ++ tailWord_846346) baseStart_846346 baseEnd_846346 := by
    simpa [prefixWord, tailWord_846346, baseEnd_846346] using wordTrace_append hprefix tailTrace_846346
  have hstable : (prefixWord ++ tailWord_846346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846346).length < 2 ^ (prefixWord ++ tailWord_846346).sum := by decide
  have hdescent : baseEnd_846346 < baseStart_846346 := by decide
  rcases family_descends (prefixWord ++ tailWord_846346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846394 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_846394 : Nat := 118140960795 + 846394 * 2 ^ 59
def prefixEnd_846394 : Nat := 4983230072969 + 3 ^ 40 * 846394 * 2
def baseEnd_846394 : Nat := 386317284517037078473343

theorem tailTrace_846394 : CollatzResearch.WordTrace tailWord_846394 prefixEnd_846394 386317284517037078473343 := by
  unfold tailWord_846394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7717631323916641357972559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20580350197111043621260157 7717631323916641357972559)
  ·
    refine ⟨11576446985874962036958839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7717631323916641357972559 11576446985874962036958839)
    ·
      refine ⟨17364670478812443055438259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11576446985874962036958839 17364670478812443055438259)
      ·
        refine ⟨26047005718218664583157389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17364670478812443055438259 26047005718218664583157389)
        ·
          refine ⟨9767627144331999218684021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26047005718218664583157389 9767627144331999218684021)
          ·
            refine ⟨915715044781124926751627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9767627144331999218684021 915715044781124926751627)
            ·
              refine ⟨1373572567171687390127441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915715044781124926751627 1373572567171687390127441)
              ·
                refine ⟨1030179425378765542595581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1373572567171687390127441 1030179425378765542595581)
                ·
                  refine ⟨386317284517037078473343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030179425378765542595581 386317284517037078473343)
                  ·
                    rfl

theorem cell20_846394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_846394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846394 prefixEnd_846394 := by exact prefixLift 846394
  have htrace : WordTrace (prefixWord ++ tailWord_846394) baseStart_846394 baseEnd_846394 := by
    simpa [prefixWord, tailWord_846394, baseEnd_846394] using wordTrace_append hprefix tailTrace_846394
  have hstable : (prefixWord ++ tailWord_846394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846394).length < 2 ^ (prefixWord ++ tailWord_846394).sum := by decide
  have hdescent : baseEnd_846394 < baseStart_846394 := by decide
  rcases family_descends (prefixWord ++ tailWord_846394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846401 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_846401 : Nat := 118140960795 + 846401 * 2 ^ 59
def prefixEnd_846401 : Nat := 4983230072969 + 3 ^ 40 * 846401 * 2
def baseEnd_846401 : Nat := 386320479507776165239981

theorem tailTrace_846401 : CollatzResearch.WordTrace tailWord_846401 prefixEnd_846401 386320479507776165239981 := by
  unfold tailWord_846401
  simp only [CollatzResearch.WordTrace]
  refine ⟨30870780606641205627395057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20580520404427470418263371 30870780606641205627395057)
  ·
    refine ⟨23153085454980904220546293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30870780606641205627395057 23153085454980904220546293)
    ·
      refine ⟨2170601761404459770676215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23153085454980904220546293 2170601761404459770676215)
      ·
        refine ⟨3255902642106689656014323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170601761404459770676215 3255902642106689656014323)
        ·
          refine ⟨4883853963160034484021485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3255902642106689656014323 4883853963160034484021485)
          ·
            refine ⟨1831445236185012931508057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4883853963160034484021485 1831445236185012931508057)
            ·
              refine ⟨1373583927138759698631043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831445236185012931508057 1373583927138759698631043)
              ·
                refine ⟨2060375890708139547946565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373583927138759698631043 2060375890708139547946565)
                ·
                  refine ⟨386320479507776165239981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060375890708139547946565 386320479507776165239981)
                  ·
                    rfl

theorem cell20_846401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_846401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846401 prefixEnd_846401 := by exact prefixLift 846401
  have htrace : WordTrace (prefixWord ++ tailWord_846401) baseStart_846401 baseEnd_846401 := by
    simpa [prefixWord, tailWord_846401, baseEnd_846401] using wordTrace_append hprefix tailTrace_846401
  have hstable : (prefixWord ++ tailWord_846401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846401).length < 2 ^ (prefixWord ++ tailWord_846401).sum := by decide
  have hdescent : baseEnd_846401 < baseStart_846401 := by decide
  rcases family_descends (prefixWord ++ tailWord_846401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846436 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_846436 : Nat := 118140960795 + 846436 * 2 ^ 59
def prefixEnd_846436 : Nat := 4983230072969 + 3 ^ 40 * 846436 * 2
def baseEnd_846436 : Nat := 386336454461471599073171

theorem tailTrace_846436 : CollatzResearch.WordTrace tailWord_846436 prefixEnd_846436 386336454461471599073171 := by
  unfold tailWord_846436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436028580757203302459581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20581371441009604403279441 15436028580757203302459581)
  ·
    refine ⟨5788510717783951238422343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15436028580757203302459581 5788510717783951238422343)
    ·
      refine ⟨8682766076675926857633515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788510717783951238422343 8682766076675926857633515)
      ·
        refine ⟨13024149115013890286450273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8682766076675926857633515 13024149115013890286450273)
        ·
          refine ⟨9768111836260417714837705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13024149115013890286450273 9768111836260417714837705)
          ·
            refine ⟨7326083877195313286128279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9768111836260417714837705 7326083877195313286128279)
            ·
              refine ⟨10989125815792969929192419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326083877195313286128279 10989125815792969929192419)
              ·
                refine ⟨16483688723689454893788629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10989125815792969929192419 16483688723689454893788629)
                ·
                  refine ⟨386336454461471599073171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16483688723689454893788629 386336454461471599073171)
                  ·
                    rfl

theorem cell20_846436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_846436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846436 prefixEnd_846436 := by exact prefixLift 846436
  have htrace : WordTrace (prefixWord ++ tailWord_846436) baseStart_846436 baseEnd_846436 := by
    simpa [prefixWord, tailWord_846436, baseEnd_846436] using wordTrace_append hprefix tailTrace_846436
  have hstable : (prefixWord ++ tailWord_846436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846436).length < 2 ^ (prefixWord ++ tailWord_846436).sum := by decide
  have hdescent : baseEnd_846436 < baseStart_846436 := by decide
  rcases family_descends (prefixWord ++ tailWord_846436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846446 : List Nat := [4, 1, 2, 2, 2, 3, 6]
def baseStart_846446 : Nat := 118140960795 + 846446 * 2 ^ 59
def prefixEnd_846446 : Nat := 4983230072969 + 3 ^ 40 * 846446 * 2
def baseEnd_846446 : Nat := 42926779859328445415533

theorem tailTrace_846446 : CollatzResearch.WordTrace tailWord_846446 prefixEnd_846446 42926779859328445415533 := by
  unfold tailWord_846446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859052736434772289097899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20581614594318785541855461 3859052736434772289097899)
  ·
    refine ⟨5788579104652158433646849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3859052736434772289097899 5788579104652158433646849)
    ·
      refine ⟨4341434328489118825235137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5788579104652158433646849 4341434328489118825235137)
      ·
        refine ⟨3256075746366839118926353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4341434328489118825235137 3256075746366839118926353)
        ·
          refine ⟨2442056809775129339194765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256075746366839118926353 2442056809775129339194765)
          ·
            refine ⟨915771303665673502198037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2442056809775129339194765 915771303665673502198037)
            ·
              refine ⟨42926779859328445415533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 915771303665673502198037 42926779859328445415533)
              ·
                rfl

theorem cell20_846446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_846446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846446 prefixEnd_846446 := by exact prefixLift 846446
  have htrace : WordTrace (prefixWord ++ tailWord_846446) baseStart_846446 baseEnd_846446 := by
    simpa [prefixWord, tailWord_846446, baseEnd_846446] using wordTrace_append hprefix tailTrace_846446
  have hstable : (prefixWord ++ tailWord_846446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846446).length < 2 ^ (prefixWord ++ tailWord_846446).sum := by decide
  have hdescent : baseEnd_846446 < baseStart_846446 := by decide
  rcases family_descends (prefixWord ++ tailWord_846446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846460 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_846460 : Nat := 118140960795 + 846460 * 2 ^ 59
def prefixEnd_846460 : Nat := 4983230072969 + 3 ^ 40 * 846460 * 2
def baseEnd_846460 : Nat := 386347408715434182273073

theorem tailTrace_846460 : CollatzResearch.WordTrace tailWord_846460 prefixEnd_846460 386347408715434182273073 := by
  unfold tailWord_846460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436466256713729351896417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20581955008951639135861889 15436466256713729351896417)
  ·
    refine ⟨11577349692535297013922313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15436466256713729351896417 11577349692535297013922313)
    ·
      refine ⟨8683012269401472760441735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11577349692535297013922313 8683012269401472760441735)
      ·
        refine ⟨13024518404102209140662603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683012269401472760441735 13024518404102209140662603)
        ·
          refine ⟨19536777606153313710993905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024518404102209140662603 19536777606153313710993905)
          ·
            refine ⟨14652583204614985283245429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19536777606153313710993905 14652583204614985283245429)
            ·
              refine ⟨1373679675432654870304259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14652583204614985283245429 1373679675432654870304259)
              ·
                refine ⟨2060519513148982305456389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1373679675432654870304259 2060519513148982305456389)
                ·
                  refine ⟨386347408715434182273073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060519513148982305456389 386347408715434182273073)
                  ·
                    rfl

theorem cell20_846460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_846460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846460 prefixEnd_846460 := by exact prefixLift 846460
  have htrace : WordTrace (prefixWord ++ tailWord_846460) baseStart_846460 baseEnd_846460 := by
    simpa [prefixWord, tailWord_846460, baseEnd_846460] using wordTrace_append hprefix tailTrace_846460
  have hstable : (prefixWord ++ tailWord_846460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846460).length < 2 ^ (prefixWord ++ tailWord_846460).sum := by decide
  have hdescent : baseEnd_846460 < baseStart_846460 := by decide
  rcases family_descends (prefixWord ++ tailWord_846460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846484 : List Nat := [2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_846484 : Nat := 118140960795 + 846484 * 2 ^ 59
def prefixEnd_846484 : Nat := 4983230072969 + 3 ^ 40 * 846484 * 2
def baseEnd_846484 : Nat := 128786120989798921824325

theorem tailTrace_846484 : CollatzResearch.WordTrace tailWord_846484 prefixEnd_846484 128786120989798921824325 := by
  unfold tailWord_846484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436903932670255401333253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20582538576893673868444337 15436903932670255401333253)
  ·
    refine ⟨2894419487375672887749985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15436903932670255401333253 2894419487375672887749985)
    ·
      refine ⟨2170814615531754665812489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2894419487375672887749985 2170814615531754665812489)
      ·
        refine ⟨1628110961648815999359367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170814615531754665812489 1628110961648815999359367)
        ·
          refine ⟨2442166442473223999039051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628110961648815999359367 2442166442473223999039051)
          ·
            refine ⟨3663249663709835998558577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442166442473223999039051 3663249663709835998558577)
            ·
              refine ⟨2747437247782376998918933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3663249663709835998558577 2747437247782376998918933)
              ·
                refine ⟨128786120989798921824325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2747437247782376998918933 128786120989798921824325)
                ·
                  rfl

theorem cell20_846484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_846484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846484 prefixEnd_846484 := by exact prefixLift 846484
  have htrace : WordTrace (prefixWord ++ tailWord_846484) baseStart_846484 baseEnd_846484 := by
    simpa [prefixWord, tailWord_846484, baseEnd_846484] using wordTrace_append hprefix tailTrace_846484
  have hstable : (prefixWord ++ tailWord_846484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846484).length < 2 ^ (prefixWord ++ tailWord_846484).sum := by decide
  have hdescent : baseEnd_846484 < baseStart_846484 := by decide
  rcases family_descends (prefixWord ++ tailWord_846484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846494 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_846494 : Nat := 118140960795 + 846494 * 2 ^ 59
def prefixEnd_846494 : Nat := 4983230072969 + 3 ^ 40 * 846494 * 2
def baseEnd_846494 : Nat := 386362927241881175139601

theorem tailTrace_846494 : CollatzResearch.WordTrace tailWord_846494 prefixEnd_846494 386362927241881175139601 := by
  unfold tailWord_846494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859271574413035313816317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20582781730202855007020357 3859271574413035313816317)
  ·
    refine ⟨1447226840404888242681119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3859271574413035313816317 1447226840404888242681119)
    ·
      refine ⟨2170840260607332364021679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447226840404888242681119 2170840260607332364021679)
      ·
        refine ⟨3256260390910998546032519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170840260607332364021679 3256260390910998546032519)
        ·
          refine ⟨4884390586366497819048779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256260390910998546032519 4884390586366497819048779)
          ·
            refine ⟨7326585879549746728573169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884390586366497819048779 7326585879549746728573169)
            ·
              refine ⟨5494939409662310046429877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7326585879549746728573169 5494939409662310046429877)
              ·
                refine ⟨515150569655841566852801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5494939409662310046429877 515150569655841566852801)
                ·
                  refine ⟨386362927241881175139601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515150569655841566852801 386362927241881175139601)
                  ·
                    rfl

theorem cell20_846494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_846494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846494 prefixEnd_846494 := by exact prefixLift 846494
  have htrace : WordTrace (prefixWord ++ tailWord_846494) baseStart_846494 baseEnd_846494 := by
    simpa [prefixWord, tailWord_846494, baseEnd_846494] using wordTrace_append hprefix tailTrace_846494
  have hstable : (prefixWord ++ tailWord_846494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846494).length < 2 ^ (prefixWord ++ tailWord_846494).sum := by decide
  have hdescent : baseEnd_846494 < baseStart_846494 := by decide
  rcases family_descends (prefixWord ++ tailWord_846494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846515 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 2]
def baseStart_846515 : Nat := 118140960795 + 846515 * 2 ^ 59
def prefixEnd_846515 : Nat := 4983230072969 + 3 ^ 40 * 846515 * 2
def baseEnd_846515 : Nat := 386372512214098435439515

theorem tailTrace_846515 : CollatzResearch.WordTrace tailWord_846515 prefixEnd_846515 386372512214098435439515 := by
  unfold tailWord_846515
  simp only [CollatzResearch.WordTrace]
  refine ⟨30874938528228203097044999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20583292352152135398029999 30874938528228203097044999)
  ·
    refine ⟨46312407792342304645567499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30874938528228203097044999 46312407792342304645567499)
    ·
      refine ⟨69468611688513456968351249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46312407792342304645567499 69468611688513456968351249)
      ·
        refine ⟨52101458766385092726263437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69468611688513456968351249 52101458766385092726263437)
        ·
          refine ⟨19538047037394409772348789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52101458766385092726263437 19538047037394409772348789)
          ·
            refine ⟨1831691909755725916157699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19538047037394409772348789 1831691909755725916157699)
            ·
              refine ⟨2747537864633588874236549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831691909755725916157699 2747537864633588874236549)
              ·
                refine ⟨515163349618797913919353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2747537864633588874236549 515163349618797913919353)
                ·
                  refine ⟨386372512214098435439515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515163349618797913919353 386372512214098435439515)
                  ·
                    rfl

theorem cell20_846515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 2].length) (baseStart_846515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846515 prefixEnd_846515 := by exact prefixLift 846515
  have htrace : WordTrace (prefixWord ++ tailWord_846515) baseStart_846515 baseEnd_846515 := by
    simpa [prefixWord, tailWord_846515, baseEnd_846515] using wordTrace_append hprefix tailTrace_846515
  have hstable : (prefixWord ++ tailWord_846515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846515).length < 2 ^ (prefixWord ++ tailWord_846515).sum := by decide
  have hdescent : baseEnd_846515 < baseStart_846515 := by decide
  rcases family_descends (prefixWord ++ tailWord_846515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846518 : List Nat := [5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_846518 : Nat := 118140960795 + 846518 * 2 ^ 59
def prefixEnd_846518 : Nat := 4983230072969 + 3 ^ 40 * 846518 * 2
def baseEnd_846518 : Nat := 128791293831947919446501

theorem tailTrace_846518 : CollatzResearch.WordTrace tailWord_846518 prefixEnd_846518 128791293831947919446501 := by
  unfold tailWord_846518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929690496701083413087763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20583365298144889739602805 1929690496701083413087763)
  ·
    refine ⟨2894535745051625119631645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929690496701083413087763 2894535745051625119631645)
    ·
      refine ⟨1085450904394359419861867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2894535745051625119631645 1085450904394359419861867)
      ·
        refine ⟨1628176356591539129792801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085450904394359419861867 1628176356591539129792801)
        ·
          refine ⟨1221132267443654347344601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1628176356591539129792801 1221132267443654347344601)
          ·
            refine ⟨915849200582740760508451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221132267443654347344601 915849200582740760508451)
            ·
              refine ⟨1373773800874111140762677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915849200582740760508451 1373773800874111140762677)
              ·
                refine ⟨128791293831947919446501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1373773800874111140762677 128791293831947919446501)
                ·
                  rfl

theorem cell20_846518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_846518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846518 prefixEnd_846518 := by exact prefixLift 846518
  have htrace : WordTrace (prefixWord ++ tailWord_846518) baseStart_846518 baseEnd_846518 := by
    simpa [prefixWord, tailWord_846518, baseEnd_846518] using wordTrace_append hprefix tailTrace_846518
  have hstable : (prefixWord ++ tailWord_846518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846518).length < 2 ^ (prefixWord ++ tailWord_846518).sum := by decide
  have hdescent : baseEnd_846518 < baseStart_846518 := by decide
  rcases family_descends (prefixWord ++ tailWord_846518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846536 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_846536 : Nat := 118140960795 + 846536 * 2 ^ 59
def prefixEnd_846536 : Nat := 4983230072969 + 3 ^ 40 * 846536 * 2
def baseEnd_846536 : Nat := 386382097186315695739429

theorem tailTrace_846536 : CollatzResearch.WordTrace tailWord_846536 prefixEnd_846536 386382097186315695739429 := by
  unfold tailWord_846536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437852230576061841779731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20583802974101415789039641 15437852230576061841779731)
  ·
    refine ⟨23156778345864092762669597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15437852230576061841779731 23156778345864092762669597)
    ·
      refine ⟨8683791879699034786001099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23156778345864092762669597 8683791879699034786001099)
      ·
        refine ⟨13025687819548552179001649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683791879699034786001099 13025687819548552179001649)
        ·
          refine ⟨9769265864661414134251237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13025687819548552179001649 9769265864661414134251237)
          ·
            refine ⟨1831737349624015150172107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9769265864661414134251237 1831737349624015150172107)
            ·
              refine ⟨2747606024436022725258161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831737349624015150172107 2747606024436022725258161)
              ·
                refine ⟨2060704518327017043943621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2747606024436022725258161 2060704518327017043943621)
                ·
                  refine ⟨386382097186315695739429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060704518327017043943621 386382097186315695739429)
                  ·
                    rfl

theorem cell20_846536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_846536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846536 prefixEnd_846536 := by exact prefixLift 846536
  have htrace : WordTrace (prefixWord ++ tailWord_846536) baseStart_846536 baseEnd_846536 := by
    simpa [prefixWord, tailWord_846536, baseEnd_846536] using wordTrace_append hprefix tailTrace_846536
  have hstable : (prefixWord ++ tailWord_846536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846536).length < 2 ^ (prefixWord ++ tailWord_846536).sum := by decide
  have hdescent : baseEnd_846536 < baseStart_846536 := by decide
  rcases family_descends (prefixWord ++ tailWord_846536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846549 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 2]
def baseStart_846549 : Nat := 118140960795 + 846549 * 2 ^ 59
def prefixEnd_846549 : Nat := 4983230072969 + 3 ^ 40 * 846549 * 2
def baseEnd_846549 : Nat := 386388030740545428306043

theorem tailTrace_846549 : CollatzResearch.WordTrace tailWord_846549 prefixEnd_846549 386388030740545428306043 := by
  unfold tailWord_846549
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876178610105026903782701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20584119073403351269188467 30876178610105026903782701)
  ·
    refine ⟨11578566978789385088918513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30876178610105026903782701 11578566978789385088918513)
    ·
      refine ⟨8683925234092038816688885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11578566978789385088918513 8683925234092038816688885)
      ·
        refine ⟨814117990696128639064583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8683925234092038816688885 814117990696128639064583)
        ·
          refine ⟨1221176986044192958596875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814117990696128639064583 1221176986044192958596875)
          ·
            refine ⟨1831765479066289437895313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221176986044192958596875 1831765479066289437895313)
            ·
              refine ⟨1373824109299717078421485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831765479066289437895313 1373824109299717078421485)
              ·
                refine ⟨515184040987393904408057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373824109299717078421485 515184040987393904408057)
                ·
                  refine ⟨386388030740545428306043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515184040987393904408057 386388030740545428306043)
                  ·
                    rfl

theorem cell20_846549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_846549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846549 prefixEnd_846549 := by exact prefixLift 846549
  have htrace : WordTrace (prefixWord ++ tailWord_846549) baseStart_846549 baseEnd_846549 := by
    simpa [prefixWord, tailWord_846549, baseEnd_846549] using wordTrace_append hprefix tailTrace_846549
  have hstable : (prefixWord ++ tailWord_846549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846549).length < 2 ^ (prefixWord ++ tailWord_846549).sum := by decide
  have hdescent : baseEnd_846549 < baseStart_846549 := by decide
  rcases family_descends (prefixWord ++ tailWord_846549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846553 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 2]
def baseStart_846553 : Nat := 118140960795 + 846553 * 2 ^ 59
def prefixEnd_846553 : Nat := 4983230072969 + 3 ^ 40 * 846553 * 2
def baseEnd_846553 : Nat := 386389856449539192172693

theorem tailTrace_846553 : CollatzResearch.WordTrace tailWord_846553 prefixEnd_846553 386389856449539192172693 := by
  unfold tailWord_846553
  simp only [CollatzResearch.WordTrace]
  refine ⟨30876324502090535586928313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20584216334727023724618875 30876324502090535586928313)
  ·
    refine ⟨23157243376567901690196235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30876324502090535586928313 23157243376567901690196235)
    ·
      refine ⟨34735865064851852535294353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23157243376567901690196235 34735865064851852535294353)
      ·
        refine ⟨26051898798638889401470765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34735865064851852535294353 26051898798638889401470765)
        ·
          refine ⟨9769462049489583525551537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26051898798638889401470765 9769462049489583525551537)
          ·
            refine ⟨7327096537117187644163653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9769462049489583525551537 7327096537117187644163653)
            ·
              refine ⟨1373830600709472683280685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7327096537117187644163653 1373830600709472683280685)
              ·
                refine ⟨515186475266052256230257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373830600709472683280685 515186475266052256230257)
                ·
                  refine ⟨386389856449539192172693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515186475266052256230257 386389856449539192172693)
                  ·
                    rfl

theorem cell20_846553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_846553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846553 prefixEnd_846553 := by exact prefixLift 846553
  have htrace : WordTrace (prefixWord ++ tailWord_846553) baseStart_846553 baseEnd_846553 := by
    simpa [prefixWord, tailWord_846553, baseEnd_846553] using wordTrace_append hprefix tailTrace_846553
  have hstable : (prefixWord ++ tailWord_846553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846553).length < 2 ^ (prefixWord ++ tailWord_846553).sum := by decide
  have hdescent : baseEnd_846553 < baseStart_846553 := by decide
  rcases family_descends (prefixWord ++ tailWord_846553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846574 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_846574 : Nat := 118140960795 + 846574 * 2 ^ 59
def prefixEnd_846574 : Nat := 4983230072969 + 3 ^ 40 * 846574 * 2
def baseEnd_846574 : Nat := 386399441421756452472607

theorem tailTrace_846574 : CollatzResearch.WordTrace tailWord_846574 prefixEnd_846574 386399441421756452472607 := by
  unfold tailWord_846574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859636304376807021680347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20584726956676304115628517 3859636304376807021680347)
  ·
    refine ⟨5789454456565210532520521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3859636304376807021680347 5789454456565210532520521)
    ·
      refine ⟨4342090842423907899390391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5789454456565210532520521 4342090842423907899390391)
      ·
        refine ⟨6513136263635861849085587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342090842423907899390391 6513136263635861849085587)
        ·
          refine ⟨9769704395453792773628381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513136263635861849085587 9769704395453792773628381)
          ·
            refine ⟨3663639148295172290110643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9769704395453792773628381 3663639148295172290110643)
            ·
              refine ⟨5495458722442758435165965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663639148295172290110643 5495458722442758435165965)
              ·
                refine ⟨2060797020916034413187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5495458722442758435165965 2060797020916034413187237)
                ·
                  refine ⟨386399441421756452472607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060797020916034413187237 386399441421756452472607)
                  ·
                    rfl

theorem cell20_846574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_846574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846574 prefixEnd_846574 := by exact prefixLift 846574
  have htrace : WordTrace (prefixWord ++ tailWord_846574) baseStart_846574 baseEnd_846574 := by
    simpa [prefixWord, tailWord_846574, baseEnd_846574] using wordTrace_append hprefix tailTrace_846574
  have hstable : (prefixWord ++ tailWord_846574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846574).length < 2 ^ (prefixWord ++ tailWord_846574).sum := by decide
  have hdescent : baseEnd_846574 < baseStart_846574 := by decide
  rcases family_descends (prefixWord ++ tailWord_846574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846643 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_846643 : Nat := 118140960795 + 846643 * 2 ^ 59
def prefixEnd_846643 : Nat := 4983230072969 + 3 ^ 40 * 846643 * 2
def baseEnd_846643 : Nat := 386430934901898879172325

theorem tailTrace_846643 : CollatzResearch.WordTrace tailWord_846643 prefixEnd_846643 386430934901898879172325 := by
  unfold tailWord_846643
  simp only [CollatzResearch.WordTrace]
  refine ⟨30879607071764480957704583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20586404714509653971803055 30879607071764480957704583)
  ·
    refine ⟨46319410607646721436556875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30879607071764480957704583 46319410607646721436556875)
    ·
      refine ⟨69479115911470082154835313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46319410607646721436556875 69479115911470082154835313)
      ·
        refine ⟨52109336933602561616126485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69479115911470082154835313 52109336933602561616126485)
        ·
          refine ⟨2442625168762620075755929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52109336933602561616126485 2442625168762620075755929)
          ·
            refine ⟨1831968876571965056816947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442625168762620075755929 1831968876571965056816947)
            ·
              refine ⟨2747953314857947585225421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831968876571965056816947 2747953314857947585225421)
              ·
                refine ⟨1030482493071730344459533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2747953314857947585225421 1030482493071730344459533)
                ·
                  refine ⟨386430934901898879172325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030482493071730344459533 386430934901898879172325)
                  ·
                    rfl

theorem cell20_846643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_846643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846643 prefixEnd_846643 := by exact prefixLift 846643
  have htrace : WordTrace (prefixWord ++ tailWord_846643) baseStart_846643 baseEnd_846643 := by
    simpa [prefixWord, tailWord_846643, baseEnd_846643] using wordTrace_append hprefix tailTrace_846643
  have hstable : (prefixWord ++ tailWord_846643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846643).length < 2 ^ (prefixWord ++ tailWord_846643).sum := by decide
  have hdescent : baseEnd_846643 < baseStart_846643 := by decide
  rcases family_descends (prefixWord ++ tailWord_846643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846681 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_846681 : Nat := 118140960795 + 846681 * 2 ^ 59
def prefixEnd_846681 : Nat := 4983230072969 + 3 ^ 40 * 846681 * 2
def baseEnd_846681 : Nat := 386448279137339635905503

theorem tailTrace_846681 : CollatzResearch.WordTrace tailWord_846681 prefixEnd_846681 386448279137339635905503 := by
  unfold tailWord_846681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880993045626813447587897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20587328697084542298391931 30880993045626813447587897)
  ·
    refine ⟨23160744784220110085690923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30880993045626813447587897 23160744784220110085690923)
    ·
      refine ⟨34741117176330165128536385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23160744784220110085690923 34741117176330165128536385)
      ·
        refine ⟨26055837882247623846402289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34741117176330165128536385 26055837882247623846402289)
        ·
          refine ⟨19541878411685717884801717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26055837882247623846402289 19541878411685717884801717)
          ·
            refine ⟨1832051101095536051700161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19541878411685717884801717 1832051101095536051700161)
            ·
              refine ⟨1374038325821652038775121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832051101095536051700161 1374038325821652038775121)
              ·
                refine ⟨1030528744366239029081341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374038325821652038775121 1030528744366239029081341)
                ·
                  refine ⟨386448279137339635905503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030528744366239029081341 386448279137339635905503)
                  ·
                    rfl

theorem cell20_846681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_846681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846681 prefixEnd_846681 := by exact prefixLift 846681
  have htrace : WordTrace (prefixWord ++ tailWord_846681) baseStart_846681 baseEnd_846681 := by
    simpa [prefixWord, tailWord_846681, baseEnd_846681] using wordTrace_append hprefix tailTrace_846681
  have hstable : (prefixWord ++ tailWord_846681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846681).length < 2 ^ (prefixWord ++ tailWord_846681).sum := by decide
  have hdescent : baseEnd_846681 < baseStart_846681 := by decide
  rcases family_descends (prefixWord ++ tailWord_846681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846684 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_846684 : Nat := 118140960795 + 846684 * 2 ^ 59
def prefixEnd_846684 : Nat := 4983230072969 + 3 ^ 40 * 846684 * 2
def baseEnd_846684 : Nat := 386449648419084958805491

theorem tailTrace_846684 : CollatzResearch.WordTrace tailWord_846684 prefixEnd_846684 386449648419084958805491 := by
  unfold tailWord_846684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440551232307972479973553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20587401643077296639964737 15440551232307972479973553)
  ·
    refine ⟨11580413424230979359980165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15440551232307972479973553 11580413424230979359980165)
    ·
      refine ⟨2171327517043308629996281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11580413424230979359980165 2171327517043308629996281)
      ·
        refine ⟨1628495637782481472497211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2171327517043308629996281 1628495637782481472497211)
        ·
          refine ⟨2442743456673722208745817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628495637782481472497211 2442743456673722208745817)
          ·
            refine ⟨1832057592505291656559363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442743456673722208745817 1832057592505291656559363)
            ·
              refine ⟨2748086388757937484839045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832057592505291656559363 2748086388757937484839045)
              ·
                refine ⟨515266197892113278407321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2748086388757937484839045 515266197892113278407321)
                ·
                  refine ⟨386449648419084958805491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515266197892113278407321 386449648419084958805491)
                  ·
                    rfl

theorem cell20_846684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_846684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846684 prefixEnd_846684 := by exact prefixLift 846684
  have htrace : WordTrace (prefixWord ++ tailWord_846684) baseStart_846684 baseEnd_846684 := by
    simpa [prefixWord, tailWord_846684, baseEnd_846684] using wordTrace_append hprefix tailTrace_846684
  have hstable : (prefixWord ++ tailWord_846684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846684).length < 2 ^ (prefixWord ++ tailWord_846684).sum := by decide
  have hdescent : baseEnd_846684 < baseStart_846684 := by decide
  rcases family_descends (prefixWord ++ tailWord_846684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846695 : List Nat := [1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_846695 : Nat := 118140960795 + 846695 * 2 ^ 59
def prefixEnd_846695 : Nat := 4983230072969 + 3 ^ 40 * 846695 * 2
def baseEnd_846695 : Nat := 128818223039605936479593

theorem tailTrace_846695 : CollatzResearch.WordTrace tailWord_846695 prefixEnd_846695 128818223039605936479593 := by
  unfold tailWord_846695
  simp only [CollatzResearch.WordTrace]
  refine ⟨30881503667576093838597539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20587669111717395892398359 30881503667576093838597539)
  ·
    refine ⟨46322255501364140757896309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30881503667576093838597539 46322255501364140757896309)
    ·
      refine ⟨4342711453252888196052779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46322255501364140757896309 4342711453252888196052779)
      ·
        refine ⟨6514067179879332294079169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4342711453252888196052779 6514067179879332294079169)
        ·
          refine ⟨4885550384909499220559377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514067179879332294079169 4885550384909499220559377)
          ·
            refine ⟨3664162788682124415419533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4885550384909499220559377 3664162788682124415419533)
            ·
              refine ⟨1374061045755796655782325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3664162788682124415419533 1374061045755796655782325)
              ·
                refine ⟨128818223039605936479593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374061045755796655782325 128818223039605936479593)
                ·
                  rfl

theorem cell20_846695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_846695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846695 prefixEnd_846695 := by exact prefixLift 846695
  have htrace : WordTrace (prefixWord ++ tailWord_846695) baseStart_846695 baseEnd_846695 := by
    simpa [prefixWord, tailWord_846695, baseEnd_846695] using wordTrace_append hprefix tailTrace_846695
  have hstable : (prefixWord ++ tailWord_846695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846695).length < 2 ^ (prefixWord ++ tailWord_846695).sum := by decide
  have hdescent : baseEnd_846695 < baseStart_846695 := by decide
  rcases family_descends (prefixWord ++ tailWord_846695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846716 : List Nat := [2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_846716 : Nat := 118140960795 + 846716 * 2 ^ 59
def prefixEnd_846716 : Nat := 4983230072969 + 3 ^ 40 * 846716 * 2
def baseEnd_846716 : Nat := 128821418030345023246231

theorem tailTrace_846716 : CollatzResearch.WordTrace tailWord_846716 prefixEnd_846716 128821418030345023246231 := by
  unfold tailWord_846716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15441134800250007212556001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20588179733666676283408001 15441134800250007212556001)
  ·
    refine ⟨11580851100187505409417001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15441134800250007212556001 11580851100187505409417001)
    ·
      refine ⟨8685638325140629057062751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11580851100187505409417001 8685638325140629057062751)
      ·
        refine ⟨13028457487710943585594127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8685638325140629057062751 13028457487710943585594127)
        ·
          refine ⟨19542686231566415378391191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13028457487710943585594127 19542686231566415378391191)
          ·
            refine ⟨29314029347349623067586787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19542686231566415378391191 29314029347349623067586787)
            ·
              refine ⟨43971044021024434601380181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29314029347349623067586787 43971044021024434601380181)
              ·
                refine ⟨128821418030345023246231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43971044021024434601380181 128821418030345023246231)
                ·
                  rfl

theorem cell20_846716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_846716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846716 prefixEnd_846716 := by exact prefixLift 846716
  have htrace : WordTrace (prefixWord ++ tailWord_846716) baseStart_846716 baseEnd_846716 := by
    simpa [prefixWord, tailWord_846716, baseEnd_846716] using wordTrace_append hprefix tailTrace_846716
  have hstable : (prefixWord ++ tailWord_846716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846716).length < 2 ^ (prefixWord ++ tailWord_846716).sum := by decide
  have hdescent : baseEnd_846716 < baseStart_846716 := by decide
  rcases family_descends (prefixWord ++ tailWord_846716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846790 : List Nat := [6, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_846790 : Nat := 118140960795 + 846790 * 2 ^ 59
def prefixEnd_846790 : Nat := 4983230072969 + 3 ^ 40 * 846790 * 2
def baseEnd_846790 : Nat := 386498029707419701271725

theorem tailTrace_846790 : CollatzResearch.WordTrace tailWord_846790 prefixEnd_846790 386498029707419701271725 := by
  unfold tailWord_846790
  simp only [CollatzResearch.WordTrace]
  refine ⟨965155268819747658228307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20589979068154616708870549 965155268819747658228307)
  ·
    refine ⟨1447732903229621487342461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965155268819747658228307 1447732903229621487342461)
    ·
      refine ⟨542899838711108057753423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1447732903229621487342461 542899838711108057753423)
      ·
        refine ⟨814349758066662086630135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542899838711108057753423 814349758066662086630135)
        ·
          refine ⟨1221524637099993129945203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814349758066662086630135 1221524637099993129945203)
          ·
            refine ⟨1832286955649989694917805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221524637099993129945203 1832286955649989694917805)
            ·
              refine ⟨687107608368746135594177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832286955649989694917805 687107608368746135594177)
              ·
                refine ⟨515330706276559601695633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687107608368746135594177 515330706276559601695633)
                ·
                  refine ⟨386498029707419701271725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515330706276559601695633 386498029707419701271725)
                  ·
                    rfl

theorem cell20_846790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_846790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846790 prefixEnd_846790 := by exact prefixLift 846790
  have htrace : WordTrace (prefixWord ++ tailWord_846790) baseStart_846790 baseEnd_846790 := by
    simpa [prefixWord, tailWord_846790, baseEnd_846790] using wordTrace_append hprefix tailTrace_846790
  have hstable : (prefixWord ++ tailWord_846790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846790).length < 2 ^ (prefixWord ++ tailWord_846790).sum := by decide
  have hdescent : baseEnd_846790 < baseStart_846790 := by decide
  rcases family_descends (prefixWord ++ tailWord_846790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846798 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_846798 : Nat := 118140960795 + 846798 * 2 ^ 59
def prefixEnd_846798 : Nat := 4983230072969 + 3 ^ 40 * 846798 * 2
def baseEnd_846798 : Nat := 386501681125407229005025

theorem tailTrace_846798 : CollatzResearch.WordTrace tailWord_846798 prefixEnd_846798 386501681125407229005025 := by
  unfold tailWord_846798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860657548275367803699631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20590173590801961619731365 3860657548275367803699631)
  ·
    refine ⟨5790986322413051705549447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3860657548275367803699631 5790986322413051705549447)
    ·
      refine ⟨8686479483619577558324171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790986322413051705549447 8686479483619577558324171)
      ·
        refine ⟨13029719225429366337486257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8686479483619577558324171 13029719225429366337486257)
        ·
          refine ⟨9772289419072024753114693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13029719225429366337486257 9772289419072024753114693)
          ·
            refine ⟨1832304266076004641209005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9772289419072024753114693 1832304266076004641209005)
            ·
              refine ⟨687114099778501740453377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832304266076004641209005 687114099778501740453377)
              ·
                refine ⟨515335574833876305340033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687114099778501740453377 515335574833876305340033)
                ·
                  refine ⟨386501681125407229005025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515335574833876305340033 386501681125407229005025)
                  ·
                    rfl

theorem cell20_846798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_846798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846798 prefixEnd_846798 := by exact prefixLift 846798
  have htrace : WordTrace (prefixWord ++ tailWord_846798) baseStart_846798 baseEnd_846798 := by
    simpa [prefixWord, tailWord_846798, baseEnd_846798] using wordTrace_append hprefix tailTrace_846798
  have hstable : (prefixWord ++ tailWord_846798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846798).length < 2 ^ (prefixWord ++ tailWord_846798).sum := by decide
  have hdescent : baseEnd_846798 < baseStart_846798 := by decide
  rcases family_descends (prefixWord ++ tailWord_846798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846809 : List Nat := [1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_846809 : Nat := 118140960795 + 846809 * 2 ^ 59
def prefixEnd_846809 : Nat := 4983230072969 + 3 ^ 40 * 846809 * 2
def baseEnd_846809 : Nat := 128835567275046693212771

theorem tailTrace_846809 : CollatzResearch.WordTrace tailWord_846809 prefixEnd_846809 128835567275046693212771 := by
  unfold tailWord_846809
  simp only [CollatzResearch.WordTrace]
  refine ⟨30885661589163091308247481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20590441059442060872164987 30885661589163091308247481)
  ·
    refine ⟨23164246191872318481185611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30885661589163091308247481 23164246191872318481185611)
    ·
      refine ⟨34746369287808477721778417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23164246191872318481185611 34746369287808477721778417)
      ·
        refine ⟨26059776965856358291333813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34746369287808477721778417 26059776965856358291333813)
        ·
          refine ⟨2443104090549033589812545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26059776965856358291333813 2443104090549033589812545)
          ·
            refine ⟨1832328067911775192359409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2443104090549033589812545 1832328067911775192359409)
            ·
              refine ⟨1374246050933831394269557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832328067911775192359409 1374246050933831394269557)
              ·
                refine ⟨128835567275046693212771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374246050933831394269557 128835567275046693212771)
                ·
                  rfl

theorem cell20_846809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_846809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846809 prefixEnd_846809 := by exact prefixLift 846809
  have htrace : WordTrace (prefixWord ++ tailWord_846809) baseStart_846809 baseEnd_846809 := by
    simpa [prefixWord, tailWord_846809, baseEnd_846809] using wordTrace_append hprefix tailTrace_846809
  have hstable : (prefixWord ++ tailWord_846809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846809).length < 2 ^ (prefixWord ++ tailWord_846809).sum := by decide
  have hdescent : baseEnd_846809 < baseStart_846809 := by decide
  rcases family_descends (prefixWord ++ tailWord_846809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846840 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_846840 : Nat := 118140960795 + 846840 * 2 ^ 59
def prefixEnd_846840 : Nat := 4983230072969 + 3 ^ 40 * 846840 * 2
def baseEnd_846840 : Nat := 386520851069841749604853

theorem tailTrace_846840 : CollatzResearch.WordTrace tailWord_846840 prefixEnd_846840 386520851069841749604853 := by
  unfold tailWord_846840
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443396126025391801312987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20591194834700522401750649 15443396126025391801312987)
  ·
    refine ⟨23165094189038087701969481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15443396126025391801312987 23165094189038087701969481)
    ·
      refine ⟨17373820641778565776477111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23165094189038087701969481 17373820641778565776477111)
      ·
        refine ⟨26060730962667848664715667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17373820641778565776477111 26060730962667848664715667)
        ·
          refine ⟨39091096444001772997073501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26060730962667848664715667 39091096444001772997073501)
          ·
            refine ⟨14659161166500664873902563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39091096444001772997073501 14659161166500664873902563)
            ·
              refine ⟨21988741749750997310853845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14659161166500664873902563 21988741749750997310853845)
              ·
                refine ⟨515361134759788999473137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21988741749750997310853845 515361134759788999473137)
                ·
                  refine ⟨386520851069841749604853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515361134759788999473137 386520851069841749604853)
                  ·
                    rfl

theorem cell20_846840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_846840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846840 prefixEnd_846840 := by exact prefixLift 846840
  have htrace : WordTrace (prefixWord ++ tailWord_846840) baseStart_846840 baseEnd_846840 := by
    simpa [prefixWord, tailWord_846840, baseEnd_846840] using wordTrace_append hprefix tailTrace_846840
  have hstable : (prefixWord ++ tailWord_846840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846840).length < 2 ^ (prefixWord ++ tailWord_846840).sum := by decide
  have hdescent : baseEnd_846840 < baseStart_846840 := by decide
  rcases family_descends (prefixWord ++ tailWord_846840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846871 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_846871 : Nat := 118140960795 + 846871 * 2 ^ 59
def prefixEnd_846871 : Nat := 4983230072969 + 3 ^ 40 * 846871 * 2
def baseEnd_846871 : Nat := 386535000314543419571393

theorem tailTrace_846871 : CollatzResearch.WordTrace tailWord_846871 prefixEnd_846871 386535000314543419571393 := by
  unfold tailWord_846871
  simp only [CollatzResearch.WordTrace]
  refine ⟨30887922914938475897004467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20591948609958983931336311 30887922914938475897004467)
  ·
    refine ⟨46331884372407713845506701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30887922914938475897004467 46331884372407713845506701)
    ·
      refine ⟨17374456639652892692065013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46331884372407713845506701 17374456639652892692065013)
      ·
        refine ⟨1628855309967458689881095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17374456639652892692065013 1628855309967458689881095)
        ·
          refine ⟨2443282964951188034821643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1628855309967458689881095 2443282964951188034821643)
          ·
            refine ⟨3664924447426782052232465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443282964951188034821643 3664924447426782052232465)
            ·
              refine ⟨2748693335570086539174349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664924447426782052232465 2748693335570086539174349)
              ·
                refine ⟨1030760000838782452190381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2748693335570086539174349 1030760000838782452190381)
                ·
                  refine ⟨386535000314543419571393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030760000838782452190381 386535000314543419571393)
                  ·
                    rfl

theorem cell20_846871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_846871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846871 prefixEnd_846871 := by exact prefixLift 846871
  have htrace : WordTrace (prefixWord ++ tailWord_846871) baseStart_846871 baseEnd_846871 := by
    simpa [prefixWord, tailWord_846871, baseEnd_846871] using wordTrace_append hprefix tailTrace_846871
  have hstable : (prefixWord ++ tailWord_846871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846871).length < 2 ^ (prefixWord ++ tailWord_846871).sum := by decide
  have hdescent : baseEnd_846871 < baseStart_846871 := by decide
  rcases family_descends (prefixWord ++ tailWord_846871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846885 : List Nat := [1, 3, 1, 2, 2, 2, 5, 4]
def baseStart_846885 : Nat := 118140960795 + 846885 * 2 ^ 59
def prefixEnd_846885 : Nat := 4983230072969 + 3 ^ 40 * 846885 * 2
def baseEnd_846885 : Nat := 128847130098673864368223

theorem tailTrace_846885 : CollatzResearch.WordTrace tailWord_846885 prefixEnd_846885 128847130098673864368223 := by
  unfold tailWord_846885
  simp only [CollatzResearch.WordTrace]
  refine ⟨30888433536887756288014109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20592289024591837525342739 30888433536887756288014109)
  ·
    refine ⟨11583162576332908608005291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30888433536887756288014109 11583162576332908608005291)
    ·
      refine ⟨17374743864499362912007937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583162576332908608005291 17374743864499362912007937)
      ·
        refine ⟨13031057898374522184005953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17374743864499362912007937 13031057898374522184005953)
        ·
          refine ⟨9773293423780891638004465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13031057898374522184005953 9773293423780891638004465)
          ·
            refine ⟨7329970067835668728503349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9773293423780891638004465 7329970067835668728503349)
            ·
              refine ⟨687184693859593943297189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7329970067835668728503349 687184693859593943297189)
              ·
                refine ⟨128847130098673864368223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687184693859593943297189 128847130098673864368223)
                ·
                  rfl

theorem cell20_846885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 4].length) (baseStart_846885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846885 prefixEnd_846885 := by exact prefixLift 846885
  have htrace : WordTrace (prefixWord ++ tailWord_846885) baseStart_846885 baseEnd_846885 := by
    simpa [prefixWord, tailWord_846885, baseEnd_846885] using wordTrace_append hprefix tailTrace_846885
  have hstable : (prefixWord ++ tailWord_846885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846885).length < 2 ^ (prefixWord ++ tailWord_846885).sum := by decide
  have hdescent : baseEnd_846885 < baseStart_846885 := by decide
  rcases family_descends (prefixWord ++ tailWord_846885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846909 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_846909 : Nat := 118140960795 + 846909 * 2 ^ 59
def prefixEnd_846909 : Nat := 4983230072969 + 3 ^ 40 * 846909 * 2
def baseEnd_846909 : Nat := 386552344549984176304571

theorem tailTrace_846909 : CollatzResearch.WordTrace tailWord_846909 prefixEnd_846909 386552344549984176304571 := by
  unfold tailWord_846909
  simp only [CollatzResearch.WordTrace]
  refine ⟨30889308888800808386887781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20592872592533872257925187 30889308888800808386887781)
  ·
    refine ⟨5791745416650151572541459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30889308888800808386887781 5791745416650151572541459)
    ·
      refine ⟨8687618124975227358812189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5791745416650151572541459 8687618124975227358812189)
      ·
        refine ⟨3257856796865710259554571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8687618124975227358812189 3257856796865710259554571)
        ·
          refine ⟨4886785195298565389331857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257856796865710259554571 4886785195298565389331857)
          ·
            refine ⟨3665088896473924041998893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4886785195298565389331857 3665088896473924041998893)
            ·
              refine ⟨1374408336177721515749585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3665088896473924041998893 1374408336177721515749585)
              ·
                refine ⟨1030806252133291136812189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1374408336177721515749585 1030806252133291136812189)
                ·
                  refine ⟨386552344549984176304571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030806252133291136812189 386552344549984176304571)
                  ·
                    rfl

theorem cell20_846909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_846909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846909 prefixEnd_846909 := by exact prefixLift 846909
  have htrace : WordTrace (prefixWord ++ tailWord_846909) baseStart_846909 baseEnd_846909 := by
    simpa [prefixWord, tailWord_846909, baseEnd_846909] using wordTrace_append hprefix tailTrace_846909
  have hstable : (prefixWord ++ tailWord_846909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846909).length < 2 ^ (prefixWord ++ tailWord_846909).sum := by decide
  have hdescent : baseEnd_846909 < baseStart_846909 := by decide
  rcases family_descends (prefixWord ++ tailWord_846909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846944 : List Nat := [2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_846944 : Nat := 118140960795 + 846944 * 2 ^ 59
def prefixEnd_846944 : Nat := 4983230072969 + 3 ^ 40 * 846944 * 2
def baseEnd_846944 : Nat := 128856106501226536712587

theorem tailTrace_846944 : CollatzResearch.WordTrace tailWord_846944 prefixEnd_846944 128856106501226536712587 := by
  unfold tailWord_846944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15445292721837004682205943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20593723629116006242941257 15445292721837004682205943)
  ·
    refine ⟨23167939082755507023308915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15445292721837004682205943 23167939082755507023308915)
    ·
      refine ⟨34751908624133260534963373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23167939082755507023308915 34751908624133260534963373)
      ·
        refine ⟨13031965734049972700611265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34751908624133260534963373 13031965734049972700611265)
        ·
          refine ⟨9773974300537479525458449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13031965734049972700611265 9773974300537479525458449)
          ·
            refine ⟨7330480725403109644093837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9773974300537479525458449 7330480725403109644093837)
            ·
              refine ⟨2748930272026166116535189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7330480725403109644093837 2748930272026166116535189)
              ·
                refine ⟨128856106501226536712587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2748930272026166116535189 128856106501226536712587)
                ·
                  rfl

theorem cell20_846944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_846944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846944 prefixEnd_846944 := by exact prefixLift 846944
  have htrace : WordTrace (prefixWord ++ tailWord_846944) baseStart_846944 baseEnd_846944 := by
    simpa [prefixWord, tailWord_846944, baseEnd_846944] using wordTrace_append hprefix tailTrace_846944
  have hstable : (prefixWord ++ tailWord_846944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846944).length < 2 ^ (prefixWord ++ tailWord_846944).sum := by decide
  have hdescent : baseEnd_846944 < baseStart_846944 := by decide
  rcases family_descends (prefixWord ++ tailWord_846944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846974 : List Nat := [4, 2, 4, 1, 1, 1, 2, 5]
def baseStart_846974 : Nat := 118140960795 + 846974 * 2 ^ 59
def prefixEnd_846974 : Nat := 4983230072969 + 3 ^ 40 * 846974 * 2
def baseEnd_846974 : Nat := 128860670773710946379213

theorem tailTrace_846974 : CollatzResearch.WordTrace tailWord_846974 prefixEnd_846974 128860670773710946379213 := by
  unfold tailWord_846974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861459954195665561000497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20594453089043549658669317 3861459954195665561000497)
  ·
    refine ⟨2896094965646749170750373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3861459954195665561000497 2896094965646749170750373)
    ·
      refine ⟨543017806058765469515695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2896094965646749170750373 543017806058765469515695)
      ·
        refine ⟨814526709088148204273543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543017806058765469515695 814526709088148204273543)
        ·
          refine ⟨1221790063632222306410315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814526709088148204273543 1221790063632222306410315)
          ·
            refine ⟨1832685095448333459615473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221790063632222306410315 1832685095448333459615473)
            ·
              refine ⟨1374513821586250094711605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1832685095448333459615473 1374513821586250094711605)
              ·
                refine ⟨128860670773710946379213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1374513821586250094711605 128860670773710946379213)
                ·
                  rfl

theorem cell20_846974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_846974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846974 prefixEnd_846974 := by exact prefixLift 846974
  have htrace : WordTrace (prefixWord ++ tailWord_846974) baseStart_846974 baseEnd_846974 := by
    simpa [prefixWord, tailWord_846974, baseEnd_846974] using wordTrace_append hprefix tailTrace_846974
  have hstable : (prefixWord ++ tailWord_846974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846974).length < 2 ^ (prefixWord ++ tailWord_846974).sum := by decide
  have hdescent : baseEnd_846974 < baseStart_846974 := by decide
  rcases family_descends (prefixWord ++ tailWord_846974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846981 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 3]
def baseStart_846981 : Nat := 118140960795 + 846981 * 2 ^ 59
def prefixEnd_846981 : Nat := 4983230072969 + 3 ^ 40 * 846981 * 2
def baseEnd_846981 : Nat := 386585207311871925904277

theorem tailTrace_846981 : CollatzResearch.WordTrace tailWord_846981 prefixEnd_846981 386585207311871925904277 := by
  unfold tailWord_846981
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891934944539964683508797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20594623296359976455672531 30891934944539964683508797)
  ·
    refine ⟨11584475604202486756315799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30891934944539964683508797 11584475604202486756315799)
    ·
      refine ⟨17376713406303730134473699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584475604202486756315799 17376713406303730134473699)
      ·
        refine ⟨26065070109455595201710549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376713406303730134473699 26065070109455595201710549)
        ·
          refine ⟨610900080690365512540091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26065070109455595201710549 610900080690365512540091)
          ·
            refine ⟨916350121035548268810137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610900080690365512540091 916350121035548268810137)
            ·
              refine ⟨687262590776661201607603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916350121035548268810137 687262590776661201607603)
              ·
                refine ⟨1030893886164991802411405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687262590776661201607603 1030893886164991802411405)
                ·
                  refine ⟨386585207311871925904277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030893886164991802411405 386585207311871925904277)
                  ·
                    rfl

theorem cell20_846981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_846981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846981 prefixEnd_846981 := by exact prefixLift 846981
  have htrace : WordTrace (prefixWord ++ tailWord_846981) baseStart_846981 baseEnd_846981 := by
    simpa [prefixWord, tailWord_846981, baseEnd_846981] using wordTrace_append hprefix tailTrace_846981
  have hstable : (prefixWord ++ tailWord_846981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846981).length < 2 ^ (prefixWord ++ tailWord_846981).sum := by decide
  have hdescent : baseEnd_846981 < baseStart_846981 := by decide
  rcases family_descends (prefixWord ++ tailWord_846981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_846985 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 3]
def baseStart_846985 : Nat := 118140960795 + 846985 * 2 ^ 59
def prefixEnd_846985 : Nat := 4983230072969 + 3 ^ 40 * 846985 * 2
def baseEnd_846985 : Nat := 386587033020865689770927

theorem tailTrace_846985 : CollatzResearch.WordTrace tailWord_846985 prefixEnd_846985 386587033020865689770927 := by
  unfold tailWord_846985
  simp only [CollatzResearch.WordTrace]
  refine ⟨30892080836525473366654409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20594720557683648911102939 30892080836525473366654409)
  ·
    refine ⟨23169060627394105024990807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30892080836525473366654409 23169060627394105024990807)
    ·
      refine ⟨34753590941091157537486211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23169060627394105024990807 34753590941091157537486211)
      ·
        refine ⟨52130386411636736306229317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34753590941091157537486211 52130386411636736306229317)
        ·
          refine ⟨9774447452181888057417997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52130386411636736306229317 9774447452181888057417997)
          ·
            refine ⟨3665417794568208021531749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9774447452181888057417997 3665417794568208021531749)
            ·
              refine ⟨687265836481539004037203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3665417794568208021531749 687265836481539004037203)
              ·
                refine ⟨1030898754722308506055805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687265836481539004037203 1030898754722308506055805)
                ·
                  refine ⟨386587033020865689770927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1030898754722308506055805 386587033020865689770927)
                  ·
                    rfl

theorem cell20_846985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_846985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_846985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_846985 prefixEnd_846985 := by exact prefixLift 846985
  have htrace : WordTrace (prefixWord ++ tailWord_846985) baseStart_846985 baseEnd_846985 := by
    simpa [prefixWord, tailWord_846985, baseEnd_846985] using wordTrace_append hprefix tailTrace_846985
  have hstable : (prefixWord ++ tailWord_846985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_846985).length < 2 ^ (prefixWord ++ tailWord_846985).sum := by decide
  have hdescent : baseEnd_846985 < baseStart_846985 := by decide
  rcases family_descends (prefixWord ++ tailWord_846985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847026 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_847026 : Nat := 118140960795 + 847026 * 2 ^ 59
def prefixEnd_847026 : Nat := 4983230072969 + 3 ^ 40 * 847026 * 2
def baseEnd_847026 : Nat := 386605746538051769404093

theorem tailTrace_847026 : CollatzResearch.WordTrace tailWord_847026 prefixEnd_847026 386605746538051769404093 := by
  unfold tailWord_847026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723394057344234342224233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20595717486251291579264621 7723394057344234342224233)
  ·
    refine ⟨5792545543008175756668175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7723394057344234342224233 5792545543008175756668175)
    ·
      refine ⟨8688818314512263635002263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5792545543008175756668175 8688818314512263635002263)
      ·
        refine ⟨13033227471768395452503395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8688818314512263635002263 13033227471768395452503395)
        ·
          refine ⟨19549841207652593178755093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13033227471768395452503395 19549841207652593178755093)
          ·
            refine ⟨916398806608715305254145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19549841207652593178755093 916398806608715305254145)
            ·
              refine ⟨687299104956536478940609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916398806608715305254145 687299104956536478940609)
              ·
                refine ⟨515474328717402359205457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687299104956536478940609 515474328717402359205457)
                ·
                  refine ⟨386605746538051769404093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515474328717402359205457 386605746538051769404093)
                  ·
                    rfl

theorem cell20_847026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_847026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847026 prefixEnd_847026 := by exact prefixLift 847026
  have htrace : WordTrace (prefixWord ++ tailWord_847026) baseStart_847026 baseEnd_847026 := by
    simpa [prefixWord, tailWord_847026, baseEnd_847026] using wordTrace_append hprefix tailTrace_847026
  have hstable : (prefixWord ++ tailWord_847026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847026).length < 2 ^ (prefixWord ++ tailWord_847026).sum := by decide
  have hdescent : baseEnd_847026 < baseStart_847026 := by decide
  rcases family_descends (prefixWord ++ tailWord_847026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847027 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_847027 : Nat := 118140960795 + 847027 * 2 ^ 59
def prefixEnd_847027 : Nat := 4983230072969 + 3 ^ 40 * 847027 * 2
def baseEnd_847027 : Nat := 386606202965300210370755

theorem tailTrace_847027 : CollatzResearch.WordTrace tailWord_847027 prefixEnd_847027 386606202965300210370755 := by
  unfold tailWord_847027
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893612702373314539683335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20595741801582209693122223 30893612702373314539683335)
  ·
    refine ⟨46340419053559971809525003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30893612702373314539683335 46340419053559971809525003)
    ·
      refine ⟨69510628580339957714287505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46340419053559971809525003 69510628580339957714287505)
      ·
        refine ⟨52132971435254968285715629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69510628580339957714287505 52132971435254968285715629)
        ·
          refine ⟨19549864288220613107143361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52132971435254968285715629 19549864288220613107143361)
          ·
            refine ⟨14662398216165459830357521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19549864288220613107143361 14662398216165459830357521)
            ·
              refine ⟨10996798662124094872768141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14662398216165459830357521 10996798662124094872768141)
              ·
                refine ⟨4123799498296535577288053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10996798662124094872768141 4123799498296535577288053)
                ·
                  refine ⟨386606202965300210370755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123799498296535577288053 386606202965300210370755)
                  ·
                    rfl

theorem cell20_847027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_847027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847027 prefixEnd_847027 := by exact prefixLift 847027
  have htrace : WordTrace (prefixWord ++ tailWord_847027) baseStart_847027 baseEnd_847027 := by
    simpa [prefixWord, tailWord_847027, baseEnd_847027] using wordTrace_append hprefix tailTrace_847027
  have hstable : (prefixWord ++ tailWord_847027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847027).length < 2 ^ (prefixWord ++ tailWord_847027).sum := by decide
  have hdescent : baseEnd_847027 < baseStart_847027 := by decide
  rcases family_descends (prefixWord ++ tailWord_847027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847054 : List Nat := [4, 1, 1, 1, 5, 1, 3, 4]
def baseStart_847054 : Nat := 118140960795 + 847054 * 2 ^ 59
def prefixEnd_847054 : Nat := 4983230072969 + 3 ^ 40 * 847054 * 2
def baseEnd_847054 : Nat := 128872842167002705490215

theorem tailTrace_847054 : CollatzResearch.WordTrace tailWord_847054 prefixEnd_847054 128872842167002705490215 := by
  unfold tailWord_847054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3861824684159437268864527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20596398315516998767277477 3861824684159437268864527)
  ·
    refine ⟨5792737026239155903296791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3861824684159437268864527 5792737026239155903296791)
    ·
      refine ⟨8689105539358733854945187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5792737026239155903296791 8689105539358733854945187)
      ·
        refine ⟨13033658309038100782417781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8689105539358733854945187 13033658309038100782417781)
        ·
          refine ⟨1221905466472321948351667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13033658309038100782417781 1221905466472321948351667)
          ·
            refine ⟨1832858199708482922527501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1221905466472321948351667 1832858199708482922527501)
            ·
              refine ⟨687321824890681095947813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1832858199708482922527501 687321824890681095947813)
              ·
                refine ⟨128872842167002705490215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687321824890681095947813 128872842167002705490215)
                ·
                  rfl

theorem cell20_847054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_847054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847054 prefixEnd_847054 := by exact prefixLift 847054
  have htrace : WordTrace (prefixWord ++ tailWord_847054) baseStart_847054 baseEnd_847054 := by
    simpa [prefixWord, tailWord_847054, baseEnd_847054] using wordTrace_append hprefix tailTrace_847054
  have hstable : (prefixWord ++ tailWord_847054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847054).length < 2 ^ (prefixWord ++ tailWord_847054).sum := by decide
  have hdescent : baseEnd_847054 < baseStart_847054 := by decide
  rcases family_descends (prefixWord ++ tailWord_847054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847065 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_847065 : Nat := 118140960795 + 847065 * 2 ^ 59
def prefixEnd_847065 : Nat := 4983230072969 + 3 ^ 40 * 847065 * 2
def baseEnd_847065 : Nat := 386623547200740967103933

theorem tailTrace_847065 : CollatzResearch.WordTrace tailWord_847065 prefixEnd_847065 386623547200740967103933 := by
  unfold tailWord_847065
  simp only [CollatzResearch.WordTrace]
  refine ⟨30894998676235647029566649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20596665784157098019711099 30894998676235647029566649)
  ·
    refine ⟨23171249007176735272174987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30894998676235647029566649 23171249007176735272174987)
    ·
      refine ⟨34756873510765102908262481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23171249007176735272174987 34756873510765102908262481)
      ·
        refine ⟨26067655133073827181196861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34756873510765102908262481 26067655133073827181196861)
        ·
          refine ⟨9775370674902685192948823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26067655133073827181196861 9775370674902685192948823)
          ·
            refine ⟨14663056012354027789423235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775370674902685192948823 14663056012354027789423235)
            ·
              refine ⟨21994584018531041684134853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14663056012354027789423235 21994584018531041684134853)
              ·
                refine ⟨4123984503474570315775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21994584018531041684134853 4123984503474570315775285)
                ·
                  refine ⟨386623547200740967103933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123984503474570315775285 386623547200740967103933)
                  ·
                    rfl

theorem cell20_847065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_847065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847065 prefixEnd_847065 := by exact prefixLift 847065
  have htrace : WordTrace (prefixWord ++ tailWord_847065) baseStart_847065 baseEnd_847065 := by
    simpa [prefixWord, tailWord_847065, baseEnd_847065] using wordTrace_append hprefix tailTrace_847065
  have hstable : (prefixWord ++ tailWord_847065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847065).length < 2 ^ (prefixWord ++ tailWord_847065).sum := by decide
  have hdescent : baseEnd_847065 < baseStart_847065 := by decide
  rcases family_descends (prefixWord ++ tailWord_847065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847082 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_847082 : Nat := 118140960795 + 847082 * 2 ^ 59
def prefixEnd_847082 : Nat := 4983230072969 + 3 ^ 40 * 847082 * 2
def baseEnd_847082 : Nat := 386631306463964463537197

theorem tailTrace_847082 : CollatzResearch.WordTrace tailWord_847082 prefixEnd_847082 386631306463964463537197 := by
  unfold tailWord_847082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723904679293514733233875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20597079144782705955290333 7723904679293514733233875)
  ·
    refine ⟨11585857018940272099850813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7723904679293514733233875 11585857018940272099850813)
    ·
      refine ⟨4344696382102602037444055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11585857018940272099850813 4344696382102602037444055)
      ·
        refine ⟨6517044573153903056166083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344696382102602037444055 6517044573153903056166083)
        ·
          refine ⟨9775566859730854584249125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517044573153903056166083 9775566859730854584249125)
          ·
            refine ⟨1832918786199535234546711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9775566859730854584249125 1832918786199535234546711)
            ·
              refine ⟨2749378179299302851820067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1832918786199535234546711 2749378179299302851820067)
              ·
                refine ⟨4124067268948954277730101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749378179299302851820067 4124067268948954277730101)
                ·
                  refine ⟨386631306463964463537197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4124067268948954277730101 386631306463964463537197)
                  ·
                    rfl

theorem cell20_847082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_847082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847082 prefixEnd_847082 := by exact prefixLift 847082
  have htrace : WordTrace (prefixWord ++ tailWord_847082) baseStart_847082 baseEnd_847082 := by
    simpa [prefixWord, tailWord_847082, baseEnd_847082] using wordTrace_append hprefix tailTrace_847082
  have hstable : (prefixWord ++ tailWord_847082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847082).length < 2 ^ (prefixWord ++ tailWord_847082).sum := by decide
  have hdescent : baseEnd_847082 < baseStart_847082 := by decide
  rcases family_descends (prefixWord ++ tailWord_847082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847085 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 2]
def baseStart_847085 : Nat := 118140960795 + 847085 * 2 ^ 59
def prefixEnd_847085 : Nat := 4983230072969 + 3 ^ 40 * 847085 * 2
def baseEnd_847085 : Nat := 386632675745709786437185

theorem tailTrace_847085 : CollatzResearch.WordTrace tailWord_847085 prefixEnd_847085 386632675745709786437185 := by
  unfold tailWord_847085
  simp only [CollatzResearch.WordTrace]
  refine ⟨30895728136163190445294709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20597152090775460296863139 30895728136163190445294709)
  ·
    refine ⟨2896474512765299104246379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30895728136163190445294709 2896474512765299104246379)
    ·
      refine ⟨4344711769147948656369569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896474512765299104246379 4344711769147948656369569)
      ·
        refine ⟨3258533826860961492277177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4344711769147948656369569 3258533826860961492277177)
        ·
          refine ⟨2443900370145721119207883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3258533826860961492277177 2443900370145721119207883)
          ·
            refine ⟨3665850555218581678811825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443900370145721119207883 3665850555218581678811825)
            ·
              refine ⟨2749387916413936259108869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3665850555218581678811825 2749387916413936259108869)
              ·
                refine ⟨515510234327613048582913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2749387916413936259108869 515510234327613048582913)
                ·
                  refine ⟨386632675745709786437185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515510234327613048582913 386632675745709786437185)
                  ·
                    rfl

theorem cell20_847085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_847085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847085 prefixEnd_847085 := by exact prefixLift 847085
  have htrace : WordTrace (prefixWord ++ tailWord_847085) baseStart_847085 baseEnd_847085 := by
    simpa [prefixWord, tailWord_847085, baseEnd_847085] using wordTrace_append hprefix tailTrace_847085
  have hstable : (prefixWord ++ tailWord_847085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847085).length < 2 ^ (prefixWord ++ tailWord_847085).sum := by decide
  have hdescent : baseEnd_847085 < baseStart_847085 := by decide
  rcases family_descends (prefixWord ++ tailWord_847085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847144 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_847144 : Nat := 118140960795 + 847144 * 2 ^ 59
def prefixEnd_847144 : Nat := 4983230072969 + 3 ^ 40 * 847144 * 2
def baseEnd_847144 : Nat := 386659604953367803470277

theorem tailTrace_847144 : CollatzResearch.WordTrace tailWord_847144 prefixEnd_847144 386659604953367803470277 := by
  unfold tailWord_847144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15448940021474721760846243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20598586695299629014461657 15448940021474721760846243)
  ·
    refine ⟨23173410032212082641269365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15448940021474721760846243 23173410032212082641269365)
    ·
      refine ⟨2172507190519882747619003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23173410032212082641269365 2172507190519882747619003)
      ·
        refine ⟨3258760785779824121428505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172507190519882747619003 3258760785779824121428505)
        ·
          refine ⟨2444070589334868091071379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3258760785779824121428505 2444070589334868091071379)
          ·
            refine ⟨3666105884002302136607069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444070589334868091071379 3666105884002302136607069)
            ·
              refine ⟨1374789706500863301227651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3666105884002302136607069 1374789706500863301227651)
              ·
                refine ⟨2062184559751294951841477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374789706500863301227651 2062184559751294951841477)
                ·
                  refine ⟨386659604953367803470277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062184559751294951841477 386659604953367803470277)
                  ·
                    rfl

theorem cell20_847144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_847144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847144 prefixEnd_847144 := by exact prefixLift 847144
  have htrace : WordTrace (prefixWord ++ tailWord_847144) baseStart_847144 baseEnd_847144 := by
    simpa [prefixWord, tailWord_847144, baseEnd_847144] using wordTrace_append hprefix tailTrace_847144
  have hstable : (prefixWord ++ tailWord_847144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847144).length < 2 ^ (prefixWord ++ tailWord_847144).sum := by decide
  have hdescent : baseEnd_847144 < baseStart_847144 := by decide
  rcases family_descends (prefixWord ++ tailWord_847144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847154 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_847154 : Nat := 118140960795 + 847154 * 2 ^ 59
def prefixEnd_847154 : Nat := 4983230072969 + 3 ^ 40 * 847154 * 2
def baseEnd_847154 : Nat := 386664169225852213136903

theorem tailTrace_847154 : CollatzResearch.WordTrace tailWord_847154 prefixEnd_847154 386664169225852213136903 := by
  unfold tailWord_847154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724561193228303807389129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20598829848608810153037677 7724561193228303807389129)
  ·
    refine ⟨5793420894921227855541847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7724561193228303807389129 5793420894921227855541847)
    ·
      refine ⟨8690131342381841783312771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5793420894921227855541847 8690131342381841783312771)
      ·
        refine ⟨13035197013572762674969157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690131342381841783312771 13035197013572762674969157)
        ·
          refine ⟨2444099440044893001556717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13035197013572762674969157 2444099440044893001556717)
          ·
            refine ⟨916537290016834875583769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2444099440044893001556717 916537290016834875583769)
            ·
              refine ⟨687402967512626156687827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 916537290016834875583769 687402967512626156687827)
              ·
                refine ⟨1031104451268939235031741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687402967512626156687827 1031104451268939235031741)
                ·
                  refine ⟨386664169225852213136903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031104451268939235031741 386664169225852213136903)
                  ·
                    rfl

theorem cell20_847154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_847154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847154 prefixEnd_847154 := by exact prefixLift 847154
  have htrace : WordTrace (prefixWord ++ tailWord_847154) baseStart_847154 baseEnd_847154 := by
    simpa [prefixWord, tailWord_847154, baseEnd_847154] using wordTrace_append hprefix tailTrace_847154
  have hstable : (prefixWord ++ tailWord_847154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847154).length < 2 ^ (prefixWord ++ tailWord_847154).sum := by decide
  have hdescent : baseEnd_847154 < baseStart_847154 := by decide
  rcases family_descends (prefixWord ++ tailWord_847154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847182 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_847182 : Nat := 118140960795 + 847182 * 2 ^ 59
def prefixEnd_847182 : Nat := 4983230072969 + 3 ^ 40 * 847182 * 2
def baseEnd_847182 : Nat := 386676949188808560203455

theorem tailTrace_847182 : CollatzResearch.WordTrace tailWord_847182 prefixEnd_847182 386676949188808560203455 := by
  unfold tailWord_847182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862408252101472001446975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20599510677874517341050533 3862408252101472001446975)
  ·
    refine ⟨5793612378152208002170463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3862408252101472001446975 5793612378152208002170463)
    ·
      refine ⟨8690418567228312003255695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5793612378152208002170463 8690418567228312003255695)
      ·
        refine ⟨13035627850842468004883543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690418567228312003255695 13035627850842468004883543)
        ·
          refine ⟨19553441776263702007325315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13035627850842468004883543 19553441776263702007325315)
          ·
            refine ⟨29330162664395553010987973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19553441776263702007325315 29330162664395553010987973)
            ·
              refine ⟨5499405499574166189560245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29330162664395553010987973 5499405499574166189560245)
              ·
                refine ⟨515569265585078080271273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5499405499574166189560245 515569265585078080271273)
                ·
                  refine ⟨386676949188808560203455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515569265585078080271273 386676949188808560203455)
                  ·
                    rfl

theorem cell20_847182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_847182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847182 prefixEnd_847182 := by exact prefixLift 847182
  have htrace : WordTrace (prefixWord ++ tailWord_847182) baseStart_847182 baseEnd_847182 := by
    simpa [prefixWord, tailWord_847182, baseEnd_847182] using wordTrace_append hprefix tailTrace_847182
  have hstable : (prefixWord ++ tailWord_847182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847182).length < 2 ^ (prefixWord ++ tailWord_847182).sum := by decide
  have hdescent : baseEnd_847182 < baseStart_847182 := by decide
  rcases family_descends (prefixWord ++ tailWord_847182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847258 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_847258 : Nat := 118140960795 + 847258 * 2 ^ 59
def prefixEnd_847258 : Nat := 4983230072969 + 3 ^ 40 * 847258 * 2
def baseEnd_847258 : Nat := 386711637659690073669811

theorem tailTrace_847258 : CollatzResearch.WordTrace tailWord_847258 prefixEnd_847258 386711637659690073669811 := by
  unfold tailWord_847258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725509491134110247835607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20601358643024293994228285 7725509491134110247835607)
  ·
    refine ⟨11588264236701165371753411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725509491134110247835607 11588264236701165371753411)
    ·
      refine ⟨17382396355051748057630117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588264236701165371753411 17382396355051748057630117)
      ·
        refine ⟨3259199316572202760805647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17382396355051748057630117 3259199316572202760805647)
        ·
          refine ⟨4888798974858304141208471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259199316572202760805647 4888798974858304141208471)
          ·
            refine ⟨7333198462287456211812707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888798974858304141208471 7333198462287456211812707)
            ·
              refine ⟨10999797693431184317719061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333198462287456211812707 10999797693431184317719061)
              ·
                refine ⟨515615516879586764893081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10999797693431184317719061 515615516879586764893081)
                ·
                  refine ⟨386711637659690073669811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515615516879586764893081 386711637659690073669811)
                  ·
                    rfl

theorem cell20_847258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_847258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847258 prefixEnd_847258 := by exact prefixLift 847258
  have htrace : WordTrace (prefixWord ++ tailWord_847258) baseStart_847258 baseEnd_847258 := by
    simpa [prefixWord, tailWord_847258, baseEnd_847258] using wordTrace_append hprefix tailTrace_847258
  have hstable : (prefixWord ++ tailWord_847258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847258).length < 2 ^ (prefixWord ++ tailWord_847258).sum := by decide
  have hdescent : baseEnd_847258 < baseStart_847258 := by decide
  rcases family_descends (prefixWord ++ tailWord_847258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847292 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 2]
def baseStart_847292 : Nat := 118140960795 + 847292 * 2 ^ 59
def prefixEnd_847292 : Nat := 4983230072969 + 3 ^ 40 * 847292 * 2
def baseEnd_847292 : Nat := 386727156186137066536339

theorem tailTrace_847292 : CollatzResearch.WordTrace tailWord_847292 prefixEnd_847292 386727156186137066536339 := by
  unfold tailWord_847292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15451639023206632399040065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20602185364275509865386753 15451639023206632399040065)
  ·
    refine ⟨11588729267404974299280049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15451639023206632399040065 11588729267404974299280049)
    ·
      refine ⟨8691546950553730724460037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11588729267404974299280049 8691546950553730724460037)
      ·
        refine ⟨1629665053228824510836257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8691546950553730724460037 1629665053228824510836257)
        ·
          refine ⟨1222248789921618383127193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629665053228824510836257 1222248789921618383127193)
          ·
            refine ⟨916686592441213787345395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222248789921618383127193 916686592441213787345395)
            ·
              refine ⟨1375029888661820681018093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916686592441213787345395 1375029888661820681018093)
              ·
                refine ⟨515636208248182755381785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375029888661820681018093 515636208248182755381785)
                ·
                  refine ⟨386727156186137066536339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515636208248182755381785 386727156186137066536339)
                  ·
                    rfl

theorem cell20_847292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_847292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847292 prefixEnd_847292 := by exact prefixLift 847292
  have htrace : WordTrace (prefixWord ++ tailWord_847292) baseStart_847292 baseEnd_847292 := by
    simpa [prefixWord, tailWord_847292, baseEnd_847292] using wordTrace_append hprefix tailTrace_847292
  have hstable : (prefixWord ++ tailWord_847292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847292).length < 2 ^ (prefixWord ++ tailWord_847292).sum := by decide
  have hdescent : baseEnd_847292 < baseStart_847292 := by decide
  rcases family_descends (prefixWord ++ tailWord_847292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847293 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_847293 : Nat := 118140960795 + 847293 * 2 ^ 59
def prefixEnd_847293 : Nat := 4983230072969 + 3 ^ 40 * 847293 * 2
def baseEnd_847293 : Nat := 386727612613385507503001

theorem tailTrace_847293 : CollatzResearch.WordTrace tailWord_847293 prefixEnd_847293 386727612613385507503001 := by
  unfold tailWord_847293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30903314519409641968866533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20602209679606427979244355 30903314519409641968866533)
  ·
    refine ⟨5794371472389307869162475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30903314519409641968866533 5794371472389307869162475)
    ·
      refine ⟨8691557208583961803743713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5794371472389307869162475 8691557208583961803743713)
      ·
        refine ⟨6518667906437971352807785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8691557208583961803743713 6518667906437971352807785)
        ·
          refine ⟨4889000929828478514605839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6518667906437971352807785 4889000929828478514605839)
          ·
            refine ⟨7333501394742717771908759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889000929828478514605839 7333501394742717771908759)
            ·
              refine ⟨11000252092114076657863139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333501394742717771908759 11000252092114076657863139)
              ·
                refine ⟨16500378138171114986794709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000252092114076657863139 16500378138171114986794709)
                ·
                  refine ⟨386727612613385507503001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16500378138171114986794709 386727612613385507503001)
                  ·
                    rfl

theorem cell20_847293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_847293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847293 prefixEnd_847293 := by exact prefixLift 847293
  have htrace : WordTrace (prefixWord ++ tailWord_847293) baseStart_847293 baseEnd_847293 := by
    simpa [prefixWord, tailWord_847293, baseEnd_847293] using wordTrace_append hprefix tailTrace_847293
  have hstable : (prefixWord ++ tailWord_847293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847293).length < 2 ^ (prefixWord ++ tailWord_847293).sum := by decide
  have hdescent : baseEnd_847293 < baseStart_847293 := by decide
  rcases family_descends (prefixWord ++ tailWord_847293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847296 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_847296 : Nat := 118140960795 + 847296 * 2 ^ 59
def prefixEnd_847296 : Nat := 4983230072969 + 3 ^ 40 * 847296 * 2
def baseEnd_847296 : Nat := 386728981895130830402989

theorem tailTrace_847296 : CollatzResearch.WordTrace tailWord_847296 prefixEnd_847296 386728981895130830402989 := by
  unfold tailWord_847296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15451711969199386740612871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20602282625599182320817161 15451711969199386740612871)
  ·
    refine ⟨23177567953799080110919307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15451711969199386740612871 23177567953799080110919307)
    ·
      refine ⟨34766351930698620166378961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23177567953799080110919307 34766351930698620166378961)
      ·
        refine ⟨26074763948023965124784221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34766351930698620166378961 26074763948023965124784221)
        ·
          refine ⟨9778036480508986921794083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26074763948023965124784221 9778036480508986921794083)
          ·
            refine ⟨14667054720763480382691125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778036480508986921794083 14667054720763480382691125)
            ·
              refine ⟨1375036380071576285877293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14667054720763480382691125 1375036380071576285877293)
              ·
                refine ⟨515638642526841107203985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375036380071576285877293 515638642526841107203985)
                ·
                  refine ⟨386728981895130830402989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515638642526841107203985 386728981895130830402989)
                  ·
                    rfl

theorem cell20_847296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_847296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847296 prefixEnd_847296 := by exact prefixLift 847296
  have htrace : WordTrace (prefixWord ++ tailWord_847296) baseStart_847296 baseEnd_847296 := by
    simpa [prefixWord, tailWord_847296, baseEnd_847296] using wordTrace_append hprefix tailTrace_847296
  have hstable : (prefixWord ++ tailWord_847296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847296).length < 2 ^ (prefixWord ++ tailWord_847296).sum := by decide
  have hdescent : baseEnd_847296 < baseStart_847296 := by decide
  rcases family_descends (prefixWord ++ tailWord_847296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847307 : List Nat := [1, 1, 1, 1, 3, 3, 10]
def baseStart_847307 : Nat := 118140960795 + 847307 * 2 ^ 59
def prefixEnd_847307 : Nat := 4983230072969 + 3 ^ 40 * 847307 * 2
def baseEnd_847307 : Nat := 42970444732762631226253

theorem tailTrace_847307 : CollatzResearch.WordTrace tailWord_847307 prefixEnd_847307 42970444732762631226253 := by
  unfold tailWord_847307
  simp only [CollatzResearch.WordTrace]
  refine ⟨30903825141358922359876175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20602550094239281573250783 30903825141358922359876175)
  ·
    refine ⟨46355737712038383539814263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30903825141358922359876175 46355737712038383539814263)
    ·
      refine ⟨69533606568057575309721395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46355737712038383539814263 69533606568057575309721395)
      ·
        refine ⟨104300409852086362964582093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69533606568057575309721395 104300409852086362964582093)
        ·
          refine ⟨39112653694532386111718285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104300409852086362964582093 39112653694532386111718285)
          ·
            refine ⟨14667245135449644791894357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39112653694532386111718285 14667245135449644791894357)
            ·
              refine ⟨42970444732762631226253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14667245135449644791894357 42970444732762631226253)
              ·
                rfl

theorem cell20_847307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_847307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847307 prefixEnd_847307 := by exact prefixLift 847307
  have htrace : WordTrace (prefixWord ++ tailWord_847307) baseStart_847307 baseEnd_847307 := by
    simpa [prefixWord, tailWord_847307, baseEnd_847307] using wordTrace_append hprefix tailTrace_847307
  have hstable : (prefixWord ++ tailWord_847307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847307).length < 2 ^ (prefixWord ++ tailWord_847307).sum := by decide
  have hdescent : baseEnd_847307 < baseStart_847307 := by decide
  rcases family_descends (prefixWord ++ tailWord_847307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847358 : List Nat := [4, 2, 2, 3, 2, 7]
def baseStart_847358 : Nat := 118140960795 + 847358 * 2 ^ 59
def prefixEnd_847358 : Nat := 4983230072969 + 3 ^ 40 * 847358 * 2
def baseEnd_847358 : Nat := 14324343717945710012447

theorem tailTrace_847358 : CollatzResearch.WordTrace tailWord_847358 prefixEnd_847358 14324343717945710012447 := by
  unfold tailWord_847358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863210658021769758747841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20603790176116105379988485 3863210658021769758747841)
  ·
    refine ⟨2897407993516327319060881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3863210658021769758747841 2897407993516327319060881)
    ·
      refine ⟨2173055995137245489295661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2897407993516327319060881 2173055995137245489295661)
      ·
        refine ⟨814895998176467058485873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2173055995137245489295661 814895998176467058485873)
        ·
          refine ⟨611171998632350293864405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814895998176467058485873 611171998632350293864405)
          ·
            refine ⟨14324343717945710012447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 611171998632350293864405 14324343717945710012447)
            ·
              rfl

theorem cell20_847358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 7].length) (baseStart_847358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847358 prefixEnd_847358 := by exact prefixLift 847358
  have htrace : WordTrace (prefixWord ++ tailWord_847358) baseStart_847358 baseEnd_847358 := by
    simpa [prefixWord, tailWord_847358, baseEnd_847358] using wordTrace_append hprefix tailTrace_847358
  have hstable : (prefixWord ++ tailWord_847358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847358).length < 2 ^ (prefixWord ++ tailWord_847358).sum := by decide
  have hdescent : baseEnd_847358 < baseStart_847358 := by decide
  rcases family_descends (prefixWord ++ tailWord_847358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847393 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_847393 : Nat := 118140960795 + 847393 * 2 ^ 59
def prefixEnd_847393 : Nat := 4983230072969 + 3 ^ 40 * 847393 * 2
def baseEnd_847393 : Nat := 386773255338229604169259

theorem tailTrace_847393 : CollatzResearch.WordTrace tailWord_847393 prefixEnd_847393 386773255338229604169259 := by
  unfold tailWord_847393
  simp only [CollatzResearch.WordTrace]
  refine ⟨30906961819047359047506833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20604641212698239365004555 30906961819047359047506833)
  ·
    refine ⟨23180221364285519285630125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30906961819047359047506833 23180221364285519285630125)
    ·
      refine ⟨8692583011607069732111297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23180221364285519285630125 8692583011607069732111297)
      ·
        refine ⟨6519437258705302299083473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8692583011607069732111297 6519437258705302299083473)
        ·
          refine ⟨4889577944028976724312605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6519437258705302299083473 4889577944028976724312605)
          ·
            refine ⟨1833591729010866271617227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4889577944028976724312605 1833591729010866271617227)
            ·
              refine ⟨2750387593516299407425841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833591729010866271617227 2750387593516299407425841)
              ·
                refine ⟨2062790695137224555569381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750387593516299407425841 2062790695137224555569381)
                ·
                  refine ⟨386773255338229604169259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062790695137224555569381 386773255338229604169259)
                  ·
                    rfl

theorem cell20_847393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_847393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847393 prefixEnd_847393 := by exact prefixLift 847393
  have htrace : WordTrace (prefixWord ++ tailWord_847393) baseStart_847393 baseEnd_847393 := by
    simpa [prefixWord, tailWord_847393, baseEnd_847393] using wordTrace_append hprefix tailTrace_847393
  have hstable : (prefixWord ++ tailWord_847393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847393).length < 2 ^ (prefixWord ++ tailWord_847393).sum := by decide
  have hdescent : baseEnd_847393 < baseStart_847393 := by decide
  rcases family_descends (prefixWord ++ tailWord_847393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847420 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_847420 : Nat := 118140960795 + 847420 * 2 ^ 59
def prefixEnd_847420 : Nat := 4983230072969 + 3 ^ 40 * 847420 * 2
def baseEnd_847420 : Nat := 386785578873937510269149

theorem tailTrace_847420 : CollatzResearch.WordTrace tailWord_847420 prefixEnd_847420 386785578873937510269149 := by
  unfold tailWord_847420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453973294974771329369857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20605297726633028439159809 15453973294974771329369857)
  ·
    refine ⟨11590479971231078497027393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15453973294974771329369857 11590479971231078497027393)
    ·
      refine ⟨8692859978423308872770545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11590479971231078497027393 8692859978423308872770545)
      ·
        refine ⟨6519644983817481654577909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8692859978423308872770545 6519644983817481654577909)
        ·
          refine ⟨611216717232888905116679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6519644983817481654577909 611216717232888905116679)
          ·
            refine ⟨916825075849333357675019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611216717232888905116679 916825075849333357675019)
            ·
              refine ⟨1375237613774000036512529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916825075849333357675019 1375237613774000036512529)
              ·
                refine ⟨1031428210330500027384397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375237613774000036512529 1031428210330500027384397)
                ·
                  refine ⟨386785578873937510269149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031428210330500027384397 386785578873937510269149)
                  ·
                    rfl

theorem cell20_847420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_847420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847420 prefixEnd_847420 := by exact prefixLift 847420
  have htrace : WordTrace (prefixWord ++ tailWord_847420) baseStart_847420 baseEnd_847420 := by
    simpa [prefixWord, tailWord_847420, baseEnd_847420] using wordTrace_append hprefix tailTrace_847420
  have hstable : (prefixWord ++ tailWord_847420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847420).length < 2 ^ (prefixWord ++ tailWord_847420).sum := by decide
  have hdescent : baseEnd_847420 < baseStart_847420 := by decide
  rcases family_descends (prefixWord ++ tailWord_847420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847483 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_847483 : Nat := 118140960795 + 847483 * 2 ^ 59
def prefixEnd_847483 : Nat := 4983230072969 + 3 ^ 40 * 847483 * 2
def baseEnd_847483 : Nat := 386814333790589291168891

theorem tailTrace_847483 : CollatzResearch.WordTrace tailWord_847483 prefixEnd_847483 386814333790589291168891 := by
  unfold tailWord_847483
  simp only [CollatzResearch.WordTrace]
  refine ⟨30910244388721304418283103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20606829592480869612188735 30910244388721304418283103)
  ·
    refine ⟨46365366583081956627424655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30910244388721304418283103 46365366583081956627424655)
    ·
      refine ⟨69548049874622934941136983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46365366583081956627424655 69548049874622934941136983)
      ·
        refine ⟨104322074811934402411705475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69548049874622934941136983 104322074811934402411705475)
        ·
          refine ⟨156483112217901603617558213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104322074811934402411705475 156483112217901603617558213)
          ·
            refine ⟨29340583540856550678292165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156483112217901603617558213 29340583540856550678292165)
            ·
              refine ⟨5501359413910603252179781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29340583540856550678292165 5501359413910603252179781)
              ·
                refine ⟨1031504890108238109783709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5501359413910603252179781 1031504890108238109783709)
                ·
                  refine ⟨386814333790589291168891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031504890108238109783709 386814333790589291168891)
                  ·
                    rfl

theorem cell20_847483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_847483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847483 prefixEnd_847483 := by exact prefixLift 847483
  have htrace : WordTrace (prefixWord ++ tailWord_847483) baseStart_847483 baseEnd_847483 := by
    simpa [prefixWord, tailWord_847483, baseEnd_847483] using wordTrace_append hprefix tailTrace_847483
  have hstable : (prefixWord ++ tailWord_847483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847483).length < 2 ^ (prefixWord ++ tailWord_847483).sum := by decide
  have hdescent : baseEnd_847483 < baseStart_847483 := by decide
  rcases family_descends (prefixWord ++ tailWord_847483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847497 : List Nat := [1, 2, 1, 1, 4, 1, 3, 7]
def baseStart_847497 : Nat := 118140960795 + 847497 * 2 ^ 59
def prefixEnd_847497 : Nat := 4983230072969 + 3 ^ 40 * 847497 * 2
def baseEnd_847497 : Nat := 128940241257355821567389

theorem tailTrace_847497 : CollatzResearch.WordTrace tailWord_847497 prefixEnd_847497 128940241257355821567389 := by
  unfold tailWord_847497
  simp only [CollatzResearch.WordTrace]
  refine ⟨30910755010670584809292745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20607170007113723206195163 30910755010670584809292745)
  ·
    refine ⟨23183066258002938606969559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30910755010670584809292745 23183066258002938606969559)
    ·
      refine ⟨34774599387004407910454339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23183066258002938606969559 34774599387004407910454339)
      ·
        refine ⟨52161899080506611865681509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34774599387004407910454339 52161899080506611865681509)
        ·
          refine ⟨9780356077594989724815283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52161899080506611865681509 9780356077594989724815283)
          ·
            refine ⟨14670534116392484587222925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780356077594989724815283 14670534116392484587222925)
            ·
              refine ⟨5501450293647181720208597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14670534116392484587222925 5501450293647181720208597)
              ·
                refine ⟨128940241257355821567389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5501450293647181720208597 128940241257355821567389)
                ·
                  rfl

theorem cell20_847497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_847497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847497 prefixEnd_847497 := by exact prefixLift 847497
  have htrace : WordTrace (prefixWord ++ tailWord_847497) baseStart_847497 baseEnd_847497 := by
    simpa [prefixWord, tailWord_847497, baseEnd_847497] using wordTrace_append hprefix tailTrace_847497
  have hstable : (prefixWord ++ tailWord_847497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847497).length < 2 ^ (prefixWord ++ tailWord_847497).sum := by decide
  have hdescent : baseEnd_847497 < baseStart_847497 := by decide
  rcases family_descends (prefixWord ++ tailWord_847497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847534 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_847534 : Nat := 118140960795 + 847534 * 2 ^ 59
def prefixEnd_847534 : Nat := 4983230072969 + 3 ^ 40 * 847534 * 2
def baseEnd_847534 : Nat := 386837611580259780468683

theorem tailTrace_847534 : CollatzResearch.WordTrace tailWord_847534 prefixEnd_847534 386837611580259780468683 := by
  unfold tailWord_847534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864013063942067516048707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20608069674357693418926437 3864013063942067516048707)
  ·
    refine ⟨5796019595913101274073061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3864013063942067516048707 5796019595913101274073061)
    ·
      refine ⟨1086753674233706488888699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5796019595913101274073061 1086753674233706488888699)
      ·
        refine ⟨1630130511350559733333049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086753674233706488888699 1630130511350559733333049)
        ·
          refine ⟨1222597883512919799999787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630130511350559733333049 1222597883512919799999787)
          ·
            refine ⟨1833896825269379699999681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222597883512919799999787 1833896825269379699999681)
            ·
              refine ⟨1375422618952034774999761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833896825269379699999681 1375422618952034774999761)
              ·
                refine ⟨1031566964214026081249821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375422618952034774999761 1031566964214026081249821)
                ·
                  refine ⟨386837611580259780468683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031566964214026081249821 386837611580259780468683)
                  ·
                    rfl

theorem cell20_847534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_847534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847534 prefixEnd_847534 := by exact prefixLift 847534
  have htrace : WordTrace (prefixWord ++ tailWord_847534) baseStart_847534 baseEnd_847534 := by
    simpa [prefixWord, tailWord_847534, baseEnd_847534] using wordTrace_append hprefix tailTrace_847534
  have hstable : (prefixWord ++ tailWord_847534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847534).length < 2 ^ (prefixWord ++ tailWord_847534).sum := by decide
  have hdescent : baseEnd_847534 < baseStart_847534 := by decide
  rcases family_descends (prefixWord ++ tailWord_847534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847541 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 2]
def baseStart_847541 : Nat := 118140960795 + 847541 * 2 ^ 59
def prefixEnd_847541 : Nat := 4983230072969 + 3 ^ 40 * 847541 * 2
def baseEnd_847541 : Nat := 386840806570998867235321

theorem tailTrace_847541 : CollatzResearch.WordTrace tailWord_847541 prefixEnd_847541 386840806570998867235321 := by
  unfold tailWord_847541
  simp only [CollatzResearch.WordTrace]
  refine ⟨30912359822511180323894477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20608239881674120215929651 30912359822511180323894477)
  ·
    refine ⟨11592134933441692621460429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30912359822511180323894477 11592134933441692621460429)
    ·
      refine ⟨4347050600040634733047661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11592134933441692621460429 4347050600040634733047661)
      ·
        refine ⟨1630143975015238024892873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4347050600040634733047661 1630143975015238024892873)
        ·
          refine ⟨1222607981261428518669655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630143975015238024892873 1222607981261428518669655)
          ·
            refine ⟨1833911971892142778004483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222607981261428518669655 1833911971892142778004483)
            ·
              refine ⟨2750867957838214167006725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833911971892142778004483 2750867957838214167006725)
              ·
                refine ⟨515787742094665156313761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2750867957838214167006725 515787742094665156313761)
                ·
                  refine ⟨386840806570998867235321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515787742094665156313761 386840806570998867235321)
                  ·
                    rfl

theorem cell20_847541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_847541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847541 prefixEnd_847541 := by exact prefixLift 847541
  have htrace : WordTrace (prefixWord ++ tailWord_847541) baseStart_847541 baseEnd_847541 := by
    simpa [prefixWord, tailWord_847541, baseEnd_847541] using wordTrace_append hprefix tailTrace_847541
  have hstable : (prefixWord ++ tailWord_847541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847541).length < 2 ^ (prefixWord ++ tailWord_847541).sum := by decide
  have hdescent : baseEnd_847541 < baseStart_847541 := by decide
  rcases family_descends (prefixWord ++ tailWord_847541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847559 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_847559 : Nat := 118140960795 + 847559 * 2 ^ 59
def prefixEnd_847559 : Nat := 4983230072969 + 3 ^ 40 * 847559 * 2
def baseEnd_847559 : Nat := 386849022261470804635247

theorem tailTrace_847559 : CollatzResearch.WordTrace tailWord_847559 prefixEnd_847559 386849022261470804635247 := by
  unfold tailWord_847559
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913016336445969398049731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20608677557630646265366487 30913016336445969398049731)
  ·
    refine ⟨46369524504668954097074597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30913016336445969398049731 46369524504668954097074597)
    ·
      refine ⟨8694285844625428893201487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46369524504668954097074597 8694285844625428893201487)
      ·
        refine ⟨13041428766938143339802231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8694285844625428893201487 13041428766938143339802231)
        ·
          refine ⟨19562143150407215009703347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13041428766938143339802231 19562143150407215009703347)
          ·
            refine ⟨29343214725610822514555021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19562143150407215009703347 29343214725610822514555021)
            ·
              refine ⟨11003705522104058442958133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29343214725610822514555021 11003705522104058442958133)
              ·
                refine ⟨1031597392697255479027325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11003705522104058442958133 1031597392697255479027325)
                ·
                  refine ⟨386849022261470804635247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031597392697255479027325 386849022261470804635247)
                  ·
                    rfl

theorem cell20_847559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_847559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847559 prefixEnd_847559 := by exact prefixLift 847559
  have htrace : WordTrace (prefixWord ++ tailWord_847559) baseStart_847559 baseEnd_847559 := by
    simpa [prefixWord, tailWord_847559, baseEnd_847559] using wordTrace_append hprefix tailTrace_847559
  have hstable : (prefixWord ++ tailWord_847559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847559).length < 2 ^ (prefixWord ++ tailWord_847559).sum := by decide
  have hdescent : baseEnd_847559 < baseStart_847559 := by decide
  rcases family_descends (prefixWord ++ tailWord_847559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847628 : List Nat := [2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_847628 : Nat := 118140960795 + 847628 * 2 ^ 59
def prefixEnd_847628 : Nat := 4983230072969 + 3 ^ 40 * 847628 * 2
def baseEnd_847628 : Nat := 128960171913871077111655

theorem tailTrace_847628 : CollatzResearch.WordTrace tailWord_847628 prefixEnd_847628 128960171913871077111655 := by
  unfold tailWord_847628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457766486597997091155769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20610355315463996121541025 15457766486597997091155769)
  ·
    refine ⟨11593324864948497818366827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15457766486597997091155769 11593324864948497818366827)
    ·
      refine ⟨17389987297422746727550241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593324864948497818366827 17389987297422746727550241)
      ·
        refine ⟨13042490473067060045662681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17389987297422746727550241 13042490473067060045662681)
        ·
          refine ⟨9781867854800295034247011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13042490473067060045662681 9781867854800295034247011)
          ·
            refine ⟨14672801782200442551370517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781867854800295034247011 14672801782200442551370517)
            ·
              refine ⟨687787583540645744595493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14672801782200442551370517 687787583540645744595493)
              ·
                refine ⟨128960171913871077111655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687787583540645744595493 128960171913871077111655)
                ·
                  rfl

theorem cell20_847628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_847628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847628 prefixEnd_847628 := by exact prefixLift 847628
  have htrace : WordTrace (prefixWord ++ tailWord_847628) baseStart_847628 baseEnd_847628 := by
    simpa [prefixWord, tailWord_847628, baseEnd_847628] using wordTrace_append hprefix tailTrace_847628
  have hstable : (prefixWord ++ tailWord_847628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847628).length < 2 ^ (prefixWord ++ tailWord_847628).sum := by decide
  have hdescent : baseEnd_847628 < baseStart_847628 := by decide
  rcases family_descends (prefixWord ++ tailWord_847628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847634 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_847634 : Nat := 118140960795 + 847634 * 2 ^ 59
def prefixEnd_847634 : Nat := 4983230072969 + 3 ^ 40 * 847634 * 2
def baseEnd_847634 : Nat := 386883254305103877134941

theorem tailTrace_847634 : CollatzResearch.WordTrace tailWord_847634 prefixEnd_847634 386883254305103877134941 := by
  unfold tailWord_847634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728937952793564301757489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20610501207449504804686637 7728937952793564301757489)
  ·
    refine ⟨5796703464595173226318117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7728937952793564301757489 5796703464595173226318117)
    ·
      refine ⟨1086881899611594979934647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5796703464595173226318117 1086881899611594979934647)
      ·
        refine ⟨1630322849417392469901971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086881899611594979934647 1630322849417392469901971)
        ·
          refine ⟨2445484274126088704852957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630322849417392469901971 2445484274126088704852957)
          ·
            refine ⟨917056602797283264319859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2445484274126088704852957 917056602797283264319859)
            ·
              refine ⟨1375584904195924896479789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917056602797283264319859 1375584904195924896479789)
              ·
                refine ⟨515844339073471836179921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375584904195924896479789 515844339073471836179921)
                ·
                  refine ⟨386883254305103877134941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515844339073471836179921 386883254305103877134941)
                  ·
                    rfl

theorem cell20_847634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_847634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847634 prefixEnd_847634 := by exact prefixLift 847634
  have htrace : WordTrace (prefixWord ++ tailWord_847634) baseStart_847634 baseEnd_847634 := by
    simpa [prefixWord, tailWord_847634, baseEnd_847634] using wordTrace_append hprefix tailTrace_847634
  have hstable : (prefixWord ++ tailWord_847634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847634).length < 2 ^ (prefixWord ++ tailWord_847634).sum := by decide
  have hdescent : baseEnd_847634 < baseStart_847634 := by decide
  rcases family_descends (prefixWord ++ tailWord_847634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847649 : List Nat := [1, 2, 3, 2, 1, 3, 8]
def baseStart_847649 : Nat := 118140960795 + 847649 * 2 ^ 59
def prefixEnd_847649 : Nat := 4983230072969 + 3 ^ 40 * 847649 * 2
def baseEnd_847649 : Nat := 42987788968203387959431

theorem tailTrace_847649 : CollatzResearch.WordTrace tailWord_847649 prefixEnd_847649 42987788968203387959431 := by
  unfold tailWord_847649
  simp only [CollatzResearch.WordTrace]
  refine ⟨30916298906119914768826001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20610865937413276512550667 30916298906119914768826001)
  ·
    refine ⟨23187224179589936076619501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30916298906119914768826001 23187224179589936076619501)
    ·
      refine ⟨8695209067346226028732313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23187224179589936076619501 8695209067346226028732313)
      ·
        refine ⟨6521406800509669521549235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8695209067346226028732313 6521406800509669521549235)
        ·
          refine ⟨9782110200764504282323853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521406800509669521549235 9782110200764504282323853)
          ·
            refine ⟨3668291325286689105871445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9782110200764504282323853 3668291325286689105871445)
            ·
              refine ⟨42987788968203387959431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3668291325286689105871445 42987788968203387959431)
              ·
                rfl

theorem cell20_847649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_847649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847649 prefixEnd_847649 := by exact prefixLift 847649
  have htrace : WordTrace (prefixWord ++ tailWord_847649) baseStart_847649 baseEnd_847649 := by
    simpa [prefixWord, tailWord_847649, baseEnd_847649] using wordTrace_append hprefix tailTrace_847649
  have hstable : (prefixWord ++ tailWord_847649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847649).length < 2 ^ (prefixWord ++ tailWord_847649).sum := by decide
  have hdescent : baseEnd_847649 < baseStart_847649 := by decide
  rcases family_descends (prefixWord ++ tailWord_847649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847666 : List Nat := [3, 2, 1, 1, 3, 3, 2, 5]
def baseStart_847666 : Nat := 118140960795 + 847666 * 2 ^ 59
def prefixEnd_847666 : Nat := 4983230072969 + 3 ^ 40 * 847666 * 2
def baseEnd_847666 : Nat := 128965953325684662689381

theorem tailTrace_847666 : CollatzResearch.WordTrace tailWord_847666 prefixEnd_847666 128965953325684662689381 := by
  unfold tailWord_847666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729229736764581668048713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20611279298038884448129901 7729229736764581668048713)
  ·
    refine ⟨5796922302573436251036535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7729229736764581668048713 5796922302573436251036535)
    ·
      refine ⟨8695383453860154376554803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796922302573436251036535 8695383453860154376554803)
      ·
        refine ⟨13043075180790231564832205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695383453860154376554803 13043075180790231564832205)
        ·
          refine ⟨4891153192796336836812077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13043075180790231564832205 4891153192796336836812077)
          ·
            refine ⟨1834182447298626313804529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4891153192796336836812077 1834182447298626313804529)
            ·
              refine ⟨1375636835473969735353397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834182447298626313804529 1375636835473969735353397)
              ·
                refine ⟨128965953325684662689381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1375636835473969735353397 128965953325684662689381)
                ·
                  rfl

theorem cell20_847666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_847666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847666 prefixEnd_847666 := by exact prefixLift 847666
  have htrace : WordTrace (prefixWord ++ tailWord_847666) baseStart_847666 baseEnd_847666 := by
    simpa [prefixWord, tailWord_847666, baseEnd_847666] using wordTrace_append hprefix tailTrace_847666
  have hstable : (prefixWord ++ tailWord_847666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847666).length < 2 ^ (prefixWord ++ tailWord_847666).sum := by decide
  have hdescent : baseEnd_847666 < baseStart_847666 := by decide
  rcases family_descends (prefixWord ++ tailWord_847666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847687 : List Nat := [1, 1, 4, 1, 2, 1, 4, 6]
def baseStart_847687 : Nat := 118140960795 + 847687 * 2 ^ 59
def prefixEnd_847687 : Nat := 4983230072969 + 3 ^ 40 * 847687 * 2
def baseEnd_847687 : Nat := 128969148316423749456019

theorem tailTrace_847687 : CollatzResearch.WordTrace tailWord_847687 prefixEnd_847687 128969148316423749456019 := by
  unfold tailWord_847687
  simp only [CollatzResearch.WordTrace]
  refine ⟨30917684879982247258709315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20611789919988164839139543 30917684879982247258709315)
  ·
    refine ⟨46376527319973370888063973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30917684879982247258709315 46376527319973370888063973)
    ·
      refine ⟨8695598872495007041511995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46376527319973370888063973 8695598872495007041511995)
      ·
        refine ⟨13043398308742510562267993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8695598872495007041511995 13043398308742510562267993)
        ·
          refine ⟨9782548731556882921700995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13043398308742510562267993 9782548731556882921700995)
          ·
            refine ⟨14673823097335324382551493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9782548731556882921700995 14673823097335324382551493)
            ·
              refine ⟨2751341830750373321728405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14673823097335324382551493 2751341830750373321728405)
              ·
                refine ⟨128969148316423749456019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2751341830750373321728405 128969148316423749456019)
                ·
                  rfl

theorem cell20_847687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_847687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847687 prefixEnd_847687 := by exact prefixLift 847687
  have htrace : WordTrace (prefixWord ++ tailWord_847687) baseStart_847687 baseEnd_847687 := by
    simpa [prefixWord, tailWord_847687, baseEnd_847687] using wordTrace_append hprefix tailTrace_847687
  have hstable : (prefixWord ++ tailWord_847687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847687).length < 2 ^ (prefixWord ++ tailWord_847687).sum := by decide
  have hdescent : baseEnd_847687 < baseStart_847687 := by decide
  rcases family_descends (prefixWord ++ tailWord_847687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847711 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_847711 : Nat := 118140960795 + 847711 * 2 ^ 59
def prefixEnd_847711 : Nat := 4983230072969 + 3 ^ 40 * 847711 * 2
def baseEnd_847711 : Nat := 386918399203233831567959

theorem tailTrace_847711 : CollatzResearch.WordTrace tailWord_847711 prefixEnd_847711 386918399203233831567959 := by
  unfold tailWord_847711
  simp only [CollatzResearch.WordTrace]
  refine ⟨30918560231895299357582987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20612373487930199571721991 30918560231895299357582987)
  ·
    refine ⟨46377840347842949036374481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30918560231895299357582987 46377840347842949036374481)
    ·
      refine ⟨34783380260882211777280861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46377840347842949036374481 34783380260882211777280861)
      ·
        refine ⟨13043767597830829416480323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34783380260882211777280861 13043767597830829416480323)
        ·
          refine ⟨19565651396746244124720485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13043767597830829416480323 19565651396746244124720485)
          ·
            refine ⟨3668559636889920773385091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19565651396746244124720485 3668559636889920773385091)
            ·
              refine ⟨5502839455334881160077637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668559636889920773385091 5502839455334881160077637)
              ·
                refine ⟨1031782397875290217514557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5502839455334881160077637 1031782397875290217514557)
                ·
                  refine ⟨386918399203233831567959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031782397875290217514557 386918399203233831567959)
                  ·
                    rfl

theorem cell20_847711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_847711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847711 prefixEnd_847711 := by exact prefixLift 847711
  have htrace : WordTrace (prefixWord ++ tailWord_847711) baseStart_847711 baseEnd_847711 := by
    simpa [prefixWord, tailWord_847711, baseEnd_847711] using wordTrace_append hprefix tailTrace_847711
  have hstable : (prefixWord ++ tailWord_847711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847711).length < 2 ^ (prefixWord ++ tailWord_847711).sum := by decide
  have hdescent : baseEnd_847711 < baseStart_847711 := by decide
  rcases family_descends (prefixWord ++ tailWord_847711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847773 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_847773 : Nat := 118140960795 + 847773 * 2 ^ 59
def prefixEnd_847773 : Nat := 4983230072969 + 3 ^ 40 * 847773 * 2
def baseEnd_847773 : Nat := 386946697692637171501039

theorem tailTrace_847773 : CollatzResearch.WordTrace tailWord_847773 prefixEnd_847773 386946697692637171501039 := by
  unfold tailWord_847773
  simp only [CollatzResearch.WordTrace]
  refine ⟨30920821557670683946339973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20613881038447122630893315 30920821557670683946339973)
  ·
    refine ⟨5797654042063253239938745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30920821557670683946339973 5797654042063253239938745)
    ·
      refine ⟨4348240531547439929954059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5797654042063253239938745 4348240531547439929954059)
      ·
        refine ⟨6522360797321159894931089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348240531547439929954059 6522360797321159894931089)
        ·
          refine ⟨4891770597990869921198317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522360797321159894931089 4891770597990869921198317)
          ·
            refine ⟨1834413974246576220449369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4891770597990869921198317 1834413974246576220449369)
            ·
              refine ⟨1375810480684932165337027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834413974246576220449369 1375810480684932165337027)
              ·
                refine ⟨2063715721027398248005541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375810480684932165337027 2063715721027398248005541)
                ·
                  refine ⟨386946697692637171501039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063715721027398248005541 386946697692637171501039)
                  ·
                    rfl

theorem cell20_847773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_847773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847773 prefixEnd_847773 := by exact prefixLift 847773
  have htrace : WordTrace (prefixWord ++ tailWord_847773) baseStart_847773 baseEnd_847773 := by
    simpa [prefixWord, tailWord_847773, baseEnd_847773] using wordTrace_append hprefix tailTrace_847773
  have hstable : (prefixWord ++ tailWord_847773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847773).length < 2 ^ (prefixWord ++ tailWord_847773).sum := by decide
  have hdescent : baseEnd_847773 < baseStart_847773 := by decide
  rcases family_descends (prefixWord ++ tailWord_847773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847783 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 3]
def baseStart_847783 : Nat := 118140960795 + 847783 * 2 ^ 59
def prefixEnd_847783 : Nat := 4983230072969 + 3 ^ 40 * 847783 * 2
def baseEnd_847783 : Nat := 386951261965121581167665

theorem tailTrace_847783 : CollatzResearch.WordTrace tailWord_847783 prefixEnd_847783 386951261965121581167665 := by
  unfold tailWord_847783
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921186287634455654204003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20614124191756303769469335 30921186287634455654204003)
  ·
    refine ⟨46381779431451683481306005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30921186287634455654204003 46381779431451683481306005)
    ·
      refine ⟨2174145910849297663186219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46381779431451683481306005 2174145910849297663186219)
      ·
        refine ⟨3261218866273946494779329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174145910849297663186219 3261218866273946494779329)
        ·
          refine ⟨2445914149705459871084497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3261218866273946494779329 2445914149705459871084497)
          ·
            refine ⟨1834435612279094903313373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2445914149705459871084497 1834435612279094903313373)
            ·
              refine ⟨687913354604660588742515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1834435612279094903313373 687913354604660588742515)
              ·
                refine ⟨1031870031906990883113773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687913354604660588742515 1031870031906990883113773)
                ·
                  refine ⟨386951261965121581167665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031870031906990883113773 386951261965121581167665)
                  ·
                    rfl

theorem cell20_847783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_847783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847783 prefixEnd_847783 := by exact prefixLift 847783
  have htrace : WordTrace (prefixWord ++ tailWord_847783) baseStart_847783 baseEnd_847783 := by
    simpa [prefixWord, tailWord_847783, baseEnd_847783] using wordTrace_append hprefix tailTrace_847783
  have hstable : (prefixWord ++ tailWord_847783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847783).length < 2 ^ (prefixWord ++ tailWord_847783).sum := by decide
  have hdescent : baseEnd_847783 < baseStart_847783 := by decide
  rcases family_descends (prefixWord ++ tailWord_847783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847797 : List Nat := [1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_847797 : Nat := 118140960795 + 847797 * 2 ^ 59
def prefixEnd_847797 : Nat := 4983230072969 + 3 ^ 40 * 847797 * 2
def baseEnd_847797 : Nat := 128985883982199918233647

theorem tailTrace_847797 : CollatzResearch.WordTrace tailWord_847797 prefixEnd_847797 128985883982199918233647 := by
  unfold tailWord_847797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921696909583736045213645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20614464606389157363475763 30921696909583736045213645)
  ·
    refine ⟨11595636341093901016955117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30921696909583736045213645 11595636341093901016955117)
    ·
      refine ⟨4348363627910212881358169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11595636341093901016955117 4348363627910212881358169)
      ·
        refine ⟨3261272720932659661018627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4348363627910212881358169 3261272720932659661018627)
        ·
          refine ⟨4891909081398989491527941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261272720932659661018627 4891909081398989491527941)
          ·
            refine ⟨917232952762310529661489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4891909081398989491527941 917232952762310529661489)
            ·
              refine ⟨687924714571732897246117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917232952762310529661489 687924714571732897246117)
              ·
                refine ⟨128985883982199918233647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 687924714571732897246117 128985883982199918233647)
                ·
                  rfl

theorem cell20_847797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_847797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847797 prefixEnd_847797 := by exact prefixLift 847797
  have htrace : WordTrace (prefixWord ++ tailWord_847797) baseStart_847797 baseEnd_847797 := by
    simpa [prefixWord, tailWord_847797, baseEnd_847797] using wordTrace_append hprefix tailTrace_847797
  have hstable : (prefixWord ++ tailWord_847797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847797).length < 2 ^ (prefixWord ++ tailWord_847797).sum := by decide
  have hdescent : baseEnd_847797 < baseStart_847797 := by decide
  rcases family_descends (prefixWord ++ tailWord_847797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847801 : List Nat := [1, 2, 1, 4, 2, 1, 3, 6]
def baseStart_847801 : Nat := 118140960795 + 847801 * 2 ^ 59
def prefixEnd_847801 : Nat := 4983230072969 + 3 ^ 40 * 847801 * 2
def baseEnd_847801 : Nat := 128986492551864506189197

theorem tailTrace_847801 : CollatzResearch.WordTrace tailWord_847801 prefixEnd_847801 128986492551864506189197 := by
  unfold tailWord_847801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921842801569244728359257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20614561867712829818906171 30921842801569244728359257)
  ·
    refine ⟨23191382101176933546269443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30921842801569244728359257 23191382101176933546269443)
    ·
      refine ⟨34787073151765400319404165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23191382101176933546269443 34787073151765400319404165)
      ·
        refine ⟨6522576215956012559888281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34787073151765400319404165 6522576215956012559888281)
        ·
          refine ⟨4891932161967009419916211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6522576215956012559888281 4891932161967009419916211)
          ·
            refine ⟨7337898242950514129874317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891932161967009419916211 7337898242950514129874317)
            ·
              refine ⟨2751711841106442798702869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7337898242950514129874317 2751711841106442798702869)
              ·
                refine ⟨128986492551864506189197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2751711841106442798702869 128986492551864506189197)
                ·
                  rfl

theorem cell20_847801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_847801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847801 prefixEnd_847801 := by exact prefixLift 847801
  have htrace : WordTrace (prefixWord ++ tailWord_847801) baseStart_847801 baseEnd_847801 := by
    simpa [prefixWord, tailWord_847801, baseEnd_847801] using wordTrace_append hprefix tailTrace_847801
  have hstable : (prefixWord ++ tailWord_847801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847801).length < 2 ^ (prefixWord ++ tailWord_847801).sum := by decide
  have hdescent : baseEnd_847801 < baseStart_847801 := by decide
  rcases family_descends (prefixWord ++ tailWord_847801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847808 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_847808 : Nat := 118140960795 + 847808 * 2 ^ 59
def prefixEnd_847808 : Nat := 4983230072969 + 3 ^ 40 * 847808 * 2
def baseEnd_847808 : Nat := 386962672646332605334229

theorem tailTrace_847808 : CollatzResearch.WordTrace tailWord_847808 prefixEnd_847808 386962672646332605334229 := by
  unfold tailWord_847808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461049056271942461932039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20614732075029256615909385 15461049056271942461932039)
  ·
    refine ⟨23191573584407913692898059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15461049056271942461932039 23191573584407913692898059)
    ·
      refine ⟨34787360376611870539347089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23191573584407913692898059 34787360376611870539347089)
      ·
        refine ⟨26090520282458902904510317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34787360376611870539347089 26090520282458902904510317)
        ·
          refine ⟨9783945105922088589191369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26090520282458902904510317 9783945105922088589191369)
          ·
            refine ⟨7337958829441566441893527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9783945105922088589191369 7337958829441566441893527)
            ·
              refine ⟨11006938244162349662840291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337958829441566441893527 11006938244162349662840291)
              ·
                refine ⟨16510407366243524494260437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11006938244162349662840291 16510407366243524494260437)
                ·
                  refine ⟨386962672646332605334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16510407366243524494260437 386962672646332605334229)
                  ·
                    rfl

theorem cell20_847808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_847808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847808 prefixEnd_847808 := by exact prefixLift 847808
  have htrace : WordTrace (prefixWord ++ tailWord_847808) baseStart_847808 baseEnd_847808 := by
    simpa [prefixWord, tailWord_847808, baseEnd_847808] using wordTrace_append hprefix tailTrace_847808
  have hstable : (prefixWord ++ tailWord_847808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847808).length < 2 ^ (prefixWord ++ tailWord_847808).sum := by decide
  have hdescent : baseEnd_847808 < baseStart_847808 := by decide
  rcases family_descends (prefixWord ++ tailWord_847808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847839 : List Nat := [1, 1, 2, 3, 4, 1, 1, 7]
def baseStart_847839 : Nat := 118140960795 + 847839 * 2 ^ 59
def prefixEnd_847839 : Nat := 4983230072969 + 3 ^ 40 * 847839 * 2
def baseEnd_847839 : Nat := 128992273963678091766923

theorem tailTrace_847839 : CollatzResearch.WordTrace tailWord_847839 prefixEnd_847839 128992273963678091766923 := by
  unfold tailWord_847839
  simp only [CollatzResearch.WordTrace]
  refine ⟨30923228775431577218242571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20615485850287718145495047 30923228775431577218242571)
  ·
    refine ⟨46384843163147365827363857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30923228775431577218242571 46384843163147365827363857)
    ·
      refine ⟨34788632372360524370522893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46384843163147365827363857 34788632372360524370522893)
      ·
        refine ⟨13045737139635196638946085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34788632372360524370522893 13045737139635196638946085)
        ·
          refine ⟨2446075713681599369802391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13045737139635196638946085 2446075713681599369802391)
          ·
            refine ⟨3669113570522399054703587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446075713681599369802391 3669113570522399054703587)
            ·
              refine ⟨5503670355783598582055381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669113570522399054703587 5503670355783598582055381)
              ·
                refine ⟨128992273963678091766923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5503670355783598582055381 128992273963678091766923)
                ·
                  rfl

theorem cell20_847839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_847839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847839 prefixEnd_847839 := by exact prefixLift 847839
  have htrace : WordTrace (prefixWord ++ tailWord_847839) baseStart_847839 baseEnd_847839 := by
    simpa [prefixWord, tailWord_847839, baseEnd_847839] using wordTrace_append hprefix tailTrace_847839
  have hstable : (prefixWord ++ tailWord_847839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847839).length < 2 ^ (prefixWord ++ tailWord_847839).sum := by decide
  have hdescent : baseEnd_847839 < baseStart_847839 := by decide
  rcases family_descends (prefixWord ++ tailWord_847839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847925 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 2]
def baseStart_847925 : Nat := 118140960795 + 847925 * 2 ^ 59
def prefixEnd_847925 : Nat := 4983230072969 + 3 ^ 40 * 847925 * 2
def baseEnd_847925 : Nat := 387016074634400198433751

theorem tailTrace_847925 : CollatzResearch.WordTrace tailWord_847925 prefixEnd_847925 387016074634400198433751 := by
  unfold tailWord_847925
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926365453120013905873229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20617576968746675937248819 30926365453120013905873229)
  ·
    refine ⟨11597387044920005214702461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30926365453120013905873229 11597387044920005214702461)
    ·
      refine ⟨4349020141845001955513423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11597387044920005214702461 4349020141845001955513423)
      ·
        refine ⟨6523530212767502933270135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349020141845001955513423 6523530212767502933270135)
        ·
          refine ⟨9785295319151254399905203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6523530212767502933270135 9785295319151254399905203)
          ·
            refine ⟨14677942978726881599857805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785295319151254399905203 14677942978726881599857805)
            ·
              refine ⟨5504228617022580599946677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14677942978726881599857805 5504228617022580599946677)
              ·
                refine ⟨516021432845866931245001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5504228617022580599946677 516021432845866931245001)
                ·
                  refine ⟨387016074634400198433751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516021432845866931245001 387016074634400198433751)
                  ·
                    rfl

theorem cell20_847925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_847925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847925 prefixEnd_847925 := by exact prefixLift 847925
  have htrace : WordTrace (prefixWord ++ tailWord_847925) baseStart_847925 baseEnd_847925 := by
    simpa [prefixWord, tailWord_847925, baseEnd_847925] using wordTrace_append hprefix tailTrace_847925
  have hstable : (prefixWord ++ tailWord_847925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847925).length < 2 ^ (prefixWord ++ tailWord_847925).sum := by decide
  have hdescent : baseEnd_847925 < baseStart_847925 := by decide
  rcases family_descends (prefixWord ++ tailWord_847925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847942 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_847942 : Nat := 118140960795 + 847942 * 2 ^ 59
def prefixEnd_847942 : Nat := 4983230072969 + 3 ^ 40 * 847942 * 2
def baseEnd_847942 : Nat := 387023833897623694867015

theorem tailTrace_847942 : CollatzResearch.WordTrace tailWord_847942 prefixEnd_847942 387023833897623694867015 := by
  unfold tailWord_847942
  simp only [CollatzResearch.WordTrace]
  refine ⟨966468296689325806538815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20617990329372283872828053 966468296689325806538815)
  ·
    refine ⟨1449702445033988709808223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966468296689325806538815 1449702445033988709808223)
    ·
      refine ⟨2174553667550983064712335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1449702445033988709808223 2174553667550983064712335)
      ·
        refine ⟨3261830501326474597068503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174553667550983064712335 3261830501326474597068503)
        ·
          refine ⟨4892745751989711895602755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261830501326474597068503 4892745751989711895602755)
          ·
            refine ⟨7339118627984567843404133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892745751989711895602755 7339118627984567843404133)
            ·
              refine ⟨1376084742747106470638275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7339118627984567843404133 1376084742747106470638275)
              ·
                refine ⟨2064127114120659705957413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376084742747106470638275 2064127114120659705957413)
                ·
                  refine ⟨387023833897623694867015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064127114120659705957413 387023833897623694867015)
                  ·
                    rfl

theorem cell20_847942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_847942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847942 prefixEnd_847942 := by exact prefixLift 847942
  have htrace : WordTrace (prefixWord ++ tailWord_847942) baseStart_847942 baseEnd_847942 := by
    simpa [prefixWord, tailWord_847942, baseEnd_847942] using wordTrace_append hprefix tailTrace_847942
  have hstable : (prefixWord ++ tailWord_847942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847942).length < 2 ^ (prefixWord ++ tailWord_847942).sum := by decide
  have hdescent : baseEnd_847942 < baseStart_847942 := by decide
  rcases family_descends (prefixWord ++ tailWord_847942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847966 : List Nat := [4, 4, 1, 1, 2, 1, 1, 6]
def baseStart_847966 : Nat := 118140960795 + 847966 * 2 ^ 59
def prefixEnd_847966 : Nat := 4983230072969 + 3 ^ 40 * 847966 * 2
def baseEnd_847966 : Nat := 129011596050528759355639

theorem tailTrace_847966 : CollatzResearch.WordTrace tailWord_847966 prefixEnd_847966 129011596050528759355639 := by
  unfold tailWord_847966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3865982605746434738514469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20618573897314318605410501 3865982605746434738514469)
  ·
    refine ⟨724871738577456513471463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3865982605746434738514469 724871738577456513471463)
    ·
      refine ⟨1087307607866184770207195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724871738577456513471463 1087307607866184770207195)
      ·
        refine ⟨1630961411799277155310793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087307607866184770207195 1630961411799277155310793)
        ·
          refine ⟨1223221058849457866483095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630961411799277155310793 1223221058849457866483095)
          ·
            refine ⟨1834831588274186799724643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223221058849457866483095 1834831588274186799724643)
            ·
              refine ⟨2752247382411280199586965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1834831588274186799724643 2752247382411280199586965)
              ·
                refine ⟨129011596050528759355639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2752247382411280199586965 129011596050528759355639)
                ·
                  rfl

theorem cell20_847966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_847966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847966 prefixEnd_847966 := by exact prefixLift 847966
  have htrace : WordTrace (prefixWord ++ tailWord_847966) baseStart_847966 baseEnd_847966 := by
    simpa [prefixWord, tailWord_847966, baseEnd_847966] using wordTrace_append hprefix tailTrace_847966
  have hstable : (prefixWord ++ tailWord_847966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847966).length < 2 ^ (prefixWord ++ tailWord_847966).sum := by decide
  have hdescent : baseEnd_847966 < baseStart_847966 := by decide
  rcases family_descends (prefixWord ++ tailWord_847966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847967 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_847967 : Nat := 118140960795 + 847967 * 2 ^ 59
def prefixEnd_847967 : Nat := 4983230072969 + 3 ^ 40 * 847967 * 2
def baseEnd_847967 : Nat := 387035244578834719033579

theorem tailTrace_847967 : CollatzResearch.WordTrace tailWord_847967 prefixEnd_847967 387035244578834719033579 := by
  unfold tailWord_847967
  simp only [CollatzResearch.WordTrace]
  refine ⟨30927897318967855078902155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20618598212645236719268103 30927897318967855078902155)
  ·
    refine ⟨46391845978451782618353233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30927897318967855078902155 46391845978451782618353233)
    ·
      refine ⟨34793884483838836963764925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46391845978451782618353233 34793884483838836963764925)
      ·
        refine ⟨13047706681439563861411847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34793884483838836963764925 13047706681439563861411847)
        ·
          refine ⟨19571560022159345792117771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13047706681439563861411847 19571560022159345792117771)
          ·
            refine ⟨29357340033239018688176657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19571560022159345792117771 29357340033239018688176657)
            ·
              refine ⟨22018005024929264016132493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29357340033239018688176657 22018005024929264016132493)
              ·
                refine ⟨8256751884348474006049685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22018005024929264016132493 8256751884348474006049685)
                ·
                  refine ⟨387035244578834719033579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8256751884348474006049685 387035244578834719033579)
                  ·
                    rfl

theorem cell20_847967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_847967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847967 prefixEnd_847967 := by exact prefixLift 847967
  have htrace : WordTrace (prefixWord ++ tailWord_847967) baseStart_847967 baseEnd_847967 := by
    simpa [prefixWord, tailWord_847967, baseEnd_847967] using wordTrace_append hprefix tailTrace_847967
  have hstable : (prefixWord ++ tailWord_847967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847967).length < 2 ^ (prefixWord ++ tailWord_847967).sum := by decide
  have hdescent : baseEnd_847967 < baseStart_847967 := by decide
  rcases family_descends (prefixWord ++ tailWord_847967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847980 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_847980 : Nat := 118140960795 + 847980 * 2 ^ 59
def prefixEnd_847980 : Nat := 4983230072969 + 3 ^ 40 * 847980 * 2
def baseEnd_847980 : Nat := 387041178133064451600193

theorem tailTrace_847980 : CollatzResearch.WordTrace tailWord_847980 prefixEnd_847980 387041178133064451600193 := by
  unfold tailWord_847980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464185733960379149562697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20618914311947172199416929 15464185733960379149562697)
  ·
    refine ⟨11598139300470284362172023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15464185733960379149562697 11598139300470284362172023)
    ·
      refine ⟨17397208950705426543258035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11598139300470284362172023 17397208950705426543258035)
      ·
        refine ⟨26095813426058139814887053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17397208950705426543258035 26095813426058139814887053)
        ·
          refine ⟨9785930034771802430582645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26095813426058139814887053 9785930034771802430582645)
          ·
            refine ⟨917430940759856477867123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9785930034771802430582645 917430940759856477867123)
            ·
              refine ⟨1376146411139784716800685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917430940759856477867123 1376146411139784716800685)
              ·
                refine ⟨516054904177419268800257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376146411139784716800685 516054904177419268800257)
                ·
                  refine ⟨387041178133064451600193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516054904177419268800257 387041178133064451600193)
                  ·
                    rfl

theorem cell20_847980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_847980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847980 prefixEnd_847980 := by exact prefixLift 847980
  have htrace : WordTrace (prefixWord ++ tailWord_847980) baseStart_847980 baseEnd_847980 := by
    simpa [prefixWord, tailWord_847980, baseEnd_847980] using wordTrace_append hprefix tailTrace_847980
  have hstable : (prefixWord ++ tailWord_847980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847980).length < 2 ^ (prefixWord ++ tailWord_847980).sum := by decide
  have hdescent : baseEnd_847980 < baseStart_847980 := by decide
  rcases family_descends (prefixWord ++ tailWord_847980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_847991 : List Nat := [1, 1, 3, 1, 1, 7, 6]
def baseStart_847991 : Nat := 118140960795 + 847991 * 2 ^ 59
def prefixEnd_847991 : Nat := 4983230072969 + 3 ^ 40 * 847991 * 2
def baseEnd_847991 : Nat := 43005133203644144692609

theorem tailTrace_847991 : CollatzResearch.WordTrace tailWord_847991 prefixEnd_847991 43005133203644144692609 := by
  unfold tailWord_847991
  simp only [CollatzResearch.WordTrace]
  refine ⟨30928772670880907177775827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20619181780587271451850551 30928772670880907177775827)
  ·
    refine ⟨46393159006321360766663741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30928772670880907177775827 46393159006321360766663741)
    ·
      refine ⟨17397434627370510287498903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46393159006321360766663741 17397434627370510287498903)
      ·
        refine ⟨26096151941055765431248355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17397434627370510287498903 26096151941055765431248355)
        ·
          refine ⟨39144227911583648146872533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26096151941055765431248355 39144227911583648146872533)
          ·
            refine ⟨917442841677741753442325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39144227911583648146872533 917442841677741753442325)
            ·
              refine ⟨43005133203644144692609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917442841677741753442325 43005133203644144692609)
              ·
                rfl

theorem cell20_847991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_847991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_847991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_847991 prefixEnd_847991 := by exact prefixLift 847991
  have htrace : WordTrace (prefixWord ++ tailWord_847991) baseStart_847991 baseEnd_847991 := by
    simpa [prefixWord, tailWord_847991, baseEnd_847991] using wordTrace_append hprefix tailTrace_847991
  have hstable : (prefixWord ++ tailWord_847991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_847991).length < 2 ^ (prefixWord ++ tailWord_847991).sum := by decide
  have hdescent : baseEnd_847991 < baseStart_847991 := by decide
  rcases family_descends (prefixWord ++ tailWord_847991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848008 : List Nat := [2, 1, 3, 4, 1, 2, 2, 5]
def baseStart_848008 : Nat := 118140960795 + 848008 * 2 ^ 59
def prefixEnd_848008 : Nat := 4983230072969 + 3 ^ 40 * 848008 * 2
def baseEnd_848008 : Nat := 129017986032006932888915

theorem tailTrace_848008 : CollatzResearch.WordTrace tailWord_848008 prefixEnd_848008 129017986032006932888915 := by
  unfold tailWord_848008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15464696355909659540572339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20619595141212879387429785 15464696355909659540572339)
  ·
    refine ⟨23197044533864489310858509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15464696355909659540572339 23197044533864489310858509)
    ·
      refine ⟨8698891700199183491571941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23197044533864489310858509 8698891700199183491571941)
      ·
        refine ⟨1631042193787346904669739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8698891700199183491571941 1631042193787346904669739)
        ·
          refine ⟨2446563290681020357004609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631042193787346904669739 2446563290681020357004609)
          ·
            refine ⟨1834922468010765267753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2446563290681020357004609 1834922468010765267753457)
            ·
              refine ⟨1376191851008073950815093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834922468010765267753457 1376191851008073950815093)
              ·
                refine ⟨129017986032006932888915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376191851008073950815093 129017986032006932888915)
                ·
                  rfl

theorem cell20_848008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_848008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848008 prefixEnd_848008 := by exact prefixLift 848008
  have htrace : WordTrace (prefixWord ++ tailWord_848008) baseStart_848008 baseEnd_848008 := by
    simpa [prefixWord, tailWord_848008, baseEnd_848008] using wordTrace_append hprefix tailTrace_848008
  have hstable : (prefixWord ++ tailWord_848008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848008).length < 2 ^ (prefixWord ++ tailWord_848008).sum := by decide
  have hdescent : baseEnd_848008 < baseStart_848008 := by decide
  rcases family_descends (prefixWord ++ tailWord_848008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848029 : List Nat := [1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_848029 : Nat := 118140960795 + 848029 * 2 ^ 59
def prefixEnd_848029 : Nat := 4983230072969 + 3 ^ 40 * 848029 * 2
def baseEnd_848029 : Nat := 129021181022746019655553

theorem tailTrace_848029 : CollatzResearch.WordTrace tailWord_848029 prefixEnd_848029 129021181022746019655553 := by
  unfold tailWord_848029
  simp only [CollatzResearch.WordTrace]
  refine ⟨30930158644743239667659141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20620105763162159778439427 30930158644743239667659141)
  ·
    refine ⟨5799404745889357437686089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30930158644743239667659141 5799404745889357437686089)
    ·
      refine ⟨4349553559417018078264567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5799404745889357437686089 4349553559417018078264567)
      ·
        refine ⟨6524330339125527117396851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349553559417018078264567 6524330339125527117396851)
        ·
          refine ⟨9786495508688290676095277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524330339125527117396851 9786495508688290676095277)
          ·
            refine ⟨3669935815758109003535729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9786495508688290676095277 3669935815758109003535729)
            ·
              refine ⟨2752451861818581752651797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669935815758109003535729 2752451861818581752651797)
              ·
                refine ⟨129021181022746019655553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2752451861818581752651797 129021181022746019655553)
                ·
                  rfl

theorem cell20_848029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_848029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848029 prefixEnd_848029 := by exact prefixLift 848029
  have htrace : WordTrace (prefixWord ++ tailWord_848029) baseStart_848029 baseEnd_848029 := by
    simpa [prefixWord, tailWord_848029, baseEnd_848029] using wordTrace_append hprefix tailTrace_848029
  have hstable : (prefixWord ++ tailWord_848029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848029).length < 2 ^ (prefixWord ++ tailWord_848029).sum := by decide
  have hdescent : baseEnd_848029 < baseStart_848029 := by decide
  rcases family_descends (prefixWord ++ tailWord_848029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848046 : List Nat := [4, 1, 4, 2, 9]
def baseStart_848046 : Nat := 118140960795 + 848046 * 2 ^ 59
def prefixEnd_848046 : Nat := 4983230072969 + 3 ^ 40 * 848046 * 2
def baseEnd_848046 : Nat := 4778658053474834017283

theorem tailTrace_848046 : CollatzResearch.WordTrace tailWord_848046 prefixEnd_848046 4778658053474834017283 := by
  unfold tailWord_848046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3866347335710206446378499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20620519123787767714018661 3866347335710206446378499)
  ·
    refine ⟨5799521003565309669567749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3866347335710206446378499 5799521003565309669567749)
    ·
      refine ⟨1087410188168495563043953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5799521003565309669567749 1087410188168495563043953)
      ·
        refine ⟨815557641126371672282965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1087410188168495563043953 815557641126371672282965)
        ·
          refine ⟨4778658053474834017283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 815557641126371672282965 4778658053474834017283)
          ·
            rfl

theorem cell20_848046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 9].length) (baseStart_848046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848046 prefixEnd_848046 := by exact prefixLift 848046
  have htrace : WordTrace (prefixWord ++ tailWord_848046) baseStart_848046 baseEnd_848046 := by
    simpa [prefixWord, tailWord_848046, baseEnd_848046] using wordTrace_append hprefix tailTrace_848046
  have hstable : (prefixWord ++ tailWord_848046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848046).length < 2 ^ (prefixWord ++ tailWord_848046).sum := by decide
  have hdescent : baseEnd_848046 < baseStart_848046 := by decide
  rcases family_descends (prefixWord ++ tailWord_848046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848081 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_848081 : Nat := 118140960795 + 848081 * 2 ^ 59
def prefixEnd_848081 : Nat := 4983230072969 + 3 ^ 40 * 848081 * 2
def baseEnd_848081 : Nat := 387087277285156989233113

theorem tailTrace_848081 : CollatzResearch.WordTrace tailWord_848081 prefixEnd_848081 387087277285156989233113 := by
  unfold tailWord_848081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30932055240554852548552097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20621370160369901699034731 30932055240554852548552097)
  ·
    refine ⟨23199041430416139411414073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30932055240554852548552097 23199041430416139411414073)
    ·
      refine ⟨17399281072812104558560555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23199041430416139411414073 17399281072812104558560555)
      ·
        refine ⟨26098921609218156837840833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17399281072812104558560555 26098921609218156837840833)
        ·
          refine ⟨19574191206913617628380625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26098921609218156837840833 19574191206913617628380625)
          ·
            refine ⟨14680643405185213221285469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19574191206913617628380625 14680643405185213221285469)
            ·
              refine ⟨5505241276944454957982051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14680643405185213221285469 5505241276944454957982051)
              ·
                refine ⟨8257861915416682436973077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505241276944454957982051 8257861915416682436973077)
                ·
                  refine ⟨387087277285156989233113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8257861915416682436973077 387087277285156989233113)
                  ·
                    rfl

theorem cell20_848081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_848081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848081 prefixEnd_848081 := by exact prefixLift 848081
  have htrace : WordTrace (prefixWord ++ tailWord_848081) baseStart_848081 baseEnd_848081 := by
    simpa [prefixWord, tailWord_848081, baseEnd_848081] using wordTrace_append hprefix tailTrace_848081
  have hstable : (prefixWord ++ tailWord_848081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848081).length < 2 ^ (prefixWord ++ tailWord_848081).sum := by decide
  have hdescent : baseEnd_848081 < baseStart_848081 := by decide
  rcases family_descends (prefixWord ++ tailWord_848081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848136 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_848136 : Nat := 118140960795 + 848136 * 2 ^ 59
def prefixEnd_848136 : Nat := 4983230072969 + 3 ^ 40 * 848136 * 2
def baseEnd_848136 : Nat := 387112380783821242399555

theorem tailTrace_848136 : CollatzResearch.WordTrace tailWord_848136 prefixEnd_848136 387112380783821242399555 := by
  unfold tailWord_848136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467030627677798470902131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20622707503570397961202841 15467030627677798470902131)
  ·
    refine ⟨23200545941516697706353197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15467030627677798470902131 23200545941516697706353197)
    ·
      refine ⟨8700204728068761639882449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23200545941516697706353197 8700204728068761639882449)
      ·
        refine ⟨6525153546051571229911837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8700204728068761639882449 6525153546051571229911837)
        ·
          refine ⟨2446932579769339211216939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6525153546051571229911837 2446932579769339211216939)
          ·
            refine ⟨3670398869654008816825409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446932579769339211216939 3670398869654008816825409)
            ·
              refine ⟨2752799152240506612619057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3670398869654008816825409 2752799152240506612619057)
              ·
                refine ⟨2064599364180379959464293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752799152240506612619057 2064599364180379959464293)
                ·
                  refine ⟨387112380783821242399555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064599364180379959464293 387112380783821242399555)
                  ·
                    rfl

theorem cell20_848136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_848136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848136 prefixEnd_848136 := by exact prefixLift 848136
  have htrace : WordTrace (prefixWord ++ tailWord_848136) baseStart_848136 baseEnd_848136 := by
    simpa [prefixWord, tailWord_848136, baseEnd_848136] using wordTrace_append hprefix tailTrace_848136
  have hstable : (prefixWord ++ tailWord_848136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848136).length < 2 ^ (prefixWord ++ tailWord_848136).sum := by decide
  have hdescent : baseEnd_848136 < baseStart_848136 := by decide
  rcases family_descends (prefixWord ++ tailWord_848136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848170 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_848170 : Nat := 118140960795 + 848170 * 2 ^ 59
def prefixEnd_848170 : Nat := 4983230072969 + 3 ^ 40 * 848170 * 2
def baseEnd_848170 : Nat := 387127899310268235266083

theorem tailTrace_848170 : CollatzResearch.WordTrace tailWord_848170 prefixEnd_848170 387127899310268235266083 := by
  unfold tailWord_848170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733825334308105187135491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20623534224821613832361309 7733825334308105187135491)
  ·
    refine ⟨11600738001462157780703237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7733825334308105187135491 11600738001462157780703237)
    ·
      refine ⟨2175138375274154583881857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11600738001462157780703237 2175138375274154583881857)
      ·
        refine ⟨1631353781455615937911393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2175138375274154583881857 1631353781455615937911393)
        ·
          refine ⟨1223515336091711953433545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1631353781455615937911393 1223515336091711953433545)
          ·
            refine ⟨917636502068783965075159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223515336091711953433545 917636502068783965075159)
            ·
              refine ⟨1376454753103175947612739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917636502068783965075159 1376454753103175947612739)
              ·
                refine ⟨2064682129654763921419109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376454753103175947612739 2064682129654763921419109)
                ·
                  refine ⟨387127899310268235266083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064682129654763921419109 387127899310268235266083)
                  ·
                    rfl

theorem cell20_848170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_848170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848170 prefixEnd_848170 := by exact prefixLift 848170
  have htrace : WordTrace (prefixWord ++ tailWord_848170) baseStart_848170 baseEnd_848170 := by
    simpa [prefixWord, tailWord_848170, baseEnd_848170] using wordTrace_append hprefix tailTrace_848170
  have hstable : (prefixWord ++ tailWord_848170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848170).length < 2 ^ (prefixWord ++ tailWord_848170).sum := by decide
  have hdescent : baseEnd_848170 < baseStart_848170 := by decide
  rcases family_descends (prefixWord ++ tailWord_848170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848181 : List Nat := [1, 3, 3, 1, 2, 1, 4, 5]
def baseStart_848181 : Nat := 118140960795 + 848181 * 2 ^ 59
def prefixEnd_848181 : Nat := 4983230072969 + 3 ^ 40 * 848181 * 2
def baseEnd_848181 : Nat := 129044306670000361966457

theorem tailTrace_848181 : CollatzResearch.WordTrace tailWord_848181 prefixEnd_848181 129044306670000361966457 := by
  unfold tailWord_848181
  simp only [CollatzResearch.WordTrace]
  refine ⟨30935702540192569627192397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20623801693461713084794931 30935702540192569627192397)
  ·
    refine ⟨11600888452572213610197149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30935702540192569627192397 11600888452572213610197149)
    ·
      refine ⟨4350333169714580103823931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11600888452572213610197149 4350333169714580103823931)
      ·
        refine ⟨6525499754571870155735897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350333169714580103823931 6525499754571870155735897)
        ·
          refine ⟨4894124815928902616801923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6525499754571870155735897 4894124815928902616801923)
          ·
            refine ⟨7341187223893353925202885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894124815928902616801923 7341187223893353925202885)
            ·
              refine ⟨1376472604480003860975541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7341187223893353925202885 1376472604480003860975541)
              ·
                refine ⟨129044306670000361966457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376472604480003860975541 129044306670000361966457)
                ·
                  rfl

theorem cell20_848181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_848181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848181 prefixEnd_848181 := by exact prefixLift 848181
  have htrace : WordTrace (prefixWord ++ tailWord_848181) baseStart_848181 baseEnd_848181 := by
    simpa [prefixWord, tailWord_848181, baseEnd_848181] using wordTrace_append hprefix tailTrace_848181
  have hstable : (prefixWord ++ tailWord_848181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848181).length < 2 ^ (prefixWord ++ tailWord_848181).sum := by decide
  have hdescent : baseEnd_848181 < baseStart_848181 := by decide
  rcases family_descends (prefixWord ++ tailWord_848181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848195 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_848195 : Nat := 118140960795 + 848195 * 2 ^ 59
def prefixEnd_848195 : Nat := 4983230072969 + 3 ^ 40 * 848195 * 2
def baseEnd_848195 : Nat := 387139309991479259432647

theorem tailTrace_848195 : CollatzResearch.WordTrace tailWord_848195 prefixEnd_848195 387139309991479259432647 := by
  unfold tailWord_848195
  simp only [CollatzResearch.WordTrace]
  refine ⟨30936213162141850018202039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20624142108094566678801359 30936213162141850018202039)
  ·
    refine ⟨46404319743212775027303059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30936213162141850018202039 46404319743212775027303059)
    ·
      refine ⟨69606479614819162540954589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46404319743212775027303059 69606479614819162540954589)
      ·
        refine ⟨26102429855557185952857971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69606479614819162540954589 26102429855557185952857971)
        ·
          refine ⟨39153644783335778929286957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26102429855557185952857971 39153644783335778929286957)
          ·
            refine ⟨14682616793750917098482609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39153644783335778929286957 14682616793750917098482609)
            ·
              refine ⟨11011962595313187823861957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682616793750917098482609 11011962595313187823861957)
              ·
                refine ⟨2064742986621222716974117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11011962595313187823861957 2064742986621222716974117)
                ·
                  refine ⟨387139309991479259432647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064742986621222716974117 387139309991479259432647)
                  ·
                    rfl

theorem cell20_848195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_848195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848195 prefixEnd_848195 := by exact prefixLift 848195
  have htrace : WordTrace (prefixWord ++ tailWord_848195) baseStart_848195 baseEnd_848195 := by
    simpa [prefixWord, tailWord_848195, baseEnd_848195] using wordTrace_append hprefix tailTrace_848195
  have hstable : (prefixWord ++ tailWord_848195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848195).length < 2 ^ (prefixWord ++ tailWord_848195).sum := by decide
  have hdescent : baseEnd_848195 < baseStart_848195 := by decide
  rcases family_descends (prefixWord ++ tailWord_848195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848229 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 2]
def baseStart_848229 : Nat := 118140960795 + 848229 * 2 ^ 59
def prefixEnd_848229 : Nat := 4983230072969 + 3 ^ 40 * 848229 * 2
def baseEnd_848229 : Nat := 387154828517926252299175

theorem tailTrace_848229 : CollatzResearch.WordTrace tailWord_848229 prefixEnd_848229 387154828517926252299175 := by
  unfold tailWord_848229
  simp only [CollatzResearch.WordTrace]
  refine ⟨30937453244018673824939741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20624968829345782549959827 30937453244018673824939741)
  ·
    refine ⟨11601544966507002684352403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30937453244018673824939741 11601544966507002684352403)
    ·
      refine ⟨17402317449760504026528605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601544966507002684352403 17402317449760504026528605)
      ·
        refine ⟨6525869043660189009948227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17402317449760504026528605 6525869043660189009948227)
        ·
          refine ⟨9788803565490283514922341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6525869043660189009948227 9788803565490283514922341)
          ·
            refine ⟨1835400668529428159047939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9788803565490283514922341 1835400668529428159047939)
            ·
              refine ⟨2753101002794142238571909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835400668529428159047939 2753101002794142238571909)
              ·
                refine ⟨516206438023901669732233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2753101002794142238571909 516206438023901669732233)
                ·
                  refine ⟨387154828517926252299175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516206438023901669732233 387154828517926252299175)
                  ·
                    rfl

theorem cell20_848229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_848229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848229 prefixEnd_848229 := by exact prefixLift 848229
  have htrace : WordTrace (prefixWord ++ tailWord_848229) baseStart_848229 baseEnd_848229 := by
    simpa [prefixWord, tailWord_848229, baseEnd_848229] using wordTrace_append hprefix tailTrace_848229
  have hstable : (prefixWord ++ tailWord_848229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848229).length < 2 ^ (prefixWord ++ tailWord_848229).sum := by decide
  have hdescent : baseEnd_848229 < baseStart_848229 := by decide
  rcases family_descends (prefixWord ++ tailWord_848229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848233 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_848233 : Nat := 118140960795 + 848233 * 2 ^ 59
def prefixEnd_848233 : Nat := 4983230072969 + 3 ^ 40 * 848233 * 2
def baseEnd_848233 : Nat := 387156654226920016165825

theorem tailTrace_848233 : CollatzResearch.WordTrace tailWord_848233 prefixEnd_848233 387156654226920016165825 := by
  unfold tailWord_848233
  simp only [CollatzResearch.WordTrace]
  refine ⟨30937599136004182508085353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20625066090669455005390235 30937599136004182508085353)
  ·
    refine ⟨23203199352003136881064015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30937599136004182508085353 23203199352003136881064015)
    ·
      refine ⟨34804799028004705321596023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23203199352003136881064015 34804799028004705321596023)
      ·
        refine ⟨52207198542007057982394035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34804799028004705321596023 52207198542007057982394035)
        ·
          refine ⟨78310797813010586973591053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52207198542007057982394035 78310797813010586973591053)
          ·
            refine ⟨29366549179878970115096645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78310797813010586973591053 29366549179878970115096645)
            ·
              refine ⟨5506227971227306896580621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29366549179878970115096645 5506227971227306896580621)
              ·
                refine ⟨2064835489210240086217733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5506227971227306896580621 2064835489210240086217733)
                ·
                  refine ⟨387156654226920016165825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064835489210240086217733 387156654226920016165825)
                  ·
                    rfl

theorem cell20_848233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_848233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848233 prefixEnd_848233 := by exact prefixLift 848233
  have htrace : WordTrace (prefixWord ++ tailWord_848233) baseStart_848233 baseEnd_848233 := by
    simpa [prefixWord, tailWord_848233, baseEnd_848233] using wordTrace_append hprefix tailTrace_848233
  have hstable : (prefixWord ++ tailWord_848233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848233).length < 2 ^ (prefixWord ++ tailWord_848233).sum := by decide
  have hdescent : baseEnd_848233 < baseStart_848233 := by decide
  rcases family_descends (prefixWord ++ tailWord_848233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848236 : List Nat := [2, 2, 1, 1, 6, 2, 1, 5]
def baseStart_848236 : Nat := 118140960795 + 848236 * 2 ^ 59
def prefixEnd_848236 : Nat := 4983230072969 + 3 ^ 40 * 848236 * 2
def baseEnd_848236 : Nat := 129052674502888446355271

theorem tailTrace_848236 : CollatzResearch.WordTrace tailWord_848236 prefixEnd_848236 129052674502888446355271 := by
  unfold tailWord_848236
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468854277496657010222281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20625139036662209346963041 15468854277496657010222281)
  ·
    refine ⟨11601640708122492757666711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15468854277496657010222281 11601640708122492757666711)
    ·
      refine ⟨17402461062183739136500067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601640708122492757666711 17402461062183739136500067)
      ·
        refine ⟨26103691593275608704750101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402461062183739136500067 26103691593275608704750101)
        ·
          refine ⟨1223610543434794158035161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26103691593275608704750101 1223610543434794158035161)
          ·
            refine ⟨917707907576095618526371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223610543434794158035161 917707907576095618526371)
            ·
              refine ⟨1376561861364143427789557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917707907576095618526371 1376561861364143427789557)
              ·
                refine ⟨129052674502888446355271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376561861364143427789557 129052674502888446355271)
                ·
                  rfl

theorem cell20_848236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_848236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848236 prefixEnd_848236 := by exact prefixLift 848236
  have htrace : WordTrace (prefixWord ++ tailWord_848236) baseStart_848236 baseEnd_848236 := by
    simpa [prefixWord, tailWord_848236, baseEnd_848236] using wordTrace_append hprefix tailTrace_848236
  have hstable : (prefixWord ++ tailWord_848236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848236).length < 2 ^ (prefixWord ++ tailWord_848236).sum := by decide
  have hdescent : baseEnd_848236 < baseStart_848236 := by decide
  rcases family_descends (prefixWord ++ tailWord_848236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848246 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_848246 : Nat := 118140960795 + 848246 * 2 ^ 59
def prefixEnd_848246 : Nat := 4983230072969 + 3 ^ 40 * 848246 * 2
def baseEnd_848246 : Nat := 387162587781149748732439

theorem tailTrace_848246 : CollatzResearch.WordTrace tailWord_848246 prefixEnd_848246 387162587781149748732439 := by
  unfold tailWord_848246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933629580309817858019287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20625382189971390485539061 1933629580309817858019287)
  ·
    refine ⟨2900444370464726787028931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933629580309817858019287 2900444370464726787028931)
    ·
      refine ⟨4350666555697090180543397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2900444370464726787028931 4350666555697090180543397)
      ·
        refine ⟨815749979193204408851887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4350666555697090180543397 815749979193204408851887)
        ·
          refine ⟨1223624968789806613277831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815749979193204408851887 1223624968789806613277831)
          ·
            refine ⟨1835437453184709919916747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223624968789806613277831 1835437453184709919916747)
            ·
              refine ⟨2753156179777064879875121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835437453184709919916747 2753156179777064879875121)
              ·
                refine ⟨2064867134832798659906341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753156179777064879875121 2064867134832798659906341)
                ·
                  refine ⟨387162587781149748732439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064867134832798659906341 387162587781149748732439)
                  ·
                    rfl

theorem cell20_848246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_848246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848246 prefixEnd_848246 := by exact prefixLift 848246
  have htrace : WordTrace (prefixWord ++ tailWord_848246) baseStart_848246 baseEnd_848246 := by
    simpa [prefixWord, tailWord_848246, baseEnd_848246] using wordTrace_append hprefix tailTrace_848246
  have hstable : (prefixWord ++ tailWord_848246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848246).length < 2 ^ (prefixWord ++ tailWord_848246).sum := by decide
  have hdescent : baseEnd_848246 < baseStart_848246 := by decide
  rcases family_descends (prefixWord ++ tailWord_848246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848264 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_848264 : Nat := 118140960795 + 848264 * 2 ^ 59
def prefixEnd_848264 : Nat := 4983230072969 + 3 ^ 40 * 848264 * 2
def baseEnd_848264 : Nat := 387170803471621686132365

theorem tailTrace_848264 : CollatzResearch.WordTrace tailWord_848264 prefixEnd_848264 387170803471621686132365 := by
  unfold tailWord_848264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469364899445937401231923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20625819865927916534975897 15469364899445937401231923)
  ·
    refine ⟨23204047349168906101847885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15469364899445937401231923 23204047349168906101847885)
    ·
      refine ⟨8701517755938339788192957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23204047349168906101847885 8701517755938339788192957)
      ·
        refine ⟨3263069158476877420572359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8701517755938339788192957 3263069158476877420572359)
        ·
          refine ⟨4894603737715316130858539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263069158476877420572359 4894603737715316130858539)
          ·
            refine ⟨7341905606572974196287809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894603737715316130858539 7341905606572974196287809)
            ·
              refine ⟨5506429204929730647215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7341905606572974196287809 5506429204929730647215857)
              ·
                refine ⟨4129821903697297985411893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506429204929730647215857 4129821903697297985411893)
                ·
                  refine ⟨387170803471621686132365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4129821903697297985411893 387170803471621686132365)
                  ·
                    rfl

theorem cell20_848264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_848264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848264 prefixEnd_848264 := by exact prefixLift 848264
  have htrace : WordTrace (prefixWord ++ tailWord_848264) baseStart_848264 baseEnd_848264 := by
    simpa [prefixWord, tailWord_848264, baseEnd_848264] using wordTrace_append hprefix tailTrace_848264
  have hstable : (prefixWord ++ tailWord_848264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848264).length < 2 ^ (prefixWord ++ tailWord_848264).sum := by decide
  have hdescent : baseEnd_848264 < baseStart_848264 := by decide
  rcases family_descends (prefixWord ++ tailWord_848264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848267 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 2]
def baseStart_848267 : Nat := 118140960795 + 848267 * 2 ^ 59
def prefixEnd_848267 : Nat := 4983230072969 + 3 ^ 40 * 848267 * 2
def baseEnd_848267 : Nat := 387172172753367009032353

theorem tailTrace_848267 : CollatzResearch.WordTrace tailWord_848267 prefixEnd_848267 387172172753367009032353 := by
  unfold tailWord_848267
  simp only [CollatzResearch.WordTrace]
  refine ⟨30938839217881006314823055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20625892811920670876548703 30938839217881006314823055)
  ·
    refine ⟨46408258826821509472234583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30938839217881006314823055 46408258826821509472234583)
    ·
      refine ⟨69612388240232264208351875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46408258826821509472234583 69612388240232264208351875)
      ·
        refine ⟨104418582360348396312527813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69612388240232264208351875 104418582360348396312527813)
        ·
          refine ⟨19578484192565324308598965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104418582360348396312527813 19578484192565324308598965)
          ·
            refine ⟨1835482893052999153931153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19578484192565324308598965 1835482893052999153931153)
            ·
              refine ⟨1376612169789749365448365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835482893052999153931153 1376612169789749365448365)
              ·
                refine ⟨516229563671156012043137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376612169789749365448365 516229563671156012043137)
                ·
                  refine ⟨387172172753367009032353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516229563671156012043137 387172172753367009032353)
                  ·
                    rfl

theorem cell20_848267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 2].length) (baseStart_848267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848267 prefixEnd_848267 := by exact prefixLift 848267
  have htrace : WordTrace (prefixWord ++ tailWord_848267) baseStart_848267 baseEnd_848267 := by
    simpa [prefixWord, tailWord_848267, baseEnd_848267] using wordTrace_append hprefix tailTrace_848267
  have hstable : (prefixWord ++ tailWord_848267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848267).length < 2 ^ (prefixWord ++ tailWord_848267).sum := by decide
  have hdescent : baseEnd_848267 < baseStart_848267 := by decide
  rcases family_descends (prefixWord ++ tailWord_848267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848288 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_848288 : Nat := 118140960795 + 848288 * 2 ^ 59
def prefixEnd_848288 : Nat := 4983230072969 + 3 ^ 40 * 848288 * 2
def baseEnd_848288 : Nat := 387181757725584269332267

theorem tailTrace_848288 : CollatzResearch.WordTrace tailWord_848288 prefixEnd_848288 387181757725584269332267 := by
  unfold tailWord_848288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15469802575402463450668759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20626403433869951267558345 15469802575402463450668759)
  ·
    refine ⟨23204703863103695176003139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15469802575402463450668759 23204703863103695176003139)
    ·
      refine ⟨34807055794655542764004709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23204703863103695176003139 34807055794655542764004709)
      ·
        refine ⟨6526322961497914268250883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34807055794655542764004709 6526322961497914268250883)
        ·
          refine ⟨9789484442246871402376325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526322961497914268250883 9789484442246871402376325)
          ·
            refine ⟨1835528332921288387945561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9789484442246871402376325 1835528332921288387945561)
            ·
              refine ⟨1376646249690966290959171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835528332921288387945561 1376646249690966290959171)
              ·
                refine ⟨2064969374536449436438757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376646249690966290959171 2064969374536449436438757)
                ·
                  refine ⟨387181757725584269332267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064969374536449436438757 387181757725584269332267)
                  ·
                    rfl

theorem cell20_848288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_848288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848288 prefixEnd_848288 := by exact prefixLift 848288
  have htrace : WordTrace (prefixWord ++ tailWord_848288) baseStart_848288 baseEnd_848288 := by
    simpa [prefixWord, tailWord_848288, baseEnd_848288] using wordTrace_append hprefix tailTrace_848288
  have hstable : (prefixWord ++ tailWord_848288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848288).length < 2 ^ (prefixWord ++ tailWord_848288).sum := by decide
  have hdescent : baseEnd_848288 < baseStart_848288 := by decide
  rcases family_descends (prefixWord ++ tailWord_848288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848361 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_848361 : Nat := 118140960795 + 848361 * 2 ^ 59
def prefixEnd_848361 : Nat := 4983230072969 + 3 ^ 40 * 848361 * 2
def baseEnd_848361 : Nat := 387215076914720459898635

theorem tailTrace_848361 : CollatzResearch.WordTrace tailWord_848361 prefixEnd_848361 387215076914720459898635 := by
  unfold tailWord_848361
  simp only [CollatzResearch.WordTrace]
  refine ⟨30942267679540460368744937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20628178453026973579163291 30942267679540460368744937)
  ·
    refine ⟨23206700759655345276558703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30942267679540460368744937 23206700759655345276558703)
    ·
      refine ⟨34810051139483017914838055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23206700759655345276558703 34810051139483017914838055)
      ·
        refine ⟨52215076709224526872257083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34810051139483017914838055 52215076709224526872257083)
        ·
          refine ⟨78322615063836790308385625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52215076709224526872257083 78322615063836790308385625)
          ·
            refine ⟨58741961297877592731289219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78322615063836790308385625 58741961297877592731289219)
            ·
              refine ⟨88112941946816389096933829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58741961297877592731289219 88112941946816389096933829)
              ·
                refine ⟨16521176615028072955675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88112941946816389096933829 16521176615028072955675093)
                ·
                  refine ⟨387215076914720459898635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16521176615028072955675093 387215076914720459898635)
                  ·
                    rfl

theorem cell20_848361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_848361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848361 prefixEnd_848361 := by exact prefixLift 848361
  have htrace : WordTrace (prefixWord ++ tailWord_848361) baseStart_848361 baseEnd_848361 := by
    simpa [prefixWord, tailWord_848361, baseEnd_848361] using wordTrace_append hprefix tailTrace_848361
  have hstable : (prefixWord ++ tailWord_848361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848361).length < 2 ^ (prefixWord ++ tailWord_848361).sum := by decide
  have hdescent : baseEnd_848361 < baseStart_848361 := by decide
  rcases family_descends (prefixWord ++ tailWord_848361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848395 : List Nat := [1, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_848395 : Nat := 118140960795 + 848395 * 2 ^ 59
def prefixEnd_848395 : Nat := 4983230072969 + 3 ^ 40 * 848395 * 2
def baseEnd_848395 : Nat := 387230595441167452765163

theorem tailTrace_848395 : CollatzResearch.WordTrace tailWord_848395 prefixEnd_848395 387230595441167452765163 := by
  unfold tailWord_848395
  simp only [CollatzResearch.WordTrace]
  refine ⟨30943507761417284175482639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20629005174278189450321759 30943507761417284175482639)
  ·
    refine ⟨46415261642125926263223959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30943507761417284175482639 46415261642125926263223959)
    ·
      refine ⟨69622892463188889394835939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46415261642125926263223959 69622892463188889394835939)
      ·
        refine ⟨104434338694783334092253909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69622892463188889394835939 104434338694783334092253909)
        ·
          refine ⟨2447679813158984392787201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 104434338694783334092253909 2447679813158984392787201)
          ·
            refine ⟨1835759859869238294590401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447679813158984392787201 1835759859869238294590401)
            ·
              refine ⟨1376819894901928720942801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835759859869238294590401 1376819894901928720942801)
              ·
                refine ⟨1032614921176446540707101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376819894901928720942801 1032614921176446540707101)
                ·
                  refine ⟨387230595441167452765163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032614921176446540707101 387230595441167452765163)
                  ·
                    rfl

theorem cell20_848395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_848395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848395 prefixEnd_848395 := by exact prefixLift 848395
  have htrace : WordTrace (prefixWord ++ tailWord_848395) baseStart_848395 baseEnd_848395 := by
    simpa [prefixWord, tailWord_848395, baseEnd_848395] using wordTrace_append hprefix tailTrace_848395
  have hstable : (prefixWord ++ tailWord_848395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848395).length < 2 ^ (prefixWord ++ tailWord_848395).sum := by decide
  have hdescent : baseEnd_848395 < baseStart_848395 := by decide
  rcases family_descends (prefixWord ++ tailWord_848395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848398 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_848398 : Nat := 118140960795 + 848398 * 2 ^ 59
def prefixEnd_848398 : Nat := 4983230072969 + 3 ^ 40 * 848398 * 2
def baseEnd_848398 : Nat := 387231964722912775665151

theorem tailTrace_848398 : CollatzResearch.WordTrace tailWord_848398 prefixEnd_848398 387231964722912775665151 := by
  unfold tailWord_848398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867952147550801960980231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20629078120270943791894565 3867952147550801960980231)
  ·
    refine ⟨5801928221326202941470347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3867952147550801960980231 5801928221326202941470347)
    ·
      refine ⟨8702892331989304412205521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801928221326202941470347 8702892331989304412205521)
      ·
        refine ⟨6527169248991978309154141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8702892331989304412205521 6527169248991978309154141)
        ·
          refine ⟨2447688468371991865932803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6527169248991978309154141 2447688468371991865932803)
          ·
            refine ⟨3671532702557987798899205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447688468371991865932803 3671532702557987798899205)
            ·
              refine ⟨688412381729622712293601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3671532702557987798899205 688412381729622712293601)
              ·
                refine ⟨516309286297217034220201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688412381729622712293601 516309286297217034220201)
                ·
                  refine ⟨387231964722912775665151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516309286297217034220201 387231964722912775665151)
                  ·
                    rfl

theorem cell20_848398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_848398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848398 prefixEnd_848398 := by exact prefixLift 848398
  have htrace : WordTrace (prefixWord ++ tailWord_848398) baseStart_848398 baseEnd_848398 := by
    simpa [prefixWord, tailWord_848398, baseEnd_848398] using wordTrace_append hprefix tailTrace_848398
  have hstable : (prefixWord ++ tailWord_848398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848398).length < 2 ^ (prefixWord ++ tailWord_848398).sum := by decide
  have hdescent : baseEnd_848398 < baseStart_848398 := by decide
  rcases family_descends (prefixWord ++ tailWord_848398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848426 : List Nat := [3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_848426 : Nat := 118140960795 + 848426 * 2 ^ 59
def prefixEnd_848426 : Nat := 4983230072969 + 3 ^ 40 * 848426 * 2
def baseEnd_848426 : Nat := 129081581561956374243901

theorem tailTrace_848426 : CollatzResearch.WordTrace tailWord_848426 prefixEnd_848426 129081581561956374243901 := by
  unfold tailWord_848426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736159606076244117465283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20629758949536650979907421 7736159606076244117465283)
  ·
    refine ⟨11604239409114366176197925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7736159606076244117465283 11604239409114366176197925)
    ·
      refine ⟨2175794889208943658037111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11604239409114366176197925 2175794889208943658037111)
      ·
        refine ⟨3263692333813415487055667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175794889208943658037111 3263692333813415487055667)
        ·
          refine ⟨4895538500720123230583501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263692333813415487055667 4895538500720123230583501)
          ·
            refine ⟨1835826937770046211468813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4895538500720123230583501 1835826937770046211468813)
            ·
              refine ⟨688435101663767329300805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1835826937770046211468813 688435101663767329300805)
              ·
                refine ⟨129081581561956374243901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688435101663767329300805 129081581561956374243901)
                ·
                  rfl

theorem cell20_848426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_848426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848426 prefixEnd_848426 := by exact prefixLift 848426
  have htrace : WordTrace (prefixWord ++ tailWord_848426) baseStart_848426 baseEnd_848426 := by
    simpa [prefixWord, tailWord_848426, baseEnd_848426] using wordTrace_append hprefix tailTrace_848426
  have hstable : (prefixWord ++ tailWord_848426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848426).length < 2 ^ (prefixWord ++ tailWord_848426).sum := by decide
  have hdescent : baseEnd_848426 < baseStart_848426 := by decide
  rcases family_descends (prefixWord ++ tailWord_848426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848446 : List Nat := [4, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_848446 : Nat := 118140960795 + 848446 * 2 ^ 59
def prefixEnd_848446 : Nat := 4983230072969 + 3 ^ 40 * 848446 * 2
def baseEnd_848446 : Nat := 387253873230837942064955

theorem tailTrace_848446 : CollatzResearch.WordTrace tailWord_848446 prefixEnd_848446 387253873230837942064955 := by
  unfold tailWord_848446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868170985529064985698649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20630245256155013257059461 3868170985529064985698649)
  ·
    refine ⟨2901128239146798739273987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3868170985529064985698649 2901128239146798739273987)
    ·
      refine ⟨4351692358720198108910981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901128239146798739273987 4351692358720198108910981)
      ·
        refine ⟨815942317260037145420809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4351692358720198108910981 815942317260037145420809)
        ·
          refine ⟨611956737945027859065607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815942317260037145420809 611956737945027859065607)
          ·
            refine ⟨917935106917541788598411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611956737945027859065607 917935106917541788598411)
            ·
              refine ⟨1376902660376312682897617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917935106917541788598411 1376902660376312682897617)
              ·
                refine ⟨1032676995282234512173213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376902660376312682897617 1032676995282234512173213)
                ·
                  refine ⟨387253873230837942064955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032676995282234512173213 387253873230837942064955)
                  ·
                    rfl

theorem cell20_848446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_848446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848446 prefixEnd_848446 := by exact prefixLift 848446
  have htrace : WordTrace (prefixWord ++ tailWord_848446) baseStart_848446 baseEnd_848446 := by
    simpa [prefixWord, tailWord_848446, baseEnd_848446] using wordTrace_append hprefix tailTrace_848446
  have hstable : (prefixWord ++ tailWord_848446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848446).length < 2 ^ (prefixWord ++ tailWord_848446).sum := by decide
  have hdescent : baseEnd_848446 < baseStart_848446 := by decide
  rcases family_descends (prefixWord ++ tailWord_848446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848471 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 3]
def baseStart_848471 : Nat := 118140960795 + 848471 * 2 ^ 59
def prefixEnd_848471 : Nat := 4983230072969 + 3 ^ 40 * 848471 * 2
def baseEnd_848471 : Nat := 387265283912048966231519

theorem tailTrace_848471 : CollatzResearch.WordTrace tailWord_848471 prefixEnd_848471 387265283912048966231519 := by
  unfold tailWord_848471
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946279709141949155249267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20630853139427966103499511 30946279709141949155249267)
  ·
    refine ⟨46419419563712923732873901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30946279709141949155249267 46419419563712923732873901)
    ·
      refine ⟨17407282336392346399827713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46419419563712923732873901 17407282336392346399827713)
      ·
        refine ⟨13055461752294259799870785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17407282336392346399827713 13055461752294259799870785)
        ·
          refine ⟨9791596314220694849903089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13055461752294259799870785 9791596314220694849903089)
          ·
            refine ⟨7343697235665521137427317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791596314220694849903089 7343697235665521137427317)
            ·
              refine ⟨688471615843642606633811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7343697235665521137427317 688471615843642606633811)
              ·
                refine ⟨1032707423765463909950717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688471615843642606633811 1032707423765463909950717)
                ·
                  refine ⟨387265283912048966231519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032707423765463909950717 387265283912048966231519)
                  ·
                    rfl

theorem cell20_848471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_848471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848471 prefixEnd_848471 := by exact prefixLift 848471
  have htrace : WordTrace (prefixWord ++ tailWord_848471) baseStart_848471 baseEnd_848471 := by
    simpa [prefixWord, tailWord_848471, baseEnd_848471] using wordTrace_append hprefix tailTrace_848471
  have hstable : (prefixWord ++ tailWord_848471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848471).length < 2 ^ (prefixWord ++ tailWord_848471).sum := by decide
  have hdescent : baseEnd_848471 < baseStart_848471 := by decide
  rcases family_descends (prefixWord ++ tailWord_848471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848485 : List Nat := [1, 3, 1, 3, 4, 1, 1, 6]
def baseStart_848485 : Nat := 118140960795 + 848485 * 2 ^ 59
def prefixEnd_848485 : Nat := 4983230072969 + 3 ^ 40 * 848485 * 2
def baseEnd_848485 : Nat := 129090557964509046588265

theorem tailTrace_848485 : CollatzResearch.WordTrace tailWord_848485 prefixEnd_848485 129090557964509046588265 := by
  unfold tailWord_848485
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946790331091229546258909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20631193554060819697505939 30946790331091229546258909)
  ·
    refine ⟨11605046374159211079847091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30946790331091229546258909 11605046374159211079847091)
    ·
      refine ⟨17407569561238816619770637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11605046374159211079847091 17407569561238816619770637)
      ·
        refine ⟨6527838585464556232413989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17407569561238816619770637 6527838585464556232413989)
        ·
          refine ⟨1223969734774604293577623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6527838585464556232413989 1223969734774604293577623)
          ·
            refine ⟨1835954602161906440366435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223969734774604293577623 1835954602161906440366435)
            ·
              refine ⟨2753931903242859660549653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835954602161906440366435 2753931903242859660549653)
              ·
                refine ⟨129090557964509046588265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2753931903242859660549653 129090557964509046588265)
                ·
                  rfl

theorem cell20_848485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_848485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848485 prefixEnd_848485 := by exact prefixLift 848485
  have htrace : WordTrace (prefixWord ++ tailWord_848485) baseStart_848485 baseEnd_848485 := by
    simpa [prefixWord, tailWord_848485, baseEnd_848485] using wordTrace_append hprefix tailTrace_848485
  have hstable : (prefixWord ++ tailWord_848485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848485).length < 2 ^ (prefixWord ++ tailWord_848485).sum := by decide
  have hdescent : baseEnd_848485 < baseStart_848485 := by decide
  rcases family_descends (prefixWord ++ tailWord_848485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848502 : List Nat := [5, 1, 1, 2, 3, 2, 6]
def baseStart_848502 : Nat := 118140960795 + 848502 * 2 ^ 59
def prefixEnd_848502 : Nat := 4983230072969 + 3 ^ 40 * 848502 * 2
def baseEnd_848502 : Nat := 43031048128527848466451

theorem tailTrace_848502 : CollatzResearch.WordTrace tailWord_848502 prefixEnd_848502 43031048128527848466451 := by
  unfold tailWord_848502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934213148251852590601735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20631606914686427633085173 1934213148251852590601735)
  ·
    refine ⟨2901319722377778885902603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1934213148251852590601735 2901319722377778885902603)
    ·
      refine ⟨4351979583566668328853905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901319722377778885902603 4351979583566668328853905)
      ·
        refine ⟨3263984687675001246640429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4351979583566668328853905 3263984687675001246640429)
        ·
          refine ⟨1223994257878125467490161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3263984687675001246640429 1223994257878125467490161)
          ·
            refine ⟨917995693408594100617621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223994257878125467490161 917995693408594100617621)
            ·
              refine ⟨43031048128527848466451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 917995693408594100617621 43031048128527848466451)
              ·
                rfl

theorem cell20_848502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_848502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848502 prefixEnd_848502 := by exact prefixLift 848502
  have htrace : WordTrace (prefixWord ++ tailWord_848502) baseStart_848502 baseEnd_848502 := by
    simpa [prefixWord, tailWord_848502, baseEnd_848502] using wordTrace_append hprefix tailTrace_848502
  have hstable : (prefixWord ++ tailWord_848502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848502).length < 2 ^ (prefixWord ++ tailWord_848502).sum := by decide
  have hdescent : baseEnd_848502 < baseStart_848502 := by decide
  rcases family_descends (prefixWord ++ tailWord_848502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848516 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_848516 : Nat := 118140960795 + 848516 * 2 ^ 59
def prefixEnd_848516 : Nat := 4983230072969 + 3 ^ 40 * 848516 * 2
def baseEnd_848516 : Nat := 387285823138228809731335

theorem tailTrace_848516 : CollatzResearch.WordTrace tailWord_848516 prefixEnd_848516 387285823138228809731335 := by
  unfold tailWord_848516
  simp only [CollatzResearch.WordTrace]
  refine ⟨15473960496989460920318701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20631947329319281227091601 15473960496989460920318701)
  ·
    refine ⟨5802735186371047845119513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15473960496989460920318701 5802735186371047845119513)
    ·
      refine ⟨4352051389778285883839635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5802735186371047845119513 4352051389778285883839635)
      ·
        refine ⟨6528077084667428825759453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352051389778285883839635 6528077084667428825759453)
        ·
          refine ⟨2448028906750285809659795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6528077084667428825759453 2448028906750285809659795)
          ·
            refine ⟨3672043360125428714489693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448028906750285809659795 3672043360125428714489693)
            ·
              refine ⟨1377016260047035767933635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3672043360125428714489693 1377016260047035767933635)
              ·
                refine ⟨2065524390070553651900453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377016260047035767933635 2065524390070553651900453)
                ·
                  refine ⟨387285823138228809731335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065524390070553651900453 387285823138228809731335)
                  ·
                    rfl

theorem cell20_848516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_848516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848516 prefixEnd_848516 := by exact prefixLift 848516
  have htrace : WordTrace (prefixWord ++ tailWord_848516) baseStart_848516 baseEnd_848516 := by
    simpa [prefixWord, tailWord_848516, baseEnd_848516] using wordTrace_append hprefix tailTrace_848516
  have hstable : (prefixWord ++ tailWord_848516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848516).length < 2 ^ (prefixWord ++ tailWord_848516).sum := by decide
  have hdescent : baseEnd_848516 < baseStart_848516 := by decide
  rcases family_descends (prefixWord ++ tailWord_848516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848561 : List Nat := [1, 2, 2, 6, 1, 8]
def baseStart_848561 : Nat := 118140960795 + 848561 * 2 ^ 59
def prefixEnd_848561 : Nat := 4983230072969 + 3 ^ 40 * 848561 * 2
def baseEnd_848561 : Nat := 14344680087570690860413

theorem tailTrace_848561 : CollatzResearch.WordTrace tailWord_848561 prefixEnd_848561 14344680087570690860413 := by
  unfold tailWord_848561
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949562278815894526025537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20633041519210596350683691 30949562278815894526025537)
  ·
    refine ⟨23212171709111920894519153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30949562278815894526025537 23212171709111920894519153)
    ·
      refine ⟨17409128781833940670889365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23212171709111920894519153 17409128781833940670889365)
      ·
        refine ⟨816052911648465968947939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17409128781833940670889365 816052911648465968947939)
        ·
          refine ⟨1224079367472698953421909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816052911648465968947939 1224079367472698953421909)
          ·
            refine ⟨14344680087570690860413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1224079367472698953421909 14344680087570690860413)
            ·
              rfl

theorem cell20_848561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 8].length) (baseStart_848561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848561 prefixEnd_848561 := by exact prefixLift 848561
  have htrace : WordTrace (prefixWord ++ tailWord_848561) baseStart_848561 baseEnd_848561 := by
    simpa [prefixWord, tailWord_848561, baseEnd_848561] using wordTrace_append hprefix tailTrace_848561
  have hstable : (prefixWord ++ tailWord_848561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848561).length < 2 ^ (prefixWord ++ tailWord_848561).sum := by decide
  have hdescent : baseEnd_848561 < baseStart_848561 := by decide
  rcases family_descends (prefixWord ++ tailWord_848561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848567 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 2]
def baseStart_848567 : Nat := 118140960795 + 848567 * 2 ^ 59
def prefixEnd_848567 : Nat := 4983230072969 + 3 ^ 40 * 848567 * 2
def baseEnd_848567 : Nat := 387309100927899299031127

theorem tailTrace_848567 : CollatzResearch.WordTrace tailWord_848567 prefixEnd_848567 387309100927899299031127 := by
  unfold tailWord_848567
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949781116794157550743955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20633187411196105033829303 30949781116794157550743955)
  ·
    refine ⟨46424671675191236326115933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30949781116794157550743955 46424671675191236326115933)
    ·
      refine ⟨17409251878196713622293475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46424671675191236326115933 17409251878196713622293475)
      ·
        refine ⟨26113877817295070433440213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17409251878196713622293475 26113877817295070433440213)
        ·
          refine ⟨612044011342853213283755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26113877817295070433440213 612044011342853213283755)
          ·
            refine ⟨918066017014279819925633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612044011342853213283755 918066017014279819925633)
            ·
              refine ⟨688549512760709864944225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918066017014279819925633 688549512760709864944225)
              ·
                refine ⟨516412134570532398708169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688549512760709864944225 516412134570532398708169)
                ·
                  refine ⟨387309100927899299031127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516412134570532398708169 387309100927899299031127)
                  ·
                    rfl

theorem cell20_848567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 2].length) (baseStart_848567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848567 prefixEnd_848567 := by exact prefixLift 848567
  have htrace : WordTrace (prefixWord ++ tailWord_848567) baseStart_848567 baseEnd_848567 := by
    simpa [prefixWord, tailWord_848567, baseEnd_848567] using wordTrace_append hprefix tailTrace_848567
  have hstable : (prefixWord ++ tailWord_848567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848567).length < 2 ^ (prefixWord ++ tailWord_848567).sum := by decide
  have hdescent : baseEnd_848567 < baseStart_848567 := by decide
  rcases family_descends (prefixWord ++ tailWord_848567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848599 : List Nat := [1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_848599 : Nat := 118140960795 + 848599 * 2 ^ 59
def prefixEnd_848599 : Nat := 4983230072969 + 3 ^ 40 * 848599 * 2
def baseEnd_848599 : Nat := 129107902199949803321443

theorem tailTrace_848599 : CollatzResearch.WordTrace tailWord_848599 prefixEnd_848599 129107902199949803321443 := by
  unfold tailWord_848599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30950948252678227015908851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20633965501785484677272567 30950948252678227015908851)
  ·
    refine ⟨46426422379017340523863277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30950948252678227015908851 46426422379017340523863277)
    ·
      refine ⟨17409908392131502696448729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46426422379017340523863277 17409908392131502696448729)
      ·
        refine ⟨13057431294098627022336547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17409908392131502696448729 13057431294098627022336547)
        ·
          refine ⟨19586146941147940533504821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13057431294098627022336547 19586146941147940533504821)
          ·
            refine ⟨1836201275732619425016077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19586146941147940533504821 1836201275732619425016077)
            ·
              refine ⟨688575478399732284381029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1836201275732619425016077 688575478399732284381029)
              ·
                refine ⟨129107902199949803321443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688575478399732284381029 129107902199949803321443)
                ·
                  rfl

theorem cell20_848599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_848599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848599 prefixEnd_848599 := by exact prefixLift 848599
  have htrace : WordTrace (prefixWord ++ tailWord_848599) baseStart_848599 baseEnd_848599 := by
    simpa [prefixWord, tailWord_848599, baseEnd_848599] using wordTrace_append hprefix tailTrace_848599
  have hstable : (prefixWord ++ tailWord_848599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848599).length < 2 ^ (prefixWord ++ tailWord_848599).sum := by decide
  have hdescent : baseEnd_848599 < baseStart_848599 := by decide
  rcases family_descends (prefixWord ++ tailWord_848599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848609 : List Nat := [1, 2, 3, 1, 4, 2, 2, 3, 2]
def baseStart_848609 : Nat := 118140960795 + 848609 * 2 ^ 59
def prefixEnd_848609 : Nat := 4983230072969 + 3 ^ 40 * 848609 * 2
def baseEnd_848609 : Nat := 387328270872333819630955

theorem tailTrace_848609 : CollatzResearch.WordTrace tailWord_848609 prefixEnd_848609 387328270872333819630955 := by
  unfold tailWord_848609
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951312982641998723772881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20634208655094665815848587 30951312982641998723772881)
  ·
    refine ⟨23213484736981499042829661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30951312982641998723772881 23213484736981499042829661)
    ·
      refine ⟨8705056776368062141061123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23213484736981499042829661 8705056776368062141061123)
      ·
        refine ⟨13057585164552093211591685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8705056776368062141061123 13057585164552093211591685)
        ·
          refine ⟨2448297218353517477173441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13057585164552093211591685 2448297218353517477173441)
          ·
            refine ⟨1836222913765138107880081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448297218353517477173441 1836222913765138107880081)
            ·
              refine ⟨1377167185323853580910061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836222913765138107880081 1377167185323853580910061)
              ·
                refine ⟨516437694496445092841273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1377167185323853580910061 516437694496445092841273)
                ·
                  refine ⟨387328270872333819630955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516437694496445092841273 387328270872333819630955)
                  ·
                    rfl

theorem cell20_848609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_848609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848609 prefixEnd_848609 := by exact prefixLift 848609
  have htrace : WordTrace (prefixWord ++ tailWord_848609) baseStart_848609 baseEnd_848609 := by
    simpa [prefixWord, tailWord_848609, baseEnd_848609] using wordTrace_append hprefix tailTrace_848609
  have hstable : (prefixWord ++ tailWord_848609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848609).length < 2 ^ (prefixWord ++ tailWord_848609).sum := by decide
  have hdescent : baseEnd_848609 < baseStart_848609 := by decide
  rcases family_descends (prefixWord ++ tailWord_848609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848623 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_848623 : Nat := 118140960795 + 848623 * 2 ^ 59
def prefixEnd_848623 : Nat := 4983230072969 + 3 ^ 40 * 848623 * 2
def baseEnd_848623 : Nat := 387334660853811993164231

theorem tailTrace_848623 : CollatzResearch.WordTrace tailWord_848623 prefixEnd_848623 387334660853811993164231 := by
  unfold tailWord_848623
  simp only [CollatzResearch.WordTrace]
  refine ⟨30951823604591279114782523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20634549069727519409855015 30951823604591279114782523)
  ·
    refine ⟨46427735406886918672173785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30951823604591279114782523 46427735406886918672173785)
    ·
      refine ⟨34820801555165189004130339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46427735406886918672173785 34820801555165189004130339)
      ·
        refine ⟨52231202332747783506195509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34820801555165189004130339 52231202332747783506195509)
        ·
          refine ⟨4896675218695104703705829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52231202332747783506195509 4896675218695104703705829)
          ·
            refine ⟨918126603505332131944843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4896675218695104703705829 918126603505332131944843)
            ·
              refine ⟨1377189905257998197917265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918126603505332131944843 1377189905257998197917265)
              ·
                refine ⟨1032892428943498648437949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377189905257998197917265 1032892428943498648437949)
                ·
                  refine ⟨387334660853811993164231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032892428943498648437949 387334660853811993164231)
                  ·
                    rfl

theorem cell20_848623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_848623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848623 prefixEnd_848623 := by exact prefixLift 848623
  have htrace : WordTrace (prefixWord ++ tailWord_848623) baseStart_848623 baseEnd_848623 := by
    simpa [prefixWord, tailWord_848623, baseEnd_848623] using wordTrace_append hprefix tailTrace_848623
  have hstable : (prefixWord ++ tailWord_848623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848623).length < 2 ^ (prefixWord ++ tailWord_848623).sum := by decide
  have hdescent : baseEnd_848623 < baseStart_848623 := by decide
  rcases family_descends (prefixWord ++ tailWord_848623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848630 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_848630 : Nat := 118140960795 + 848630 * 2 ^ 59
def prefixEnd_848630 : Nat := 4983230072969 + 3 ^ 40 * 848630 * 2
def baseEnd_848630 : Nat := 387337855844551079930869

theorem tailTrace_848630 : CollatzResearch.WordTrace tailWord_848630 prefixEnd_848630 387337855844551079930869 := by
  unfold tailWord_848630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934504932222869956892959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20634719277043946206858229 1934504932222869956892959)
  ·
    refine ⟨2901757398334304935339439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1934504932222869956892959 2901757398334304935339439)
    ·
      refine ⟨4352636097501457403009159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901757398334304935339439 4352636097501457403009159)
      ·
        refine ⟨6528954146252186104513739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4352636097501457403009159 6528954146252186104513739)
        ·
          refine ⟨9793431219378279156770609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6528954146252186104513739 9793431219378279156770609)
          ·
            refine ⟨7345073414533709367577957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9793431219378279156770609 7345073414533709367577957)
            ·
              refine ⟨1377201265225070506420867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7345073414533709367577957 1377201265225070506420867)
              ·
                refine ⟨2065801897837605759631301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377201265225070506420867 2065801897837605759631301)
                ·
                  refine ⟨387337855844551079930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065801897837605759631301 387337855844551079930869)
                  ·
                    rfl

theorem cell20_848630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_848630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848630 prefixEnd_848630 := by exact prefixLift 848630
  have htrace : WordTrace (prefixWord ++ tailWord_848630) baseStart_848630 baseEnd_848630 := by
    simpa [prefixWord, tailWord_848630, baseEnd_848630] using wordTrace_append hprefix tailTrace_848630
  have hstable : (prefixWord ++ tailWord_848630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848630).length < 2 ^ (prefixWord ++ tailWord_848630).sum := by decide
  have hdescent : baseEnd_848630 < baseStart_848630 := by decide
  rcases family_descends (prefixWord ++ tailWord_848630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848692 : List Nat := [2, 5, 1, 1, 3, 1, 2, 5]
def baseStart_848692 : Nat := 118140960795 + 848692 * 2 ^ 59
def prefixEnd_848692 : Nat := 4983230072969 + 3 ^ 40 * 848692 * 2
def baseEnd_848692 : Nat := 129122051444651473287983

theorem tailTrace_848692 : CollatzResearch.WordTrace tailWord_848692 prefixEnd_848692 129122051444651473287983 := by
  unfold tailWord_848692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477170120670651949522165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20636226827560869266029553 15477170120670651949522165)
  ·
    refine ⟨1450984698812873620267703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15477170120670651949522165 1450984698812873620267703)
    ·
      refine ⟨2176477048219310430401555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450984698812873620267703 2176477048219310430401555)
      ·
        refine ⟨3264715572328965645602333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2176477048219310430401555 3264715572328965645602333)
        ·
          refine ⟨1224268339623362117100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3264715572328965645602333 1224268339623362117100875)
          ·
            refine ⟨1836402509435043175651313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224268339623362117100875 1836402509435043175651313)
            ·
              refine ⟨1377301882076282381738485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836402509435043175651313 1377301882076282381738485)
              ·
                refine ⟨129122051444651473287983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377301882076282381738485 129122051444651473287983)
                ·
                  rfl

theorem cell20_848692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_848692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848692 prefixEnd_848692 := by exact prefixLift 848692
  have htrace : WordTrace (prefixWord ++ tailWord_848692) baseStart_848692 baseEnd_848692 := by
    simpa [prefixWord, tailWord_848692, baseEnd_848692] using wordTrace_append hprefix tailTrace_848692
  have hstable : (prefixWord ++ tailWord_848692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848692).length < 2 ^ (prefixWord ++ tailWord_848692).sum := by decide
  have hdescent : baseEnd_848692 < baseStart_848692 := by decide
  rcases family_descends (prefixWord ++ tailWord_848692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848696 : List Nat := [2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_848696 : Nat := 118140960795 + 848696 * 2 ^ 59
def prefixEnd_848696 : Nat := 4983230072969 + 3 ^ 40 * 848696 * 2
def baseEnd_848696 : Nat := 129122660014316061243533

theorem tailTrace_848696 : CollatzResearch.WordTrace tailWord_848696 prefixEnd_848696 129122660014316061243533 := by
  unfold tailWord_848696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15477243066663406291094971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20636324088884541721459961 15477243066663406291094971)
  ·
    refine ⟨23215864599995109436642457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15477243066663406291094971 23215864599995109436642457)
    ·
      refine ⟨17411898449996332077481843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23215864599995109436642457 17411898449996332077481843)
      ·
        refine ⟨26117847674994498116222765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17411898449996332077481843 26117847674994498116222765)
        ·
          refine ⟨9794192878122936793583537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26117847674994498116222765 9794192878122936793583537)
          ·
            refine ⟨7345644658592202595187653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9794192878122936793583537 7345644658592202595187653)
            ·
              refine ⟨1377308373486037986597685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7345644658592202595187653 1377308373486037986597685)
              ·
                refine ⟨129122660014316061243533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377308373486037986597685 129122660014316061243533)
                ·
                  rfl

theorem cell20_848696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_848696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848696 prefixEnd_848696 := by exact prefixLift 848696
  have htrace : WordTrace (prefixWord ++ tailWord_848696) baseStart_848696 baseEnd_848696 := by
    simpa [prefixWord, tailWord_848696, baseEnd_848696] using wordTrace_append hprefix tailTrace_848696
  have hstable : (prefixWord ++ tailWord_848696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848696).length < 2 ^ (prefixWord ++ tailWord_848696).sum := by decide
  have hdescent : baseEnd_848696 < baseStart_848696 := by decide
  rcases family_descends (prefixWord ++ tailWord_848696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848740 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 2]
def baseStart_848740 : Nat := 118140960795 + 848740 * 2 ^ 59
def prefixEnd_848740 : Nat := 4983230072969 + 3 ^ 40 * 848740 * 2
def baseEnd_848740 : Nat := 387388062841879586263753

theorem tailTrace_848740 : CollatzResearch.WordTrace tailWord_848740 prefixEnd_848740 387388062841879586263753 := by
  unfold tailWord_848740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15478045472583704048395837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20637393963444938731194449 15478045472583704048395837)
  ·
    refine ⟨5804267052218889018148439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15478045472583704048395837 5804267052218889018148439)
    ·
      refine ⟨8706400578328333527222659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5804267052218889018148439 8706400578328333527222659)
      ·
        refine ⟨13059600867492500290833989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706400578328333527222659 13059600867492500290833989)
        ·
          refine ⟨2448675162654843804531373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13059600867492500290833989 2448675162654843804531373)
          ·
            refine ⟨918253185995566426699265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2448675162654843804531373 918253185995566426699265)
            ·
              refine ⟨688689889496674820024449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918253185995566426699265 688689889496674820024449)
              ·
                refine ⟨516517417122506115018337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688689889496674820024449 516517417122506115018337)
                ·
                  refine ⟨387388062841879586263753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516517417122506115018337 387388062841879586263753)
                  ·
                    rfl

theorem cell20_848740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_848740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848740 prefixEnd_848740 := by exact prefixLift 848740
  have htrace : WordTrace (prefixWord ++ tailWord_848740) baseStart_848740 baseEnd_848740 := by
    simpa [prefixWord, tailWord_848740, baseEnd_848740] using wordTrace_append hprefix tailTrace_848740
  have hstable : (prefixWord ++ tailWord_848740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848740).length < 2 ^ (prefixWord ++ tailWord_848740).sum := by decide
  have hdescent : baseEnd_848740 < baseStart_848740 := by decide
  rcases family_descends (prefixWord ++ tailWord_848740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848741 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_848741 : Nat := 118140960795 + 848741 * 2 ^ 59
def prefixEnd_848741 : Nat := 4983230072969 + 3 ^ 40 * 848741 * 2
def baseEnd_848741 : Nat := 387388519269128027230415

theorem tailTrace_848741 : CollatzResearch.WordTrace tailWord_848741 prefixEnd_848741 387388519269128027230415 := by
  unfold tailWord_848741
  simp only [CollatzResearch.WordTrace]
  refine ⟨30956127418163785267578077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20637418278775856845052051 30956127418163785267578077)
  ·
    refine ⟨11608547781811419475341779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30956127418163785267578077 11608547781811419475341779)
    ·
      refine ⟨17412821672717129213012669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11608547781811419475341779 17412821672717129213012669)
      ·
        refine ⟨6529808127268923454879751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17412821672717129213012669 6529808127268923454879751)
        ·
          refine ⟨9794712190903385182319627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529808127268923454879751 9794712190903385182319627)
          ·
            refine ⟨14692068286355077773479441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9794712190903385182319627 14692068286355077773479441)
            ·
              refine ⟨11019051214766308330109581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14692068286355077773479441 11019051214766308330109581)
              ·
                refine ⟨4132144205537365623791093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11019051214766308330109581 4132144205537365623791093)
                ·
                  refine ⟨387388519269128027230415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132144205537365623791093 387388519269128027230415)
                  ·
                    rfl

theorem cell20_848741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_848741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848741 prefixEnd_848741 := by exact prefixLift 848741
  have htrace : WordTrace (prefixWord ++ tailWord_848741) baseStart_848741 baseEnd_848741 := by
    simpa [prefixWord, tailWord_848741, baseEnd_848741] using wordTrace_append hprefix tailTrace_848741
  have hstable : (prefixWord ++ tailWord_848741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848741).length < 2 ^ (prefixWord ++ tailWord_848741).sum := by decide
  have hdescent : baseEnd_848741 < baseStart_848741 := by decide
  rcases family_descends (prefixWord ++ tailWord_848741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848858 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_848858 : Nat := 118140960795 + 848858 * 2 ^ 59
def prefixEnd_848858 : Nat := 4983230072969 + 3 ^ 40 * 848858 * 2
def baseEnd_848858 : Nat := 387441921257195620329937

theorem tailTrace_848858 : CollatzResearch.WordTrace tailWord_848858 prefixEnd_848858 387441921257195620329937 := by
  unfold tailWord_848858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740098689684978562396807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20640263172493276166391485 7740098689684978562396807)
  ·
    refine ⟨11610148034527467843595211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7740098689684978562396807 11610148034527467843595211)
    ·
      refine ⟨17415222051791201765392817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11610148034527467843595211 17415222051791201765392817)
      ·
        refine ⟨13061416538843401324044613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17415222051791201765392817 13061416538843401324044613)
        ·
          refine ⟨2449015601033137748258365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13061416538843401324044613 2449015601033137748258365)
          ·
            refine ⟨918380850387426655596887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2449015601033137748258365 918380850387426655596887)
            ·
              refine ⟨1377571275581139983395331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918380850387426655596887 1377571275581139983395331)
              ·
                refine ⟨2066356913371709975092997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377571275581139983395331 2066356913371709975092997)
                ·
                  refine ⟨387441921257195620329937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066356913371709975092997 387441921257195620329937)
                  ·
                    rfl

theorem cell20_848858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_848858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848858 prefixEnd_848858 := by exact prefixLift 848858
  have htrace : WordTrace (prefixWord ++ tailWord_848858) baseStart_848858 baseEnd_848858 := by
    simpa [prefixWord, tailWord_848858, baseEnd_848858] using wordTrace_append hprefix tailTrace_848858
  have hstable : (prefixWord ++ tailWord_848858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848858).length < 2 ^ (prefixWord ++ tailWord_848858).sum := by decide
  have hdescent : baseEnd_848858 < baseStart_848858 := by decide
  rcases family_descends (prefixWord ++ tailWord_848858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848907 : List Nat := [1, 1, 1, 1, 6, 10]
def baseStart_848907 : Nat := 118140960795 + 848907 * 2 ^ 59
def prefixEnd_848907 : Nat := 4983230072969 + 3 ^ 40 * 848907 * 2
def baseEnd_848907 : Nat := 14350529118235897322089

theorem tailTrace_848907 : CollatzResearch.WordTrace tailWord_848907 prefixEnd_848907 14350529118235897322089 := by
  unfold tailWord_848907
  simp only [CollatzResearch.WordTrace]
  refine ⟨30962181935562395618120975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20641454623708263745413983 30962181935562395618120975)
  ·
    refine ⟨46443272903343593427181463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30962181935562395618120975 46443272903343593427181463)
    ·
      refine ⟨69664909355015390140772195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46443272903343593427181463 69664909355015390140772195)
      ·
        refine ⟨104497364032523085211158293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69664909355015390140772195 104497364032523085211158293)
        ·
          refine ⟨4898313939024519619273045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104497364032523085211158293 4898313939024519619273045)
          ·
            refine ⟨14350529118235897322089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4898313939024519619273045 14350529118235897322089)
            ·
              rfl

theorem cell20_848907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 10].length) (baseStart_848907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848907 prefixEnd_848907 := by exact prefixLift 848907
  have htrace : WordTrace (prefixWord ++ tailWord_848907) baseStart_848907 baseEnd_848907 := by
    simpa [prefixWord, tailWord_848907, baseEnd_848907] using wordTrace_append hprefix tailTrace_848907
  have hstable : (prefixWord ++ tailWord_848907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848907).length < 2 ^ (prefixWord ++ tailWord_848907).sum := by decide
  have hdescent : baseEnd_848907 < baseStart_848907 := by decide
  rcases family_descends (prefixWord ++ tailWord_848907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848910 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_848910 : Nat := 118140960795 + 848910 * 2 ^ 59
def prefixEnd_848910 : Nat := 4983230072969 + 3 ^ 40 * 848910 * 2
def baseEnd_848910 : Nat := 387465655474114550596391

theorem tailTrace_848910 : CollatzResearch.WordTrace tailWord_848910 prefixEnd_848910 387465655474114550596391 := by
  unfold tailWord_848910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870286419318940891310023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20641527569701018086986789 3870286419318940891310023)
  ·
    refine ⟨5805429628978411336965035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3870286419318940891310023 5805429628978411336965035)
    ·
      refine ⟨8708144443467617005447553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805429628978411336965035 8708144443467617005447553)
      ·
        refine ⟨6531108332600712754085665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8708144443467617005447553 6531108332600712754085665)
        ·
          refine ⟨4898331249450534565564249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6531108332600712754085665 4898331249450534565564249)
          ·
            refine ⟨3673748437087900924173187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4898331249450534565564249 3673748437087900924173187)
            ·
              refine ⟨5510622655631851386259781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673748437087900924173187 5510622655631851386259781)
              ·
                refine ⟨1033241747930972134923709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5510622655631851386259781 1033241747930972134923709)
                ·
                  refine ⟨387465655474114550596391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033241747930972134923709 387465655474114550596391)
                  ·
                    rfl

theorem cell20_848910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_848910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848910 prefixEnd_848910 := by exact prefixLift 848910
  have htrace : WordTrace (prefixWord ++ tailWord_848910) baseStart_848910 baseEnd_848910 := by
    simpa [prefixWord, tailWord_848910, baseEnd_848910] using wordTrace_append hprefix tailTrace_848910
  have hstable : (prefixWord ++ tailWord_848910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848910).length < 2 ^ (prefixWord ++ tailWord_848910).sum := by decide
  have hdescent : baseEnd_848910 < baseStart_848910 := by decide
  rcases family_descends (prefixWord ++ tailWord_848910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848969 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_848969 : Nat := 118140960795 + 848969 * 2 ^ 59
def prefixEnd_848969 : Nat := 4983230072969 + 3 ^ 40 * 848969 * 2
def baseEnd_848969 : Nat := 387492584681772567629483

theorem tailTrace_848969 : CollatzResearch.WordTrace tailWord_848969 prefixEnd_848969 387492584681772567629483 := by
  unfold tailWord_848969
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964443261337780206877961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20642962174225186804585307 30964443261337780206877961)
  ·
    refine ⟨23223332446003335155158471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30964443261337780206877961 23223332446003335155158471)
    ·
      refine ⟨34834998669005002732737707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23223332446003335155158471 34834998669005002732737707)
      ·
        refine ⟨52252498003507504099106561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34834998669005002732737707 52252498003507504099106561)
        ·
          refine ⟨39189373502630628074329921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52252498003507504099106561 39189373502630628074329921)
          ·
            refine ⟨29392030126972971055747441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39189373502630628074329921 29392030126972971055747441)
            ·
              refine ⟨22044022595229728291810581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29392030126972971055747441 22044022595229728291810581)
              ·
                refine ⟨1033313559151393513678621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22044022595229728291810581 1033313559151393513678621)
                ·
                  refine ⟨387492584681772567629483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033313559151393513678621 387492584681772567629483)
                  ·
                    rfl

theorem cell20_848969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_848969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848969 prefixEnd_848969 := by exact prefixLift 848969
  have htrace : WordTrace (prefixWord ++ tailWord_848969) baseStart_848969 baseEnd_848969 := by
    simpa [prefixWord, tailWord_848969, baseEnd_848969] using wordTrace_append hprefix tailTrace_848969
  have hstable : (prefixWord ++ tailWord_848969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848969).length < 2 ^ (prefixWord ++ tailWord_848969).sum := by decide
  have hdescent : baseEnd_848969 < baseStart_848969 := by decide
  rcases family_descends (prefixWord ++ tailWord_848969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_848983 : List Nat := [1, 1, 3, 2, 2, 1, 1, 9]
def baseStart_848983 : Nat := 118140960795 + 848983 * 2 ^ 59
def prefixEnd_848983 : Nat := 4983230072969 + 3 ^ 40 * 848983 * 2
def baseEnd_848983 : Nat := 129166324887750247054253

theorem tailTrace_848983 : CollatzResearch.WordTrace tailWord_848983 prefixEnd_848983 129166324887750247054253 := by
  unfold tailWord_848983
  simp only [CollatzResearch.WordTrace]
  refine ⟨30964953883287060597887603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20643302588858040398591735 30964953883287060597887603)
  ·
    refine ⟨46447430824930590896831405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30964953883287060597887603 46447430824930590896831405)
    ·
      refine ⟨17417786559348971586311777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46447430824930590896831405 17417786559348971586311777)
      ·
        refine ⟨13063339919511728689733833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17417786559348971586311777 13063339919511728689733833)
        ·
          refine ⟨9797504939633796517300375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13063339919511728689733833 9797504939633796517300375)
          ·
            refine ⟨14696257409450694775950563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9797504939633796517300375 14696257409450694775950563)
            ·
              refine ⟨22044386114176042163925845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14696257409450694775950563 22044386114176042163925845)
              ·
                refine ⟨129166324887750247054253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22044386114176042163925845 129166324887750247054253)
                ·
                  rfl

theorem cell20_848983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_848983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_848983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_848983 prefixEnd_848983 := by exact prefixLift 848983
  have htrace : WordTrace (prefixWord ++ tailWord_848983) baseStart_848983 baseEnd_848983 := by
    simpa [prefixWord, tailWord_848983, baseEnd_848983] using wordTrace_append hprefix tailTrace_848983
  have hstable : (prefixWord ++ tailWord_848983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_848983).length < 2 ^ (prefixWord ++ tailWord_848983).sum := by decide
  have hdescent : baseEnd_848983 < baseStart_848983 := by decide
  rcases family_descends (prefixWord ++ tailWord_848983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849017 : List Nat := [1, 2, 1, 3, 6, 1, 6]
def baseStart_849017 : Nat := 118140960795 + 849017 * 2 ^ 59
def prefixEnd_849017 : Nat := 4983230072969 + 3 ^ 40 * 849017 * 2
def baseEnd_849017 : Nat := 43057165909966414892143

theorem tailTrace_849017 : CollatzResearch.WordTrace tailWord_849017 prefixEnd_849017 43057165909966414892143 := by
  unfold tailWord_849017
  simp only [CollatzResearch.WordTrace]
  refine ⟨30966193965163884404625305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20644129310109256269750203 30966193965163884404625305)
  ·
    refine ⟨23224645473872913303468979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30966193965163884404625305 23224645473872913303468979)
    ·
      refine ⟨34836968210809369955203469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23224645473872913303468979 34836968210809369955203469)
      ·
        refine ⟨13063863079053513733201301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34836968210809369955203469 13063863079053513733201301)
        ·
          refine ⟨612368581830633456243811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13063863079053513733201301 612368581830633456243811)
          ·
            refine ⟨918552872745950184365717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612368581830633456243811 918552872745950184365717)
            ·
              refine ⟨43057165909966414892143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 918552872745950184365717 43057165909966414892143)
              ·
                rfl

theorem cell20_849017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 6].length) (baseStart_849017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849017 prefixEnd_849017 := by exact prefixLift 849017
  have htrace : WordTrace (prefixWord ++ tailWord_849017) baseStart_849017 baseEnd_849017 := by
    simpa [prefixWord, tailWord_849017, baseEnd_849017] using wordTrace_append hprefix tailTrace_849017
  have hstable : (prefixWord ++ tailWord_849017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849017).length < 2 ^ (prefixWord ++ tailWord_849017).sum := by decide
  have hdescent : baseEnd_849017 < baseStart_849017 := by decide
  rcases family_descends (prefixWord ++ tailWord_849017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849038 : List Nat := [4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_849038 : Nat := 118140960795 + 849038 * 2 ^ 59
def prefixEnd_849038 : Nat := 4983230072969 + 3 ^ 40 * 849038 * 2
def baseEnd_849038 : Nat := 129174692720638331443067

theorem tailTrace_849038 : CollatzResearch.WordTrace tailWord_849038 prefixEnd_849038 129174692720638331443067 := by
  unfold tailWord_849038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870869987260975623892471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20644639932058536660759845 3870869987260975623892471)
  ·
    refine ⟨5806304980891463435838707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3870869987260975623892471 5806304980891463435838707)
    ·
      refine ⟨8709457471337195153758061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806304980891463435838707 8709457471337195153758061)
      ·
        refine ⟨3266046551751448182659273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8709457471337195153758061 3266046551751448182659273)
        ·
          refine ⟨2449534913813586136994455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3266046551751448182659273 2449534913813586136994455)
          ·
            refine ⟨3674302370720379205491683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449534913813586136994455 3674302370720379205491683)
            ·
              refine ⟨5511453556080568808237525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3674302370720379205491683 5511453556080568808237525)
              ·
                refine ⟨129174692720638331443067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5511453556080568808237525 129174692720638331443067)
                ·
                  rfl

theorem cell20_849038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_849038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849038 prefixEnd_849038 := by exact prefixLift 849038
  have htrace : WordTrace (prefixWord ++ tailWord_849038) baseStart_849038 baseEnd_849038 := by
    simpa [prefixWord, tailWord_849038, baseEnd_849038] using wordTrace_append hprefix tailTrace_849038
  have hstable : (prefixWord ++ tailWord_849038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849038).length < 2 ^ (prefixWord ++ tailWord_849038).sum := by decide
  have hdescent : baseEnd_849038 < baseStart_849038 := by decide
  rcases family_descends (prefixWord ++ tailWord_849038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849078 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_849078 : Nat := 118140960795 + 849078 * 2 ^ 59
def prefixEnd_849078 : Nat := 4983230072969 + 3 ^ 40 * 849078 * 2
def baseEnd_849078 : Nat := 387542335251852632995705

theorem tailTrace_849078 : CollatzResearch.WordTrace tailWord_849078 prefixEnd_849078 387542335251852632995705 := by
  unfold tailWord_849078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935526176121430738912243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20645612545295261215063925 1935526176121430738912243)
  ·
    refine ⟨2903289264182146108368365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935526176121430738912243 2903289264182146108368365)
    ·
      refine ⟨1088733474068304790638137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2903289264182146108368365 1088733474068304790638137)
      ·
        refine ⟨816550105551228592978603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088733474068304790638137 816550105551228592978603)
        ·
          refine ⟨1224825158326842889467905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816550105551228592978603 1224825158326842889467905)
          ·
            refine ⟨918618868745132167100929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224825158326842889467905 918618868745132167100929)
            ·
              refine ⟨688964151558849125325697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918618868745132167100929 688964151558849125325697)
              ·
                refine ⟨516723113669136843994273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688964151558849125325697 516723113669136843994273)
                ·
                  refine ⟨387542335251852632995705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516723113669136843994273 387542335251852632995705)
                  ·
                    rfl

theorem cell20_849078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_849078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849078 prefixEnd_849078 := by exact prefixLift 849078
  have htrace : WordTrace (prefixWord ++ tailWord_849078) baseStart_849078 baseEnd_849078 := by
    simpa [prefixWord, tailWord_849078, baseEnd_849078] using wordTrace_append hprefix tailTrace_849078
  have hstable : (prefixWord ++ tailWord_849078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849078).length < 2 ^ (prefixWord ++ tailWord_849078).sum := by decide
  have hdescent : baseEnd_849078 < baseStart_849078 := by decide
  rcases family_descends (prefixWord ++ tailWord_849078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849128 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_849128 : Nat := 118140960795 + 849128 * 2 ^ 59
def prefixEnd_849128 : Nat := 4983230072969 + 3 ^ 40 * 849128 * 2
def baseEnd_849128 : Nat := 387565156614274681328833

theorem tailTrace_849128 : CollatzResearch.WordTrace tailWord_849128 prefixEnd_849128 387565156614274681328833 := by
  unfold tailWord_849128
  simp only [CollatzResearch.WordTrace]
  refine ⟨15485121233880875180958019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20646828311841166907944025 15485121233880875180958019)
  ·
    refine ⟨23227681850821312771437029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15485121233880875180958019 23227681850821312771437029)
    ·
      refine ⟨4355190347028996144644443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23227681850821312771437029 4355190347028996144644443)
      ·
        refine ⟨6532785520543494216966665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4355190347028996144644443 6532785520543494216966665)
        ·
          refine ⟨4899589140407620662724999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6532785520543494216966665 4899589140407620662724999)
          ·
            refine ⟨7349383710611430994087499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4899589140407620662724999 7349383710611430994087499)
            ·
              refine ⟨11024075565917146491131249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7349383710611430994087499 11024075565917146491131249)
              ·
                refine ⟨8268056674437859868348437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11024075565917146491131249 8268056674437859868348437)
                ·
                  refine ⟨387565156614274681328833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8268056674437859868348437 387565156614274681328833)
                  ·
                    rfl

theorem cell20_849128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_849128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849128 prefixEnd_849128 := by exact prefixLift 849128
  have htrace : WordTrace (prefixWord ++ tailWord_849128) baseStart_849128 baseEnd_849128 := by
    simpa [prefixWord, tailWord_849128, baseEnd_849128] using wordTrace_append hprefix tailTrace_849128
  have hstable : (prefixWord ++ tailWord_849128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849128).length < 2 ^ (prefixWord ++ tailWord_849128).sum := by decide
  have hdescent : baseEnd_849128 < baseStart_849128 := by decide
  rcases family_descends (prefixWord ++ tailWord_849128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849138 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_849138 : Nat := 118140960795 + 849138 * 2 ^ 59
def prefixEnd_849138 : Nat := 4983230072969 + 3 ^ 40 * 849138 * 2
def baseEnd_849138 : Nat := 387569720886759090995459

theorem tailTrace_849138 : CollatzResearch.WordTrace tailWord_849138 prefixEnd_849138 387569720886759090995459 := by
  unfold tailWord_849138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742651799431380517445017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20647071465150348046520045 7742651799431380517445017)
  ·
    refine ⟨5806988849573535388083763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7742651799431380517445017 5806988849573535388083763)
    ·
      refine ⟨8710483274360303082125645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806988849573535388083763 8710483274360303082125645)
      ·
        refine ⟨3266431227885113655797117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8710483274360303082125645 3266431227885113655797117)
        ·
          refine ⟨1224911710456917620923919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3266431227885113655797117 1224911710456917620923919)
          ·
            refine ⟨1837367565685376431385879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224911710456917620923919 1837367565685376431385879)
            ·
              refine ⟨2756051348528064647078819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837367565685376431385879 2756051348528064647078819)
              ·
                refine ⟨4134077022792096970618229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756051348528064647078819 4134077022792096970618229)
                ·
                  refine ⟨387569720886759090995459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134077022792096970618229 387569720886759090995459)
                  ·
                    rfl

theorem cell20_849138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_849138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849138 prefixEnd_849138 := by exact prefixLift 849138
  have htrace : WordTrace (prefixWord ++ tailWord_849138) baseStart_849138 baseEnd_849138 := by
    simpa [prefixWord, tailWord_849138, baseEnd_849138] using wordTrace_append hprefix tailTrace_849138
  have hstable : (prefixWord ++ tailWord_849138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849138).length < 2 ^ (prefixWord ++ tailWord_849138).sum := by decide
  have hdescent : baseEnd_849138 < baseStart_849138 := by decide
  rcases family_descends (prefixWord ++ tailWord_849138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849145 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 2]
def baseStart_849145 : Nat := 118140960795 + 849145 * 2 ^ 59
def prefixEnd_849145 : Nat := 4983230072969 + 3 ^ 40 * 849145 * 2
def baseEnd_849145 : Nat := 387572915877498177762097

theorem tailTrace_849145 : CollatzResearch.WordTrace tailWord_849145 prefixEnd_849145 387572915877498177762097 := by
  unfold tailWord_849145
  simp only [CollatzResearch.WordTrace]
  refine ⟨30970862508700162265284889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20647241672466774843523259 30970862508700162265284889)
  ·
    refine ⟨23228146881525121698963667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30970862508700162265284889 23228146881525121698963667)
    ·
      refine ⟨34842220322287682548445501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23228146881525121698963667 34842220322287682548445501)
      ·
        refine ⟨13065832620857880955667063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34842220322287682548445501 13065832620857880955667063)
        ·
          refine ⟨19598748931286821433500595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13065832620857880955667063 19598748931286821433500595)
          ·
            refine ⟨29398123396930232150250893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19598748931286821433500595 29398123396930232150250893)
            ·
              refine ⟨11024296273848837056344085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29398123396930232150250893 11024296273848837056344085)
              ·
                refine ⟨516763887836664237016129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11024296273848837056344085 516763887836664237016129)
                ·
                  refine ⟨387572915877498177762097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516763887836664237016129 387572915877498177762097)
                  ·
                    rfl

theorem cell20_849145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_849145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849145 prefixEnd_849145 := by exact prefixLift 849145
  have htrace : WordTrace (prefixWord ++ tailWord_849145) baseStart_849145 baseEnd_849145 := by
    simpa [prefixWord, tailWord_849145, baseEnd_849145] using wordTrace_append hprefix tailTrace_849145
  have hstable : (prefixWord ++ tailWord_849145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849145).length < 2 ^ (prefixWord ++ tailWord_849145).sum := by decide
  have hdescent : baseEnd_849145 < baseStart_849145 := by decide
  rcases family_descends (prefixWord ++ tailWord_849145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849200 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_849200 : Nat := 118140960795 + 849200 * 2 ^ 59
def prefixEnd_849200 : Nat := 4983230072969 + 3 ^ 40 * 849200 * 2
def baseEnd_849200 : Nat := 387598019376162430928539

theorem tailTrace_849200 : CollatzResearch.WordTrace tailWord_849200 prefixEnd_849200 387598019376162430928539 := by
  unfold tailWord_849200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15486434261750453329268527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20648579015667271105691369 15486434261750453329268527)
  ·
    refine ⟨23229651392625679993902791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15486434261750453329268527 23229651392625679993902791)
    ·
      refine ⟨34844477088938519990854187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23229651392625679993902791 34844477088938519990854187)
      ·
        refine ⟨52266715633407779986281281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34844477088938519990854187 52266715633407779986281281)
        ·
          refine ⟨39200036725055834989710961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52266715633407779986281281 39200036725055834989710961)
          ·
            refine ⟨29400027543791876242283221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39200036725055834989710961 29400027543791876242283221)
            ·
              refine ⟨689063145557622099428513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29400027543791876242283221 689063145557622099428513)
              ·
                refine ⟨516797359168216574571385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689063145557622099428513 516797359168216574571385)
                ·
                  refine ⟨387598019376162430928539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516797359168216574571385 387598019376162430928539)
                  ·
                    rfl

theorem cell20_849200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_849200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849200 prefixEnd_849200 := by exact prefixLift 849200
  have htrace : WordTrace (prefixWord ++ tailWord_849200) baseStart_849200 baseEnd_849200 := by
    simpa [prefixWord, tailWord_849200, baseEnd_849200] using wordTrace_append hprefix tailTrace_849200
  have hstable : (prefixWord ++ tailWord_849200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849200).length < 2 ^ (prefixWord ++ tailWord_849200).sum := by decide
  have hdescent : baseEnd_849200 < baseStart_849200 := by decide
  rcases family_descends (prefixWord ++ tailWord_849200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849206 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_849206 : Nat := 118140960795 + 849206 * 2 ^ 59
def prefixEnd_849206 : Nat := 4983230072969 + 3 ^ 40 * 849206 * 2
def baseEnd_849206 : Nat := 387600757939653076728515

theorem tailTrace_849206 : CollatzResearch.WordTrace tailWord_849206 prefixEnd_849206 387600757939653076728515 := by
  unfold tailWord_849206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935817960092448105203467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20648724907652779788836981 1935817960092448105203467)
  ·
    refine ⟨2903726940138672157805201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935817960092448105203467 2903726940138672157805201)
    ·
      refine ⟨2177795205104004118353901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2903726940138672157805201 2177795205104004118353901)
      ·
        refine ⟨816673201914001544382713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2177795205104004118353901 816673201914001544382713)
        ·
          refine ⟨612504901435501158287035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816673201914001544382713 612504901435501158287035)
          ·
            refine ⟨918757352153251737430553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612504901435501158287035 918757352153251737430553)
            ·
              refine ⟨689068014114938803072915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918757352153251737430553 689068014114938803072915)
              ·
                refine ⟨1033602021172408204609373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689068014114938803072915 1033602021172408204609373)
                ·
                  refine ⟨387600757939653076728515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033602021172408204609373 387600757939653076728515)
                  ·
                    rfl

theorem cell20_849206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_849206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849206 prefixEnd_849206 := by exact prefixLift 849206
  have htrace : WordTrace (prefixWord ++ tailWord_849206) baseStart_849206 baseEnd_849206 := by
    simpa [prefixWord, tailWord_849206, baseEnd_849206] using wordTrace_append hprefix tailTrace_849206
  have hstable : (prefixWord ++ tailWord_849206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849206).length < 2 ^ (prefixWord ++ tailWord_849206).sum := by decide
  have hdescent : baseEnd_849206 < baseStart_849206 := by decide
  rcases family_descends (prefixWord ++ tailWord_849206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849214 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_849214 : Nat := 118140960795 + 849214 * 2 ^ 59
def prefixEnd_849214 : Nat := 4983230072969 + 3 ^ 40 * 849214 * 2
def baseEnd_849214 : Nat := 387604409357640604461815

theorem tailTrace_849214 : CollatzResearch.WordTrace tailWord_849214 prefixEnd_849214 387604409357640604461815 := by
  unfold tailWord_849214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871672393181273381193337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20648919430300124699697797 3871672393181273381193337)
  ·
    refine ⟨2903754294885955035895003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3871672393181273381193337 2903754294885955035895003)
    ·
      refine ⟨4355631442328932553842505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903754294885955035895003 4355631442328932553842505)
      ·
        refine ⟨3266723581746699415381879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4355631442328932553842505 3266723581746699415381879)
        ·
          refine ⟨4900085372620049123072819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266723581746699415381879 4900085372620049123072819)
          ·
            refine ⟨7350128058930073684609229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4900085372620049123072819 7350128058930073684609229)
            ·
              refine ⟨2756298022098777631728461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7350128058930073684609229 2756298022098777631728461)
              ·
                refine ⟨1033611758287041611898173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756298022098777631728461 1033611758287041611898173)
                ·
                  refine ⟨387604409357640604461815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033611758287041611898173 387604409357640604461815)
                  ·
                    rfl

theorem cell20_849214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_849214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849214 prefixEnd_849214 := by exact prefixLift 849214
  have htrace : WordTrace (prefixWord ++ tailWord_849214) baseStart_849214 baseEnd_849214 := by
    simpa [prefixWord, tailWord_849214, baseEnd_849214] using wordTrace_append hprefix tailTrace_849214
  have hstable : (prefixWord ++ tailWord_849214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849214).length < 2 ^ (prefixWord ++ tailWord_849214).sum := by decide
  have hdescent : baseEnd_849214 < baseStart_849214 := by decide
  rcases family_descends (prefixWord ++ tailWord_849214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849245 : List Nat := [1, 4, 5, 1, 9]
def baseStart_849245 : Nat := 118140960795 + 849245 * 2 ^ 59
def prefixEnd_849245 : Nat := 4983230072969 + 3 ^ 40 * 849245 * 2
def baseEnd_849245 : Nat := 4785414303732620671955

theorem tailTrace_849245 : CollatzResearch.WordTrace tailWord_849245 prefixEnd_849245 4785414303732620671955 := by
  unfold tailWord_849245
  simp only [CollatzResearch.WordTrace]
  refine ⟨30974509808337879343925189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20649673205558586229283459 30974509808337879343925189)
  ·
    refine ⟨5807720589063352376985973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30974509808337879343925189 5807720589063352376985973)
    ·
      refine ⟨544473805224689285342435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5807720589063352376985973 544473805224689285342435)
      ·
        refine ⟨816710707837033928013653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544473805224689285342435 816710707837033928013653)
        ·
          refine ⟨4785414303732620671955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 816710707837033928013653 4785414303732620671955)
          ·
            rfl

theorem cell20_849245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 9].length) (baseStart_849245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849245 prefixEnd_849245 := by exact prefixLift 849245
  have htrace : WordTrace (prefixWord ++ tailWord_849245) baseStart_849245 baseEnd_849245 := by
    simpa [prefixWord, tailWord_849245, baseEnd_849245] using wordTrace_append hprefix tailTrace_849245
  have hstable : (prefixWord ++ tailWord_849245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849245).length < 2 ^ (prefixWord ++ tailWord_849245).sum := by decide
  have hdescent : baseEnd_849245 < baseStart_849245 := by decide
  rcases family_descends (prefixWord ++ tailWord_849245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849252 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_849252 : Nat := 118140960795 + 849252 * 2 ^ 59
def prefixEnd_849252 : Nat := 4983230072969 + 3 ^ 40 * 849252 * 2
def baseEnd_849252 : Nat := 387621753593081361194993

theorem tailTrace_849252 : CollatzResearch.WordTrace tailWord_849252 prefixEnd_849252 387621753593081361194993 := by
  unfold tailWord_849252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487382559656259769715005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20649843412875013026286673 15487382559656259769715005)
  ·
    refine ⟨5807768459871097413643127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15487382559656259769715005 5807768459871097413643127)
    ·
      refine ⟨8711652689806646120464691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807768459871097413643127 8711652689806646120464691)
      ·
        refine ⟨13067479034709969180697037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8711652689806646120464691 13067479034709969180697037)
        ·
          refine ⟨4900304638016238442761389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13067479034709969180697037 4900304638016238442761389)
          ·
            refine ⟨1837614239256089416035521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4900304638016238442761389 1837614239256089416035521)
            ·
              refine ⟨1378210679442067062026641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1837614239256089416035521 1378210679442067062026641)
              ·
                refine ⟨1033658009581550296519981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378210679442067062026641 1033658009581550296519981)
                ·
                  refine ⟨387621753593081361194993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033658009581550296519981 387621753593081361194993)
                  ·
                    rfl

theorem cell20_849252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_849252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849252 prefixEnd_849252 := by exact prefixLift 849252
  have htrace : WordTrace (prefixWord ++ tailWord_849252) baseStart_849252 baseEnd_849252 := by
    simpa [prefixWord, tailWord_849252, baseEnd_849252] using wordTrace_append hprefix tailTrace_849252
  have hstable : (prefixWord ++ tailWord_849252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849252).length < 2 ^ (prefixWord ++ tailWord_849252).sum := by decide
  have hdescent : baseEnd_849252 < baseStart_849252 := by decide
  rcases family_descends (prefixWord ++ tailWord_849252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849262 : List Nat := [4, 1, 2, 4, 1, 2, 1, 5]
def baseStart_849262 : Nat := 118140960795 + 849262 * 2 ^ 59
def prefixEnd_849262 : Nat := 4983230072969 + 3 ^ 40 * 849262 * 2
def baseEnd_849262 : Nat := 129208772621855256953873

theorem tailTrace_849262 : CollatzResearch.WordTrace tailWord_849262 prefixEnd_849262 129208772621855256953873 := by
  unfold tailWord_849262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871891231159536405911755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20650086566184194164862693 3871891231159536405911755)
  ·
    refine ⟨5807836846739304608867633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871891231159536405911755 5807836846739304608867633)
    ·
      refine ⟨4355877635054478456650725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5807836846739304608867633 4355877635054478456650725)
      ·
        refine ⟨816727056572714710622011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4355877635054478456650725 816727056572714710622011)
        ·
          refine ⟨1225090584859072065933017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816727056572714710622011 1225090584859072065933017)
          ·
            refine ⟨918817938644304049449763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225090584859072065933017 918817938644304049449763)
            ·
              refine ⟨1378226907966456074174645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918817938644304049449763 1378226907966456074174645)
              ·
                refine ⟨129208772621855256953873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1378226907966456074174645 129208772621855256953873)
                ·
                  rfl

theorem cell20_849262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_849262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849262 prefixEnd_849262 := by exact prefixLift 849262
  have htrace : WordTrace (prefixWord ++ tailWord_849262) baseStart_849262 baseEnd_849262 := by
    simpa [prefixWord, tailWord_849262, baseEnd_849262] using wordTrace_append hprefix tailTrace_849262
  have hstable : (prefixWord ++ tailWord_849262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849262).length < 2 ^ (prefixWord ++ tailWord_849262).sum := by decide
  have hdescent : baseEnd_849262 < baseStart_849262 := by decide
  rcases family_descends (prefixWord ++ tailWord_849262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849273 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_849273 : Nat := 118140960795 + 849273 * 2 ^ 59
def prefixEnd_849273 : Nat := 4983230072969 + 3 ^ 40 * 849273 * 2
def baseEnd_849273 : Nat := 387631338565298621494907

theorem tailTrace_849273 : CollatzResearch.WordTrace tailWord_849273 prefixEnd_849273 387631338565298621494907 := by
  unfold tailWord_849273
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975531052236440125944473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20650354034824293417296315 30975531052236440125944473)
  ·
    refine ⟨23231648289177330094458355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30975531052236440125944473 23231648289177330094458355)
    ·
      refine ⟨34847472433765995141687533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23231648289177330094458355 34847472433765995141687533)
      ·
        refine ⟨13067802162662248178132825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34847472433765995141687533 13067802162662248178132825)
        ·
          refine ⟨9800851621996686133599619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13067802162662248178132825 9800851621996686133599619)
          ·
            refine ⟨14701277432995029200399429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9800851621996686133599619 14701277432995029200399429)
            ·
              refine ⟨2756489518686567975074893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14701277432995029200399429 2756489518686567975074893)
              ·
                refine ⟨1033683569507462990653085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756489518686567975074893 1033683569507462990653085)
                ·
                  refine ⟨387631338565298621494907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033683569507462990653085 387631338565298621494907)
                  ·
                    rfl

theorem cell20_849273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_849273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849273 prefixEnd_849273 := by exact prefixLift 849273
  have htrace : WordTrace (prefixWord ++ tailWord_849273) baseStart_849273 baseEnd_849273 := by
    simpa [prefixWord, tailWord_849273, baseEnd_849273] using wordTrace_append hprefix tailTrace_849273
  have hstable : (prefixWord ++ tailWord_849273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849273).length < 2 ^ (prefixWord ++ tailWord_849273).sum := by decide
  have hdescent : baseEnd_849273 < baseStart_849273 := by decide
  rcases family_descends (prefixWord ++ tailWord_849273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849304 : List Nat := [2, 1, 2, 5, 2, 1, 7]
def baseStart_849304 : Nat := 118140960795 + 849304 * 2 ^ 59
def prefixEnd_849304 : Nat := 4983230072969 + 3 ^ 40 * 849304 * 2
def baseEnd_849304 : Nat := 43071720867777810162383

theorem tailTrace_849304 : CollatzResearch.WordTrace tailWord_849304 prefixEnd_849304 43071720867777810162383 := by
  unfold tailWord_849304
  simp only [CollatzResearch.WordTrace]
  refine ⟨15488330857562066210161483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20651107810082754946881977 15488330857562066210161483)
  ·
    refine ⟨23232496286343099315242225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15488330857562066210161483 23232496286343099315242225)
    ·
      refine ⟨17424372214757324486431669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23232496286343099315242225 17424372214757324486431669)
      ·
        refine ⟨1633534895133499170602969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17424372214757324486431669 1633534895133499170602969)
        ·
          refine ⟨1225151171350124377952227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633534895133499170602969 1225151171350124377952227)
          ·
            refine ⟨1837726757025186566928341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225151171350124377952227 1837726757025186566928341)
            ·
              refine ⟨43071720867777810162383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1837726757025186566928341 43071720867777810162383)
              ·
                rfl

theorem cell20_849304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_849304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849304 prefixEnd_849304 := by exact prefixLift 849304
  have htrace : WordTrace (prefixWord ++ tailWord_849304) baseStart_849304 baseEnd_849304 := by
    simpa [prefixWord, tailWord_849304, baseEnd_849304] using wordTrace_append hprefix tailTrace_849304
  have hstable : (prefixWord ++ tailWord_849304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849304).length < 2 ^ (prefixWord ++ tailWord_849304).sum := by decide
  have hdescent : baseEnd_849304 < baseStart_849304 := by decide
  rcases family_descends (prefixWord ++ tailWord_849304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849311 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_849311 : Nat := 118140960795 + 849311 * 2 ^ 59
def prefixEnd_849311 : Nat := 4983230072969 + 3 ^ 40 * 849311 * 2
def baseEnd_849311 : Nat := 387648682800739378228085

theorem tailTrace_849311 : CollatzResearch.WordTrace tailWord_849311 prefixEnd_849311 387648682800739378228085 := by
  unfold tailWord_849311
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976917026098772615827787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20651278017399181743885191 30976917026098772615827787)
  ·
    refine ⟨46465375539148158923741681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30976917026098772615827787 46465375539148158923741681)
    ·
      refine ⟨34849031654361119192806261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46465375539148158923741681 34849031654361119192806261)
      ·
        refine ⟨3267096717596354924325587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34849031654361119192806261 3267096717596354924325587)
        ·
          refine ⟨4900645076394532386488381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267096717596354924325587 4900645076394532386488381)
          ·
            refine ⟨1837741903647949644933143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4900645076394532386488381 1837741903647949644933143)
            ·
              refine ⟨2756612855471924467399715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837741903647949644933143 2756612855471924467399715)
              ·
                refine ⟨4134919283207886701099573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756612855471924467399715 4134919283207886701099573)
                ·
                  refine ⟨387648682800739378228085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134919283207886701099573 387648682800739378228085)
                  ·
                    rfl

theorem cell20_849311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_849311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849311 prefixEnd_849311 := by exact prefixLift 849311
  have htrace : WordTrace (prefixWord ++ tailWord_849311) baseStart_849311 baseEnd_849311 := by
    simpa [prefixWord, tailWord_849311, baseEnd_849311] using wordTrace_append hprefix tailTrace_849311
  have hstable : (prefixWord ++ tailWord_849311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849311).length < 2 ^ (prefixWord ++ tailWord_849311).sum := by decide
  have hdescent : baseEnd_849311 < baseStart_849311 := by decide
  rcases family_descends (prefixWord ++ tailWord_849311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849314 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_849314 : Nat := 118140960795 + 849314 * 2 ^ 59
def prefixEnd_849314 : Nat := 4983230072969 + 3 ^ 40 * 849314 * 2
def baseEnd_849314 : Nat := 387650052082484701128073

theorem tailTrace_849314 : CollatzResearch.WordTrace tailWord_849314 prefixEnd_849314 387650052082484701128073 := by
  unfold tailWord_849314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7744256611271976032046749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20651350963391936085457997 7744256611271976032046749)
  ·
    refine ⟨2904096229226991012017531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7744256611271976032046749 2904096229226991012017531)
    ·
      refine ⟨4356144343840486518026297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904096229226991012017531 4356144343840486518026297)
      ·
        refine ⟨3267108257880364888519723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4356144343840486518026297 3267108257880364888519723)
        ·
          refine ⟨4900662386820547332779585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267108257880364888519723 4900662386820547332779585)
          ·
            refine ⟨3675496790115410499584689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900662386820547332779585 3675496790115410499584689)
            ·
              refine ⟨2756622592586557874688517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675496790115410499584689 2756622592586557874688517)
              ·
                refine ⟨516866736109979601504097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2756622592586557874688517 516866736109979601504097)
                ·
                  refine ⟨387650052082484701128073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516866736109979601504097 387650052082484701128073)
                  ·
                    rfl

theorem cell20_849314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_849314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849314 prefixEnd_849314 := by exact prefixLift 849314
  have htrace : WordTrace (prefixWord ++ tailWord_849314) baseStart_849314 baseEnd_849314 := by
    simpa [prefixWord, tailWord_849314, baseEnd_849314] using wordTrace_append hprefix tailTrace_849314
  have hstable : (prefixWord ++ tailWord_849314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849314).length < 2 ^ (prefixWord ++ tailWord_849314).sum := by decide
  have hdescent : baseEnd_849314 < baseStart_849314 := by decide
  rcases family_descends (prefixWord ++ tailWord_849314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849366 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_849366 : Nat := 118140960795 + 849366 * 2 ^ 59
def prefixEnd_849366 : Nat := 4983230072969 + 3 ^ 40 * 849366 * 2
def baseEnd_849366 : Nat := 387673786299403631394527

theorem tailTrace_849366 : CollatzResearch.WordTrace tailWord_849366 prefixEnd_849366 387673786299403631394527 := by
  unfold tailWord_849366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936182690056219813067497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20652615360599678006053301 1936182690056219813067497)
  ·
    refine ⟨1452137017542164859800623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1936182690056219813067497 1452137017542164859800623)
    ·
      refine ⟨2178205526313247289700935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1452137017542164859800623 2178205526313247289700935)
      ·
        refine ⟨3267308289469870934551403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178205526313247289700935 3267308289469870934551403)
        ·
          refine ⟨4900962434204806401827105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267308289469870934551403 4900962434204806401827105)
          ·
            refine ⟨3675721825653604801370329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900962434204806401827105 3675721825653604801370329)
            ·
              refine ⟨2756791369240203601027747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675721825653604801370329 2756791369240203601027747)
              ·
                refine ⟨4135187053860305401541621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756791369240203601027747 4135187053860305401541621)
                ·
                  refine ⟨387673786299403631394527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4135187053860305401541621 387673786299403631394527)
                  ·
                    rfl

theorem cell20_849366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_849366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849366 prefixEnd_849366 := by exact prefixLift 849366
  have htrace : WordTrace (prefixWord ++ tailWord_849366) baseStart_849366 baseEnd_849366 := by
    simpa [prefixWord, tailWord_849366, baseEnd_849366] using wordTrace_append hprefix tailTrace_849366
  have hstable : (prefixWord ++ tailWord_849366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849366).length < 2 ^ (prefixWord ++ tailWord_849366).sum := by decide
  have hdescent : baseEnd_849366 < baseStart_849366 := by decide
  rcases family_descends (prefixWord ++ tailWord_849366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849373 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_849373 : Nat := 118140960795 + 849373 * 2 ^ 59
def prefixEnd_849373 : Nat := 4983230072969 + 3 ^ 40 * 849373 * 2
def baseEnd_849373 : Nat := 387676981290142718161165

theorem tailTrace_849373 : CollatzResearch.WordTrace tailWord_849373 prefixEnd_849373 387676981290142718161165 := by
  unfold tailWord_849373
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979178351874157204584773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20652785567916104803056515 30979178351874157204584773)
  ·
    refine ⟨5808595940976404475859645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30979178351874157204584773 5808595940976404475859645)
    ·
      refine ⟨2178223477866151678447367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5808595940976404475859645 2178223477866151678447367)
      ·
        refine ⟨3267335216799227517671051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2178223477866151678447367 3267335216799227517671051)
        ·
          refine ⟨4901002825198841276506577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267335216799227517671051 4901002825198841276506577)
          ·
            refine ⟨3675752118899130957379933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901002825198841276506577 3675752118899130957379933)
            ·
              refine ⟨1378407044587174109017475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3675752118899130957379933 1378407044587174109017475)
              ·
                refine ⟨2067610566880761163526213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378407044587174109017475 2067610566880761163526213)
                ·
                  refine ⟨387676981290142718161165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067610566880761163526213 387676981290142718161165)
                  ·
                    rfl

theorem cell20_849373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_849373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849373 prefixEnd_849373 := by exact prefixLift 849373
  have htrace : WordTrace (prefixWord ++ tailWord_849373) baseStart_849373 baseEnd_849373 := by
    simpa [prefixWord, tailWord_849373, baseEnd_849373] using wordTrace_append hprefix tailTrace_849373
  have hstable : (prefixWord ++ tailWord_849373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849373).length < 2 ^ (prefixWord ++ tailWord_849373).sum := by decide
  have hdescent : baseEnd_849373 < baseStart_849373 := by decide
  rcases family_descends (prefixWord ++ tailWord_849373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849383 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 3]
def baseStart_849383 : Nat := 118140960795 + 849383 * 2 ^ 59
def prefixEnd_849383 : Nat := 4983230072969 + 3 ^ 40 * 849383 * 2
def baseEnd_849383 : Nat := 387681545562627127827791

theorem tailTrace_849383 : CollatzResearch.WordTrace tailWord_849383 prefixEnd_849383 387681545562627127827791 := by
  unfold tailWord_849383
  simp only [CollatzResearch.WordTrace]
  refine ⟨30979543081837928912448803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20653028721225285941632535 30979543081837928912448803)
  ·
    refine ⟨46469314622756893368673205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30979543081837928912448803 46469314622756893368673205)
    ·
      refine ⟨4356498245883458753313113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46469314622756893368673205 4356498245883458753313113)
      ·
        refine ⟨3267373684412594064984835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4356498245883458753313113 3267373684412594064984835)
        ·
          refine ⟨4901060526618891097477253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267373684412594064984835 4901060526618891097477253)
          ·
            refine ⟨918948848741042080776985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4901060526618891097477253 918948848741042080776985)
            ·
              refine ⟨689211636555781560582739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918948848741042080776985 689211636555781560582739)
              ·
                refine ⟨1033817454833672340874109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689211636555781560582739 1033817454833672340874109)
                ·
                  refine ⟨387681545562627127827791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033817454833672340874109 387681545562627127827791)
                  ·
                    rfl

theorem cell20_849383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_849383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849383 prefixEnd_849383 := by exact prefixLift 849383
  have htrace : WordTrace (prefixWord ++ tailWord_849383) baseStart_849383 baseEnd_849383 := by
    simpa [prefixWord, tailWord_849383, baseEnd_849383] using wordTrace_append hprefix tailTrace_849383
  have hstable : (prefixWord ++ tailWord_849383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849383).length < 2 ^ (prefixWord ++ tailWord_849383).sum := by decide
  have hdescent : baseEnd_849383 < baseStart_849383 := by decide
  rcases family_descends (prefixWord ++ tailWord_849383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849414 : List Nat := [6, 2, 1, 1, 2, 8]
def baseStart_849414 : Nat := 118140960795 + 849414 * 2 ^ 59
def prefixEnd_849414 : Nat := 4983230072969 + 3 ^ 40 * 849414 * 2
def baseEnd_849414 : Nat := 14359099807678844362753

theorem tailTrace_849414 : CollatzResearch.WordTrace tailWord_849414 prefixEnd_849414 14359099807678844362753 := by
  unfold tailWord_849414
  simp only [CollatzResearch.WordTrace]
  refine ⟨968146054522675662713353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20653782496483747471218197 968146054522675662713353)
  ·
    refine ⟨726109540892006747035015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 968146054522675662713353 726109540892006747035015)
    ·
      refine ⟨1089164311338010120552523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726109540892006747035015 1089164311338010120552523)
      ·
        refine ⟨1633746467007015180828785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089164311338010120552523 1633746467007015180828785)
        ·
          refine ⟨1225309850255261385621589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633746467007015180828785 1225309850255261385621589)
          ·
            refine ⟨14359099807678844362753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1225309850255261385621589 14359099807678844362753)
            ·
              rfl

theorem cell20_849414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 8].length) (baseStart_849414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849414 prefixEnd_849414 := by exact prefixLift 849414
  have htrace : WordTrace (prefixWord ++ tailWord_849414) baseStart_849414 baseEnd_849414 := by
    simpa [prefixWord, tailWord_849414, baseEnd_849414] using wordTrace_append hprefix tailTrace_849414
  have hstable : (prefixWord ++ tailWord_849414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849414).length < 2 ^ (prefixWord ++ tailWord_849414).sum := by decide
  have hdescent : baseEnd_849414 < baseStart_849414 := by decide
  rcases family_descends (prefixWord ++ tailWord_849414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849425 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_849425 : Nat := 118140960795 + 849425 * 2 ^ 59
def prefixEnd_849425 : Nat := 4983230072969 + 3 ^ 40 * 849425 * 2
def baseEnd_849425 : Nat := 387700715507061648427619

theorem tailTrace_849425 : CollatzResearch.WordTrace tailWord_849425 prefixEnd_849425 387700715507061648427619 := by
  unfold tailWord_849425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30981074947685770085477729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20654049965123846723651819 30981074947685770085477729)
  ·
    refine ⟨23235806210764327564108297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30981074947685770085477729 23235806210764327564108297)
    ·
      refine ⟨17426854658073245673081223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23235806210764327564108297 17426854658073245673081223)
      ·
        refine ⟨26140281987109868509621835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17426854658073245673081223 26140281987109868509621835)
        ·
          refine ⟨39210422980664802764432753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26140281987109868509621835 39210422980664802764432753)
          ·
            refine ⟨29407817235498602073324565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39210422980664802764432753 29407817235498602073324565)
            ·
              refine ⟨1378491432913996972187089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29407817235498602073324565 1378491432913996972187089)
              ·
                refine ⟨1033868574685497729140317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378491432913996972187089 1033868574685497729140317)
                ·
                  refine ⟨387700715507061648427619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033868574685497729140317 387700715507061648427619)
                  ·
                    rfl

theorem cell20_849425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_849425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849425 prefixEnd_849425 := by exact prefixLift 849425
  have htrace : WordTrace (prefixWord ++ tailWord_849425) baseStart_849425 baseEnd_849425 := by
    simpa [prefixWord, tailWord_849425, baseEnd_849425] using wordTrace_append hprefix tailTrace_849425
  have hstable : (prefixWord ++ tailWord_849425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849425).length < 2 ^ (prefixWord ++ tailWord_849425).sum := by decide
  have hdescent : baseEnd_849425 < baseStart_849425 := by decide
  rcases family_descends (prefixWord ++ tailWord_849425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849439 : List Nat := [1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_849439 : Nat := 118140960795 + 849439 * 2 ^ 59
def prefixEnd_849439 : Nat := 4983230072969 + 3 ^ 40 * 849439 * 2
def baseEnd_849439 : Nat := 129235701829513273986965

theorem tailTrace_849439 : CollatzResearch.WordTrace tailWord_849439 prefixEnd_849439 129235701829513273986965 := by
  unfold tailWord_849439
  simp only [CollatzResearch.WordTrace]
  refine ⟨30981585569635050476487371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20654390379756700317658247 30981585569635050476487371)
  ·
    refine ⟨46472378354452575714731057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30981585569635050476487371 46472378354452575714731057)
    ·
      refine ⟨34854283765839431786048293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46472378354452575714731057 34854283765839431786048293)
      ·
        refine ⟨6535178206094893459884055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34854283765839431786048293 6535178206094893459884055)
        ·
          refine ⟨9802767309142340189826083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535178206094893459884055 9802767309142340189826083)
          ·
            refine ⟨14704150963713510284739125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9802767309142340189826083 14704150963713510284739125)
            ·
              refine ⟨1378514152848141589194293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14704150963713510284739125 1378514152848141589194293)
              ·
                refine ⟨129235701829513273986965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1378514152848141589194293 129235701829513273986965)
                ·
                  rfl

theorem cell20_849439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_849439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849439 prefixEnd_849439 := by exact prefixLift 849439
  have htrace : WordTrace (prefixWord ++ tailWord_849439) baseStart_849439 baseEnd_849439 := by
    simpa [prefixWord, tailWord_849439, baseEnd_849439] using wordTrace_append hprefix tailTrace_849439
  have hstable : (prefixWord ++ tailWord_849439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849439).length < 2 ^ (prefixWord ++ tailWord_849439).sum := by decide
  have hdescent : baseEnd_849439 < baseStart_849439 := by decide
  rcases family_descends (prefixWord ++ tailWord_849439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849508 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_849508 : Nat := 118140960795 + 849508 * 2 ^ 59
def prefixEnd_849508 : Nat := 4983230072969 + 3 ^ 40 * 849508 * 2
def baseEnd_849508 : Nat := 387738598968682248660613

theorem tailTrace_849508 : CollatzResearch.WordTrace tailWord_849508 prefixEnd_849508 387738598968682248660613 := by
  unfold tailWord_849508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15492051103192537630374589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20656068137590050173832785 15492051103192537630374589)
  ·
    refine ⟨5809519163697201611390471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15492051103192537630374589 5809519163697201611390471)
    ·
      refine ⟨8714278745545802417085707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5809519163697201611390471 8714278745545802417085707)
      ·
        refine ⟨13071418118318703625628561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714278745545802417085707 13071418118318703625628561)
        ·
          refine ⟨9803563588739027719221421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13071418118318703625628561 9803563588739027719221421)
          ·
            refine ⟨3676336345777135394708033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9803563588739027719221421 3676336345777135394708033)
            ·
              refine ⟨2757252259332851546031025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3676336345777135394708033 2757252259332851546031025)
              ·
                refine ⟨2067939194499638659523269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2757252259332851546031025 2067939194499638659523269)
                ·
                  refine ⟨387738598968682248660613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067939194499638659523269 387738598968682248660613)
                  ·
                    rfl

theorem cell20_849508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_849508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849508 prefixEnd_849508 := by exact prefixLift 849508
  have htrace : WordTrace (prefixWord ++ tailWord_849508) baseStart_849508 baseEnd_849508 := by
    simpa [prefixWord, tailWord_849508, baseEnd_849508] using wordTrace_append hprefix tailTrace_849508
  have hstable : (prefixWord ++ tailWord_849508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849508).length < 2 ^ (prefixWord ++ tailWord_849508).sum := by decide
  have hdescent : baseEnd_849508 < baseStart_849508 := by decide
  rcases family_descends (prefixWord ++ tailWord_849508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849636 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_849636 : Nat := 118140960795 + 849636 * 2 ^ 59
def prefixEnd_849636 : Nat := 4983230072969 + 3 ^ 40 * 849636 * 2
def baseEnd_849636 : Nat := 387797021656482692393423

theorem tailTrace_849636 : CollatzResearch.WordTrace tailWord_849636 prefixEnd_849636 387797021656482692393423 := by
  unfold tailWord_849636
  simp only [CollatzResearch.WordTrace]
  refine ⟨15494385374960676560704381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20659180499947568747605841 15494385374960676560704381)
  ·
    refine ⟨5810394515610253710264143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15494385374960676560704381 5810394515610253710264143)
    ·
      refine ⟨8715591773415380565396215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810394515610253710264143 8715591773415380565396215)
      ·
        refine ⟨13073387660123070848094323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715591773415380565396215 13073387660123070848094323)
        ·
          refine ⟨19610081490184606272141485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13073387660123070848094323 19610081490184606272141485)
          ·
            refine ⟨7353780558819227352053057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19610081490184606272141485 7353780558819227352053057)
            ·
              refine ⟨5515335419114420514039793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353780558819227352053057 5515335419114420514039793)
              ·
                refine ⟨4136501564335815385529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5515335419114420514039793 4136501564335815385529845)
                ·
                  refine ⟨387797021656482692393423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4136501564335815385529845 387797021656482692393423)
                  ·
                    rfl

theorem cell20_849636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_849636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849636 prefixEnd_849636 := by exact prefixLift 849636
  have htrace : WordTrace (prefixWord ++ tailWord_849636) baseStart_849636 baseEnd_849636 := by
    simpa [prefixWord, tailWord_849636, baseEnd_849636] using wordTrace_append hprefix tailTrace_849636
  have hstable : (prefixWord ++ tailWord_849636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849636).length < 2 ^ (prefixWord ++ tailWord_849636).sum := by decide
  have hdescent : baseEnd_849636 < baseStart_849636 := by decide
  rcases family_descends (prefixWord ++ tailWord_849636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849660 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_849660 : Nat := 118140960795 + 849660 * 2 ^ 59
def prefixEnd_849660 : Nat := 4983230072969 + 3 ^ 40 * 849660 * 2
def baseEnd_849660 : Nat := 387807975910445275593325

theorem tailTrace_849660 : CollatzResearch.WordTrace tailWord_849660 prefixEnd_849660 387807975910445275593325 := by
  unfold tailWord_849660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15494823050917202610141217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20659764067889603480188289 15494823050917202610141217)
  ·
    refine ⟨11621117288187901957605913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15494823050917202610141217 11621117288187901957605913)
    ·
      refine ⟨8715837966140926468204435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11621117288187901957605913 8715837966140926468204435)
      ·
        refine ⟨13073756949211389702306653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715837966140926468204435 13073756949211389702306653)
        ·
          refine ⟨4902658855954271138364995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13073756949211389702306653 4902658855954271138364995)
          ·
            refine ⟨7353988283931406707547493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4902658855954271138364995 7353988283931406707547493)
            ·
              refine ⟨1378872803237138757665155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7353988283931406707547493 1378872803237138757665155)
              ·
                refine ⟨2068309204855708136497733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378872803237138757665155 2068309204855708136497733)
                ·
                  refine ⟨387807975910445275593325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068309204855708136497733 387807975910445275593325)
                  ·
                    rfl

theorem cell20_849660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_849660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849660 prefixEnd_849660 := by exact prefixLift 849660
  have htrace : WordTrace (prefixWord ++ tailWord_849660) baseStart_849660 baseEnd_849660 := by
    simpa [prefixWord, tailWord_849660, baseEnd_849660] using wordTrace_append hprefix tailTrace_849660
  have hstable : (prefixWord ++ tailWord_849660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849660).length < 2 ^ (prefixWord ++ tailWord_849660).sum := by decide
  have hdescent : baseEnd_849660 < baseStart_849660 := by decide
  rcases family_descends (prefixWord ++ tailWord_849660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849715 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_849715 : Nat := 118140960795 + 849715 * 2 ^ 59
def prefixEnd_849715 : Nat := 4983230072969 + 3 ^ 40 * 849715 * 2
def baseEnd_849715 : Nat := 387833079409109528759767

theorem tailTrace_849715 : CollatzResearch.WordTrace tailWord_849715 prefixEnd_849715 387833079409109528759767 := by
  unfold tailWord_849715
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991652116635149613534599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20661101411090099742356399 30991652116635149613534599)
  ·
    refine ⟨46487478174952724420301899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30991652116635149613534599 46487478174952724420301899)
    ·
      refine ⟨69731217262429086630452849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46487478174952724420301899 69731217262429086630452849)
      ·
        refine ⟨52298412946821814972839637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69731217262429086630452849 52298412946821814972839637)
        ·
          refine ⟨1225744053441136288425929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52298412946821814972839637 1225744053441136288425929)
          ·
            refine ⟨919308040080852216319447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225744053441136288425929 919308040080852216319447)
            ·
              refine ⟨1378962060121278324479171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919308040080852216319447 1378962060121278324479171)
              ·
                refine ⟨2068443090181917486718757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378962060121278324479171 2068443090181917486718757)
                ·
                  refine ⟨387833079409109528759767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068443090181917486718757 387833079409109528759767)
                  ·
                    rfl

theorem cell20_849715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_849715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849715 prefixEnd_849715 := by exact prefixLift 849715
  have htrace : WordTrace (prefixWord ++ tailWord_849715) baseStart_849715 baseEnd_849715 := by
    simpa [prefixWord, tailWord_849715, baseEnd_849715] using wordTrace_append hprefix tailTrace_849715
  have hstable : (prefixWord ++ tailWord_849715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849715).length < 2 ^ (prefixWord ++ tailWord_849715).sum := by decide
  have hdescent : baseEnd_849715 < baseStart_849715 := by decide
  rcases family_descends (prefixWord ++ tailWord_849715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849719 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_849719 : Nat := 118140960795 + 849719 * 2 ^ 59
def prefixEnd_849719 : Nat := 4983230072969 + 3 ^ 40 * 849719 * 2
def baseEnd_849719 : Nat := 387834905118103292626417

theorem tailTrace_849719 : CollatzResearch.WordTrace tailWord_849719 prefixEnd_849719 387834905118103292626417 := by
  unfold tailWord_849719
  simp only [CollatzResearch.WordTrace]
  refine ⟨30991798008620658296680211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20661198672413772197786807 30991798008620658296680211)
  ·
    refine ⟨46487697012930987445020317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30991798008620658296680211 46487697012930987445020317)
    ·
      refine ⟨17432886379849120291882619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46487697012930987445020317 17432886379849120291882619)
      ·
        refine ⟨26149329569773680437823929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17432886379849120291882619 26149329569773680437823929)
        ·
          refine ⟨19611997177330260328367947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26149329569773680437823929 19611997177330260328367947)
          ·
            refine ⟨29417995765995390492551921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611997177330260328367947 29417995765995390492551921)
            ·
              refine ⟨22063496824496542869413941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29417995765995390492551921 22063496824496542869413941)
              ·
                refine ⟨2068452827296550894007557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22063496824496542869413941 2068452827296550894007557)
                ·
                  refine ⟨387834905118103292626417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068452827296550894007557 387834905118103292626417)
                  ·
                    rfl

theorem cell20_849719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_849719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849719 prefixEnd_849719 := by exact prefixLift 849719
  have htrace : WordTrace (prefixWord ++ tailWord_849719) baseStart_849719 baseEnd_849719 := by
    simpa [prefixWord, tailWord_849719, baseEnd_849719] using wordTrace_append hprefix tailTrace_849719
  have hstable : (prefixWord ++ tailWord_849719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849719).length < 2 ^ (prefixWord ++ tailWord_849719).sum := by decide
  have hdescent : baseEnd_849719 < baseStart_849719 := by decide
  rcases family_descends (prefixWord ++ tailWord_849719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849725 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 3]
def baseStart_849725 : Nat := 118140960795 + 849725 * 2 ^ 59
def prefixEnd_849725 : Nat := 4983230072969 + 3 ^ 40 * 849725 * 2
def baseEnd_849725 : Nat := 387837643681593938426393

theorem tailTrace_849725 : CollatzResearch.WordTrace tailWord_849725 prefixEnd_849725 387837643681593938426393 := by
  unfold tailWord_849725
  simp only [CollatzResearch.WordTrace]
  refine ⟨30992016846598921321398629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20661344564399280880932419 30992016846598921321398629)
  ·
    refine ⟨5811003158737297747762243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30992016846598921321398629 5811003158737297747762243)
    ·
      refine ⟨8716504738105946621643365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811003158737297747762243 8716504738105946621643365)
      ·
        refine ⟨1634344638394864991558131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8716504738105946621643365 1634344638394864991558131)
        ·
          refine ⟨2451516957592297487337197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634344638394864991558131 2451516957592297487337197)
          ·
            refine ⟨919318859097111557751449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2451516957592297487337197 919318859097111557751449)
            ·
              refine ⟨689489144322833668313587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919318859097111557751449 689489144322833668313587)
              ·
                refine ⟨1034233716484250502470381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689489144322833668313587 1034233716484250502470381)
                ·
                  refine ⟨387837643681593938426393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034233716484250502470381 387837643681593938426393)
                  ·
                    rfl

theorem cell20_849725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_849725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849725 prefixEnd_849725 := by exact prefixLift 849725
  have htrace : WordTrace (prefixWord ++ tailWord_849725) baseStart_849725 baseEnd_849725 := by
    simpa [prefixWord, tailWord_849725, baseEnd_849725] using wordTrace_append hprefix tailTrace_849725
  have hstable : (prefixWord ++ tailWord_849725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849725).length < 2 ^ (prefixWord ++ tailWord_849725).sum := by decide
  have hdescent : baseEnd_849725 < baseStart_849725 := by decide
  rcases family_descends (prefixWord ++ tailWord_849725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849764 : List Nat := [2, 3, 1, 1, 13]
def baseStart_849764 : Nat := 118140960795 + 849764 * 2 ^ 59
def prefixEnd_849764 : Nat := 4983230072969 + 3 ^ 40 * 849764 * 2
def baseEnd_849764 : Nat := 4788338819065223902793

theorem tailTrace_849764 : CollatzResearch.WordTrace tailWord_849764 prefixEnd_849764 4788338819065223902793 := by
  unfold tailWord_849764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496719646728815491034173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20662292862305087321378897 15496719646728815491034173)
  ·
    refine ⟨5811269867523305809137815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15496719646728815491034173 5811269867523305809137815)
    ·
      refine ⟨8716904801284958713706723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811269867523305809137815 8716904801284958713706723)
      ·
        refine ⟨13075357201927438070560085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8716904801284958713706723 13075357201927438070560085)
        ·
          refine ⟨4788338819065223902793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13075357201927438070560085 4788338819065223902793)
          ·
            rfl

theorem cell20_849764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 13].length) (baseStart_849764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849764 prefixEnd_849764 := by exact prefixLift 849764
  have htrace : WordTrace (prefixWord ++ tailWord_849764) baseStart_849764 baseEnd_849764 := by
    simpa [prefixWord, tailWord_849764, baseEnd_849764] using wordTrace_append hprefix tailTrace_849764
  have hstable : (prefixWord ++ tailWord_849764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849764).length < 2 ^ (prefixWord ++ tailWord_849764).sum := by decide
  have hdescent : baseEnd_849764 < baseStart_849764 := by decide
  rcases family_descends (prefixWord ++ tailWord_849764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849767 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_849767 : Nat := 118140960795 + 849767 * 2 ^ 59
def prefixEnd_849767 : Nat := 4983230072969 + 3 ^ 40 * 849767 * 2
def baseEnd_849767 : Nat := 387856813626028459026221

theorem tailTrace_849767 : CollatzResearch.WordTrace tailWord_849767 prefixEnd_849767 387856813626028459026221 := by
  unfold tailWord_849767
  simp only [CollatzResearch.WordTrace]
  refine ⟨30993548712446762494427555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20662365808297841662951703 30993548712446762494427555)
  ·
    refine ⟨46490323068670143741641333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30993548712446762494427555 46490323068670143741641333)
    ·
      refine ⟨4358467787687825975778875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46490323068670143741641333 4358467787687825975778875)
      ·
        refine ⟨6537701681531738963668313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358467787687825975778875 6537701681531738963668313)
        ·
          refine ⟨4903276261148804222751235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6537701681531738963668313 4903276261148804222751235)
          ·
            refine ⟨7354914391723206334126853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903276261148804222751235 7354914391723206334126853)
            ·
              refine ⟨1379046448448101187648785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7354914391723206334126853 1379046448448101187648785)
              ·
                refine ⟨1034284836336075890736589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379046448448101187648785 1034284836336075890736589)
                ·
                  refine ⟨387856813626028459026221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034284836336075890736589 387856813626028459026221)
                  ·
                    rfl

theorem cell20_849767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_849767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849767 prefixEnd_849767 := by exact prefixLift 849767
  have htrace : WordTrace (prefixWord ++ tailWord_849767) baseStart_849767 baseEnd_849767 := by
    simpa [prefixWord, tailWord_849767, baseEnd_849767] using wordTrace_append hprefix tailTrace_849767
  have hstable : (prefixWord ++ tailWord_849767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849767).length < 2 ^ (prefixWord ++ tailWord_849767).sum := by decide
  have hdescent : baseEnd_849767 < baseStart_849767 := by decide
  rcases family_descends (prefixWord ++ tailWord_849767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849795 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_849795 : Nat := 118140960795 + 849795 * 2 ^ 59
def prefixEnd_849795 : Nat := 4983230072969 + 3 ^ 40 * 849795 * 2
def baseEnd_849795 : Nat := 387869593588984806092773

theorem tailTrace_849795 : CollatzResearch.WordTrace tailWord_849795 prefixEnd_849795 387869593588984806092773 := by
  unfold tailWord_849795
  simp only [CollatzResearch.WordTrace]
  refine ⟨30994569956345323276446839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20663046637563548850964559 30994569956345323276446839)
  ·
    refine ⟨46491854934517984914670259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30994569956345323276446839 46491854934517984914670259)
    ·
      refine ⟨69737782401776977372005389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46491854934517984914670259 69737782401776977372005389)
      ·
        refine ⟨26151668400666366514502021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69737782401776977372005389 26151668400666366514502021)
        ·
          refine ⟨4903437825124943721469129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26151668400666366514502021 4903437825124943721469129)
          ·
            refine ⟨3677578368843707791101847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4903437825124943721469129 3677578368843707791101847)
            ·
              refine ⟨5516367553265561686652771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677578368843707791101847 5516367553265561686652771)
              ·
                refine ⟨8274551329898342529979157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516367553265561686652771 8274551329898342529979157)
                ·
                  refine ⟨387869593588984806092773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8274551329898342529979157 387869593588984806092773)
                  ·
                    rfl

theorem cell20_849795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_849795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849795 prefixEnd_849795 := by exact prefixLift 849795
  have htrace : WordTrace (prefixWord ++ tailWord_849795) baseStart_849795 baseEnd_849795 := by
    simpa [prefixWord, tailWord_849795, baseEnd_849795] using wordTrace_append hprefix tailTrace_849795
  have hstable : (prefixWord ++ tailWord_849795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849795).length < 2 ^ (prefixWord ++ tailWord_849795).sum := by decide
  have hdescent : baseEnd_849795 < baseStart_849795 := by decide
  rcases family_descends (prefixWord ++ tailWord_849795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849843 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 3]
def baseStart_849843 : Nat := 118140960795 + 849843 * 2 ^ 59
def prefixEnd_849843 : Nat := 4983230072969 + 3 ^ 40 * 849843 * 2
def baseEnd_849843 : Nat := 387891502096909972492577

theorem tailTrace_849843 : CollatzResearch.WordTrace tailWord_849843 prefixEnd_849843 387891502096909972492577 := by
  unfold tailWord_849843
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996320660171427474194183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20664213773447618316129455 30996320660171427474194183)
  ·
    refine ⟨46494480990257141211291275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30996320660171427474194183 46494480990257141211291275)
    ·
      refine ⟨69741721485385711816936913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46494480990257141211291275 69741721485385711816936913)
      ·
        refine ⟨52306291114039283862702685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69741721485385711816936913 52306291114039283862702685)
        ·
          refine ⟨19614859167764731448513507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52306291114039283862702685 19614859167764731448513507)
          ·
            refine ⟨29422288751647097172770261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19614859167764731448513507 29422288751647097172770261)
            ·
              refine ⟨689584892616728839986803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29422288751647097172770261 689584892616728839986803)
              ·
                refine ⟨1034377338925093259980205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689584892616728839986803 1034377338925093259980205)
                ·
                  refine ⟨387891502096909972492577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034377338925093259980205 387891502096909972492577)
                  ·
                    rfl

theorem cell20_849843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_849843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849843 prefixEnd_849843 := by exact prefixLift 849843
  have htrace : WordTrace (prefixWord ++ tailWord_849843) baseStart_849843 baseEnd_849843 := by
    simpa [prefixWord, tailWord_849843, baseEnd_849843] using wordTrace_append hprefix tailTrace_849843
  have hstable : (prefixWord ++ tailWord_849843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849843).length < 2 ^ (prefixWord ++ tailWord_849843).sum := by decide
  have hdescent : baseEnd_849843 < baseStart_849843 := by decide
  rcases family_descends (prefixWord ++ tailWord_849843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849864 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_849864 : Nat := 118140960795 + 849864 * 2 ^ 59
def prefixEnd_849864 : Nat := 4983230072969 + 3 ^ 40 * 849864 * 2
def baseEnd_849864 : Nat := 387901087069127232792491

theorem tailTrace_849864 : CollatzResearch.WordTrace tailWord_849864 prefixEnd_849864 387901087069127232792491 := by
  unfold tailWord_849864
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498543296547674030354323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20664724395396898707139097 15498543296547674030354323)
  ·
    refine ⟨23247814944821511045531485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15498543296547674030354323 23247814944821511045531485)
    ·
      refine ⟨8717930604308066642074307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23247814944821511045531485 8717930604308066642074307)
      ·
        refine ⟨13076895906462099963111461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717930604308066642074307 13076895906462099963111461)
        ·
          refine ⟨2451917982461643743083399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13076895906462099963111461 2451917982461643743083399)
          ·
            refine ⟨3677876973692465614625099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451917982461643743083399 3677876973692465614625099)
            ·
              refine ⟨5516815460538698421937649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677876973692465614625099 5516815460538698421937649)
              ·
                refine ⟨4137611595404023816453237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516815460538698421937649 4137611595404023816453237)
                ·
                  refine ⟨387901087069127232792491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137611595404023816453237 387901087069127232792491)
                  ·
                    rfl

theorem cell20_849864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_849864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849864 prefixEnd_849864 := by exact prefixLift 849864
  have htrace : WordTrace (prefixWord ++ tailWord_849864) baseStart_849864 baseEnd_849864 := by
    simpa [prefixWord, tailWord_849864, baseEnd_849864] using wordTrace_append hprefix tailTrace_849864
  have hstable : (prefixWord ++ tailWord_849864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849864).length < 2 ^ (prefixWord ++ tailWord_849864).sum := by decide
  have hdescent : baseEnd_849864 < baseStart_849864 := by decide
  rcases family_descends (prefixWord ++ tailWord_849864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849874 : List Nat := [3, 2, 2, 3, 2, 2, 6]
def baseStart_849874 : Nat := 118140960795 + 849874 * 2 ^ 59
def prefixEnd_849874 : Nat := 4983230072969 + 3 ^ 40 * 849874 * 2
def baseEnd_849874 : Nat := 43100627926845738051013

theorem tailTrace_849874 : CollatzResearch.WordTrace tailWord_849874 prefixEnd_849874 43100627926845738051013 := by
  unfold tailWord_849874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749362830764779942143169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20664967548706079845715117 7749362830764779942143169)
  ·
    refine ⟨5812022123073584956607377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7749362830764779942143169 5812022123073584956607377)
    ·
      refine ⟨4359016592305188717455533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5812022123073584956607377 4359016592305188717455533)
      ·
        refine ⟨1634631222114445769045825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4359016592305188717455533 1634631222114445769045825)
        ·
          refine ⟨1225973416585834326784369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1634631222114445769045825 1225973416585834326784369)
          ·
            refine ⟨919480062439375745088277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225973416585834326784369 919480062439375745088277)
            ·
              refine ⟨43100627926845738051013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 919480062439375745088277 43100627926845738051013)
              ·
                rfl

theorem cell20_849874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 6].length) (baseStart_849874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849874 prefixEnd_849874 := by exact prefixLift 849874
  have htrace : WordTrace (prefixWord ++ tailWord_849874) baseStart_849874 baseEnd_849874 := by
    simpa [prefixWord, tailWord_849874, baseEnd_849874] using wordTrace_append hprefix tailTrace_849874
  have hstable : (prefixWord ++ tailWord_849874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849874).length < 2 ^ (prefixWord ++ tailWord_849874).sum := by decide
  have hdescent : baseEnd_849874 < baseStart_849874 := by decide
  rcases family_descends (prefixWord ++ tailWord_849874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849888 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 2]
def baseStart_849888 : Nat := 118140960795 + 849888 * 2 ^ 59
def prefixEnd_849888 : Nat := 4983230072969 + 3 ^ 40 * 849888 * 2
def baseEnd_849888 : Nat := 387912041323089815992393

theorem tailTrace_849888 : CollatzResearch.WordTrace tailWord_849888 prefixEnd_849888 387912041323089815992393 := by
  unfold tailWord_849888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498980972504200079791159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20665307963338933439721545 15498980972504200079791159)
  ·
    refine ⟨23248471458756300119686739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15498980972504200079791159 23248471458756300119686739)
    ·
      refine ⟨34872707188134450179530109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23248471458756300119686739 34872707188134450179530109)
      ·
        refine ⟨13077265195550418817323791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34872707188134450179530109 13077265195550418817323791)
        ·
          refine ⟨19615897793325628225985687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13077265195550418817323791 19615897793325628225985687)
          ·
            refine ⟨29423846689988442338978531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19615897793325628225985687 29423846689988442338978531)
            ·
              refine ⟨44135770034982663508467797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29423846689988442338978531 44135770034982663508467797)
              ·
                refine ⟨517216055097453087989857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44135770034982663508467797 517216055097453087989857)
                ·
                  refine ⟨387912041323089815992393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517216055097453087989857 387912041323089815992393)
                  ·
                    rfl

theorem cell20_849888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 2].length) (baseStart_849888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849888 prefixEnd_849888 := by exact prefixLift 849888
  have htrace : WordTrace (prefixWord ++ tailWord_849888) baseStart_849888 baseEnd_849888 := by
    simpa [prefixWord, tailWord_849888, baseEnd_849888] using wordTrace_append hprefix tailTrace_849888
  have hstable : (prefixWord ++ tailWord_849888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849888).length < 2 ^ (prefixWord ++ tailWord_849888).sum := by decide
  have hdescent : baseEnd_849888 < baseStart_849888 := by decide
  rcases family_descends (prefixWord ++ tailWord_849888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849916 : List Nat := [2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_849916 : Nat := 118140960795 + 849916 * 2 ^ 59
def prefixEnd_849916 : Nat := 4983230072969 + 3 ^ 40 * 849916 * 2
def baseEnd_849916 : Nat := 129308273762015387686315

theorem tailTrace_849916 : CollatzResearch.WordTrace tailWord_849916 prefixEnd_849916 129308273762015387686315 := by
  unfold tailWord_849916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15499491594453480470800801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20665988792604640627734401 15499491594453480470800801)
  ·
    refine ⟨11624618695840110353100601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15499491594453480470800801 11624618695840110353100601)
    ·
      refine ⟨8718464021880082764825451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624618695840110353100601 8718464021880082764825451)
      ·
        refine ⟨13077696032820124147238177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718464021880082764825451 13077696032820124147238177)
        ·
          refine ⟨9808272024615093110428633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13077696032820124147238177 9808272024615093110428633)
          ·
            refine ⟨7356204018461319832821475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9808272024615093110428633 7356204018461319832821475)
            ·
              refine ⟨11034306027691979749232213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356204018461319832821475 11034306027691979749232213)
              ·
                refine ⟨129308273762015387686315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11034306027691979749232213 129308273762015387686315)
                ·
                  rfl

theorem cell20_849916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_849916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849916 prefixEnd_849916 := by exact prefixLift 849916
  have htrace : WordTrace (prefixWord ++ tailWord_849916) baseStart_849916 baseEnd_849916 := by
    simpa [prefixWord, tailWord_849916, baseEnd_849916] using wordTrace_append hprefix tailTrace_849916
  have hstable : (prefixWord ++ tailWord_849916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849916).length < 2 ^ (prefixWord ++ tailWord_849916).sum := by decide
  have hdescent : baseEnd_849916 < baseStart_849916 := by decide
  rcases family_descends (prefixWord ++ tailWord_849916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849923 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_849923 : Nat := 118140960795 + 849923 * 2 ^ 59
def prefixEnd_849923 : Nat := 4983230072969 + 3 ^ 40 * 849923 * 2
def baseEnd_849923 : Nat := 387928016276785249825583

theorem tailTrace_849923 : CollatzResearch.WordTrace tailWord_849923 prefixEnd_849923 387928016276785249825583 := by
  unfold tailWord_849923
  simp only [CollatzResearch.WordTrace]
  refine ⟨30999238499881601137106423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20666158999921067424737615 30999238499881601137106423)
  ·
    refine ⟨46498857749822401705659635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30999238499881601137106423 46498857749822401705659635)
    ·
      refine ⟨69748286624733602558489453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46498857749822401705659635 69748286624733602558489453)
      ·
        refine ⟨26155607484275100959433545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69748286624733602558489453 26155607484275100959433545)
        ·
          refine ⟨19616705613206325719575159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26155607484275100959433545 19616705613206325719575159)
          ·
            refine ⟨29425058419809488579362739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19616705613206325719575159 29425058419809488579362739)
            ·
              refine ⟨44137587629714232869044109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29425058419809488579362739 44137587629714232869044109)
              ·
                refine ⟨16551595361142837325891541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44137587629714232869044109 16551595361142837325891541)
                ·
                  refine ⟨387928016276785249825583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16551595361142837325891541 387928016276785249825583)
                  ·
                    rfl

theorem cell20_849923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_849923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849923 prefixEnd_849923 := by exact prefixLift 849923
  have htrace : WordTrace (prefixWord ++ tailWord_849923) baseStart_849923 baseEnd_849923 := by
    simpa [prefixWord, tailWord_849923, baseEnd_849923] using wordTrace_append hprefix tailTrace_849923
  have hstable : (prefixWord ++ tailWord_849923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849923).length < 2 ^ (prefixWord ++ tailWord_849923).sum := by decide
  have hdescent : baseEnd_849923 < baseStart_849923 := by decide
  rcases family_descends (prefixWord ++ tailWord_849923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849981 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 2]
def baseStart_849981 : Nat := 118140960795 + 849981 * 2 ^ 59
def prefixEnd_849981 : Nat := 4983230072969 + 3 ^ 40 * 849981 * 2
def baseEnd_849981 : Nat := 387954489057194825892013

theorem tailTrace_849981 : CollatzResearch.WordTrace tailWord_849981 prefixEnd_849981 387954489057194825892013 := by
  unfold tailWord_849981
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001353933671477042717797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20667569289114318028478531 31001353933671477042717797)
  ·
    refine ⟨5812753862563401945509587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31001353933671477042717797 5812753862563401945509587)
    ·
      refine ⟨8719130793845102918264381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5812753862563401945509587 8719130793845102918264381)
      ·
        refine ⟨3269674047691913594349143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8719130793845102918264381 3269674047691913594349143)
        ·
          refine ⟨4904511071537870391523715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269674047691913594349143 4904511071537870391523715)
          ·
            refine ⟨7356766607306805587285573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904511071537870391523715 7356766607306805587285573)
            ·
              refine ⟨1379393738870026047616045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7356766607306805587285573 1379393738870026047616045)
              ·
                refine ⟨517272652076259767856017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379393738870026047616045 517272652076259767856017)
                ·
                  refine ⟨387954489057194825892013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517272652076259767856017 387954489057194825892013)
                  ·
                    rfl

theorem cell20_849981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_849981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849981 prefixEnd_849981 := by exact prefixLift 849981
  have htrace : WordTrace (prefixWord ++ tailWord_849981) baseStart_849981 baseEnd_849981 := by
    simpa [prefixWord, tailWord_849981, baseEnd_849981] using wordTrace_append hprefix tailTrace_849981
  have hstable : (prefixWord ++ tailWord_849981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849981).length < 2 ^ (prefixWord ++ tailWord_849981).sum := by decide
  have hdescent : baseEnd_849981 < baseStart_849981 := by decide
  rcases family_descends (prefixWord ++ tailWord_849981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_849999 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_849999 : Nat := 118140960795 + 849999 * 2 ^ 59
def prefixEnd_849999 : Nat := 4983230072969 + 3 ^ 40 * 849999 * 2
def baseEnd_849999 : Nat := 387962704747666763291939

theorem tailTrace_849999 : CollatzResearch.WordTrace tailWord_849999 prefixEnd_849999 387962704747666763291939 := by
  unfold tailWord_849999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31002010447606266116873051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20668006965070844077915367 31002010447606266116873051)
  ·
    refine ⟨46503015671409399175309577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31002010447606266116873051 46503015671409399175309577)
    ·
      refine ⟨34877261753557049381482183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46503015671409399175309577 34877261753557049381482183)
      ·
        refine ⟨52315892630335574072223275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34877261753557049381482183 52315892630335574072223275)
        ·
          refine ⟨78473838945503361108334913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52315892630335574072223275 78473838945503361108334913)
          ·
            refine ⟨58855379209127520831251185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78473838945503361108334913 58855379209127520831251185)
            ·
              refine ⟨44141534406845640623438389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58855379209127520831251185 44141534406845640623438389)
              ·
                refine ⟨4138268850641778808447349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44141534406845640623438389 4138268850641778808447349)
                ·
                  refine ⟨387962704747666763291939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4138268850641778808447349 387962704747666763291939)
                  ·
                    rfl

theorem cell20_849999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_849999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_849999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_849999 prefixEnd_849999 := by exact prefixLift 849999
  have htrace : WordTrace (prefixWord ++ tailWord_849999) baseStart_849999 baseEnd_849999 := by
    simpa [prefixWord, tailWord_849999, baseEnd_849999] using wordTrace_append hprefix tailTrace_849999
  have hstable : (prefixWord ++ tailWord_849999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_849999).length < 2 ^ (prefixWord ++ tailWord_849999).sum := by decide
  have hdescent : baseEnd_849999 < baseStart_849999 := by decide
  rcases family_descends (prefixWord ++ tailWord_849999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850012 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_850012 : Nat := 118140960795 + 850012 * 2 ^ 59
def prefixEnd_850012 : Nat := 4983230072969 + 3 ^ 40 * 850012 * 2
def baseEnd_850012 : Nat := 387968638301896495858553

theorem tailTrace_850012 : CollatzResearch.WordTrace tailWord_850012 prefixEnd_850012 387968638301896495858553 := by
  unfold tailWord_850012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501242298279584668548145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20668323064372779558064193 15501242298279584668548145)
  ·
    refine ⟨11625931723709688501411109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501242298279584668548145 11625931723709688501411109)
    ·
      refine ⟨2179862198195566594014583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11625931723709688501411109 2179862198195566594014583)
      ·
        refine ⟨3269793297293349891021875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179862198195566594014583 3269793297293349891021875)
        ·
          refine ⟨4904689945940024836532813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269793297293349891021875 4904689945940024836532813)
          ·
            refine ⟨1839258729727509313699805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4904689945940024836532813 1839258729727509313699805)
            ·
              refine ⟨689722023647815992637427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1839258729727509313699805 689722023647815992637427)
              ·
                refine ⟨1034583035471723988956141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689722023647815992637427 1034583035471723988956141)
                ·
                  refine ⟨387968638301896495858553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034583035471723988956141 387968638301896495858553)
                  ·
                    rfl

theorem cell20_850012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_850012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850012 prefixEnd_850012 := by exact prefixLift 850012
  have htrace : WordTrace (prefixWord ++ tailWord_850012) baseStart_850012 baseEnd_850012 := by
    simpa [prefixWord, tailWord_850012, baseEnd_850012] using wordTrace_append hprefix tailTrace_850012
  have hstable : (prefixWord ++ tailWord_850012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850012).length < 2 ^ (prefixWord ++ tailWord_850012).sum := by decide
  have hdescent : baseEnd_850012 < baseStart_850012 := by decide
  rcases family_descends (prefixWord ++ tailWord_850012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850023 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_850023 : Nat := 118140960795 + 850023 * 2 ^ 59
def prefixEnd_850023 : Nat := 4983230072969 + 3 ^ 40 * 850023 * 2
def baseEnd_850023 : Nat := 387973659001629346491841

theorem tailTrace_850023 : CollatzResearch.WordTrace tailWord_850023 prefixEnd_850023 387973659001629346491841 := by
  unfold tailWord_850023
  simp only [CollatzResearch.WordTrace]
  refine ⟨31002885799519318215746723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20668590533012878810497815 31002885799519318215746723)
  ·
    refine ⟨46504328699278977323620085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31002885799519318215746723 46504328699278977323620085)
    ·
      refine ⟨4359780815557404124089383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46504328699278977323620085 4359780815557404124089383)
      ·
        refine ⟨6539671223336106186134075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359780815557404124089383 6539671223336106186134075)
        ·
          refine ⟨9809506835004159279201113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539671223336106186134075 9809506835004159279201113)
          ·
            refine ⟨7357130126253119459400835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9809506835004159279201113 7357130126253119459400835)
            ·
              refine ⟨11035695189379679189101253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357130126253119459400835 11035695189379679189101253)
              ·
                refine ⟨2069192848008689847956485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11035695189379679189101253 2069192848008689847956485)
                ·
                  refine ⟨387973659001629346491841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069192848008689847956485 387973659001629346491841)
                  ·
                    rfl

theorem cell20_850023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_850023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850023 prefixEnd_850023 := by exact prefixLift 850023
  have htrace : WordTrace (prefixWord ++ tailWord_850023) baseStart_850023 baseEnd_850023 := by
    simpa [prefixWord, tailWord_850023, baseEnd_850023] using wordTrace_append hprefix tailTrace_850023
  have hstable : (prefixWord ++ tailWord_850023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850023).length < 2 ^ (prefixWord ++ tailWord_850023).sum := by decide
  have hdescent : baseEnd_850023 < baseStart_850023 := by decide
  rcases family_descends (prefixWord ++ tailWord_850023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850057 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 2]
def baseStart_850057 : Nat := 118140960795 + 850057 * 2 ^ 59
def prefixEnd_850057 : Nat := 4983230072969 + 3 ^ 40 * 850057 * 2
def baseEnd_850057 : Nat := 387989177528076339358369

theorem tailTrace_850057 : CollatzResearch.WordTrace tailWord_850057 prefixEnd_850057 387989177528076339358369 := by
  unfold tailWord_850057
  simp only [CollatzResearch.WordTrace]
  refine ⟨31004125881396142022484425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20669417254264094681656283 31004125881396142022484425)
  ·
    refine ⟨23253094411047106516863319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31004125881396142022484425 23253094411047106516863319)
    ·
      refine ⟨34879641616570659775294979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23253094411047106516863319 34879641616570659775294979)
      ·
        refine ⟨52319462424855989662942469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34879641616570659775294979 52319462424855989662942469)
        ·
          refine ⟨9809899204660498061801713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52319462424855989662942469 9809899204660498061801713)
          ·
            refine ⟨7357424403495373546351285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9809899204660498061801713 7357424403495373546351285)
            ·
              refine ⟨689758537827691269970433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7357424403495373546351285 689758537827691269970433)
              ·
                refine ⟨517318903370768452477825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689758537827691269970433 517318903370768452477825)
                ·
                  refine ⟨387989177528076339358369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517318903370768452477825 387989177528076339358369)
                  ·
                    rfl

theorem cell20_850057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_850057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850057 prefixEnd_850057 := by exact prefixLift 850057
  have htrace : WordTrace (prefixWord ++ tailWord_850057) baseStart_850057 baseEnd_850057 := by
    simpa [prefixWord, tailWord_850057, baseEnd_850057] using wordTrace_append hprefix tailTrace_850057
  have hstable : (prefixWord ++ tailWord_850057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850057).length < 2 ^ (prefixWord ++ tailWord_850057).sum := by decide
  have hdescent : baseEnd_850057 < baseStart_850057 := by decide
  rcases family_descends (prefixWord ++ tailWord_850057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850071 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_850071 : Nat := 118140960795 + 850071 * 2 ^ 59
def prefixEnd_850071 : Nat := 4983230072969 + 3 ^ 40 * 850071 * 2
def baseEnd_850071 : Nat := 387995567509554512891645

theorem tailTrace_850071 : CollatzResearch.WordTrace tailWord_850071 prefixEnd_850071 387995567509554512891645 := by
  unfold tailWord_850071
  simp only [CollatzResearch.WordTrace]
  refine ⟨31004636503345422413494067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20669757668896948275662711 31004636503345422413494067)
  ·
    refine ⟨46506954755018133620241101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31004636503345422413494067 46506954755018133620241101)
    ·
      refine ⟨17440108033131800107590413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46506954755018133620241101 17440108033131800107590413)
      ·
        refine ⟨6540040512424425040346405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17440108033131800107590413 6540040512424425040346405)
        ·
          refine ⟨1226257596079579695064951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6540040512424425040346405 1226257596079579695064951)
          ·
            refine ⟨1839386394119369542597427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226257596079579695064951 1839386394119369542597427)
            ·
              refine ⟨2759079591179054313896141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839386394119369542597427 2759079591179054313896141)
              ·
                refine ⟨1034654846692145367711053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2759079591179054313896141 1034654846692145367711053)
                ·
                  refine ⟨387995567509554512891645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034654846692145367711053 387995567509554512891645)
                  ·
                    rfl

theorem cell20_850071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_850071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850071 prefixEnd_850071 := by exact prefixLift 850071
  have htrace : WordTrace (prefixWord ++ tailWord_850071) baseStart_850071 baseEnd_850071 := by
    simpa [prefixWord, tailWord_850071, baseEnd_850071] using wordTrace_append hprefix tailTrace_850071
  have hstable : (prefixWord ++ tailWord_850071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850071).length < 2 ^ (prefixWord ++ tailWord_850071).sum := by decide
  have hdescent : baseEnd_850071 < baseStart_850071 := by decide
  rcases family_descends (prefixWord ++ tailWord_850071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850112 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_850112 : Nat := 118140960795 + 850112 * 2 ^ 59
def prefixEnd_850112 : Nat := 4983230072969 + 3 ^ 40 * 850112 * 2
def baseEnd_850112 : Nat := 388014281026740592524811

theorem tailTrace_850112 : CollatzResearch.WordTrace tailWord_850112 prefixEnd_850112 388014281026740592524811 := by
  unfold tailWord_850112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503065948098443207868295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20670754597464590943824393 15503065948098443207868295)
  ·
    refine ⟨23254598922147664811802443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503065948098443207868295 23254598922147664811802443)
    ·
      refine ⟨34881898383221497217703665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254598922147664811802443 34881898383221497217703665)
      ·
        refine ⟨26161423787416122913277749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34881898383221497217703665 26161423787416122913277749)
        ·
          refine ⟨2452633480070261523119789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26161423787416122913277749 2452633480070261523119789)
          ·
            refine ⟨919737555026348071169921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2452633480070261523119789 919737555026348071169921)
            ·
              refine ⟨689803166269761053377441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919737555026348071169921 689803166269761053377441)
              ·
                refine ⟨517352374702320790033081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689803166269761053377441 517352374702320790033081)
                ·
                  refine ⟨388014281026740592524811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517352374702320790033081 388014281026740592524811)
                  ·
                    rfl

theorem cell20_850112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_850112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850112 prefixEnd_850112 := by exact prefixLift 850112
  have htrace : WordTrace (prefixWord ++ tailWord_850112) baseStart_850112 baseEnd_850112 := by
    simpa [prefixWord, tailWord_850112, baseEnd_850112] using wordTrace_append hprefix tailTrace_850112
  have hstable : (prefixWord ++ tailWord_850112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850112).length < 2 ^ (prefixWord ++ tailWord_850112).sum := by decide
  have hdescent : baseEnd_850112 < baseStart_850112 := by decide
  rcases family_descends (prefixWord ++ tailWord_850112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850146 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_850146 : Nat := 118140960795 + 850146 * 2 ^ 59
def prefixEnd_850146 : Nat := 4983230072969 + 3 ^ 40 * 850146 * 2
def baseEnd_850146 : Nat := 388029799553187585391339

theorem tailTrace_850146 : CollatzResearch.WordTrace tailWord_850146 prefixEnd_850146 388029799553187585391339 := by
  unfold tailWord_850146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751842994518427555618573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20671581318715806814982861 7751842994518427555618573)
  ·
    refine ⟨2906941122944410333356965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7751842994518427555618573 2906941122944410333356965)
    ·
      refine ⟨545051460552076937504431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2906941122944410333356965 545051460552076937504431)
      ·
        refine ⟨817577190828115406256647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545051460552076937504431 817577190828115406256647)
        ·
          refine ⟨1226365786242173109384971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817577190828115406256647 1226365786242173109384971)
          ·
            refine ⟨1839548679363259664077457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226365786242173109384971 1839548679363259664077457)
            ·
              refine ⟨1379661509522444748058093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839548679363259664077457 1379661509522444748058093)
              ·
                refine ⟨517373066070916780521785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379661509522444748058093 517373066070916780521785)
                ·
                  refine ⟨388029799553187585391339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517373066070916780521785 388029799553187585391339)
                  ·
                    rfl

theorem cell20_850146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_850146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850146 prefixEnd_850146 := by exact prefixLift 850146
  have htrace : WordTrace (prefixWord ++ tailWord_850146) baseStart_850146 baseEnd_850146 := by
    simpa [prefixWord, tailWord_850146, baseEnd_850146] using wordTrace_append hprefix tailTrace_850146
  have hstable : (prefixWord ++ tailWord_850146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850146).length < 2 ^ (prefixWord ++ tailWord_850146).sum := by decide
  have hdescent : baseEnd_850146 < baseStart_850146 := by decide
  rcases family_descends (prefixWord ++ tailWord_850146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850175 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_850175 : Nat := 118140960795 + 850175 * 2 ^ 59
def prefixEnd_850175 : Nat := 4983230072969 + 3 ^ 40 * 850175 * 2
def baseEnd_850175 : Nat := 388043035943392373424553

theorem tailTrace_850175 : CollatzResearch.WordTrace tailWord_850175 prefixEnd_850175 388043035943392373424553 := by
  unfold tailWord_850175
  simp only [CollatzResearch.WordTrace]
  refine ⟨31008429694968648175279979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20672286463312432116853319 31008429694968648175279979)
  ·
    refine ⟨46512644542452972262919969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31008429694968648175279979 46512644542452972262919969)
    ·
      refine ⟨34884483406839729197189977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46512644542452972262919969 34884483406839729197189977)
      ·
        refine ⟨26163362555129796897892483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34884483406839729197189977 26163362555129796897892483)
        ·
          refine ⟨39245043832694695346838725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26163362555129796897892483 39245043832694695346838725)
          ·
            refine ⟨7358445718630255377532261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39245043832694695346838725 7358445718630255377532261)
            ·
              refine ⟨1379708572243172883287299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7358445718630255377532261 1379708572243172883287299)
              ·
                refine ⟨2069562858364759324930949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379708572243172883287299 2069562858364759324930949)
                ·
                  refine ⟨388043035943392373424553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069562858364759324930949 388043035943392373424553)
                  ·
                    rfl

theorem cell20_850175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_850175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850175 prefixEnd_850175 := by exact prefixLift 850175
  have htrace : WordTrace (prefixWord ++ tailWord_850175) baseStart_850175 baseEnd_850175 := by
    simpa [prefixWord, tailWord_850175, baseEnd_850175] using wordTrace_append hprefix tailTrace_850175
  have hstable : (prefixWord ++ tailWord_850175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850175).length < 2 ^ (prefixWord ++ tailWord_850175).sum := by decide
  have hdescent : baseEnd_850175 < baseStart_850175 := by decide
  rcases family_descends (prefixWord ++ tailWord_850175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850185 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 3]
def baseStart_850185 : Nat := 118140960795 + 850185 * 2 ^ 59
def prefixEnd_850185 : Nat := 4983230072969 + 3 ^ 40 * 850185 * 2
def baseEnd_850185 : Nat := 388047600215876783091179

theorem tailTrace_850185 : CollatzResearch.WordTrace tailWord_850185 prefixEnd_850185 388047600215876783091179 := by
  unfold tailWord_850185
  simp only [CollatzResearch.WordTrace]
  refine ⟨31008794424932419883144009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20672529616621613255429339 31008794424932419883144009)
  ·
    refine ⟨23256595818699314912358007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31008794424932419883144009 23256595818699314912358007)
    ·
      refine ⟨34884893728048972368537011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23256595818699314912358007 34884893728048972368537011)
      ·
        refine ⟨52327340592073458552805517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34884893728048972368537011 52327340592073458552805517)
        ·
          refine ⟨19622752722027546957302069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52327340592073458552805517 19622752722027546957302069)
          ·
            refine ⟨1839633067690082527247069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19622752722027546957302069 1839633067690082527247069)
            ·
              refine ⟨689862400383780947717651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1839633067690082527247069 689862400383780947717651)
              ·
                refine ⟨1034793600575671421576477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689862400383780947717651 1034793600575671421576477)
                ·
                  refine ⟨388047600215876783091179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034793600575671421576477 388047600215876783091179)
                  ·
                    rfl

theorem cell20_850185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_850185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850185 prefixEnd_850185 := by exact prefixLift 850185
  have htrace : WordTrace (prefixWord ++ tailWord_850185) baseStart_850185 baseEnd_850185 := by
    simpa [prefixWord, tailWord_850185, baseEnd_850185] using wordTrace_append hprefix tailTrace_850185
  have hstable : (prefixWord ++ tailWord_850185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850185).length < 2 ^ (prefixWord ++ tailWord_850185).sum := by decide
  have hdescent : baseEnd_850185 < baseStart_850185 := by decide
  rcases family_descends (prefixWord ++ tailWord_850185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850199 : List Nat := [1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_850199 : Nat := 118140960795 + 850199 * 2 ^ 59
def prefixEnd_850199 : Nat := 4983230072969 + 3 ^ 40 * 850199 * 2
def baseEnd_850199 : Nat := 129351330065784985541485

theorem tailTrace_850199 : CollatzResearch.WordTrace tailWord_850199 prefixEnd_850199 129351330065784985541485 := by
  unfold tailWord_850199
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009305046881700274153651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20672870031254466849435767 31009305046881700274153651)
  ·
    refine ⟨46513957570322550411230477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31009305046881700274153651 46513957570322550411230477)
    ·
      refine ⟨17442734088870956404211429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46513957570322550411230477 17442734088870956404211429)
      ·
        refine ⟨3270512641663304325789643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17442734088870956404211429 3270512641663304325789643)
        ·
          refine ⟨4905768962494956488684465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270512641663304325789643 4905768962494956488684465)
          ·
            refine ⟨3679326721871217366513349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4905768962494956488684465 3679326721871217366513349)
            ·
              refine ⟨689873760350853256221253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3679326721871217366513349 689873760350853256221253)
              ·
                refine ⟨129351330065784985541485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689873760350853256221253 129351330065784985541485)
                ·
                  rfl

theorem cell20_850199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_850199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850199 prefixEnd_850199 := by exact prefixLift 850199
  have htrace : WordTrace (prefixWord ++ tailWord_850199) baseStart_850199 baseEnd_850199 := by
    simpa [prefixWord, tailWord_850199, baseEnd_850199] using wordTrace_append hprefix tailTrace_850199
  have hstable : (prefixWord ++ tailWord_850199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850199).length < 2 ^ (prefixWord ++ tailWord_850199).sum := by decide
  have hdescent : baseEnd_850199 < baseStart_850199 := by decide
  rcases family_descends (prefixWord ++ tailWord_850199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850205 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 2]
def baseStart_850205 : Nat := 118140960795 + 850205 * 2 ^ 59
def prefixEnd_850205 : Nat := 4983230072969 + 3 ^ 40 * 850205 * 2
def baseEnd_850205 : Nat := 388056728760845602424431

theorem tailTrace_850205 : CollatzResearch.WordTrace tailWord_850205 prefixEnd_850205 388056728760845602424431 := by
  unfold tailWord_850205
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009523884859963298872069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20673015923239975532581379 31009523884859963298872069)
  ·
    refine ⟨5814285728411243118538513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31009523884859963298872069 5814285728411243118538513)
    ·
      refine ⟨4360714296308432338903885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5814285728411243118538513 4360714296308432338903885)
      ·
        refine ⟨1635267861115662127088957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4360714296308432338903885 1635267861115662127088957)
        ·
          refine ⟨613225447918373297658359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1635267861115662127088957 613225447918373297658359)
          ·
            refine ⟨919838171877559946487539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613225447918373297658359 919838171877559946487539)
            ·
              refine ⟨1379757257816339919731309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919838171877559946487539 1379757257816339919731309)
              ·
                refine ⟨517408971681127469899241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379757257816339919731309 517408971681127469899241)
                ·
                  refine ⟨388056728760845602424431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517408971681127469899241 388056728760845602424431)
                  ·
                    rfl

theorem cell20_850205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_850205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850205 prefixEnd_850205 := by exact prefixLift 850205
  have htrace : WordTrace (prefixWord ++ tailWord_850205) baseStart_850205 baseEnd_850205 := by
    simpa [prefixWord, tailWord_850205, baseEnd_850205] using wordTrace_append hprefix tailTrace_850205
  have hstable : (prefixWord ++ tailWord_850205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850205).length < 2 ^ (prefixWord ++ tailWord_850205).sum := by decide
  have hdescent : baseEnd_850205 < baseStart_850205 := by decide
  rcases family_descends (prefixWord ++ tailWord_850205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850216 : List Nat := [2, 1, 5, 1, 4, 1, 6]
def baseStart_850216 : Nat := 118140960795 + 850216 * 2 ^ 59
def prefixEnd_850216 : Nat := 4983230072969 + 3 ^ 40 * 850216 * 2
def baseEnd_850216 : Nat := 43117972162286494784191

theorem tailTrace_850216 : CollatzResearch.WordTrace tailWord_850216 prefixEnd_850216 43117972162286494784191 := by
  unfold tailWord_850216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15504962543910056088761251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20673283391880074785015001 15504962543910056088761251)
  ·
    refine ⟨23257443815865084133141877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15504962543910056088761251 23257443815865084133141877)
    ·
      refine ⟨2180385357737351637482051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23257443815865084133141877 2180385357737351637482051)
      ·
        refine ⟨3270578036606027456223077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180385357737351637482051 3270578036606027456223077)
        ·
          refine ⟨613233381863630148041827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3270578036606027456223077 613233381863630148041827)
          ·
            refine ⟨919850072795445222062741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613233381863630148041827 919850072795445222062741)
            ·
              refine ⟨43117972162286494784191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 919850072795445222062741 43117972162286494784191)
              ·
                rfl

theorem cell20_850216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 6].length) (baseStart_850216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850216 prefixEnd_850216 := by exact prefixLift 850216
  have htrace : WordTrace (prefixWord ++ tailWord_850216) baseStart_850216 baseEnd_850216 := by
    simpa [prefixWord, tailWord_850216, baseEnd_850216] using wordTrace_append hprefix tailTrace_850216
  have hstable : (prefixWord ++ tailWord_850216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850216).length < 2 ^ (prefixWord ++ tailWord_850216).sum := by decide
  have hdescent : baseEnd_850216 < baseStart_850216 := by decide
  rcases family_descends (prefixWord ++ tailWord_850216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850226 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_850226 : Nat := 118140960795 + 850226 * 2 ^ 59
def prefixEnd_850226 : Nat := 4983230072969 + 3 ^ 40 * 850226 * 2
def baseEnd_850226 : Nat := 388066313733062862724345

theorem tailTrace_850226 : CollatzResearch.WordTrace tailWord_850226 prefixEnd_850226 388066313733062862724345 := by
  unfold tailWord_850226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752572454445970971346633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20673526545189255923591021 7752572454445970971346633)
  ·
    refine ⟨5814429340834478228509975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7752572454445970971346633 5814429340834478228509975)
    ·
      refine ⟨8721644011251717342764963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814429340834478228509975 8721644011251717342764963)
      ·
        refine ⟨13082466016877576014147445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721644011251717342764963 13082466016877576014147445)
        ·
          refine ⟨1226481189082272751326323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13082466016877576014147445 1226481189082272751326323)
          ·
            refine ⟨1839721783623409126989485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226481189082272751326323 1839721783623409126989485)
            ·
              refine ⟨689895668858778422621057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1839721783623409126989485 689895668858778422621057)
              ·
                refine ⟨517421751644083816965793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689895668858778422621057 517421751644083816965793)
                ·
                  refine ⟨388066313733062862724345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517421751644083816965793 388066313733062862724345)
                  ·
                    rfl

theorem cell20_850226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_850226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850226 prefixEnd_850226 := by exact prefixLift 850226
  have htrace : WordTrace (prefixWord ++ tailWord_850226) baseStart_850226 baseEnd_850226 := by
    simpa [prefixWord, tailWord_850226, baseEnd_850226] using wordTrace_append hprefix tailTrace_850226
  have hstable : (prefixWord ++ tailWord_850226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850226).length < 2 ^ (prefixWord ++ tailWord_850226).sum := by decide
  have hdescent : baseEnd_850226 < baseStart_850226 := by decide
  rcases family_descends (prefixWord ++ tailWord_850226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850227 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_850227 : Nat := 118140960795 + 850227 * 2 ^ 59
def prefixEnd_850227 : Nat := 4983230072969 + 3 ^ 40 * 850227 * 2
def baseEnd_850227 : Nat := 388066770160311303691007

theorem tailTrace_850227 : CollatzResearch.WordTrace tailWord_850227 prefixEnd_850227 388066770160311303691007 := by
  unfold tailWord_850227
  simp only [CollatzResearch.WordTrace]
  refine ⟨31010326290780261056172935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20673550860520174037448623 31010326290780261056172935)
  ·
    refine ⟨46515489436170391584259403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31010326290780261056172935 46515489436170391584259403)
    ·
      refine ⟨69773234154255587376389105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46515489436170391584259403 69773234154255587376389105)
      ·
        refine ⟨52329925615691690532291829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69773234154255587376389105 52329925615691690532291829)
        ·
          refine ⟨4905930526471095987402359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52329925615691690532291829 4905930526471095987402359)
          ·
            refine ⟨7358895789706643981103539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905930526471095987402359 7358895789706643981103539)
            ·
              refine ⟨11038343684559965971655309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358895789706643981103539 11038343684559965971655309)
              ·
                refine ⟨4139378881709987239370741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11038343684559965971655309 4139378881709987239370741)
                ·
                  refine ⟨388066770160311303691007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4139378881709987239370741 388066770160311303691007)
                  ·
                    rfl

theorem cell20_850227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_850227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850227 prefixEnd_850227 := by exact prefixLift 850227
  have htrace : WordTrace (prefixWord ++ tailWord_850227) baseStart_850227 baseEnd_850227 := by
    simpa [prefixWord, tailWord_850227, baseEnd_850227] using wordTrace_append hprefix tailTrace_850227
  have hstable : (prefixWord ++ tailWord_850227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850227).length < 2 ^ (prefixWord ++ tailWord_850227).sum := by decide
  have hdescent : baseEnd_850227 < baseStart_850227 := by decide
  rcases family_descends (prefixWord ++ tailWord_850227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850258 : List Nat := [3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_850258 : Nat := 118140960795 + 850258 * 2 ^ 59
def prefixEnd_850258 : Nat := 4983230072969 + 3 ^ 40 * 850258 * 2
def baseEnd_850258 : Nat := 129360306468337657885849

theorem tailTrace_850258 : CollatzResearch.WordTrace tailWord_850258 prefixEnd_850258 129360306468337657885849 := by
  unfold tailWord_850258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752864238416988337637857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20674304635778635567034285 7752864238416988337637857)
  ·
    refine ⟨5814648178812741253228393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7752864238416988337637857 5814648178812741253228393)
    ·
      refine ⟨4360986134109555939921295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5814648178812741253228393 4360986134109555939921295)
      ·
        refine ⟨6541479201164333909881943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360986134109555939921295 6541479201164333909881943)
        ·
          refine ⟨9812218801746500864822915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541479201164333909881943 9812218801746500864822915)
          ·
            refine ⟨14718328202619751297234373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812218801746500864822915 14718328202619751297234373)
            ·
              refine ⟨2759686537991203368231445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14718328202619751297234373 2759686537991203368231445)
              ·
                refine ⟨129360306468337657885849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2759686537991203368231445 129360306468337657885849)
                ·
                  rfl

theorem cell20_850258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_850258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850258 prefixEnd_850258 := by exact prefixLift 850258
  have htrace : WordTrace (prefixWord ++ tailWord_850258) baseStart_850258 baseEnd_850258 := by
    simpa [prefixWord, tailWord_850258, baseEnd_850258] using wordTrace_append hprefix tailTrace_850258
  have hstable : (prefixWord ++ tailWord_850258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850258).length < 2 ^ (prefixWord ++ tailWord_850258).sum := by decide
  have hdescent : baseEnd_850258 < baseStart_850258 := by decide
  rcases family_descends (prefixWord ++ tailWord_850258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850313 : List Nat := [1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_850313 : Nat := 118140960795 + 850313 * 2 ^ 59
def prefixEnd_850313 : Nat := 4983230072969 + 3 ^ 40 * 850313 * 2
def baseEnd_850313 : Nat := 129368674301225742274663

theorem tailTrace_850313 : CollatzResearch.WordTrace tailWord_850313 prefixEnd_850313 129368674301225742274663 := by
  unfold tailWord_850313
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013462968468697743803593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20675641978979131829202395 31013462968468697743803593)
  ·
    refine ⟨23260097226351523307852695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31013462968468697743803593 23260097226351523307852695)
    ·
      refine ⟨34890145839527284961779043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23260097226351523307852695 34890145839527284961779043)
      ·
        refine ⟨52335218759290927442668565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34890145839527284961779043 52335218759290927442668565)
        ·
          refine ⟨2453213379341762223875089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52335218759290927442668565 2453213379341762223875089)
          ·
            refine ⟨1839910034506321667906317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2453213379341762223875089 1839910034506321667906317)
            ·
              refine ⟨689966262939870625464869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1839910034506321667906317 689966262939870625464869)
              ·
                refine ⟨129368674301225742274663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689966262939870625464869 129368674301225742274663)
                ·
                  rfl

theorem cell20_850313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_850313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850313 prefixEnd_850313 := by exact prefixLift 850313
  have htrace : WordTrace (prefixWord ++ tailWord_850313) baseStart_850313 baseEnd_850313 := by
    simpa [prefixWord, tailWord_850313, baseEnd_850313] using wordTrace_append hprefix tailTrace_850313
  have hstable : (prefixWord ++ tailWord_850313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850313).length < 2 ^ (prefixWord ++ tailWord_850313).sum := by decide
  have hdescent : baseEnd_850313 < baseStart_850313 := by decide
  rcases family_descends (prefixWord ++ tailWord_850313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850337 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_850337 : Nat := 118140960795 + 850337 * 2 ^ 59
def prefixEnd_850337 : Nat := 4983230072969 + 3 ^ 40 * 850337 * 2
def baseEnd_850337 : Nat := 388116977157639810023891

theorem tailTrace_850337 : CollatzResearch.WordTrace tailWord_850337 prefixEnd_850337 388116977157639810023891 := by
  unfold tailWord_850337
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014338320381749842677265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20676225546921166561784843 31014338320381749842677265)
  ·
    refine ⟨23260753740286312382007949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31014338320381749842677265 23260753740286312382007949)
    ·
      refine ⟨8722782652607367143252981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23260753740286312382007949 8722782652607367143252981)
      ·
        refine ⟨817760873681940669679967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8722782652607367143252981 817760873681940669679967)
        ·
          refine ⟨1226641310522911004519951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817760873681940669679967 1226641310522911004519951)
          ·
            refine ⟨1839961965784366506779927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226641310522911004519951 1839961965784366506779927)
            ·
              refine ⟨2759942948676549760169891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839961965784366506779927 2759942948676549760169891)
              ·
                refine ⟨4139914423014824640254837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759942948676549760169891 4139914423014824640254837)
                ·
                  refine ⟨388116977157639810023891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4139914423014824640254837 388116977157639810023891)
                  ·
                    rfl

theorem cell20_850337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_850337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850337 prefixEnd_850337 := by exact prefixLift 850337
  have htrace : WordTrace (prefixWord ++ tailWord_850337) baseStart_850337 baseEnd_850337 := by
    simpa [prefixWord, tailWord_850337, baseEnd_850337] using wordTrace_append hprefix tailTrace_850337
  have hstable : (prefixWord ++ tailWord_850337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850337).length < 2 ^ (prefixWord ++ tailWord_850337).sum := by decide
  have hdescent : baseEnd_850337 < baseStart_850337 := by decide
  rcases family_descends (prefixWord ++ tailWord_850337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850341 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_850341 : Nat := 118140960795 + 850341 * 2 ^ 59
def prefixEnd_850341 : Nat := 4983230072969 + 3 ^ 40 * 850341 * 2
def baseEnd_850341 : Nat := 388118802866633573890541

theorem tailTrace_850341 : CollatzResearch.WordTrace tailWord_850341 prefixEnd_850341 388118802866633573890541 := by
  unfold tailWord_850341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014484212367258525822877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20676322808244839017215251 31014484212367258525822877)
  ·
    refine ⟨11630431579637721947183579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31014484212367258525822877 11630431579637721947183579)
    ·
      refine ⟨17445647369456582920775369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11630431579637721947183579 17445647369456582920775369)
      ·
        refine ⟨13084235527092437190581527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17445647369456582920775369 13084235527092437190581527)
        ·
          refine ⟨19626353290638655785872291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084235527092437190581527 19626353290638655785872291)
          ·
            refine ⟨29439529935957983678808437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19626353290638655785872291 29439529935957983678808437)
            ·
              refine ⟨2759955931496060969888291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29439529935957983678808437 2759955931496060969888291)
              ·
                refine ⟨4139933897244091454832437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759955931496060969888291 4139933897244091454832437)
                ·
                  refine ⟨388118802866633573890541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4139933897244091454832437 388118802866633573890541)
                  ·
                    rfl

theorem cell20_850341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_850341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850341 prefixEnd_850341 := by exact prefixLift 850341
  have htrace : WordTrace (prefixWord ++ tailWord_850341) baseStart_850341 baseEnd_850341 := by
    simpa [prefixWord, tailWord_850341, baseEnd_850341] using wordTrace_append hprefix tailTrace_850341
  have hstable : (prefixWord ++ tailWord_850341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850341).length < 2 ^ (prefixWord ++ tailWord_850341).sum := by decide
  have hdescent : baseEnd_850341 < baseStart_850341 := by decide
  rcases family_descends (prefixWord ++ tailWord_850341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850344 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_850344 : Nat := 118140960795 + 850344 * 2 ^ 59
def prefixEnd_850344 : Nat := 4983230072969 + 3 ^ 40 * 850344 * 2
def baseEnd_850344 : Nat := 388120172148378896790529

theorem tailTrace_850344 : CollatzResearch.WordTrace tailWord_850344 prefixEnd_850344 388120172148378896790529 := by
  unfold tailWord_850344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15507296815678195019091043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20676395754237593358788057 15507296815678195019091043)
  ·
    refine ⟨23260945223517292528636565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15507296815678195019091043 23260945223517292528636565)
    ·
      refine ⟨1090356807352373087279839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23260945223517292528636565 1090356807352373087279839)
      ·
        refine ⟨1635535211028559630919759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090356807352373087279839 1635535211028559630919759)
        ·
          refine ⟨2453302816542839446379639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635535211028559630919759 2453302816542839446379639)
          ·
            refine ⟨3679954224814259169569459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453302816542839446379639 3679954224814259169569459)
            ·
              refine ⟨5519931337221388754354189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679954224814259169569459 5519931337221388754354189)
              ·
                refine ⟨2069974251458020782882821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5519931337221388754354189 2069974251458020782882821)
                ·
                  refine ⟨388120172148378896790529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069974251458020782882821 388120172148378896790529)
                  ·
                    rfl

theorem cell20_850344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_850344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850344 prefixEnd_850344 := by exact prefixLift 850344
  have htrace : WordTrace (prefixWord ++ tailWord_850344) baseStart_850344 baseEnd_850344 := by
    simpa [prefixWord, tailWord_850344, baseEnd_850344] using wordTrace_append hprefix tailTrace_850344
  have hstable : (prefixWord ++ tailWord_850344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850344).length < 2 ^ (prefixWord ++ tailWord_850344).sum := by decide
  have hdescent : baseEnd_850344 < baseStart_850344 := by decide
  rcases family_descends (prefixWord ++ tailWord_850344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850365 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_850365 : Nat := 118140960795 + 850365 * 2 ^ 59
def prefixEnd_850365 : Nat := 4983230072969 + 3 ^ 40 * 850365 * 2
def baseEnd_850365 : Nat := 388129757120596157090443

theorem tailTrace_850365 : CollatzResearch.WordTrace tailWord_850365 prefixEnd_850365 388129757120596157090443 := by
  unfold tailWord_850365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015359564280310624696549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20676906376186873749797699 31015359564280310624696549)
  ·
    refine ⟨5815379918302558242130603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31015359564280310624696549 5815379918302558242130603)
    ·
      refine ⟨8723069877453837363195905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5815379918302558242130603 8723069877453837363195905)
      ·
        refine ⟨6542302408090378022396929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8723069877453837363195905 6542302408090378022396929)
        ·
          refine ⟨4906726806067783516797697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6542302408090378022396929 4906726806067783516797697)
          ·
            refine ⟨3680045104550837637598273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906726806067783516797697 3680045104550837637598273)
            ·
              refine ⟨2760033828413128228198705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680045104550837637598273 2760033828413128228198705)
              ·
                refine ⟨2070025371309846171149029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760033828413128228198705 2070025371309846171149029)
                ·
                  refine ⟨388129757120596157090443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070025371309846171149029 388129757120596157090443)
                  ·
                    rfl

theorem cell20_850365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_850365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850365 prefixEnd_850365 := by exact prefixLift 850365
  have htrace : WordTrace (prefixWord ++ tailWord_850365) baseStart_850365 baseEnd_850365 := by
    simpa [prefixWord, tailWord_850365, baseEnd_850365] using wordTrace_append hprefix tailTrace_850365
  have hstable : (prefixWord ++ tailWord_850365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850365).length < 2 ^ (prefixWord ++ tailWord_850365).sum := by decide
  have hdescent : baseEnd_850365 < baseStart_850365 := by decide
  rcases family_descends (prefixWord ++ tailWord_850365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850399 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 2]
def baseStart_850399 : Nat := 118140960795 + 850399 * 2 ^ 59
def prefixEnd_850399 : Nat := 4983230072969 + 3 ^ 40 * 850399 * 2
def baseEnd_850399 : Nat := 388145275647043149956971

theorem tailTrace_850399 : CollatzResearch.WordTrace tailWord_850399 prefixEnd_850399 388145275647043149956971 := by
  unfold tailWord_850399
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016599646157134431434251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20677733097438089620956167 31016599646157134431434251)
  ·
    refine ⟨46524899469235701647151377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31016599646157134431434251 46524899469235701647151377)
    ·
      refine ⟨34893674601926776235363533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46524899469235701647151377 34893674601926776235363533)
      ·
        refine ⟨13085127975722541088261325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34893674601926776235363533 13085127975722541088261325)
        ·
          refine ⟨4906922990895952908097997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13085127975722541088261325 4906922990895952908097997)
          ·
            refine ⟨1840096121585982340536749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4906922990895952908097997 1840096121585982340536749)
            ·
              refine ⟨690036045594743377701281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1840096121585982340536749 690036045594743377701281)
              ·
                refine ⟨517527034196057533275961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690036045594743377701281 517527034196057533275961)
                ·
                  refine ⟨388145275647043149956971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517527034196057533275961 388145275647043149956971)
                  ·
                    rfl

theorem cell20_850399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2].length) (baseStart_850399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850399 prefixEnd_850399 := by exact prefixLift 850399
  have htrace : WordTrace (prefixWord ++ tailWord_850399) baseStart_850399 baseEnd_850399 := by
    simpa [prefixWord, tailWord_850399, baseEnd_850399] using wordTrace_append hprefix tailTrace_850399
  have hstable : (prefixWord ++ tailWord_850399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850399).length < 2 ^ (prefixWord ++ tailWord_850399).sum := by decide
  have hdescent : baseEnd_850399 < baseStart_850399 := by decide
  rcases family_descends (prefixWord ++ tailWord_850399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850410 : List Nat := [3, 1, 3, 1, 3, 1, 1, 7]
def baseStart_850410 : Nat := 118140960795 + 850410 * 2 ^ 59
def prefixEnd_850410 : Nat := 4983230072969 + 3 ^ 40 * 850410 * 2
def baseEnd_850410 : Nat := 129383432115592000196753

theorem tailTrace_850410 : CollatzResearch.WordTrace tailWord_850410 prefixEnd_850410 129383432115592000196753 := by
  unfold tailWord_850410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7754250212279320827521171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20678000566078188873389789 7754250212279320827521171)
  ·
    refine ⟨11631375318418981241281757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7754250212279320827521171 11631375318418981241281757)
    ·
      refine ⟨4361765744407117965480659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11631375318418981241281757 4361765744407117965480659)
      ·
        refine ⟨6542648616610676948220989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361765744407117965480659 6542648616610676948220989)
        ·
          refine ⟨2453493231229003855582871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6542648616610676948220989 2453493231229003855582871)
          ·
            refine ⟨3680239846843505783374307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453493231229003855582871 3680239846843505783374307)
            ·
              refine ⟨5520359770265258675061461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680239846843505783374307 5520359770265258675061461)
              ·
                refine ⟨129383432115592000196753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5520359770265258675061461 129383432115592000196753)
                ·
                  rfl

theorem cell20_850410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_850410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850410 prefixEnd_850410 := by exact prefixLift 850410
  have htrace : WordTrace (prefixWord ++ tailWord_850410) baseStart_850410 baseEnd_850410 := by
    simpa [prefixWord, tailWord_850410, baseEnd_850410] using wordTrace_append hprefix tailTrace_850410
  have hstable : (prefixWord ++ tailWord_850410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850410).length < 2 ^ (prefixWord ++ tailWord_850410).sum := by decide
  have hdescent : baseEnd_850410 < baseStart_850410 := by decide
  rcases family_descends (prefixWord ++ tailWord_850410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850413 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_850413 : Nat := 118140960795 + 850413 * 2 ^ 59
def prefixEnd_850413 : Nat := 4983230072969 + 3 ^ 40 * 850413 * 2
def baseEnd_850413 : Nat := 388151665628521323490247

theorem tailTrace_850413 : CollatzResearch.WordTrace tailWord_850413 prefixEnd_850413 388151665628521323490247 := by
  unfold tailWord_850413
  simp only [CollatzResearch.WordTrace]
  refine ⟨31017110268106414822443893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20678073512070943214962595 31017110268106414822443893)
  ·
    refine ⟨2907854087634976389604115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31017110268106414822443893 2907854087634976389604115)
    ·
      refine ⟨4361781131452464584406173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907854087634976389604115 4361781131452464584406173)
      ·
        refine ⟨1635667924294674219152315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4361781131452464584406173 1635667924294674219152315)
        ·
          refine ⟨2453501886442011328728473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635667924294674219152315 2453501886442011328728473)
          ·
            refine ⟨1840126414831508496546355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2453501886442011328728473 1840126414831508496546355)
            ·
              refine ⟨2760189622247262744819533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840126414831508496546355 2760189622247262744819533)
              ·
                refine ⟨1035071108342723529307325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2760189622247262744819533 1035071108342723529307325)
                ·
                  refine ⟨388151665628521323490247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035071108342723529307325 388151665628521323490247)
                  ·
                    rfl

theorem cell20_850413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_850413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850413 prefixEnd_850413 := by exact prefixLift 850413
  have htrace : WordTrace (prefixWord ++ tailWord_850413) baseStart_850413 baseEnd_850413 := by
    simpa [prefixWord, tailWord_850413, baseEnd_850413] using wordTrace_append hprefix tailTrace_850413
  have hstable : (prefixWord ++ tailWord_850413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850413).length < 2 ^ (prefixWord ++ tailWord_850413).sum := by decide
  have hdescent : baseEnd_850413 < baseStart_850413 := by decide
  rcases family_descends (prefixWord ++ tailWord_850413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850424 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_850424 : Nat := 118140960795 + 850424 * 2 ^ 59
def prefixEnd_850424 : Nat := 4983230072969 + 3 ^ 40 * 850424 * 2
def baseEnd_850424 : Nat := 388156686328254174123535

theorem tailTrace_850424 : CollatzResearch.WordTrace tailWord_850424 prefixEnd_850424 388156686328254174123535 := by
  unfold tailWord_850424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15508755735533281850547163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20678340980711042467396217 15508755735533281850547163)
  ·
    refine ⟨23263133603299922775820745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15508755735533281850547163 23263133603299922775820745)
    ·
      refine ⟨17447350202474942081865559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23263133603299922775820745 17447350202474942081865559)
      ·
        refine ⟨26171025303712413122798339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17447350202474942081865559 26171025303712413122798339)
        ·
          refine ⟨39256537955568619684197509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26171025303712413122798339 39256537955568619684197509)
          ·
            refine ⟨7360600866669116190787033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39256537955568619684197509 7360600866669116190787033)
            ·
              refine ⟨5520450650001837143090275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360600866669116190787033 5520450650001837143090275)
              ·
                refine ⟨8280675975002755714635413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520450650001837143090275 8280675975002755714635413)
                ·
                  refine ⟨388156686328254174123535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8280675975002755714635413 388156686328254174123535)
                  ·
                    rfl

theorem cell20_850424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_850424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850424 prefixEnd_850424 := by exact prefixLift 850424
  have htrace : WordTrace (prefixWord ++ tailWord_850424) baseStart_850424 baseEnd_850424 := by
    simpa [prefixWord, tailWord_850424, baseEnd_850424] using wordTrace_append hprefix tailTrace_850424
  have hstable : (prefixWord ++ tailWord_850424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850424).length < 2 ^ (prefixWord ++ tailWord_850424).sum := by decide
  have hdescent : baseEnd_850424 < baseStart_850424 := by decide
  rcases family_descends (prefixWord ++ tailWord_850424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850431 : List Nat := [1, 1, 2, 2, 1, 2, 3, 8]
def baseStart_850431 : Nat := 118140960795 + 850431 * 2 ^ 59
def prefixEnd_850431 : Nat := 4983230072969 + 3 ^ 40 * 850431 * 2
def baseEnd_850431 : Nat := 129386627106331086963391

theorem tailTrace_850431 : CollatzResearch.WordTrace tailWord_850431 prefixEnd_850431 129386627106331086963391 := by
  unfold tailWord_850431
  simp only [CollatzResearch.WordTrace]
  refine ⟨31017766782041203896599147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20678511188027469264399431 31017766782041203896599147)
  ·
    refine ⟨46526650173061805844898721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31017766782041203896599147 46526650173061805844898721)
    ·
      refine ⟨34894987629796354383674041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46526650173061805844898721 34894987629796354383674041)
      ·
        refine ⟨26171240722347265787755531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34894987629796354383674041 26171240722347265787755531)
        ·
          refine ⟨39256861083520898681633297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26171240722347265787755531 39256861083520898681633297)
          ·
            refine ⟨29442645812640674011224973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39256861083520898681633297 29442645812640674011224973)
            ·
              refine ⟨11040992179740252754209365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29442645812640674011224973 11040992179740252754209365)
              ·
                refine ⟨129386627106331086963391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11040992179740252754209365 129386627106331086963391)
                ·
                  rfl

theorem cell20_850431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_850431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850431 prefixEnd_850431 := by exact prefixLift 850431
  have htrace : WordTrace (prefixWord ++ tailWord_850431) baseStart_850431 baseEnd_850431 := by
    simpa [prefixWord, tailWord_850431, baseEnd_850431] using wordTrace_append hprefix tailTrace_850431
  have hstable : (prefixWord ++ tailWord_850431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850431).length < 2 ^ (prefixWord ++ tailWord_850431).sum := by decide
  have hdescent : baseEnd_850431 < baseStart_850431 := by decide
  rcases family_descends (prefixWord ++ tailWord_850431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850510 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_850510 : Nat := 118140960795 + 850510 * 2 ^ 59
def prefixEnd_850510 : Nat := 4983230072969 + 3 ^ 40 * 850510 * 2
def baseEnd_850510 : Nat := 388195939071620097256517

theorem tailTrace_850510 : CollatzResearch.WordTrace tailWord_850510 prefixEnd_850510 388195939071620097256517 := by
  unfold tailWord_850510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877581018594375048590623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20680432099170000259149989 3877581018594375048590623)
  ·
    refine ⟨5816371527891562572885935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3877581018594375048590623 5816371527891562572885935)
    ·
      refine ⟨8724557291837343859328903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5816371527891562572885935 8724557291837343859328903)
      ·
        refine ⟨13086835937756015788993355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8724557291837343859328903 13086835937756015788993355)
        ·
          refine ⟨19630253906634023683490033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086835937756015788993355 19630253906634023683490033)
          ·
            refine ⟨14722690429975517762617525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19630253906634023683490033 14722690429975517762617525)
            ·
              refine ⟨1380252227810204790245393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14722690429975517762617525 1380252227810204790245393)
              ·
                refine ⟨1035189170857653592684045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380252227810204790245393 1035189170857653592684045)
                ·
                  refine ⟨388195939071620097256517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035189170857653592684045 388195939071620097256517)
                  ·
                    rfl

theorem cell20_850510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_850510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850510 prefixEnd_850510 := by exact prefixLift 850510
  have htrace : WordTrace (prefixWord ++ tailWord_850510) baseStart_850510 baseEnd_850510 := by
    simpa [prefixWord, tailWord_850510, baseEnd_850510] using wordTrace_append hprefix tailTrace_850510
  have hstable : (prefixWord ++ tailWord_850510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850510).length < 2 ^ (prefixWord ++ tailWord_850510).sum := by decide
  have hdescent : baseEnd_850510 < baseStart_850510 := by decide
  rcases family_descends (prefixWord ++ tailWord_850510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850541 : List Nat := [1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_850541 : Nat := 118140960795 + 850541 * 2 ^ 59
def prefixEnd_850541 : Nat := 4983230072969 + 3 ^ 40 * 850541 * 2
def baseEnd_850541 : Nat := 129403362772107255741019

theorem tailTrace_850541 : CollatzResearch.WordTrace tailWord_850541 prefixEnd_850541 129403362772107255741019 := by
  unfold tailWord_850541
  simp only [CollatzResearch.WordTrace]
  refine ⟨31021778811642692683103477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20681185874428461788735651 31021778811642692683103477)
  ·
    refine ⟨2908291763591502439040951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31021778811642692683103477 2908291763591502439040951)
    ·
      refine ⟨4362437645387253658561427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908291763591502439040951 4362437645387253658561427)
      ·
        refine ⟨6543656468080880487842141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4362437645387253658561427 6543656468080880487842141)
        ·
          refine ⟨2453871175530330182940803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6543656468080880487842141 2453871175530330182940803)
          ·
            refine ⟨3680806763295495274411205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453871175530330182940803 3680806763295495274411205)
            ·
              refine ⟨690151268117905363952101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3680806763295495274411205 690151268117905363952101)
              ·
                refine ⟨129403362772107255741019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 690151268117905363952101 129403362772107255741019)
                ·
                  rfl

theorem cell20_850541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_850541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850541 prefixEnd_850541 := by exact prefixLift 850541
  have htrace : WordTrace (prefixWord ++ tailWord_850541) baseStart_850541 baseEnd_850541 := by
    simpa [prefixWord, tailWord_850541, baseEnd_850541] using wordTrace_append hprefix tailTrace_850541
  have hstable : (prefixWord ++ tailWord_850541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850541).length < 2 ^ (prefixWord ++ tailWord_850541).sum := by decide
  have hdescent : baseEnd_850541 < baseStart_850541 := by decide
  rcases family_descends (prefixWord ++ tailWord_850541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850555 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 2]
def baseStart_850555 : Nat := 118140960795 + 850555 * 2 ^ 59
def prefixEnd_850555 : Nat := 4983230072969 + 3 ^ 40 * 850555 * 2
def baseEnd_850555 : Nat := 388216478297799940756333

theorem tailTrace_850555 : CollatzResearch.WordTrace tailWord_850555 prefixEnd_850555 388216478297799940756333 := by
  unfold tailWord_850555
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022289433591973074113119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20681526289061315382742079 31022289433591973074113119)
  ·
    refine ⟨46533434150387959611169679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31022289433591973074113119 46533434150387959611169679)
    ·
      refine ⟨69800151225581939416754519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46533434150387959611169679 69800151225581939416754519)
      ·
        refine ⟨104700226838372909125131779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69800151225581939416754519 104700226838372909125131779)
        ·
          refine ⟨157050340257559363687697669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104700226838372909125131779 157050340257559363687697669)
          ·
            refine ⟨29446938798292380691443313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157050340257559363687697669 29446938798292380691443313)
            ·
              refine ⟨22085204098719285518582485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29446938798292380691443313 22085204098719285518582485)
              ·
                refine ⟨517621971063733254341777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22085204098719285518582485 517621971063733254341777)
                ·
                  refine ⟨388216478297799940756333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517621971063733254341777 388216478297799940756333)
                  ·
                    rfl

theorem cell20_850555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 2].length) (baseStart_850555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850555 prefixEnd_850555 := by exact prefixLift 850555
  have htrace : WordTrace (prefixWord ++ tailWord_850555) baseStart_850555 baseEnd_850555 := by
    simpa [prefixWord, tailWord_850555, baseEnd_850555] using wordTrace_append hprefix tailTrace_850555
  have hstable : (prefixWord ++ tailWord_850555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850555).length < 2 ^ (prefixWord ++ tailWord_850555).sum := by decide
  have hdescent : baseEnd_850555 < baseStart_850555 := by decide
  rcases family_descends (prefixWord ++ tailWord_850555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850569 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_850569 : Nat := 118140960795 + 850569 * 2 ^ 59
def prefixEnd_850569 : Nat := 4983230072969 + 3 ^ 40 * 850569 * 2
def baseEnd_850569 : Nat := 388222868279278114289609

theorem tailTrace_850569 : CollatzResearch.WordTrace tailWord_850569 prefixEnd_850569 388222868279278114289609 := by
  unfold tailWord_850569
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022800055541253465122761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20681866703694168976748507 31022800055541253465122761)
  ·
    refine ⟨23267100041655940098842071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31022800055541253465122761 23267100041655940098842071)
    ·
      refine ⟨34900650062483910148263107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23267100041655940098842071 34900650062483910148263107)
      ·
        refine ⟨52350975093725865222394661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34900650062483910148263107 52350975093725865222394661)
        ·
          refine ⟨9815807830073599729198999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52350975093725865222394661 9815807830073599729198999)
          ·
            refine ⟨14723711745110399593798499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815807830073599729198999 14723711745110399593798499)
            ·
              refine ⟨22085567617665599390697749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723711745110399593798499 22085567617665599390697749)
              ·
                refine ⟨1035260982078074971438957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22085567617665599390697749 1035260982078074971438957)
                ·
                  refine ⟨388222868279278114289609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035260982078074971438957 388222868279278114289609)
                  ·
                    rfl

theorem cell20_850569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_850569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850569 prefixEnd_850569 := by exact prefixLift 850569
  have htrace : WordTrace (prefixWord ++ tailWord_850569) baseStart_850569 baseEnd_850569 := by
    simpa [prefixWord, tailWord_850569, baseEnd_850569] using wordTrace_append hprefix tailTrace_850569
  have hstable : (prefixWord ++ tailWord_850569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850569).length < 2 ^ (prefixWord ++ tailWord_850569).sum := by decide
  have hdescent : baseEnd_850569 < baseStart_850569 := by decide
  rcases family_descends (prefixWord ++ tailWord_850569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850621 : List Nat := [1, 4, 1, 2, 1, 11]
def baseStart_850621 : Nat := 118140960795 + 850621 * 2 ^ 59
def prefixEnd_850621 : Nat := 4983230072969 + 3 ^ 40 * 850621 * 2
def baseEnd_850621 : Nat := 14379503796155446094669

theorem tailTrace_850621 : CollatzResearch.WordTrace tailWord_850621 prefixEnd_850621 14379503796155446094669 := by
  unfold tailWord_850621
  simp only [CollatzResearch.WordTrace]
  refine ⟨31024696651352866346015717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20683131100901910897343811 31024696651352866346015717)
  ·
    refine ⟨5817130622128662439877947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31024696651352866346015717 5817130622128662439877947)
    ·
      refine ⟨8725695933192993659816921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817130622128662439877947 8725695933192993659816921)
      ·
        refine ⟨6544271949894745244862691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8725695933192993659816921 6544271949894745244862691)
        ·
          refine ⟨9816407924842117867294037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544271949894745244862691 9816407924842117867294037)
          ·
            refine ⟨14379503796155446094669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9816407924842117867294037 14379503796155446094669)
            ·
              rfl

theorem cell20_850621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 11].length) (baseStart_850621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850621 prefixEnd_850621 := by exact prefixLift 850621
  have htrace : WordTrace (prefixWord ++ tailWord_850621) baseStart_850621 baseEnd_850621 := by
    simpa [prefixWord, tailWord_850621, baseEnd_850621] using wordTrace_append hprefix tailTrace_850621
  have hstable : (prefixWord ++ tailWord_850621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850621).length < 2 ^ (prefixWord ++ tailWord_850621).sum := by decide
  have hdescent : baseEnd_850621 < baseStart_850621 := by decide
  rcases family_descends (prefixWord ++ tailWord_850621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850624 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_850624 : Nat := 118140960795 + 850624 * 2 ^ 59
def prefixEnd_850624 : Nat := 4983230072969 + 3 ^ 40 * 850624 * 2
def baseEnd_850624 : Nat := 388247971777942367456051

theorem tailTrace_850624 : CollatzResearch.WordTrace tailWord_850624 prefixEnd_850624 388247971777942367456051 := by
  unfold tailWord_850624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512403035170998929187463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20683204046894665238916617 15512403035170998929187463)
  ·
    refine ⟨23268604552756498393781195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15512403035170998929187463 23268604552756498393781195)
    ·
      refine ⟨34902906829134747590671793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23268604552756498393781195 34902906829134747590671793)
      ·
        refine ⟨26177180121851060693003845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34902906829134747590671793 26177180121851060693003845)
        ·
          refine ⟨4908221272847073879938221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26177180121851060693003845 4908221272847073879938221)
          ·
            refine ⟨1840582977317652704976833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4908221272847073879938221 1840582977317652704976833)
            ·
              refine ⟨1380437232988239528732625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840582977317652704976833 1380437232988239528732625)
              ·
                refine ⟨1035327924741179646549469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380437232988239528732625 1035327924741179646549469)
                ·
                  refine ⟨388247971777942367456051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035327924741179646549469 388247971777942367456051)
                  ·
                    rfl

theorem cell20_850624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_850624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850624 prefixEnd_850624 := by exact prefixLift 850624
  have htrace : WordTrace (prefixWord ++ tailWord_850624) baseStart_850624 baseEnd_850624 := by
    simpa [prefixWord, tailWord_850624, baseEnd_850624] using wordTrace_append hprefix tailTrace_850624
  have hstable : (prefixWord ++ tailWord_850624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850624).length < 2 ^ (prefixWord ++ tailWord_850624).sum := by decide
  have hdescent : baseEnd_850624 < baseStart_850624 := by decide
  rcases family_descends (prefixWord ++ tailWord_850624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850630 : List Nat := [6, 1, 2, 1, 3, 1, 1, 5]
def baseStart_850630 : Nat := 118140960795 + 850630 * 2 ^ 59
def prefixEnd_850630 : Nat := 4983230072969 + 3 ^ 40 * 850630 * 2
def baseEnd_850630 : Nat := 129416903447144337752009

theorem tailTrace_850630 : CollatzResearch.WordTrace tailWord_850630 prefixEnd_850630 129416903447144337752009 := by
  unfold tailWord_850630
  simp only [CollatzResearch.WordTrace]
  refine ⟨969532028385008152596667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20683349938880173922062229 969532028385008152596667)
  ·
    refine ⟨1454298042577512228895001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969532028385008152596667 1454298042577512228895001)
    ·
      refine ⟨1090723531933134171671251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454298042577512228895001 1090723531933134171671251)
      ·
        refine ⟨1636085297899701257506877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090723531933134171671251 1636085297899701257506877)
        ·
          refine ⟨613531986712387971565079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1636085297899701257506877 613531986712387971565079)
          ·
            refine ⟨920297980068581957347619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613531986712387971565079 920297980068581957347619)
            ·
              refine ⟨1380446970102872936021429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920297980068581957347619 1380446970102872936021429)
              ·
                refine ⟨129416903447144337752009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380446970102872936021429 129416903447144337752009)
                ·
                  rfl

theorem cell20_850630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_850630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850630 prefixEnd_850630 := by exact prefixLift 850630
  have htrace : WordTrace (prefixWord ++ tailWord_850630) baseStart_850630 baseEnd_850630 := by
    simpa [prefixWord, tailWord_850630, baseEnd_850630] using wordTrace_append hprefix tailTrace_850630
  have hstable : (prefixWord ++ tailWord_850630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850630).length < 2 ^ (prefixWord ++ tailWord_850630).sum := by decide
  have hdescent : baseEnd_850630 < baseStart_850630 := by decide
  rcases family_descends (prefixWord ++ tailWord_850630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850638 : List Nat := [4, 1, 1, 1, 3, 2, 3, 5]
def baseStart_850638 : Nat := 118140960795 + 850638 * 2 ^ 59
def prefixEnd_850638 : Nat := 4983230072969 + 3 ^ 40 * 850638 * 2
def baseEnd_850638 : Nat := 129418120586473513663109

theorem tailTrace_850638 : CollatzResearch.WordTrace tailWord_850638 prefixEnd_850638 129418120586473513663109 := by
  unfold tailWord_850638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878164586536409781173071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20683544461527518832923045 3878164586536409781173071)
  ·
    refine ⟨5817246879804614671759607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3878164586536409781173071 5817246879804614671759607)
    ·
      refine ⟨8725870319706922007639411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817246879804614671759607 8725870319706922007639411)
      ·
        refine ⟨13088805479560383011459117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725870319706922007639411 13088805479560383011459117)
        ·
          refine ⟨4908302054835143629297169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13088805479560383011459117 4908302054835143629297169)
          ·
            refine ⟨3681226541126357721972877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4908302054835143629297169 3681226541126357721972877)
            ·
              refine ⟨1380459952922384145739829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3681226541126357721972877 1380459952922384145739829)
              ·
                refine ⟨129418120586473513663109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380459952922384145739829 129418120586473513663109)
                ·
                  rfl

theorem cell20_850638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_850638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850638 prefixEnd_850638 := by exact prefixLift 850638
  have htrace : WordTrace (prefixWord ++ tailWord_850638) baseStart_850638 baseEnd_850638 := by
    simpa [prefixWord, tailWord_850638, baseEnd_850638] using wordTrace_append hprefix tailTrace_850638
  have hstable : (prefixWord ++ tailWord_850638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850638).length < 2 ^ (prefixWord ++ tailWord_850638).sum := by decide
  have hdescent : baseEnd_850638 < baseStart_850638 := by decide
  rcases family_descends (prefixWord ++ tailWord_850638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850686 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_850686 : Nat := 118140960795 + 850686 * 2 ^ 59
def prefixEnd_850686 : Nat := 4983230072969 + 3 ^ 40 * 850686 * 2
def baseEnd_850686 : Nat := 388276270267345707389131

theorem tailTrace_850686 : CollatzResearch.WordTrace tailWord_850686 prefixEnd_850686 388276270267345707389131 := by
  unfold tailWord_850686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878383424514672805891489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20684711597411588298087941 3878383424514672805891489)
  ·
    refine ⟨2908787568386004604418617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3878383424514672805891489 2908787568386004604418617)
    ·
      refine ⟨2181590676289503453313963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2908787568386004604418617 2181590676289503453313963)
      ·
        refine ⟨3272386014434255179970945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181590676289503453313963 3272386014434255179970945)
        ·
          refine ⟨2454289510825691384978209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272386014434255179970945 2454289510825691384978209)
          ·
            refine ⟨1840717133119268538733657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454289510825691384978209 1840717133119268538733657)
            ·
              refine ⟨1380537849839451404050243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1840717133119268538733657 1380537849839451404050243)
              ·
                refine ⟨2070806774759177106075365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380537849839451404050243 2070806774759177106075365)
                ·
                  refine ⟨388276270267345707389131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070806774759177106075365 388276270267345707389131)
                  ·
                    rfl

theorem cell20_850686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_850686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850686 prefixEnd_850686 := by exact prefixLift 850686
  have htrace : WordTrace (prefixWord ++ tailWord_850686) baseStart_850686 baseEnd_850686 := by
    simpa [prefixWord, tailWord_850686, baseEnd_850686] using wordTrace_append hprefix tailTrace_850686
  have hstable : (prefixWord ++ tailWord_850686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850686).length < 2 ^ (prefixWord ++ tailWord_850686).sum := by decide
  have hdescent : baseEnd_850686 < baseStart_850686 := by decide
  rcases family_descends (prefixWord ++ tailWord_850686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850741 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 2]
def baseStart_850741 : Nat := 118140960795 + 850741 * 2 ^ 59
def prefixEnd_850741 : Nat := 4983230072969 + 3 ^ 40 * 850741 * 2
def baseEnd_850741 : Nat := 388301373766009960555573

theorem tailTrace_850741 : CollatzResearch.WordTrace tailWord_850741 prefixEnd_850741 388301373766009960555573 := by
  unfold tailWord_850741
  simp only [CollatzResearch.WordTrace]
  refine ⟨31029073410918126840384077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20686048940612084560256051 31029073410918126840384077)
  ·
    refine ⟨11635902529094297565144029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31029073410918126840384077 11635902529094297565144029)
    ·
      refine ⟨4363463448410361586929011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11635902529094297565144029 4363463448410361586929011)
      ·
        refine ⟨6545195172615542380393517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363463448410361586929011 6545195172615542380393517)
        ·
          refine ⟨2454448189730828392647569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6545195172615542380393517 2454448189730828392647569)
          ·
            refine ⟨1840836142298121294485677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454448189730828392647569 1840836142298121294485677)
            ·
              refine ⟨690313553361795485432129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1840836142298121294485677 690313553361795485432129)
              ·
                refine ⟨517735165021346614074097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690313553361795485432129 517735165021346614074097)
                ·
                  refine ⟨388301373766009960555573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517735165021346614074097 388301373766009960555573)
                  ·
                    rfl

theorem cell20_850741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_850741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850741 prefixEnd_850741 := by exact prefixLift 850741
  have htrace : WordTrace (prefixWord ++ tailWord_850741) baseStart_850741 baseEnd_850741 := by
    simpa [prefixWord, tailWord_850741, baseEnd_850741] using wordTrace_append hprefix tailTrace_850741
  have hstable : (prefixWord ++ tailWord_850741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850741).length < 2 ^ (prefixWord ++ tailWord_850741).sum := by decide
  have hdescent : baseEnd_850741 < baseStart_850741 := by decide
  rcases family_descends (prefixWord ++ tailWord_850741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850766 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_850766 : Nat := 118140960795 + 850766 * 2 ^ 59
def prefixEnd_850766 : Nat := 4983230072969 + 3 ^ 40 * 850766 * 2
def baseEnd_850766 : Nat := 388312784447220984722137

theorem tailTrace_850766 : CollatzResearch.WordTrace tailWord_850766 prefixEnd_850766 388312784447220984722137 := by
  unfold tailWord_850766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878748154478444513755519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20686656823885037406696101 3878748154478444513755519)
  ·
    refine ⟨5818122231717666770633279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3878748154478444513755519 5818122231717666770633279)
    ·
      refine ⟨8727183347576500155949919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5818122231717666770633279 8727183347576500155949919)
      ·
        refine ⟨13090775021364750233924879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8727183347576500155949919 13090775021364750233924879)
        ·
          refine ⟨19636162532047125350887319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13090775021364750233924879 19636162532047125350887319)
          ·
            refine ⟨29454243798070688026330979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19636162532047125350887319 29454243798070688026330979)
            ·
              refine ⟨44181365697106032039496469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29454243798070688026330979 44181365697106032039496469)
              ·
                refine ⟨2071001517051845251851397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44181365697106032039496469 2071001517051845251851397)
                ·
                  refine ⟨388312784447220984722137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071001517051845251851397 388312784447220984722137)
                  ·
                    rfl

theorem cell20_850766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_850766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850766 prefixEnd_850766 := by exact prefixLift 850766
  have htrace : WordTrace (prefixWord ++ tailWord_850766) baseStart_850766 baseEnd_850766 := by
    simpa [prefixWord, tailWord_850766, baseEnd_850766] using wordTrace_append hprefix tailTrace_850766
  have hstable : (prefixWord ++ tailWord_850766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850766).length < 2 ^ (prefixWord ++ tailWord_850766).sum := by decide
  have hdescent : baseEnd_850766 < baseStart_850766 := by decide
  rcases family_descends (prefixWord ++ tailWord_850766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850773 : List Nat := [1, 3, 2, 2, 2, 1, 1, 8]
def baseStart_850773 : Nat := 118140960795 + 850773 * 2 ^ 59
def prefixEnd_850773 : Nat := 4983230072969 + 3 ^ 40 * 850773 * 2
def baseEnd_850773 : Nat := 129438659812653357162925

theorem tailTrace_850773 : CollatzResearch.WordTrace tailWord_850773 prefixEnd_850773 129438659812653357162925 := by
  unfold tailWord_850773
  simp only [CollatzResearch.WordTrace]
  refine ⟨31030240546802196305548973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20686827031201464203699315 31030240546802196305548973)
  ·
    refine ⟨11636340205050823614580865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31030240546802196305548973 11636340205050823614580865)
    ·
      refine ⟨8727255153788117710935649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11636340205050823614580865 8727255153788117710935649)
      ·
        refine ⟨6545441365341088283201737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8727255153788117710935649 6545441365341088283201737)
        ·
          refine ⟨4909081024005816212401303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545441365341088283201737 4909081024005816212401303)
          ·
            refine ⟨7363621536008724318601955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909081024005816212401303 7363621536008724318601955)
            ·
              refine ⟨11045432304013086477902933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363621536008724318601955 11045432304013086477902933)
              ·
                refine ⟨129438659812653357162925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11045432304013086477902933 129438659812653357162925)
                ·
                  rfl

theorem cell20_850773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_850773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850773 prefixEnd_850773 := by exact prefixLift 850773
  have htrace : WordTrace (prefixWord ++ tailWord_850773) baseStart_850773 baseEnd_850773 := by
    simpa [prefixWord, tailWord_850773, baseEnd_850773] using wordTrace_append hprefix tailTrace_850773
  have hstable : (prefixWord ++ tailWord_850773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850773).length < 2 ^ (prefixWord ++ tailWord_850773).sum := by decide
  have hdescent : baseEnd_850773 < baseStart_850773 := by decide
  rcases family_descends (prefixWord ++ tailWord_850773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850783 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 2]
def baseStart_850783 : Nat := 118140960795 + 850783 * 2 ^ 59
def prefixEnd_850783 : Nat := 4983230072969 + 3 ^ 40 * 850783 * 2
def baseEnd_850783 : Nat := 388320543710444481155401

theorem tailTrace_850783 : CollatzResearch.WordTrace tailWord_850783 prefixEnd_850783 388320543710444481155401 := by
  unfold tailWord_850783
  simp only [CollatzResearch.WordTrace]
  refine ⟨31030605276765968013413003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20687070184510645342275335 31030605276765968013413003)
  ·
    refine ⟨46545907915148952020119505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31030605276765968013413003 46545907915148952020119505)
    ·
      refine ⟨34909430936361714015089629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46545907915148952020119505 34909430936361714015089629)
      ·
        refine ⟨13091036601135642755658611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34909430936361714015089629 13091036601135642755658611)
        ·
          refine ⟨19636554901703464133487917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13091036601135642755658611 19636554901703464133487917)
          ·
            refine ⟨7363708088138799050057969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19636554901703464133487917 7363708088138799050057969)
            ·
              refine ⟨5522781066104099287543477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7363708088138799050057969 5522781066104099287543477)
              ·
                refine ⟨517760724947259308207201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5522781066104099287543477 517760724947259308207201)
                ·
                  refine ⟨388320543710444481155401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517760724947259308207201 388320543710444481155401)
                  ·
                    rfl

theorem cell20_850783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 2].length) (baseStart_850783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850783 prefixEnd_850783 := by exact prefixLift 850783
  have htrace : WordTrace (prefixWord ++ tailWord_850783) baseStart_850783 baseEnd_850783 := by
    simpa [prefixWord, tailWord_850783, baseEnd_850783] using wordTrace_append hprefix tailTrace_850783
  have hstable : (prefixWord ++ tailWord_850783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850783).length < 2 ^ (prefixWord ++ tailWord_850783).sum := by decide
  have hdescent : baseEnd_850783 < baseStart_850783 := by decide
  rcases family_descends (prefixWord ++ tailWord_850783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850800 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_850800 : Nat := 118140960795 + 850800 * 2 ^ 59
def prefixEnd_850800 : Nat := 4983230072969 + 3 ^ 40 * 850800 * 2
def baseEnd_850800 : Nat := 388328302973667977588665

theorem tailTrace_850800 : CollatzResearch.WordTrace tailWord_850800 prefixEnd_850800 388328302973667977588665 := by
  unfold tailWord_850800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515612658852189958390927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20687483545136253277854569 15515612658852189958390927)
  ·
    refine ⟨23273418988278284937586391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15515612658852189958390927 23273418988278284937586391)
    ·
      refine ⟨34910128482417427406379587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23273418988278284937586391 34910128482417427406379587)
      ·
        refine ⟨52365192723626141109569381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34910128482417427406379587 52365192723626141109569381)
        ·
          refine ⟨9818473635679901458044259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52365192723626141109569381 9818473635679901458044259)
          ·
            refine ⟨14727710453519852187066389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818473635679901458044259 14727710453519852187066389)
            ·
              refine ⟨690361427508743071268737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14727710453519852187066389 690361427508743071268737)
              ·
                refine ⟨517771070631557303451553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690361427508743071268737 517771070631557303451553)
                ·
                  refine ⟨388328302973667977588665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517771070631557303451553 388328302973667977588665)
                  ·
                    rfl

theorem cell20_850800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_850800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850800 prefixEnd_850800 := by exact prefixLift 850800
  have htrace : WordTrace (prefixWord ++ tailWord_850800) baseStart_850800 baseEnd_850800 := by
    simpa [prefixWord, tailWord_850800, baseEnd_850800] using wordTrace_append hprefix tailTrace_850800
  have hstable : (prefixWord ++ tailWord_850800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850800).length < 2 ^ (prefixWord ++ tailWord_850800).sum := by decide
  have hdescent : baseEnd_850800 < baseStart_850800 := by decide
  rcases family_descends (prefixWord ++ tailWord_850800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850811 : List Nat := [1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_850811 : Nat := 118140960795 + 850811 * 2 ^ 59
def prefixEnd_850811 : Nat := 4983230072969 + 3 ^ 40 * 850811 * 2
def baseEnd_850811 : Nat := 129444441224466942740651

theorem tailTrace_850811 : CollatzResearch.WordTrace tailWord_850811 prefixEnd_850811 129444441224466942740651 := by
  unfold tailWord_850811
  simp only [CollatzResearch.WordTrace]
  refine ⟨31031626520664528795432287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20687751013776352530288191 31031626520664528795432287)
  ·
    refine ⟨46547439780996793193148431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31031626520664528795432287 46547439780996793193148431)
    ·
      refine ⟨69821159671495189789722647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46547439780996793193148431 69821159671495189789722647)
      ·
        refine ⟨104731739507242784684583971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69821159671495189789722647 104731739507242784684583971)
        ·
          refine ⟨157097609260864177026875957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104731739507242784684583971 157097609260864177026875957)
          ·
            refine ⟨14727900868206016596269621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157097609260864177026875957 14727900868206016596269621)
            ·
              refine ⟨1380740706394314055900277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14727900868206016596269621 1380740706394314055900277)
              ·
                refine ⟨129444441224466942740651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380740706394314055900277 129444441224466942740651)
                ·
                  rfl

theorem cell20_850811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_850811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850811 prefixEnd_850811 := by exact prefixLift 850811
  have htrace : WordTrace (prefixWord ++ tailWord_850811) baseStart_850811 baseEnd_850811 := by
    simpa [prefixWord, tailWord_850811, baseEnd_850811] using wordTrace_append hprefix tailTrace_850811
  have hstable : (prefixWord ++ tailWord_850811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850811).length < 2 ^ (prefixWord ++ tailWord_850811).sum := by decide
  have hdescent : baseEnd_850811 < baseStart_850811 := by decide
  rcases family_descends (prefixWord ++ tailWord_850811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850880 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_850880 : Nat := 118140960795 + 850880 * 2 ^ 59
def prefixEnd_850880 : Nat := 4983230072969 + 3 ^ 40 * 850880 * 2
def baseEnd_850880 : Nat := 388364817153543254921671

theorem tailTrace_850880 : CollatzResearch.WordTrace tailWord_850880 prefixEnd_850880 388364817153543254921671 := by
  unfold tailWord_850880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15517071578707276789847047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20689428771609702386462729 15517071578707276789847047)
  ·
    refine ⟨23275607368060915184770571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15517071578707276789847047 23275607368060915184770571)
    ·
      refine ⟨34913411052091372777155857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275607368060915184770571 34913411052091372777155857)
      ·
        refine ⟨26185058289068529582866893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34913411052091372777155857 26185058289068529582866893)
        ·
          refine ⟨9819396858400698593575085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26185058289068529582866893 9819396858400698593575085)
          ·
            refine ⟨3682273821900261972590657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9819396858400698593575085 3682273821900261972590657)
            ·
              refine ⟨2761705366425196479442993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3682273821900261972590657 2761705366425196479442993)
              ·
                refine ⟨2071279024818897359582245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2761705366425196479442993 2071279024818897359582245)
                ·
                  refine ⟨388364817153543254921671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071279024818897359582245 388364817153543254921671)
                  ·
                    rfl

theorem cell20_850880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_850880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850880 prefixEnd_850880 := by exact prefixLift 850880
  have htrace : WordTrace (prefixWord ++ tailWord_850880) baseStart_850880 baseEnd_850880 := by
    simpa [prefixWord, tailWord_850880, baseEnd_850880] using wordTrace_append hprefix tailTrace_850880
  have hstable : (prefixWord ++ tailWord_850880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850880).length < 2 ^ (prefixWord ++ tailWord_850880).sum := by decide
  have hdescent : baseEnd_850880 < baseStart_850880 := by decide
  rcases family_descends (prefixWord ++ tailWord_850880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850914 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_850914 : Nat := 118140960795 + 850914 * 2 ^ 59
def prefixEnd_850914 : Nat := 4983230072969 + 3 ^ 40 * 850914 * 2
def baseEnd_850914 : Nat := 388380335679990247788199

theorem tailTrace_850914 : CollatzResearch.WordTrace tailWord_850914 prefixEnd_850914 388380335679990247788199 := by
  unfold tailWord_850914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758845809822844346607949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20690255492860918257621197 7758845809822844346607949)
  ·
    refine ⟨2909567178683566629977981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7758845809822844346607949 2909567178683566629977981)
    ·
      refine ⟨1091087692006337486241743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2909567178683566629977981 1091087692006337486241743)
      ·
        refine ⟨1636631538009506229362615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091087692006337486241743 1636631538009506229362615)
        ·
          refine ⟨2454947307014259344043923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636631538009506229362615 2454947307014259344043923)
          ·
            refine ⟨3682420960521389016065885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454947307014259344043923 3682420960521389016065885)
            ·
              refine ⟨1380907860195520881024707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3682420960521389016065885 1380907860195520881024707)
              ·
                refine ⟨2071361790293281321537061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380907860195520881024707 2071361790293281321537061)
                ·
                  refine ⟨388380335679990247788199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071361790293281321537061 388380335679990247788199)
                  ·
                    rfl

theorem cell20_850914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_850914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850914 prefixEnd_850914 := by exact prefixLift 850914
  have htrace : WordTrace (prefixWord ++ tailWord_850914) baseStart_850914 baseEnd_850914 := by
    simpa [prefixWord, tailWord_850914, baseEnd_850914] using wordTrace_append hprefix tailTrace_850914
  have hstable : (prefixWord ++ tailWord_850914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850914).length < 2 ^ (prefixWord ++ tailWord_850914).sum := by decide
  have hdescent : baseEnd_850914 < baseStart_850914 := by decide
  rcases family_descends (prefixWord ++ tailWord_850914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850939 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_850939 : Nat := 118140960795 + 850939 * 2 ^ 59
def prefixEnd_850939 : Nat := 4983230072969 + 3 ^ 40 * 850939 * 2
def baseEnd_850939 : Nat := 388391746361201271954763

theorem tailTrace_850939 : CollatzResearch.WordTrace tailWord_850939 prefixEnd_850939 388391746361201271954763 := by
  unfold tailWord_850939
  simp only [CollatzResearch.WordTrace]
  refine ⟨31036295064200806656091871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20690863376133871104061247 31036295064200806656091871)
  ·
    refine ⟨46554442596301209984137807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31036295064200806656091871 46554442596301209984137807)
    ·
      refine ⟨69831663894451814976206711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46554442596301209984137807 69831663894451814976206711)
      ·
        refine ⟨104747495841677722464310067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69831663894451814976206711 104747495841677722464310067)
        ·
          refine ⟨157121243762516583696465101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104747495841677722464310067 157121243762516583696465101)
          ·
            refine ⟨58920466410943718886174413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157121243762516583696465101 58920466410943718886174413)
            ·
              refine ⟨22095174904103894582315405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58920466410943718886174413 22095174904103894582315405)
              ·
                refine ⟨8285690589038960468368277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22095174904103894582315405 8285690589038960468368277)
                ·
                  refine ⟨388391746361201271954763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285690589038960468368277 388391746361201271954763)
                  ·
                    rfl

theorem cell20_850939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_850939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850939 prefixEnd_850939 := by exact prefixLift 850939
  have htrace : WordTrace (prefixWord ++ tailWord_850939) baseStart_850939 baseEnd_850939 := by
    simpa [prefixWord, tailWord_850939, baseEnd_850939] using wordTrace_append hprefix tailTrace_850939
  have hstable : (prefixWord ++ tailWord_850939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850939).length < 2 ^ (prefixWord ++ tailWord_850939).sum := by decide
  have hdescent : baseEnd_850939 < baseStart_850939 := by decide
  rcases family_descends (prefixWord ++ tailWord_850939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850976 : List Nat := [2, 1, 1, 7, 2, 1, 1, 5]
def baseStart_850976 : Nat := 118140960795 + 850976 * 2 ^ 59
def prefixEnd_850976 : Nat := 4983230072969 + 3 ^ 40 * 850976 * 2
def baseEnd_850976 : Nat := 129469544723131195907093

theorem tailTrace_850976 : CollatzResearch.WordTrace tailWord_850976 prefixEnd_850976 129469544723131195907093 := by
  unfold tailWord_850976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518822282533380987594391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20691763043377841316792521 15518822282533380987594391)
  ·
    refine ⟨23278233423800071481391587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15518822282533380987594391 23278233423800071481391587)
    ·
      refine ⟨34917350135700107222087381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23278233423800071481391587 34917350135700107222087381)
      ·
        refine ⟨818375393805471263017673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34917350135700107222087381 818375393805471263017673)
        ·
          refine ⟨613781545354103447263255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818375393805471263017673 613781545354103447263255)
          ·
            refine ⟨920672318031155170894883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613781545354103447263255 920672318031155170894883)
            ·
              refine ⟨1381008477046732756342325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920672318031155170894883 1381008477046732756342325)
              ·
                refine ⟨129469544723131195907093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1381008477046732756342325 129469544723131195907093)
                ·
                  rfl

theorem cell20_850976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_850976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850976 prefixEnd_850976 := by exact prefixLift 850976
  have htrace : WordTrace (prefixWord ++ tailWord_850976) baseStart_850976 baseEnd_850976 := by
    simpa [prefixWord, tailWord_850976, baseEnd_850976] using wordTrace_append hprefix tailTrace_850976
  have hstable : (prefixWord ++ tailWord_850976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850976).length < 2 ^ (prefixWord ++ tailWord_850976).sum := by decide
  have hdescent : baseEnd_850976 < baseStart_850976 := by decide
  rcases family_descends (prefixWord ++ tailWord_850976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850980 : List Nat := [2, 3, 1, 4, 1, 1, 3, 5]
def baseStart_850980 : Nat := 118140960795 + 850980 * 2 ^ 59
def prefixEnd_850980 : Nat := 4983230072969 + 3 ^ 40 * 850980 * 2
def baseEnd_850980 : Nat := 129470153292795783862643

theorem tailTrace_850980 : CollatzResearch.WordTrace tailWord_850980 prefixEnd_850980 129470153292795783862643 := by
  unfold tailWord_850980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15518895228526135329167197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20691860304701513772222929 15518895228526135329167197)
  ·
    refine ⟨5819585710697300748437699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15518895228526135329167197 5819585710697300748437699)
    ·
      refine ⟨8729378566045951122656549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819585710697300748437699 8729378566045951122656549)
      ·
        refine ⟨1636758481133615835498103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8729378566045951122656549 1636758481133615835498103)
        ·
          refine ⟨2455137721700423753247155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636758481133615835498103 2455137721700423753247155)
          ·
            refine ⟨3682706582550635629870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455137721700423753247155 3682706582550635629870733)
            ·
              refine ⟨1381014968456488361201525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3682706582550635629870733 1381014968456488361201525)
              ·
                refine ⟨129470153292795783862643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1381014968456488361201525 129470153292795783862643)
                ·
                  rfl

theorem cell20_850980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_850980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850980 prefixEnd_850980 := by exact prefixLift 850980
  have htrace : WordTrace (prefixWord ++ tailWord_850980) baseStart_850980 baseEnd_850980 := by
    simpa [prefixWord, tailWord_850980, baseEnd_850980] using wordTrace_append hprefix tailTrace_850980
  have hstable : (prefixWord ++ tailWord_850980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850980).length < 2 ^ (prefixWord ++ tailWord_850980).sum := by decide
  have hdescent : baseEnd_850980 < baseStart_850980 := by decide
  rcases family_descends (prefixWord ++ tailWord_850980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_850994 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_850994 : Nat := 118140960795 + 850994 * 2 ^ 59
def prefixEnd_850994 : Nat := 4983230072969 + 3 ^ 40 * 850994 * 2
def baseEnd_850994 : Nat := 388416849859865525121205

theorem tailTrace_850994 : CollatzResearch.WordTrace tailWord_850994 prefixEnd_850994 388416849859865525121205 := by
  unfold tailWord_850994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759575269750387762336009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20692200719334367366229357 7759575269750387762336009)
  ·
    refine ⟨5819681452312790821752007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7759575269750387762336009 5819681452312790821752007)
    ·
      refine ⟨8729522178469186232628011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819681452312790821752007 8729522178469186232628011)
      ·
        refine ⟨13094283267703779348942017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729522178469186232628011 13094283267703779348942017)
        ·
          refine ⟨9820712450777834511706513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13094283267703779348942017 9820712450777834511706513)
          ·
            refine ⟨7365534338083375883779885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9820712450777834511706513 7365534338083375883779885)
            ·
              refine ⟨2762075376781265956417457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7365534338083375883779885 2762075376781265956417457)
              ·
                refine ⟨2071556532585949467313093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2762075376781265956417457 2071556532585949467313093)
                ·
                  refine ⟨388416849859865525121205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071556532585949467313093 388416849859865525121205)
                  ·
                    rfl

theorem cell20_850994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_850994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_850994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_850994 prefixEnd_850994 := by exact prefixLift 850994
  have htrace : WordTrace (prefixWord ++ tailWord_850994) baseStart_850994 baseEnd_850994 := by
    simpa [prefixWord, tailWord_850994, baseEnd_850994] using wordTrace_append hprefix tailTrace_850994
  have hstable : (prefixWord ++ tailWord_850994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_850994).length < 2 ^ (prefixWord ++ tailWord_850994).sum := by decide
  have hdescent : baseEnd_850994 < baseStart_850994 := by decide
  rcases family_descends (prefixWord ++ tailWord_850994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851008 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_851008 : Nat := 118140960795 + 851008 * 2 ^ 59
def prefixEnd_851008 : Nat := 4983230072969 + 3 ^ 40 * 851008 * 2
def baseEnd_851008 : Nat := 388423239841343698654481

theorem tailTrace_851008 : CollatzResearch.WordTrace tailWord_851008 prefixEnd_851008 388423239841343698654481 := by
  unfold tailWord_851008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15519405850475415720176839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20692541133967220960235785 15519405850475415720176839)
  ·
    refine ⟨23279108775713123580265259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15519405850475415720176839 23279108775713123580265259)
    ·
      refine ⟨34918663163569685370397889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23279108775713123580265259 34918663163569685370397889)
      ·
        refine ⟨26188997372677264027798417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34918663163569685370397889 26188997372677264027798417)
        ·
          refine ⟨19641748029507948020848813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26188997372677264027798417 19641748029507948020848813)
          ·
            refine ⟨7365655511065480507818305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19641748029507948020848813 7365655511065480507818305)
            ·
              refine ⟨5524241633299110380863729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7365655511065480507818305 5524241633299110380863729)
              ·
                refine ⟨4143181224974332785647797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524241633299110380863729 4143181224974332785647797)
                ·
                  refine ⟨388423239841343698654481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4143181224974332785647797 388423239841343698654481)
                  ·
                    rfl

theorem cell20_851008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_851008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851008 prefixEnd_851008 := by exact prefixLift 851008
  have htrace : WordTrace (prefixWord ++ tailWord_851008) baseStart_851008 baseEnd_851008 := by
    simpa [prefixWord, tailWord_851008, baseEnd_851008] using wordTrace_append hprefix tailTrace_851008
  have hstable : (prefixWord ++ tailWord_851008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851008).length < 2 ^ (prefixWord ++ tailWord_851008).sum := by decide
  have hdescent : baseEnd_851008 < baseStart_851008 := by decide
  rcases family_descends (prefixWord ++ tailWord_851008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851011 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 2]
def baseStart_851011 : Nat := 118140960795 + 851011 * 2 ^ 59
def prefixEnd_851011 : Nat := 4983230072969 + 3 ^ 40 * 851011 * 2
def baseEnd_851011 : Nat := 388424609123089021554469

theorem tailTrace_851011 : CollatzResearch.WordTrace tailWord_851011 prefixEnd_851011 388424609123089021554469 := by
  unfold tailWord_851011
  simp only [CollatzResearch.WordTrace]
  refine ⟨31038921119939962952712887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20692614079959975301808591 31038921119939962952712887)
  ·
    refine ⟨46558381679909944429069331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31038921119939962952712887 46558381679909944429069331)
    ·
      refine ⟨69837572519864916643603997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46558381679909944429069331 69837572519864916643603997)
      ·
        refine ⟨26189089694949343741351499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69837572519864916643603997 26189089694949343741351499)
        ·
          refine ⟨39283634542424015612027249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26189089694949343741351499 39283634542424015612027249)
          ·
            refine ⟨29462725906818011709020437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39283634542424015612027249 29462725906818011709020437)
            ·
              refine ⟨1381065276882094298860333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29462725906818011709020437 1381065276882094298860333)
              ·
                refine ⟨517899478830785362072625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381065276882094298860333 517899478830785362072625)
                ·
                  refine ⟨388424609123089021554469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517899478830785362072625 388424609123089021554469)
                  ·
                    rfl

theorem cell20_851011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2].length) (baseStart_851011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851011 prefixEnd_851011 := by exact prefixLift 851011
  have htrace : WordTrace (prefixWord ++ tailWord_851011) baseStart_851011 baseEnd_851011 := by
    simpa [prefixWord, tailWord_851011, baseEnd_851011] using wordTrace_append hprefix tailTrace_851011
  have hstable : (prefixWord ++ tailWord_851011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851011).length < 2 ^ (prefixWord ++ tailWord_851011).sum := by decide
  have hdescent : baseEnd_851011 < baseStart_851011 := by decide
  rcases family_descends (prefixWord ++ tailWord_851011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851021 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_851021 : Nat := 118140960795 + 851021 * 2 ^ 59
def prefixEnd_851021 : Nat := 4983230072969 + 3 ^ 40 * 851021 * 2
def baseEnd_851021 : Nat := 388429173395573431221095

theorem tailTrace_851021 : CollatzResearch.WordTrace tailWord_851021 prefixEnd_851021 388429173395573431221095 := by
  unfold tailWord_851021
  simp only [CollatzResearch.WordTrace]
  refine ⟨31039285849903734660576917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20692857233269156440384611 31039285849903734660576917)
  ·
    refine ⟨1454966524214237562214543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31039285849903734660576917 1454966524214237562214543)
    ·
      refine ⟨2182449786321356343321815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454966524214237562214543 2182449786321356343321815)
      ·
        refine ⟨3273674679482034514982723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182449786321356343321815 3273674679482034514982723)
        ·
          refine ⟨4910512019223051772474085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273674679482034514982723 4910512019223051772474085)
          ·
            refine ⟨920721003604322207338891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4910512019223051772474085 920721003604322207338891)
            ·
              refine ⟨1381081505406483311008337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920721003604322207338891 1381081505406483311008337)
              ·
                refine ⟨1035811129054862483256253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381081505406483311008337 1035811129054862483256253)
                ·
                  refine ⟨388429173395573431221095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035811129054862483256253 388429173395573431221095)
                  ·
                    rfl

theorem cell20_851021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_851021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851021 prefixEnd_851021 := by exact prefixLift 851021
  have htrace : WordTrace (prefixWord ++ tailWord_851021) baseStart_851021 baseEnd_851021 := by
    simpa [prefixWord, tailWord_851021, baseEnd_851021] using wordTrace_append hprefix tailTrace_851021
  have hstable : (prefixWord ++ tailWord_851021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851021).length < 2 ^ (prefixWord ++ tailWord_851021).sum := by decide
  have hdescent : baseEnd_851021 < baseStart_851021 := by decide
  rcases family_descends (prefixWord ++ tailWord_851021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851025 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_851025 : Nat := 118140960795 + 851025 * 2 ^ 59
def prefixEnd_851025 : Nat := 4983230072969 + 3 ^ 40 * 851025 * 2
def baseEnd_851025 : Nat := 388430999104567195087745

theorem tailTrace_851025 : CollatzResearch.WordTrace tailWord_851025 prefixEnd_851025 388430999104567195087745 := by
  unfold tailWord_851025
  simp only [CollatzResearch.WordTrace]
  refine ⟨31039431741889243343722529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20692954494592828895815019 31039431741889243343722529)
  ·
    refine ⟨23279573806416932507791897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31039431741889243343722529 23279573806416932507791897)
    ·
      refine ⟨17459680354812699380843923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23279573806416932507791897 17459680354812699380843923)
      ·
        refine ⟨26189520532219049071265885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17459680354812699380843923 26189520532219049071265885)
        ·
          refine ⟨9821070199582143401724707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26189520532219049071265885 9821070199582143401724707)
          ·
            refine ⟨14731605299373215102587061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9821070199582143401724707 14731605299373215102587061)
            ·
              refine ⟨1381087996816238915867537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14731605299373215102587061 1381087996816238915867537)
              ·
                refine ⟨1035815997612179186900653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381087996816238915867537 1035815997612179186900653)
                ·
                  refine ⟨388430999104567195087745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035815997612179186900653 388430999104567195087745)
                  ·
                    rfl

theorem cell20_851025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_851025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851025 prefixEnd_851025 := by exact prefixLift 851025
  have htrace : WordTrace (prefixWord ++ tailWord_851025) baseStart_851025 baseEnd_851025 := by
    simpa [prefixWord, tailWord_851025, baseEnd_851025] using wordTrace_append hprefix tailTrace_851025
  have hstable : (prefixWord ++ tailWord_851025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851025).length < 2 ^ (prefixWord ++ tailWord_851025).sum := by decide
  have hdescent : baseEnd_851025 < baseStart_851025 := by decide
  rcases family_descends (prefixWord ++ tailWord_851025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851032 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_851032 : Nat := 118140960795 + 851032 * 2 ^ 59
def prefixEnd_851032 : Nat := 4983230072969 + 3 ^ 40 * 851032 * 2
def baseEnd_851032 : Nat := 388434194095306281854383

theorem tailTrace_851032 : CollatzResearch.WordTrace tailWord_851032 prefixEnd_851032 388434194095306281854383 := by
  unfold tailWord_851032
  simp only [CollatzResearch.WordTrace]
  refine ⟨15519843526431941769613675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20693124701909255692818233 15519843526431941769613675)
  ·
    refine ⟨23279765289647912654420513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15519843526431941769613675 23279765289647912654420513)
    ·
      refine ⟨17459823967235934490815385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23279765289647912654420513 17459823967235934490815385)
      ·
        refine ⟨13094867975426950868111539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17459823967235934490815385 13094867975426950868111539)
        ·
          refine ⟨19642301963140426302167309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13094867975426950868111539 19642301963140426302167309)
          ·
            refine ⟨7365863236177659863312741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19642301963140426302167309 7365863236177659863312741)
            ·
              refine ⟨1381099356783311224371139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7365863236177659863312741 1381099356783311224371139)
              ·
                refine ⟨2071649035174966836556709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381099356783311224371139 2071649035174966836556709)
                ·
                  refine ⟨388434194095306281854383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071649035174966836556709 388434194095306281854383)
                  ·
                    rfl

theorem cell20_851032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_851032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851032 prefixEnd_851032 := by exact prefixLift 851032
  have htrace : WordTrace (prefixWord ++ tailWord_851032) baseStart_851032 baseEnd_851032 := by
    simpa [prefixWord, tailWord_851032, baseEnd_851032] using wordTrace_append hprefix tailTrace_851032
  have hstable : (prefixWord ++ tailWord_851032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851032).length < 2 ^ (prefixWord ++ tailWord_851032).sum := by decide
  have hdescent : baseEnd_851032 < baseStart_851032 := by decide
  rcases family_descends (prefixWord ++ tailWord_851032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851101 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_851101 : Nat := 118140960795 + 851101 * 2 ^ 59
def prefixEnd_851101 : Nat := 4983230072969 + 3 ^ 40 * 851101 * 2
def baseEnd_851101 : Nat := 388465687575448708554101

theorem tailTrace_851101 : CollatzResearch.WordTrace tailWord_851101 prefixEnd_851101 388465687575448708554101 := by
  unfold tailWord_851101
  simp only [CollatzResearch.WordTrace]
  refine ⟨31042203689613908323489157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20694802459742605548992771 31042203689613908323489157)
  ·
    refine ⟨5820413191802607810654217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31042203689613908323489157 5820413191802607810654217)
    ·
      refine ⟨4365309893851955857990663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5820413191802607810654217 4365309893851955857990663)
      ·
        refine ⟨6547964840777933786985995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365309893851955857990663 6547964840777933786985995)
        ·
          refine ⟨9821947261166900680478993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547964840777933786985995 9821947261166900680478993)
          ·
            refine ⟨7366460445875175510359245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9821947261166900680478993 7366460445875175510359245)
            ·
              refine ⟨2762422667203190816384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7366460445875175510359245 2762422667203190816384717)
              ·
                refine ⟨1035908500201196556144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2762422667203190816384717 1035908500201196556144269)
                ·
                  refine ⟨388465687575448708554101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035908500201196556144269 388465687575448708554101)
                  ·
                    rfl

theorem cell20_851101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_851101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851101 prefixEnd_851101 := by exact prefixLift 851101
  have htrace : WordTrace (prefixWord ++ tailWord_851101) baseStart_851101 baseEnd_851101 := by
    simpa [prefixWord, tailWord_851101, baseEnd_851101] using wordTrace_append hprefix tailTrace_851101
  have hstable : (prefixWord ++ tailWord_851101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851101).length < 2 ^ (prefixWord ++ tailWord_851101).sum := by decide
  have hdescent : baseEnd_851101 < baseStart_851101 := by decide
  rcases family_descends (prefixWord ++ tailWord_851101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851136 : List Nat := [2, 1, 1, 2, 14]
def baseStart_851136 : Nat := 118140960795 + 851136 * 2 ^ 59
def prefixEnd_851136 : Nat := 4983230072969 + 3 ^ 40 * 851136 * 2
def baseEnd_851136 : Nat := 4796069907767211634411

theorem tailTrace_851136 : CollatzResearch.WordTrace tailWord_851136 prefixEnd_851136 4796069907767211634411 := by
  unfold tailWord_851136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15521740122243554650506631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20695653496324739534008841 15521740122243554650506631)
  ·
    refine ⟨23282610183365331975759947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15521740122243554650506631 23282610183365331975759947)
    ·
      refine ⟨34923915275047997963639921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23282610183365331975759947 34923915275047997963639921)
      ·
        refine ⟨26192936456285998472729941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34923915275047997963639921 26192936456285998472729941)
        ·
          refine ⟨4796069907767211634411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 26192936456285998472729941 4796069907767211634411)
          ·
            rfl

theorem cell20_851136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 14].length) (baseStart_851136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851136 prefixEnd_851136 := by exact prefixLift 851136
  have htrace : WordTrace (prefixWord ++ tailWord_851136) baseStart_851136 baseEnd_851136 := by
    simpa [prefixWord, tailWord_851136, baseEnd_851136] using wordTrace_append hprefix tailTrace_851136
  have hstable : (prefixWord ++ tailWord_851136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851136).length < 2 ^ (prefixWord ++ tailWord_851136).sum := by decide
  have hdescent : baseEnd_851136 < baseStart_851136 := by decide
  rcases family_descends (prefixWord ++ tailWord_851136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851138 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_851138 : Nat := 118140960795 + 851138 * 2 ^ 59
def prefixEnd_851138 : Nat := 4983230072969 + 3 ^ 40 * 851138 * 2
def baseEnd_851138 : Nat := 388482575383641024320617

theorem tailTrace_851138 : CollatzResearch.WordTrace tailWord_851138 prefixEnd_851138 388482575383641024320617 := by
  unfold tailWord_851138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7760888297619965910646517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20695702126986575761724045 7760888297619965910646517)
  ·
    refine ⟨727583277901871804123111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7760888297619965910646517 727583277901871804123111)
    ·
      refine ⟨1091374916852807706184667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727583277901871804123111 1091374916852807706184667)
      ·
        refine ⟨1637062375279211559277001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091374916852807706184667 1637062375279211559277001)
        ·
          refine ⟨1227796781459408669457751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1637062375279211559277001 1227796781459408669457751)
          ·
            refine ⟨1841695172189113004186627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227796781459408669457751 1841695172189113004186627)
            ·
              refine ⟨2762542758283669506279941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841695172189113004186627 2762542758283669506279941)
              ·
                refine ⟨517976767178188032427489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2762542758283669506279941 517976767178188032427489)
                ·
                  refine ⟨388482575383641024320617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517976767178188032427489 388482575383641024320617)
                  ·
                    rfl

theorem cell20_851138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_851138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851138 prefixEnd_851138 := by exact prefixLift 851138
  have htrace : WordTrace (prefixWord ++ tailWord_851138) baseStart_851138 baseEnd_851138 := by
    simpa [prefixWord, tailWord_851138, baseEnd_851138] using wordTrace_append hprefix tailTrace_851138
  have hstable : (prefixWord ++ tailWord_851138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851138).length < 2 ^ (prefixWord ++ tailWord_851138).sum := by decide
  have hdescent : baseEnd_851138 < baseStart_851138 := by decide
  rcases family_descends (prefixWord ++ tailWord_851138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851167 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_851167 : Nat := 118140960795 + 851167 * 2 ^ 59
def prefixEnd_851167 : Nat := 4983230072969 + 3 ^ 40 * 851167 * 2
def baseEnd_851167 : Nat := 388495811773845812353831

theorem tailTrace_851167 : CollatzResearch.WordTrace tailWord_851167 prefixEnd_851167 388495811773845812353831 := by
  unfold tailWord_851167
  simp only [CollatzResearch.WordTrace]
  refine ⟨31044610907374801595391755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20696407271583201063594503 31044610907374801595391755)
  ·
    refine ⟨46566916361062202393087633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31044610907374801595391755 46566916361062202393087633)
    ·
      refine ⟨34925187270796651794815725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46566916361062202393087633 34925187270796651794815725)
      ·
        refine ⟨13096945226548744423055897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34925187270796651794815725 13096945226548744423055897)
        ·
          refine ⟨9822708919911558317291923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13096945226548744423055897 9822708919911558317291923)
          ·
            refine ⟨14734063379867337475937885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822708919911558317291923 14734063379867337475937885)
            ·
              refine ⟨5525273767450251553476707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14734063379867337475937885 5525273767450251553476707)
              ·
                refine ⟨8287910651175377330215061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525273767450251553476707 8287910651175377330215061)
                ·
                  refine ⟨388495811773845812353831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8287910651175377330215061 388495811773845812353831)
                  ·
                    rfl

theorem cell20_851167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_851167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851167 prefixEnd_851167 := by exact prefixLift 851167
  have htrace : WordTrace (prefixWord ++ tailWord_851167) baseStart_851167 baseEnd_851167 := by
    simpa [prefixWord, tailWord_851167, baseEnd_851167] using wordTrace_append hprefix tailTrace_851167
  have hstable : (prefixWord ++ tailWord_851167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851167).length < 2 ^ (prefixWord ++ tailWord_851167).sum := by decide
  have hdescent : baseEnd_851167 < baseStart_851167 := by decide
  rcases family_descends (prefixWord ++ tailWord_851167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851201 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 2]
def baseStart_851201 : Nat := 118140960795 + 851201 * 2 ^ 59
def prefixEnd_851201 : Nat := 4983230072969 + 3 ^ 40 * 851201 * 2
def baseEnd_851201 : Nat := 388511330300292805220359

theorem tailTrace_851201 : CollatzResearch.WordTrace tailWord_851201 prefixEnd_851201 388511330300292805220359 := by
  unfold tailWord_851201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045850989251625402129457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20697233992834416934752971 31045850989251625402129457)
  ·
    refine ⟨23284388241938719051597093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31045850989251625402129457 23284388241938719051597093)
    ·
      refine ⟨4365822795363509822174455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23284388241938719051597093 4365822795363509822174455)
      ·
        refine ⟨6548734193045264733261683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365822795363509822174455 6548734193045264733261683)
        ·
          refine ⟨9823101289567897099892525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548734193045264733261683 9823101289567897099892525)
          ·
            refine ⟨3683662983587961412459697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9823101289567897099892525 3683662983587961412459697)
            ·
              refine ⟨2762747237690971059344773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3683662983587961412459697 2762747237690971059344773)
              ·
                refine ⟨518015107067057073627145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2762747237690971059344773 518015107067057073627145)
                ·
                  refine ⟨388511330300292805220359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518015107067057073627145 388511330300292805220359)
                  ·
                    rfl

theorem cell20_851201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_851201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851201 prefixEnd_851201 := by exact prefixLift 851201
  have htrace : WordTrace (prefixWord ++ tailWord_851201) baseStart_851201 baseEnd_851201 := by
    simpa [prefixWord, tailWord_851201, baseEnd_851201] using wordTrace_append hprefix tailTrace_851201
  have hstable : (prefixWord ++ tailWord_851201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851201).length < 2 ^ (prefixWord ++ tailWord_851201).sum := by decide
  have hdescent : baseEnd_851201 < baseStart_851201 := by decide
  rcases family_descends (prefixWord ++ tailWord_851201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
