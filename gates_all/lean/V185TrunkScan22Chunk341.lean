import V185TrunkScan22Chunk340

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3042012 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3042012 : Nat := 118140960795 + 3042012 * 2 ^ 59
def prefixEnd_3042012 : Nat := 4983230072969 + 3 ^ 40 * 3042012 * 2
def baseEnd_3042012 : Nat := 1041342875163371565173365

theorem tailTrace_3042012 : CollatzResearch.WordTrace tailWord_3042012 prefixEnd_3042012 1041342875163371565173365 := by
  unfold tailWord_3042012
  simp only [CollatzResearch.WordTrace]
  refine ⟨55475646327658766566236145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73967528436878355421648193 55475646327658766566236145)
  ·
    refine ⟨41606734745744074924677109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55475646327658766566236145 41606734745744074924677109)
    ·
      refine ⟨3900631382413507024188479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41606734745744074924677109 3900631382413507024188479)
      ·
        refine ⟨5850947073620260536282719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900631382413507024188479 5850947073620260536282719)
        ·
          refine ⟨8776420610430390804424079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850947073620260536282719 8776420610430390804424079)
          ·
            refine ⟨13164630915645586206636119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776420610430390804424079 13164630915645586206636119)
            ·
              refine ⟨19746946373468379309954179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13164630915645586206636119 19746946373468379309954179)
              ·
                refine ⟨29620419560202568964931269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19746946373468379309954179 29620419560202568964931269)
                ·
                  refine ⟨5553828667537981680924613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29620419560202568964931269 5553828667537981680924613)
                  ·
                    refine ⟨1041342875163371565173365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553828667537981680924613 1041342875163371565173365)
                    ·
                      rfl

theorem cell22_3042012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3042012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042012 prefixEnd_3042012 := by exact prefixLift 3042012
  have htrace : WordTrace (prefixWord ++ tailWord_3042012) baseStart_3042012 baseEnd_3042012 := by
    simpa [prefixWord, tailWord_3042012, baseEnd_3042012] using wordTrace_append hprefix tailTrace_3042012
  have hstable : (prefixWord ++ tailWord_3042012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042012).length < 2 ^ (prefixWord ++ tailWord_3042012).sum := by decide
  have hdescent : baseEnd_3042012 < baseStart_3042012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042076 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3042076 : Nat := 118140960795 + 3042076 * 2 ^ 59
def prefixEnd_3042076 : Nat := 4983230072969 + 3 ^ 40 * 3042076 * 2
def baseEnd_3042076 : Nat := 1041364783671296731573169

theorem tailTrace_3042076 : CollatzResearch.WordTrace tailWord_3042076 prefixEnd_3042076 1041364783671296731573169 := by
  unfold tailWord_3042076
  simp only [CollatzResearch.WordTrace]
  refine ⟨55476813463542836031401041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73969084618057114708534721 55476813463542836031401041)
  ·
    refine ⟨41607610097657127023550781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55476813463542836031401041 41607610097657127023550781)
    ·
      refine ⟨15602853786621422633831543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41607610097657127023550781 15602853786621422633831543)
      ·
        refine ⟨23404280679932133950747315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15602853786621422633831543 23404280679932133950747315)
        ·
          refine ⟨35106421019898200926120973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23404280679932133950747315 35106421019898200926120973)
          ·
            refine ⟨13164907882461825347295365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35106421019898200926120973 13164907882461825347295365)
            ·
              refine ⟨2468420227961592252617881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13164907882461825347295365 2468420227961592252617881)
              ·
                refine ⟨1851315170971194189463411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468420227961592252617881 1851315170971194189463411)
                ·
                  refine ⟨2776972756456791284195117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851315170971194189463411 2776972756456791284195117)
                  ·
                    refine ⟨1041364783671296731573169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776972756456791284195117 1041364783671296731573169)
                    ·
                      rfl

theorem cell22_3042076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3042076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042076 prefixEnd_3042076 := by exact prefixLift 3042076
  have htrace : WordTrace (prefixWord ++ tailWord_3042076) baseStart_3042076 baseEnd_3042076 := by
    simpa [prefixWord, tailWord_3042076, baseEnd_3042076] using wordTrace_append hprefix tailTrace_3042076
  have hstable : (prefixWord ++ tailWord_3042076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042076).length < 2 ^ (prefixWord ++ tailWord_3042076).sum := by decide
  have hdescent : baseEnd_3042076 < baseStart_3042076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042085 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_3042085 : Nat := 118140960795 + 3042085 * 2 ^ 59
def prefixEnd_3042085 : Nat := 4983230072969 + 3 ^ 40 * 3042085 * 2
def baseEnd_3042085 : Nat := 1041367864555223708098141

theorem tailTrace_3042085 : CollatzResearch.WordTrace tailWord_3042085 prefixEnd_3042085 1041367864555223708098141 := by
  unfold tailWord_3042085
  simp only [CollatzResearch.WordTrace]
  refine ⟨110953955184053066599879709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73969303456035377733253139 110953955184053066599879709)
  ·
    refine ⟨41607733194019899974954891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110953955184053066599879709 41607733194019899974954891)
    ·
      refine ⟨62411599791029849962432337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41607733194019899974954891 62411599791029849962432337)
      ·
        refine ⟨46808699843272387471824253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62411599791029849962432337 46808699843272387471824253)
        ·
          refine ⟨17553262441227145301934095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46808699843272387471824253 17553262441227145301934095)
          ·
            refine ⟨26329893661840717952901143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17553262441227145301934095 26329893661840717952901143)
            ·
              refine ⟨39494840492761076929351715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26329893661840717952901143 39494840492761076929351715)
              ·
                refine ⟨59242260739141615394027573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39494840492761076929351715 59242260739141615394027573)
                ·
                  refine ⟨5553961944294526443190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59242260739141615394027573 5553961944294526443190085)
                  ·
                    refine ⟨1041367864555223708098141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5553961944294526443190085 1041367864555223708098141)
                    ·
                      rfl

theorem cell22_3042085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_3042085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042085 prefixEnd_3042085 := by exact prefixLift 3042085
  have htrace : WordTrace (prefixWord ++ tailWord_3042085) baseStart_3042085 baseEnd_3042085 := by
    simpa [prefixWord, tailWord_3042085, baseEnd_3042085] using wordTrace_append hprefix tailTrace_3042085
  have hstable : (prefixWord ++ tailWord_3042085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042085).length < 2 ^ (prefixWord ++ tailWord_3042085).sum := by decide
  have hdescent : baseEnd_3042085 < baseStart_3042085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042115 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_3042115 : Nat := 118140960795 + 3042115 * 2 ^ 59
def prefixEnd_3042115 : Nat := 4983230072969 + 3 ^ 40 * 3042115 * 2
def baseEnd_3042115 : Nat := 1041378134168313629848049

theorem tailTrace_3042115 : CollatzResearch.WordTrace tailWord_3042115 prefixEnd_3042115 1041378134168313629848049 := by
  unfold tailWord_3042115
  simp only [CollatzResearch.WordTrace]
  refine ⟨110955049373944381723471799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73970032915962921148981199 110955049373944381723471799)
  ·
    refine ⟨166432574060916572585207699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110955049373944381723471799 166432574060916572585207699)
    ·
      refine ⟨249648861091374858877811549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166432574060916572585207699 249648861091374858877811549)
      ·
        refine ⟨93618322909265572079179331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249648861091374858877811549 93618322909265572079179331)
        ·
          refine ⟨140427484363898358118768997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93618322909265572079179331 140427484363898358118768997)
          ·
            refine ⟨26330153318230942147269187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140427484363898358118768997 26330153318230942147269187)
            ·
              refine ⟨39495229977346413220903781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26330153318230942147269187 39495229977346413220903781)
              ·
                refine ⟨7405355620752452478919459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39495229977346413220903781 7405355620752452478919459)
                ·
                  refine ⟨11108033431128678718379189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405355620752452478919459 11108033431128678718379189)
                  ·
                    refine ⟨1041378134168313629848049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11108033431128678718379189 1041378134168313629848049)
                    ·
                      rfl

theorem cell22_3042115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_3042115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042115 prefixEnd_3042115 := by exact prefixLift 3042115
  have htrace : WordTrace (prefixWord ++ tailWord_3042115) baseStart_3042115 baseEnd_3042115 := by
    simpa [prefixWord, tailWord_3042115, baseEnd_3042115] using wordTrace_append hprefix tailTrace_3042115
  have hstable : (prefixWord ++ tailWord_3042115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042115).length < 2 ^ (prefixWord ++ tailWord_3042115).sum := by decide
  have hdescent : baseEnd_3042115 < baseStart_3042115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042162 : List Nat := [3, 2, 1, 2, 1, 1, 6, 6]
def baseStart_3042162 : Nat := 118140960795 + 3042162 * 2 ^ 59
def prefixEnd_3042162 : Nat := 4983230072969 + 3 ^ 40 * 3042162 * 2
def baseEnd_3042162 : Nat := 115710469247646797102545

theorem tailTrace_3042162 : CollatzResearch.WordTrace tailWord_3042162 prefixEnd_3042162 115710469247646797102545 := by
  unfold tailWord_3042162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27739190901193527187608185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73971175736516072500288493 27739190901193527187608185)
  ·
    refine ⟨20804393175895145390706139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27739190901193527187608185 20804393175895145390706139)
    ·
      refine ⟨31206589763842718086059209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20804393175895145390706139 31206589763842718086059209)
      ·
        refine ⟨23404942322882038564544407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31206589763842718086059209 23404942322882038564544407)
        ·
          refine ⟨35107413484323057846816611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23404942322882038564544407 35107413484323057846816611)
          ·
            refine ⟨52661120226484586770224917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35107413484323057846816611 52661120226484586770224917)
            ·
              refine ⟨2468490010616465004854293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52661120226484586770224917 2468490010616465004854293)
              ·
                refine ⟨115710469247646797102545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2468490010616465004854293 115710469247646797102545)
                ·
                  rfl

theorem cell22_3042162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_3042162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042162 prefixEnd_3042162 := by exact prefixLift 3042162
  have htrace : WordTrace (prefixWord ++ tailWord_3042162) baseStart_3042162 baseEnd_3042162 := by
    simpa [prefixWord, tailWord_3042162, baseEnd_3042162] using wordTrace_append hprefix tailTrace_3042162
  have hstable : (prefixWord ++ tailWord_3042162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042162).length < 2 ^ (prefixWord ++ tailWord_3042162).sum := by decide
  have hdescent : baseEnd_3042162 < baseStart_3042162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042220 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_3042220 : Nat := 118140960795 + 3042220 * 2 ^ 59
def prefixEnd_3042220 : Nat := 4983230072969 + 3 ^ 40 * 3042220 * 2
def baseEnd_3042220 : Nat := 1041414077814128355972727

theorem tailTrace_3042220 : CollatzResearch.WordTrace tailWord_3042220 prefixEnd_3042220 1041414077814128355972727 := by
  unfold tailWord_3042220
  simp only [CollatzResearch.WordTrace]
  refine ⟨55479439519281992328022057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73972586025709323104029409 55479439519281992328022057)
  ·
    refine ⟨41609579639461494246016543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55479439519281992328022057 41609579639461494246016543)
    ·
      refine ⟨62414369459192241369024815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41609579639461494246016543 62414369459192241369024815)
      ·
        refine ⟨93621554188788362053537223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62414369459192241369024815 93621554188788362053537223)
        ·
          refine ⟨140432331283182543080305835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93621554188788362053537223 140432331283182543080305835)
          ·
            refine ⟨210648496924773814620458753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140432331283182543080305835 210648496924773814620458753)
            ·
              refine ⟨157986372693580360965344065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210648496924773814620458753 157986372693580360965344065)
              ·
                refine ⟨118489779520185270724008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157986372693580360965344065 118489779520185270724008049)
                ·
                  refine ⟨88867334640138953043006037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118489779520185270724008049 88867334640138953043006037)
                  ·
                    refine ⟨1041414077814128355972727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88867334640138953043006037 1041414077814128355972727)
                    ·
                      rfl

theorem cell22_3042220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_3042220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042220 prefixEnd_3042220 := by exact prefixLift 3042220
  have htrace : WordTrace (prefixWord ++ tailWord_3042220) baseStart_3042220 baseEnd_3042220 := by
    simpa [prefixWord, tailWord_3042220, baseEnd_3042220] using wordTrace_append hprefix tailTrace_3042220
  have hstable : (prefixWord ++ tailWord_3042220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042220).length < 2 ^ (prefixWord ++ tailWord_3042220).sum := by decide
  have hdescent : baseEnd_3042220 < baseStart_3042220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042252 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 6]
def baseStart_3042252 : Nat := 118140960795 + 3042252 * 2 ^ 59
def prefixEnd_3042252 : Nat := 4983230072969 + 3 ^ 40 * 3042252 * 2
def baseEnd_3042252 : Nat := 347141677356030313057543

theorem tailTrace_3042252 : CollatzResearch.WordTrace tailWord_3042252 prefixEnd_3042252 347141677356030313057543 := by
  unfold tailWord_3042252
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480023087224027060604505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73973364116298702747472673 55480023087224027060604505)
  ·
    refine ⟨41610017315418020295453379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55480023087224027060604505 41610017315418020295453379)
    ·
      refine ⟨62415025973127030443180069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41610017315418020295453379 62415025973127030443180069)
      ·
        refine ⟨11702817369961318208096263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62415025973127030443180069 11702817369961318208096263)
        ·
          refine ⟨17554226054941977312144395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11702817369961318208096263 17554226054941977312144395)
          ·
            refine ⟨26331339082412965968216593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17554226054941977312144395 26331339082412965968216593)
            ·
              refine ⟨19748504311809724476162445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26331339082412965968216593 19748504311809724476162445)
              ·
                refine ⟨7405689116928646678560917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19748504311809724476162445 7405689116928646678560917)
                ·
                  refine ⟨347141677356030313057543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7405689116928646678560917 347141677356030313057543)
                  ·
                    rfl

theorem cell22_3042252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_3042252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042252 prefixEnd_3042252 := by exact prefixLift 3042252
  have htrace : WordTrace (prefixWord ++ tailWord_3042252) baseStart_3042252 baseEnd_3042252 := by
    simpa [prefixWord, tailWord_3042252, baseEnd_3042252] using wordTrace_append hprefix tailTrace_3042252
  have hstable : (prefixWord ++ tailWord_3042252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042252).length < 2 ^ (prefixWord ++ tailWord_3042252).sum := by decide
  have hdescent : baseEnd_3042252 < baseStart_3042252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042269 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 6]
def baseStart_3042269 : Nat := 118140960795 + 3042269 * 2 ^ 59
def prefixEnd_3042269 : Nat := 4983230072969 + 3 ^ 40 * 3042269 * 2
def baseEnd_3042269 : Nat := 347143617171836187165859

theorem tailTrace_3042269 : CollatzResearch.WordTrace tailWord_3042269 prefixEnd_3042269 347143617171836187165859 := by
  unfold tailWord_3042269
  simp only [CollatzResearch.WordTrace]
  refine ⟨110960666215386466024577861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73973777476924310683051907 110960666215386466024577861)
  ·
    refine ⟨20805124915384962379608349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110960666215386466024577861 20805124915384962379608349)
    ·
      refine ⟨7801921843269360892353131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20805124915384962379608349 7801921843269360892353131)
      ·
        refine ⟨11702882764904041338529697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801921843269360892353131 11702882764904041338529697)
        ·
          refine ⟨8777162073678031003897273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11702882764904041338529697 8777162073678031003897273)
          ·
            refine ⟨6582871555258523252922955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8777162073678031003897273 6582871555258523252922955)
            ·
              refine ⟨9874307332887784879384433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582871555258523252922955 9874307332887784879384433)
              ·
                refine ⟨7405730499665838659538325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874307332887784879384433 7405730499665838659538325)
                ·
                  refine ⟨347143617171836187165859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7405730499665838659538325 347143617171836187165859)
                  ·
                    rfl

theorem cell22_3042269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_3042269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042269 prefixEnd_3042269 := by exact prefixLift 3042269
  have htrace : WordTrace (prefixWord ++ tailWord_3042269) baseStart_3042269 baseEnd_3042269 := by
    simpa [prefixWord, tailWord_3042269, baseEnd_3042269] using wordTrace_append hprefix tailTrace_3042269
  have hstable : (prefixWord ++ tailWord_3042269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042269).length < 2 ^ (prefixWord ++ tailWord_3042269).sum := by decide
  have hdescent : baseEnd_3042269 < baseStart_3042269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042292 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3042292 : Nat := 118140960795 + 3042292 * 2 ^ 59
def prefixEnd_3042292 : Nat := 4983230072969 + 3 ^ 40 * 3042292 * 2
def baseEnd_3042292 : Nat := 347146241628514722724169

theorem tailTrace_3042292 : CollatzResearch.WordTrace tailWord_3042292 prefixEnd_3042292 347146241628514722724169 := by
  unfold tailWord_3042292
  simp only [CollatzResearch.WordTrace]
  refine ⟨55480752547151570476332565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73974336729535427301776753 55480752547151570476332565)
  ·
    refine ⟨2600660275647729866078089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55480752547151570476332565 2600660275647729866078089)
    ·
      refine ⟨1950495206735797399558567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2600660275647729866078089 1950495206735797399558567)
      ·
        refine ⟨2925742810103696099337851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950495206735797399558567 2925742810103696099337851)
        ·
          refine ⟨4388614215155544149006777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925742810103696099337851 4388614215155544149006777)
          ·
            refine ⟨3291460661366658111755083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4388614215155544149006777 3291460661366658111755083)
            ·
              refine ⟨4937190992049987167632625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291460661366658111755083 4937190992049987167632625)
              ·
                refine ⟨3702893244037490375724469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4937190992049987167632625 3702893244037490375724469)
                ·
                  refine ⟨347146241628514722724169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3702893244037490375724469 347146241628514722724169)
                  ·
                    rfl

theorem cell22_3042292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3042292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042292 prefixEnd_3042292 := by exact prefixLift 3042292
  have htrace : WordTrace (prefixWord ++ tailWord_3042292) baseStart_3042292 baseEnd_3042292 := by
    simpa [prefixWord, tailWord_3042292, baseEnd_3042292] using wordTrace_append hprefix tailTrace_3042292
  have hstable : (prefixWord ++ tailWord_3042292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042292).length < 2 ^ (prefixWord ++ tailWord_3042292).sum := by decide
  have hdescent : baseEnd_3042292 < baseStart_3042292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042318 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3042318 : Nat := 118140960795 + 3042318 * 2 ^ 59
def prefixEnd_3042318 : Nat := 4983230072969 + 3 ^ 40 * 3042318 * 2
def baseEnd_3042318 : Nat := 1041447625216888767022427

theorem tailTrace_3042318 : CollatzResearch.WordTrace tailWord_3042318 prefixEnd_3042318 1041447625216888767022427 := by
  unfold tailWord_3042318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870306674026118424138951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73974968928139298262074405 13870306674026118424138951)
  ·
    refine ⟨20805460011039177636208427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13870306674026118424138951 20805460011039177636208427)
    ·
      refine ⟨31208190016558766454312641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20805460011039177636208427 31208190016558766454312641)
      ·
        refine ⟨23406142512419074840734481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31208190016558766454312641 23406142512419074840734481)
        ·
          refine ⟨17554606884314306130550861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23406142512419074840734481 17554606884314306130550861)
          ·
            refine ⟨6582977581617864798956573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17554606884314306130550861 6582977581617864798956573)
            ·
              refine ⟨2468616593106699299608715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6582977581617864798956573 2468616593106699299608715)
              ·
                refine ⟨3702924889660048949413073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468616593106699299608715 3702924889660048949413073)
                ·
                  refine ⟨2777193667245036712059805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3702924889660048949413073 2777193667245036712059805)
                  ·
                    refine ⟨1041447625216888767022427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777193667245036712059805 1041447625216888767022427)
                    ·
                      rfl

theorem cell22_3042318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3042318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042318 prefixEnd_3042318 := by exact prefixLift 3042318
  have htrace : WordTrace (prefixWord ++ tailWord_3042318) baseStart_3042318 baseEnd_3042318 := by
    simpa [prefixWord, tailWord_3042318, baseEnd_3042318] using wordTrace_append hprefix tailTrace_3042318
  have hstable : (prefixWord ++ tailWord_3042318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042318).length < 2 ^ (prefixWord ++ tailWord_3042318).sum := by decide
  have hdescent : baseEnd_3042318 < baseStart_3042318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042329 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_3042329 : Nat := 118140960795 + 3042329 * 2 ^ 59
def prefixEnd_3042329 : Nat := 4983230072969 + 3 ^ 40 * 3042329 * 2
def baseEnd_3042329 : Nat := 1041451390741688404997393

theorem tailTrace_3042329 : CollatzResearch.WordTrace tailWord_3042329 prefixEnd_3042329 1041451390741688404997393 := by
  unfold tailWord_3042329
  simp only [CollatzResearch.WordTrace]
  refine ⟨110962854595169096271762041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73975236396779397514508027 110962854595169096271762041)
  ·
    refine ⟨83222140946376822203821531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110962854595169096271762041 83222140946376822203821531)
    ·
      refine ⟨124833211419565233305732297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83222140946376822203821531 124833211419565233305732297)
      ·
        refine ⟨93624908564673924979299223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124833211419565233305732297 93624908564673924979299223)
        ·
          refine ⟨140437362847010887468948835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93624908564673924979299223 140437362847010887468948835)
          ·
            refine ⟨210656044270516331203423253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140437362847010887468948835 210656044270516331203423253)
            ·
              refine ⟨9874502075180453025160465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210656044270516331203423253 9874502075180453025160465)
              ·
                refine ⟨7405876556385339768870349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9874502075180453025160465 7405876556385339768870349)
                ·
                  refine ⟨2777203708644502413326381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7405876556385339768870349 2777203708644502413326381)
                  ·
                    refine ⟨1041451390741688404997393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777203708644502413326381 1041451390741688404997393)
                    ·
                      rfl

theorem cell22_3042329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_3042329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042329 prefixEnd_3042329 := by exact prefixLift 3042329
  have htrace : WordTrace (prefixWord ++ tailWord_3042329) baseStart_3042329 baseEnd_3042329 := by
    simpa [prefixWord, tailWord_3042329, baseEnd_3042329] using wordTrace_append hprefix tailTrace_3042329
  have hstable : (prefixWord ++ tailWord_3042329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042329).length < 2 ^ (prefixWord ++ tailWord_3042329).sum := by decide
  have hdescent : baseEnd_3042329 < baseStart_3042329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042389 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3042389 : Nat := 118140960795 + 3042389 * 2 ^ 59
def prefixEnd_3042389 : Nat := 4983230072969 + 3 ^ 40 * 3042389 * 2
def baseEnd_3042389 : Nat := 1041471929967868248497209

theorem tailTrace_3042389 : CollatzResearch.WordTrace tailWord_3042389 prefixEnd_3042389 1041471929967868248497209 := by
  unfold tailWord_3042389
  simp only [CollatzResearch.WordTrace]
  refine ⟨110965042974951726518946221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73976695316634484345964147 110965042974951726518946221)
  ·
    refine ⟨41611891115606897444604833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110965042974951726518946221 41611891115606897444604833)
    ·
      refine ⟨31208918336705173083453625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41611891115606897444604833 31208918336705173083453625)
      ·
        refine ⟨23406688752528879812590219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31208918336705173083453625 23406688752528879812590219)
        ·
          refine ⟨35110033128793319718885329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23406688752528879812590219 35110033128793319718885329)
          ·
            refine ⟨26332524846594989789163997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35110033128793319718885329 26332524846594989789163997)
            ·
              refine ⟨9874696817473121170936499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26332524846594989789163997 9874696817473121170936499)
              ·
                refine ⟨14812045226209681756404749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9874696817473121170936499 14812045226209681756404749)
                ·
                  refine ⟨5554516959828630658651781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14812045226209681756404749 5554516959828630658651781)
                  ·
                    refine ⟨1041471929967868248497209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554516959828630658651781 1041471929967868248497209)
                    ·
                      rfl

theorem cell22_3042389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3042389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042389 prefixEnd_3042389 := by exact prefixLift 3042389
  have htrace : WordTrace (prefixWord ++ tailWord_3042389) baseStart_3042389 baseEnd_3042389 := by
    simpa [prefixWord, tailWord_3042389, baseEnd_3042389] using wordTrace_append hprefix tailTrace_3042389
  have hstable : (prefixWord ++ tailWord_3042389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042389).length < 2 ^ (prefixWord ++ tailWord_3042389).sum := by decide
  have hdescent : baseEnd_3042389 < baseStart_3042389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042436 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3042436 : Nat := 118140960795 + 3042436 * 2 ^ 59
def prefixEnd_3042436 : Nat := 4983230072969 + 3 ^ 40 * 3042436 * 2
def baseEnd_3042436 : Nat := 1041488019028375792572065

theorem tailTrace_3042436 : CollatzResearch.WordTrace tailWord_3042436 prefixEnd_3042436 1041488019028375792572065 := by
  unfold tailWord_3042436
  simp only [CollatzResearch.WordTrace]
  refine ⟨55483378602890726772953581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73977838137187635697271441 55483378602890726772953581)
  ·
    refine ⟨20806266976084022539857593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55483378602890726772953581 20806266976084022539857593)
    ·
      refine ⟨15604700232063016904893195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20806266976084022539857593 15604700232063016904893195)
      ·
        refine ⟨23407050348094525357339793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15604700232063016904893195 23407050348094525357339793)
        ·
          refine ⟨17555287761070894018004845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23407050348094525357339793 17555287761070894018004845)
          ·
            refine ⟨6583232910401585256751817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17555287761070894018004845 6583232910401585256751817)
            ·
              refine ⟨4937424682801188942563863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583232910401585256751817 4937424682801188942563863)
              ·
                refine ⟨7406137024201783413845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937424682801188942563863 7406137024201783413845795)
                ·
                  refine ⟨11109205536302675120768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406137024201783413845795 11109205536302675120768693)
                  ·
                    refine ⟨1041488019028375792572065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11109205536302675120768693 1041488019028375792572065)
                    ·
                      rfl

theorem cell22_3042436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3042436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042436 prefixEnd_3042436 := by exact prefixLift 3042436
  have htrace : WordTrace (prefixWord ++ tailWord_3042436) baseStart_3042436 baseEnd_3042436 := by
    simpa [prefixWord, tailWord_3042436, baseEnd_3042436] using wordTrace_append hprefix tailTrace_3042436
  have hstable : (prefixWord ++ tailWord_3042436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042436).length < 2 ^ (prefixWord ++ tailWord_3042436).sum := by decide
  have hdescent : baseEnd_3042436 < baseStart_3042436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042466 : List Nat := [3, 3, 1, 3, 2, 1, 9]
def baseStart_3042466 : Nat := 118140960795 + 3042466 * 2 ^ 59
def prefixEnd_3042466 : Nat := 4983230072969 + 3 ^ 40 * 3042466 * 2
def baseEnd_3042466 : Nat := 38574010690424656085999

theorem tailTrace_3042466 : CollatzResearch.WordTrace tailWord_3042466 prefixEnd_3042466 38574010690424656085999 := by
  unfold tailWord_3042466
  simp only [CollatzResearch.WordTrace]
  refine ⟨27741962848918192167374813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73978567597115179112999501 27741962848918192167374813)
  ·
    refine ⟨10403236068344322062765555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27741962848918192167374813 10403236068344322062765555)
    ·
      refine ⟨15604854102516483094148333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10403236068344322062765555 15604854102516483094148333)
      ·
        refine ⟨5851820288443681160305625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15604854102516483094148333 5851820288443681160305625)
        ·
          refine ⟨4388865216332760870229219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5851820288443681160305625 4388865216332760870229219)
          ·
            refine ⟨6583297824499141305343829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388865216332760870229219 6583297824499141305343829)
            ·
              refine ⟨38574010690424656085999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6583297824499141305343829 38574010690424656085999)
              ·
                rfl

theorem cell22_3042466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 9].length) (baseStart_3042466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042466 prefixEnd_3042466 := by exact prefixLift 3042466
  have htrace : WordTrace (prefixWord ++ tailWord_3042466) baseStart_3042466 baseEnd_3042466 := by
    simpa [prefixWord, tailWord_3042466, baseEnd_3042466] using wordTrace_append hprefix tailTrace_3042466
  have hstable : (prefixWord ++ tailWord_3042466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042466).length < 2 ^ (prefixWord ++ tailWord_3042466).sum := by decide
  have hdescent : baseEnd_3042466 < baseStart_3042466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042500 : List Nat := [2, 3, 3, 1, 4, 1, 2, 6]
def baseStart_3042500 : Nat := 118140960795 + 3042500 * 2 ^ 59
def prefixEnd_3042500 : Nat := 4983230072969 + 3 ^ 40 * 3042500 * 2
def baseEnd_3042500 : Nat := 115723325281811217663541

theorem tailTrace_3042500 : CollatzResearch.WordTrace tailWord_3042500 prefixEnd_3042500 115723325281811217663541 := by
  unfold tailWord_3042500
  simp only [CollatzResearch.WordTrace]
  refine ⟨55484545738774796238118477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73979394318366394984157969 55484545738774796238118477)
  ·
    refine ⟨20806704652040548589294429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55484545738774796238118477 20806704652040548589294429)
    ·
      refine ⟨7802514244515205720985411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20806704652040548589294429 7802514244515205720985411)
      ·
        refine ⟨11703771366772808581478117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7802514244515205720985411 11703771366772808581478117)
        ·
          refine ⟨2194457131269901609027147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11703771366772808581478117 2194457131269901609027147)
          ·
            refine ⟨3291685696904852413540721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194457131269901609027147 3291685696904852413540721)
            ·
              refine ⟨2468764272678639310155541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3291685696904852413540721 2468764272678639310155541)
              ·
                refine ⟨115723325281811217663541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2468764272678639310155541 115723325281811217663541)
                ·
                  rfl

theorem cell22_3042500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_3042500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042500 prefixEnd_3042500 := by exact prefixLift 3042500
  have htrace : WordTrace (prefixWord ++ tailWord_3042500) baseStart_3042500 baseEnd_3042500 := by
    simpa [prefixWord, tailWord_3042500, baseEnd_3042500] using wordTrace_append hprefix tailTrace_3042500
  have hstable : (prefixWord ++ tailWord_3042500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042500).length < 2 ^ (prefixWord ++ tailWord_3042500).sum := by decide
  have hdescent : baseEnd_3042500 < baseStart_3042500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042558 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3042558 : Nat := 118140960795 + 3042558 * 2 ^ 59
def prefixEnd_3042558 : Nat := 4983230072969 + 3 ^ 40 * 3042558 * 2
def baseEnd_3042558 : Nat := 1041529782121608141021691

theorem tailTrace_3042558 : CollatzResearch.WordTrace tailWord_3042558 prefixEnd_3042558 1041529782121608141021691 := by
  unfold tailWord_3042558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871400863917433547731041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73980804607559645587898885 13871400863917433547731041)
  ·
    refine ⟨10403550647938075160798281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13871400863917433547731041 10403550647938075160798281)
    ·
      refine ⟨7802662985953556370598711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10403550647938075160798281 7802662985953556370598711)
      ·
        refine ⟨11703994478930334555898067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7802662985953556370598711 11703994478930334555898067)
        ·
          refine ⟨17555991718395501833847101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11703994478930334555898067 17555991718395501833847101)
          ·
            refine ⟨6583496894398313187692663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17555991718395501833847101 6583496894398313187692663)
            ·
              refine ⟨9875245341597469781538995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583496894398313187692663 9875245341597469781538995)
              ·
                refine ⟨14812868012396204672308493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9875245341597469781538995 14812868012396204672308493)
                ·
                  refine ⟨5554825504648576752115685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14812868012396204672308493 5554825504648576752115685)
                  ·
                    refine ⟨1041529782121608141021691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5554825504648576752115685 1041529782121608141021691)
                    ·
                      rfl

theorem cell22_3042558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3042558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042558 prefixEnd_3042558 := by exact prefixLift 3042558
  have htrace : WordTrace (prefixWord ++ tailWord_3042558) baseStart_3042558 baseEnd_3042558 := by
    simpa [prefixWord, tailWord_3042558, baseEnd_3042558] using wordTrace_append hprefix tailTrace_3042558
  have hstable : (prefixWord ++ tailWord_3042558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042558).length < 2 ^ (prefixWord ++ tailWord_3042558).sum := by decide
  have hdescent : baseEnd_3042558 < baseStart_3042558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042571 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_3042571 : Nat := 118140960795 + 3042571 * 2 ^ 59
def prefixEnd_3042571 : Nat := 4983230072969 + 3 ^ 40 * 3042571 * 2
def baseEnd_3042571 : Nat := 1041534232287280440446651

theorem tailTrace_3042571 : CollatzResearch.WordTrace tailWord_3042571 prefixEnd_3042571 1041534232287280440446651 := by
  unfold tailWord_3042571
  simp only [CollatzResearch.WordTrace]
  refine ⟨110971681060292371602071567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73981120706861581068047711 110971681060292371602071567)
  ·
    refine ⟨166457521590438557403107351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110971681060292371602071567 166457521590438557403107351)
    ·
      refine ⟨249686282385657836104661027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166457521590438557403107351 249686282385657836104661027)
      ·
        refine ⟨374529423578486754156991541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249686282385657836104661027 374529423578486754156991541)
        ·
          refine ⟨35112133460483133202217957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 374529423578486754156991541 35112133460483133202217957)
          ·
            refine ⟨6583525023840587475415867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35112133460483133202217957 6583525023840587475415867)
            ·
              refine ⟨9875287535760881213123801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583525023840587475415867 9875287535760881213123801)
              ·
                refine ⟨7406465651820660909842851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9875287535760881213123801 7406465651820660909842851)
                ·
                  refine ⟨11109698477730991364764277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406465651820660909842851 11109698477730991364764277)
                  ·
                    refine ⟨1041534232287280440446651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11109698477730991364764277 1041534232287280440446651)
                    ·
                      rfl

theorem cell22_3042571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_3042571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042571 prefixEnd_3042571 := by exact prefixLift 3042571
  have htrace : WordTrace (prefixWord ++ tailWord_3042571) baseStart_3042571 baseEnd_3042571 := by
    simpa [prefixWord, tailWord_3042571, baseEnd_3042571] using wordTrace_append hprefix tailTrace_3042571
  have hstable : (prefixWord ++ tailWord_3042571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042571).length < 2 ^ (prefixWord ++ tailWord_3042571).sum := by decide
  have hdescent : baseEnd_3042571 < baseStart_3042571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042584 : List Nat := [2, 1, 2, 3, 1, 13]
def baseStart_3042584 : Nat := 118140960795 + 3042584 * 2 ^ 59
def prefixEnd_3042584 : Nat := 4983230072969 + 3 ^ 40 * 3042584 * 2
def baseEnd_3042584 : Nat := 12858502252505589381131

theorem tailTrace_3042584 : CollatzResearch.WordTrace tailWord_3042584 prefixEnd_3042584 12858502252505589381131 := by
  unfold tailWord_3042584
  simp only [CollatzResearch.WordTrace]
  refine ⟨55486077604622637411147403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73981436806163516548196537 55486077604622637411147403)
  ·
    refine ⟨83229116406933956116721105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55486077604622637411147403 83229116406933956116721105)
    ·
      refine ⟨62421837305200467087540829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83229116406933956116721105 62421837305200467087540829)
      ·
        refine ⟨23408188989450175157827811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62421837305200467087540829 23408188989450175157827811)
        ·
          refine ⟨35112283484175262736741717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23408188989450175157827811 35112283484175262736741717)
          ·
            refine ⟨12858502252505589381131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 35112283484175262736741717 12858502252505589381131)
            ·
              rfl

theorem cell22_3042584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 13].length) (baseStart_3042584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042584 prefixEnd_3042584 := by exact prefixLift 3042584
  have htrace : WordTrace (prefixWord ++ tailWord_3042584) baseStart_3042584 baseEnd_3042584 := by
    simpa [prefixWord, tailWord_3042584, baseEnd_3042584] using wordTrace_append hprefix tailTrace_3042584
  have hstable : (prefixWord ++ tailWord_3042584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042584).length < 2 ^ (prefixWord ++ tailWord_3042584).sum := by decide
  have hdescent : baseEnd_3042584 < baseStart_3042584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042588 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3042588 : Nat := 118140960795 + 3042588 * 2 ^ 59
def prefixEnd_3042588 : Nat := 4983230072969 + 3 ^ 40 * 3042588 * 2
def baseEnd_3042588 : Nat := 1041540051734698062771599

theorem tailTrace_3042588 : CollatzResearch.WordTrace tailWord_3042588 prefixEnd_3042588 1041540051734698062771599 := by
  unfold tailWord_3042588
  simp only [CollatzResearch.WordTrace]
  refine ⟨55486150550615391752720209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73981534067487189003626945 55486150550615391752720209)
  ·
    refine ⟨41614612912961543814540157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55486150550615391752720209 41614612912961543814540157)
    ·
      refine ⟨15605479842360578930452559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41614612912961543814540157 15605479842360578930452559)
      ·
        refine ⟨23408219763540868395678839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15605479842360578930452559 23408219763540868395678839)
        ·
          refine ⟨35112329645311302593518259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23408219763540868395678839 35112329645311302593518259)
          ·
            refine ⟨52668494467966953890277389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35112329645311302593518259 52668494467966953890277389)
            ·
              refine ⟨19750685425487607708854021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52668494467966953890277389 19750685425487607708854021)
              ·
                refine ⟨3703253517278926445410129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19750685425487607708854021 3703253517278926445410129)
                ·
                  refine ⟨2777440137959194834057597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3703253517278926445410129 2777440137959194834057597)
                  ·
                    refine ⟨1041540051734698062771599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777440137959194834057597 1041540051734698062771599)
                    ·
                      rfl

theorem cell22_3042588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3042588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042588 prefixEnd_3042588 := by exact prefixLift 3042588
  have htrace : WordTrace (prefixWord ++ tailWord_3042588) baseStart_3042588 baseEnd_3042588 := by
    simpa [prefixWord, tailWord_3042588, baseEnd_3042588] using wordTrace_append hprefix tailTrace_3042588
  have hstable : (prefixWord ++ tailWord_3042588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042588).length < 2 ^ (prefixWord ++ tailWord_3042588).sum := by decide
  have hdescent : baseEnd_3042588 < baseStart_3042588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042605 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3042605 : Nat := 118140960795 + 3042605 * 2 ^ 59
def prefixEnd_3042605 : Nat := 4983230072969 + 3 ^ 40 * 3042605 * 2
def baseEnd_3042605 : Nat := 1041545871182115685096547

theorem tailTrace_3042605 : CollatzResearch.WordTrace tailWord_3042605 prefixEnd_3042605 1041545871182115685096547 := by
  unfold tailWord_3042605
  simp only [CollatzResearch.WordTrace]
  refine ⟨110972921142169195408809269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73981947428112796939206179 110972921142169195408809269)
  ·
    refine ⟨10403711357078362069575869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110972921142169195408809269 10403711357078362069575869)
    ·
      refine ⟨3901391758904385776090951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10403711357078362069575869 3901391758904385776090951)
      ·
        refine ⟨5852087638356578664136427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901391758904385776090951 5852087638356578664136427)
        ·
          refine ⟨8778131457534867996204641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852087638356578664136427 8778131457534867996204641)
          ·
            refine ⟨6583598593151150997153481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8778131457534867996204641 6583598593151150997153481)
            ·
              refine ⟨4937698944863363247865111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583598593151150997153481 4937698944863363247865111)
              ·
                refine ⟨7406548417295044871797667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937698944863363247865111 7406548417295044871797667)
                ·
                  refine ⟨11109822625942567307696501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7406548417295044871797667 11109822625942567307696501)
                  ·
                    refine ⟨1041545871182115685096547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11109822625942567307696501 1041545871182115685096547)
                    ·
                      rfl

theorem cell22_3042605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3042605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042605 prefixEnd_3042605 := by exact prefixLift 3042605
  have htrace : WordTrace (prefixWord ++ tailWord_3042605) baseStart_3042605 baseEnd_3042605 := by
    simpa [prefixWord, tailWord_3042605, baseEnd_3042605] using wordTrace_append hprefix tailTrace_3042605
  have hstable : (prefixWord ++ tailWord_3042605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042605).length < 2 ^ (prefixWord ++ tailWord_3042605).sum := by decide
  have hdescent : baseEnd_3042605 < baseStart_3042605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042650 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_3042650 : Nat := 118140960795 + 3042650 * 2 ^ 59
def prefixEnd_3042650 : Nat := 4983230072969 + 3 ^ 40 * 3042650 * 2
def baseEnd_3042650 : Nat := 1041561275601750567721409

theorem tailTrace_3042650 : CollatzResearch.WordTrace tailWord_3042650 prefixEnd_3042650 1041561275601750567721409 := by
  unfold tailWord_3042650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27743640606751542023549351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73983041618004112062798269 27743640606751542023549351)
  ·
    refine ⟨41615460910127313035324027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27743640606751542023549351 41615460910127313035324027)
    ·
      refine ⟨62423191365190969552986041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41615460910127313035324027 62423191365190969552986041)
      ·
        refine ⟨46817393523893227164739531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62423191365190969552986041 46817393523893227164739531)
        ·
          refine ⟨70226090285839840747109297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46817393523893227164739531 70226090285839840747109297)
          ·
            refine ⟨52669567714379880560331973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70226090285839840747109297 52669567714379880560331973)
            ·
              refine ⟨9875543946446227605062245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52669567714379880560331973 9875543946446227605062245)
              ·
                refine ⟨1851664489958667675949171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9875543946446227605062245 1851664489958667675949171)
                ·
                  refine ⟨2777496734938001513923757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851664489958667675949171 2777496734938001513923757)
                  ·
                    refine ⟨1041561275601750567721409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777496734938001513923757 1041561275601750567721409)
                    ·
                      rfl

theorem cell22_3042650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_3042650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042650 prefixEnd_3042650 := by exact prefixLift 3042650
  have htrace : WordTrace (prefixWord ++ tailWord_3042650) baseStart_3042650 baseEnd_3042650 := by
    simpa [prefixWord, tailWord_3042650, baseEnd_3042650] using wordTrace_append hprefix tailTrace_3042650
  have hstable : (prefixWord ++ tailWord_3042650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042650).length < 2 ^ (prefixWord ++ tailWord_3042650).sum := by decide
  have hdescent : baseEnd_3042650 < baseStart_3042650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042661 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_3042661 : Nat := 118140960795 + 3042661 * 2 ^ 59
def prefixEnd_3042661 : Nat := 4983230072969 + 3 ^ 40 * 3042661 * 2
def baseEnd_3042661 : Nat := 1041565041126550205696375

theorem tailTrace_3042661 : CollatzResearch.WordTrace tailWord_3042661 prefixEnd_3042661 1041565041126550205696375 := by
  unfold tailWord_3042661
  simp only [CollatzResearch.WordTrace]
  refine ⟨110974963629966316972847837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73983309086644211315231891 110974963629966316972847837)
  ·
    refine ⟨41615611361237368864817939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110974963629966316972847837 41615611361237368864817939)
    ·
      refine ⟨62423417041856053297226909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41615611361237368864817939 62423417041856053297226909)
      ·
        refine ⟨23408781390696019986460091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62423417041856053297226909 23408781390696019986460091)
        ·
          refine ⟨35113172086044029979690137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23408781390696019986460091 35113172086044029979690137)
          ·
            refine ⟨26334879064533022484767603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35113172086044029979690137 26334879064533022484767603)
            ·
              refine ⟨39502318596799533727151405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26334879064533022484767603 39502318596799533727151405)
              ·
                refine ⟨14813369473799825147681777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39502318596799533727151405 14813369473799825147681777)
                ·
                  refine ⟨11110027105349868860761333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14813369473799825147681777 11110027105349868860761333)
                  ·
                    refine ⟨1041565041126550205696375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11110027105349868860761333 1041565041126550205696375)
                    ·
                      rfl

theorem cell22_3042661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_3042661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042661 prefixEnd_3042661 := by exact prefixLift 3042661
  have htrace : WordTrace (prefixWord ++ tailWord_3042661) baseStart_3042661 baseEnd_3042661 := by
    simpa [prefixWord, tailWord_3042661, baseEnd_3042661] using wordTrace_append hprefix tailTrace_3042661
  have hstable : (prefixWord ++ tailWord_3042661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042661).length < 2 ^ (prefixWord ++ tailWord_3042661).sum := by decide
  have hdescent : baseEnd_3042661 < baseStart_3042661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042693 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_3042693 : Nat := 118140960795 + 3042693 * 2 ^ 59
def prefixEnd_3042693 : Nat := 4983230072969 + 3 ^ 40 * 3042693 * 2
def baseEnd_3042693 : Nat := 1041575995380512788896277

theorem tailTrace_3042693 : CollatzResearch.WordTrace tailWord_3042693 prefixEnd_3042693 1041575995380512788896277 := by
  unfold tailWord_3042693
  simp only [CollatzResearch.WordTrace]
  refine ⟨110976130765850386438012733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73984087177233590958675155 110976130765850386438012733)
  ·
    refine ⟨41616049037193894914254775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110976130765850386438012733 41616049037193894914254775)
    ·
      refine ⟨62424073555790842371382163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41616049037193894914254775 62424073555790842371382163)
      ·
        refine ⟨93636110333686263557073245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62424073555790842371382163 93636110333686263557073245)
        ·
          refine ⟨35113541375132348833902467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93636110333686263557073245 35113541375132348833902467)
          ·
            refine ⟨52670312062698523250853701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35113541375132348833902467 52670312062698523250853701)
            ·
              refine ⟨9875683511755973109535069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52670312062698523250853701 9875683511755973109535069)
              ·
                refine ⟨3703381316908489916075651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9875683511755973109535069 3703381316908489916075651)
                ·
                  refine ⟨5555071975362734874113477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703381316908489916075651 5555071975362734874113477)
                  ·
                    refine ⟨1041575995380512788896277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5555071975362734874113477 1041575995380512788896277)
                    ·
                      rfl

theorem cell22_3042693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_3042693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042693 prefixEnd_3042693 := by exact prefixLift 3042693
  have htrace : WordTrace (prefixWord ++ tailWord_3042693) baseStart_3042693 baseEnd_3042693 := by
    simpa [prefixWord, tailWord_3042693, baseEnd_3042693] using wordTrace_append hprefix tailTrace_3042693
  have hstable : (prefixWord ++ tailWord_3042693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042693).length < 2 ^ (prefixWord ++ tailWord_3042693).sum := by decide
  have hdescent : baseEnd_3042693 < baseStart_3042693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042753 : List Nat := [1, 2, 7, 12]
def baseStart_3042753 : Nat := 118140960795 + 3042753 * 2 ^ 59
def prefixEnd_3042753 : Nat := 4983230072969 + 3 ^ 40 * 3042753 * 2
def baseEnd_3042753 : Nat := 1428801830736203885317

theorem tailTrace_3042753 : CollatzResearch.WordTrace tailWord_3042753 prefixEnd_3042753 1428801830736203885317 := by
  unfold tailWord_3042753
  simp only [CollatzResearch.WordTrace]
  refine ⟨110978319145633016685196913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73985546097088677790131275 110978319145633016685196913)
  ·
    refine ⟨83233739359224762513897685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110978319145633016685196913 83233739359224762513897685)
    ·
      refine ⟨1950790766231830371419477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83233739359224762513897685 1950790766231830371419477)
      ·
        refine ⟨1428801830736203885317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1950790766231830371419477 1428801830736203885317)
        ·
          rfl

theorem cell22_3042753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 12].length) (baseStart_3042753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042753 prefixEnd_3042753 := by exact prefixLift 3042753
  have htrace : WordTrace (prefixWord ++ tailWord_3042753) baseStart_3042753 baseEnd_3042753 := by
    simpa [prefixWord, tailWord_3042753, baseEnd_3042753] using wordTrace_append hprefix tailTrace_3042753
  have hstable : (prefixWord ++ tailWord_3042753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042753).length < 2 ^ (prefixWord ++ tailWord_3042753).sum := by decide
  have hdescent : baseEnd_3042753 < baseStart_3042753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042785 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_3042785 : Nat := 118140960795 + 3042785 * 2 ^ 59
def prefixEnd_3042785 : Nat := 4983230072969 + 3 ^ 40 * 3042785 * 2
def baseEnd_3042785 : Nat := 1041607488860655215595995

theorem tailTrace_3042785 : CollatzResearch.WordTrace tailWord_3042785 prefixEnd_3042785 1041607488860655215595995 := by
  unfold tailWord_3042785
  simp only [CollatzResearch.WordTrace]
  refine ⟨110979486281517086150361809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73986324187678057433574539 110979486281517086150361809)
  ·
    refine ⟨83234614711137814612771357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110979486281517086150361809 83234614711137814612771357)
    ·
      refine ⟨31212980516676680479789259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83234614711137814612771357 31212980516676680479789259)
      ·
        refine ⟨46819470775015020719683889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31212980516676680479789259 46819470775015020719683889)
        ·
          refine ⟨35114603081261265539762917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46819470775015020719683889 35114603081261265539762917)
          ·
            refine ⟨6583988077736487288705547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35114603081261265539762917 6583988077736487288705547)
            ·
              refine ⟨9875982116604730933058321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583988077736487288705547 9875982116604730933058321)
              ·
                refine ⟨7406986587453548199793741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9875982116604730933058321 7406986587453548199793741)
                ·
                  refine ⟨2777619970295080574922653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7406986587453548199793741 2777619970295080574922653)
                  ·
                    refine ⟨1041607488860655215595995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777619970295080574922653 1041607488860655215595995)
                    ·
                      rfl

theorem cell22_3042785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_3042785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042785 prefixEnd_3042785 := by exact prefixLift 3042785
  have htrace : WordTrace (prefixWord ++ tailWord_3042785) baseStart_3042785 baseEnd_3042785 := by
    simpa [prefixWord, tailWord_3042785, baseEnd_3042785] using wordTrace_append hprefix tailTrace_3042785
  have hstable : (prefixWord ++ tailWord_3042785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042785).length < 2 ^ (prefixWord ++ tailWord_3042785).sum := by decide
  have hdescent : baseEnd_3042785 < baseStart_3042785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042798 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_3042798 : Nat := 118140960795 + 3042798 * 2 ^ 59
def prefixEnd_3042798 : Nat := 4983230072969 + 3 ^ 40 * 3042798 * 2
def baseEnd_3042798 : Nat := 347203979675442505006985

theorem tailTrace_3042798 : CollatzResearch.WordTrace tailWord_3042798 prefixEnd_3042798 347203979675442505006985 := by
  unfold tailWord_3042798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872495053808748671323131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73986640286979992913723365 13872495053808748671323131)
  ·
    refine ⟨20808742580713123006984697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13872495053808748671323131 20808742580713123006984697)
    ·
      refine ⟨15606556935534842255238523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20808742580713123006984697 15606556935534842255238523)
      ·
        refine ⟨23409835403302263382857785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606556935534842255238523 23409835403302263382857785)
        ·
          refine ⟨17557376552476697537143339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23409835403302263382857785 17557376552476697537143339)
          ·
            refine ⟨26336064828715046305715009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17557376552476697537143339 26336064828715046305715009)
            ·
              refine ⟨19752048621536284729286257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26336064828715046305715009 19752048621536284729286257)
              ·
                refine ⟨14814036466152213546964693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19752048621536284729286257 14814036466152213546964693)
                ·
                  refine ⟨347203979675442505006985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14814036466152213546964693 347203979675442505006985)
                  ·
                    rfl

theorem cell22_3042798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_3042798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042798 prefixEnd_3042798 := by exact prefixLift 3042798
  have htrace : WordTrace (prefixWord ++ tailWord_3042798) baseStart_3042798 baseEnd_3042798 := by
    simpa [prefixWord, tailWord_3042798, baseEnd_3042798] using wordTrace_append hprefix tailTrace_3042798
  have hstable : (prefixWord ++ tailWord_3042798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042798).length < 2 ^ (prefixWord ++ tailWord_3042798).sum := by decide
  have hdescent : baseEnd_3042798 < baseStart_3042798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042813 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3042813 : Nat := 118140960795 + 3042813 * 2 ^ 59
def prefixEnd_3042813 : Nat := 4983230072969 + 3 ^ 40 * 3042813 * 2
def baseEnd_3042813 : Nat := 1041617073832872475895909

theorem tailTrace_3042813 : CollatzResearch.WordTrace tailWord_3042813 prefixEnd_3042813 1041617073832872475895909 := by
  unfold tailWord_3042813
  simp only [CollatzResearch.WordTrace]
  refine ⟨110980507525415646932381093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73987005016943764621587395 110980507525415646932381093)
  ·
    refine ⟨20808845161015433799821455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110980507525415646932381093 20808845161015433799821455)
    ·
      refine ⟨31213267741523150699732183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20808845161015433799821455 31213267741523150699732183)
      ·
        refine ⟨46819901612284726049598275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31213267741523150699732183 46819901612284726049598275)
        ·
          refine ⟨70229852418427089074397413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46819901612284726049598275 70229852418427089074397413)
          ·
            refine ⟨13168097328455079201449515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70229852418427089074397413 13168097328455079201449515)
            ·
              refine ⟨19752145992682618802174273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13168097328455079201449515 19752145992682618802174273)
              ·
                refine ⟨14814109494511964101630705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19752145992682618802174273 14814109494511964101630705)
                ·
                  refine ⟨11110582120883973076223029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14814109494511964101630705 11110582120883973076223029)
                  ·
                    refine ⟨1041617073832872475895909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11110582120883973076223029 1041617073832872475895909)
                    ·
                      rfl

theorem cell22_3042813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3042813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042813 prefixEnd_3042813 := by exact prefixLift 3042813
  have htrace : WordTrace (prefixWord ++ tailWord_3042813) baseStart_3042813 baseEnd_3042813 := by
    simpa [prefixWord, tailWord_3042813, baseEnd_3042813] using wordTrace_append hprefix tailTrace_3042813
  have hstable : (prefixWord ++ tailWord_3042813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042813).length < 2 ^ (prefixWord ++ tailWord_3042813).sum := by decide
  have hdescent : baseEnd_3042813 < baseStart_3042813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042862 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3042862 : Nat := 118140960795 + 3042862 * 2 ^ 59
def prefixEnd_3042862 : Nat := 4983230072969 + 3 ^ 40 * 3042862 * 2
def baseEnd_3042862 : Nat := 1041633847534252681420759

theorem tailTrace_3042862 : CollatzResearch.WordTrace tailWord_3042862 prefixEnd_3042862 1041633847534252681420759 := by
  unfold tailWord_3042862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872786837779766037614355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73988196468158752200609893 13872786837779766037614355)
  ·
    refine ⟨20809180256669649056421533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13872786837779766037614355 20809180256669649056421533)
    ·
      refine ⟨7803442596251118396158075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20809180256669649056421533 7803442596251118396158075)
      ·
        refine ⟨11705163894376677594237113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7803442596251118396158075 11705163894376677594237113)
        ·
          refine ⟨8778872920782508195677835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11705163894376677594237113 8778872920782508195677835)
          ·
            refine ⟨13168309381173762293516753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778872920782508195677835 13168309381173762293516753)
            ·
              refine ⟨9876232035880321720137565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13168309381173762293516753 9876232035880321720137565)
              ·
                refine ⟨3703587013455120645051587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9876232035880321720137565 3703587013455120645051587)
                ·
                  refine ⟨5555380520182680967577381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3703587013455120645051587 5555380520182680967577381)
                  ·
                    refine ⟨1041633847534252681420759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5555380520182680967577381 1041633847534252681420759)
                    ·
                      rfl

theorem cell22_3042862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3042862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042862 prefixEnd_3042862 := by exact prefixLift 3042862
  have htrace : WordTrace (prefixWord ++ tailWord_3042862) baseStart_3042862 baseEnd_3042862 := by
    simpa [prefixWord, tailWord_3042862, baseEnd_3042862] using wordTrace_append hprefix tailTrace_3042862
  have hstable : (prefixWord ++ tailWord_3042862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042862).length < 2 ^ (prefixWord ++ tailWord_3042862).sum := by decide
  have hdescent : baseEnd_3042862 < baseStart_3042862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042877 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 6]
def baseStart_3042877 : Nat := 118140960795 + 3042877 * 2 ^ 59
def prefixEnd_3042877 : Nat := 4983230072969 + 3 ^ 40 * 3042877 * 2
def baseEnd_3042877 : Nat := 347212994113599214098571

theorem tailTrace_3042877 : CollatzResearch.WordTrace tailWord_3042877 prefixEnd_3042877 347212994113599214098571 := by
  unfold tailWord_3042877
  simp only [CollatzResearch.WordTrace]
  refine ⟨110982841797183785862710885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73988561198122523908473923 110982841797183785862710885)
  ·
    refine ⟨20809282836971959849258291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110982841797183785862710885 20809282836971959849258291)
    ·
      refine ⟨31213924255457939773887437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20809282836971959849258291 31213924255457939773887437)
      ·
        refine ⟨11705221595796727415207789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31213924255457939773887437 11705221595796727415207789)
        ·
          refine ⟨4389458098423772780702921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11705221595796727415207789 4389458098423772780702921)
          ·
            refine ⟨3292093573817829585527191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389458098423772780702921 3292093573817829585527191)
            ·
              refine ⟨4938140360726744378290787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292093573817829585527191 4938140360726744378290787)
              ·
                refine ⟨7407210541090116567436181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938140360726744378290787 7407210541090116567436181)
                ·
                  refine ⟨347212994113599214098571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7407210541090116567436181 347212994113599214098571)
                  ·
                    rfl

theorem cell22_3042877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_3042877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042877 prefixEnd_3042877 := by exact prefixLift 3042877
  have htrace : WordTrace (prefixWord ++ tailWord_3042877) baseStart_3042877 baseEnd_3042877 := by
    simpa [prefixWord, tailWord_3042877, baseEnd_3042877] using wordTrace_append hprefix tailTrace_3042877
  have hstable : (prefixWord ++ tailWord_3042877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042877).length < 2 ^ (prefixWord ++ tailWord_3042877).sum := by decide
  have hdescent : baseEnd_3042877 < baseStart_3042877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042892 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_3042892 : Nat := 118140960795 + 3042892 * 2 ^ 59
def prefixEnd_3042892 : Nat := 4983230072969 + 3 ^ 40 * 3042892 * 2
def baseEnd_3042892 : Nat := 1041644117147342603170667

theorem tailTrace_3042892 : CollatzResearch.WordTrace tailWord_3042892 prefixEnd_3042892 1041644117147342603170667 := by
  unfold tailWord_3042892
  simp only [CollatzResearch.WordTrace]
  refine ⟨55491694446064721712253465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73988925928086295616337953 55491694446064721712253465)
  ·
    refine ⟨41618770834548541284190099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55491694446064721712253465 41618770834548541284190099)
    ·
      refine ⟨62428156251822811926285149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41618770834548541284190099 62428156251822811926285149)
      ·
        refine ⟨23410558594433554472356931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62428156251822811926285149 23410558594433554472356931)
        ·
          refine ⟨35115837891650331708535397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23410558594433554472356931 35115837891650331708535397)
          ·
            refine ⟨6584219604684437195350387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35115837891650331708535397 6584219604684437195350387)
            ·
              refine ⟨9876329407026655793025581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584219604684437195350387 9876329407026655793025581)
              ·
                refine ⟨3703623527634995922384593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9876329407026655793025581 3703623527634995922384593)
                ·
                  refine ⟨2777717645726246941788445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3703623527634995922384593 2777717645726246941788445)
                  ·
                    refine ⟨1041644117147342603170667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777717645726246941788445 1041644117147342603170667)
                    ·
                      rfl

theorem cell22_3042892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_3042892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042892 prefixEnd_3042892 := by exact prefixLift 3042892
  have htrace : WordTrace (prefixWord ++ tailWord_3042892) baseStart_3042892 baseEnd_3042892 := by
    simpa [prefixWord, tailWord_3042892, baseEnd_3042892] using wordTrace_append hprefix tailTrace_3042892
  have hstable : (prefixWord ++ tailWord_3042892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042892).length < 2 ^ (prefixWord ++ tailWord_3042892).sum := by decide
  have hdescent : baseEnd_3042892 < baseStart_3042892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042909 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3042909 : Nat := 118140960795 + 3042909 * 2 ^ 59
def prefixEnd_3042909 : Nat := 4983230072969 + 3 ^ 40 * 3042909 * 2
def baseEnd_3042909 : Nat := 1041649936594760225495615

theorem tailTrace_3042909 : CollatzResearch.WordTrace tailWord_3042909 prefixEnd_3042909 1041649936594760225495615 := by
  unfold tailWord_3042909
  simp only [CollatzResearch.WordTrace]
  refine ⟨110984008933067855327875781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73989339288711903551917187 110984008933067855327875781)
  ·
    refine ⟨20809501674950222873976709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110984008933067855327875781 20809501674950222873976709)
    ·
      refine ⟨3901781564053166788870633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20809501674950222873976709 3901781564053166788870633)
      ·
        refine ⟨2926336173039875091652975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3901781564053166788870633 2926336173039875091652975)
        ·
          refine ⟨4389504259559812637479463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926336173039875091652975 4389504259559812637479463)
          ·
            refine ⟨6584256389339718956219195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389504259559812637479463 6584256389339718956219195)
            ·
              refine ⟨9876384584009578434328793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584256389339718956219195 9876384584009578434328793)
              ·
                refine ⟨7407288438007183825746595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9876384584009578434328793 7407288438007183825746595)
                ·
                  refine ⟨11110932657010775738619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407288438007183825746595 11110932657010775738619893)
                  ·
                    refine ⟨1041649936594760225495615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11110932657010775738619893 1041649936594760225495615)
                    ·
                      rfl

theorem cell22_3042909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3042909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042909 prefixEnd_3042909 := by exact prefixLift 3042909
  have htrace : WordTrace (prefixWord ++ tailWord_3042909) baseStart_3042909 baseEnd_3042909 := by
    simpa [prefixWord, tailWord_3042909, baseEnd_3042909] using wordTrace_append hprefix tailTrace_3042909
  have hstable : (prefixWord ++ tailWord_3042909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042909).length < 2 ^ (prefixWord ++ tailWord_3042909).sum := by decide
  have hdescent : baseEnd_3042909 < baseStart_3042909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3042995 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 6]
def baseStart_3042995 : Nat := 118140960795 + 3042995 * 2 ^ 59
def prefixEnd_3042995 : Nat := 4983230072969 + 3 ^ 40 * 3042995 * 2
def baseEnd_3042995 : Nat := 347226458717428222615117

theorem tailTrace_3042995 : CollatzResearch.WordTrace tailWord_3042995 prefixEnd_3042995 347226458717428222615117 := by
  unfold tailWord_3042995
  simp only [CollatzResearch.WordTrace]
  refine ⟨110987145610756292015506439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73991430407170861343670959 110987145610756292015506439)
  ·
    refine ⟨166480718416134438023259659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110987145610756292015506439 166480718416134438023259659)
    ·
      refine ⟨249721077624201657034889489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166480718416134438023259659 249721077624201657034889489)
      ·
        refine ⟨187290808218151242776167117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249721077624201657034889489 187290808218151242776167117)
        ·
          refine ⟨70234053081806716041062669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187290808218151242776167117 70234053081806716041062669)
          ·
            refine ⟨26337769905677518515398501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70234053081806716041062669 26337769905677518515398501)
            ·
              refine ⟨4938331857314534721637219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26337769905677518515398501 4938331857314534721637219)
              ·
                refine ⟨7407497785971802082455829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938331857314534721637219 7407497785971802082455829)
                ·
                  refine ⟨347226458717428222615117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7407497785971802082455829 347226458717428222615117)
                  ·
                    rfl

theorem cell22_3042995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 6].length) (baseStart_3042995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3042995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3042995 prefixEnd_3042995 := by exact prefixLift 3042995
  have htrace : WordTrace (prefixWord ++ tailWord_3042995) baseStart_3042995 baseEnd_3042995 := by
    simpa [prefixWord, tailWord_3042995, baseEnd_3042995] using wordTrace_append hprefix tailTrace_3042995
  have hstable : (prefixWord ++ tailWord_3042995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3042995).length < 2 ^ (prefixWord ++ tailWord_3042995).sum := by decide
  have hdescent : baseEnd_3042995 < baseStart_3042995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3042995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043025 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3043025 : Nat := 118140960795 + 3043025 * 2 ^ 59
def prefixEnd_3043025 : Nat := 4983230072969 + 3 ^ 40 * 3043025 * 2
def baseEnd_3043025 : Nat := 1041689645765374589595259

theorem tailTrace_3043025 : CollatzResearch.WordTrace tailWord_3043025 prefixEnd_3043025 1041689645765374589595259 := by
  unfold tailWord_3043025
  simp only [CollatzResearch.WordTrace]
  refine ⟨110988239800647607139098529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73992159867098404759399019 110988239800647607139098529)
  ·
    refine ⟨83241179850485705354323897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110988239800647607139098529 83241179850485705354323897)
    ·
      refine ⟨62430884887864279015742923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83241179850485705354323897 62430884887864279015742923)
      ·
        refine ⟨93646327331796418523614385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62430884887864279015742923 93646327331796418523614385)
        ·
          refine ⟨70234745498847313892710789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93646327331796418523614385 70234745498847313892710789)
          ·
            refine ⟨13169014781033871354883273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70234745498847313892710789 13169014781033871354883273)
            ·
              refine ⟨9876761085775403516162455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13169014781033871354883273 9876761085775403516162455)
              ·
                refine ⟨14815141628663105274243683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876761085775403516162455 14815141628663105274243683)
                ·
                  refine ⟨22222712442994657911365525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14815141628663105274243683 22222712442994657911365525)
                  ·
                    refine ⟨1041689645765374589595259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22222712442994657911365525 1041689645765374589595259)
                    ·
                      rfl

theorem cell22_3043025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3043025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043025 prefixEnd_3043025 := by exact prefixLift 3043025
  have htrace : WordTrace (prefixWord ++ tailWord_3043025) baseStart_3043025 baseEnd_3043025 := by
    simpa [prefixWord, tailWord_3043025, baseEnd_3043025] using wordTrace_append hprefix tailTrace_3043025
  have hstable : (prefixWord ++ tailWord_3043025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043025).length < 2 ^ (prefixWord ++ tailWord_3043025).sum := by decide
  have hdescent : baseEnd_3043025 < baseStart_3043025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043089 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 1, 3]
def baseStart_3043089 : Nat := 118140960795 + 3043089 * 2 ^ 59
def prefixEnd_3043089 : Nat := 4983230072969 + 3 ^ 40 * 3043089 * 2
def baseEnd_3043089 : Nat := 1041711554273299755995063

theorem tailTrace_3043089 : CollatzResearch.WordTrace tailWord_3043089 prefixEnd_3043089 1041711554273299755995063 := by
  unfold tailWord_3043089
  simp only [CollatzResearch.WordTrace]
  refine ⟨110990574072415746069428321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73993716048277164046285547 110990574072415746069428321)
  ·
    refine ⟨83242930554311809552071241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110990574072415746069428321 83242930554311809552071241)
    ·
      refine ⟨62432197915733857164053431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83242930554311809552071241 62432197915733857164053431)
      ·
        refine ⟨93648296873600785746080147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62432197915733857164053431 93648296873600785746080147)
        ·
          refine ⟨140472445310401178619120221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93648296873600785746080147 140472445310401178619120221)
          ·
            refine ⟨52677166991400441982170083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140472445310401178619120221 52677166991400441982170083)
            ·
              refine ⟨79015750487100662973255125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52677166991400441982170083 79015750487100662973255125)
              ·
                refine ⟨1851931652041421788435667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79015750487100662973255125 1851931652041421788435667)
                ·
                  refine ⟨2777897478062132682653501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851931652041421788435667 2777897478062132682653501)
                  ·
                    refine ⟨1041711554273299755995063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777897478062132682653501 1041711554273299755995063)
                    ·
                      rfl

theorem cell22_3043089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_3043089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043089 prefixEnd_3043089 := by exact prefixLift 3043089
  have htrace : WordTrace (prefixWord ++ tailWord_3043089) baseStart_3043089 baseEnd_3043089 := by
    simpa [prefixWord, tailWord_3043089, baseEnd_3043089] using wordTrace_append hprefix tailTrace_3043089
  have hstable : (prefixWord ++ tailWord_3043089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043089).length < 2 ^ (prefixWord ++ tailWord_3043089).sum := by decide
  have hdescent : baseEnd_3043089 < baseStart_3043089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043106 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3043106 : Nat := 118140960795 + 3043106 * 2 ^ 59
def prefixEnd_3043106 : Nat := 4983230072969 + 3 ^ 40 * 3043106 * 2
def baseEnd_3043106 : Nat := 1041717373720717378320011

theorem tailTrace_3043106 : CollatzResearch.WordTrace tailWord_3043106 prefixEnd_3043106 1041717373720717378320011 := by
  unfold tailWord_3043106
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747798528338539493199293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73994129408902771981864781 27747798528338539493199293)
  ·
    refine ⟨10405424448126952309949735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27747798528338539493199293 10405424448126952309949735)
    ·
      refine ⟨15608136672190428464924603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10405424448126952309949735 15608136672190428464924603)
      ·
        refine ⟨23412205008285642697386905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15608136672190428464924603 23412205008285642697386905)
        ·
          refine ⟨17559153756214232023040179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23412205008285642697386905 17559153756214232023040179)
          ·
            refine ⟨26338730634321348034560269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17559153756214232023040179 26338730634321348034560269)
            ·
              refine ⟨9877023987870505512960101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26338730634321348034560269 9877023987870505512960101)
              ·
                refine ⟨1851941997725719783680019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9877023987870505512960101 1851941997725719783680019)
                ·
                  refine ⟨2777912996588579675520029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851941997725719783680019 2777912996588579675520029)
                  ·
                    refine ⟨1041717373720717378320011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777912996588579675520029 1041717373720717378320011)
                    ·
                      rfl

theorem cell22_3043106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3043106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043106 prefixEnd_3043106 := by exact prefixLift 3043106
  have htrace : WordTrace (prefixWord ++ tailWord_3043106) baseStart_3043106 baseEnd_3043106 := by
    simpa [prefixWord, tailWord_3043106, baseEnd_3043106] using wordTrace_append hprefix tailTrace_3043106
  have hstable : (prefixWord ++ tailWord_3043106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043106).length < 2 ^ (prefixWord ++ tailWord_3043106).sum := by decide
  have hdescent : baseEnd_3043106 < baseStart_3043106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043132 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3043132 : Nat := 118140960795 + 3043132 * 2 ^ 59
def prefixEnd_3043132 : Nat := 4983230072969 + 3 ^ 40 * 3043132 * 2
def baseEnd_3043132 : Nat := 1041726274052061977169931

theorem tailTrace_3043132 : CollatzResearch.WordTrace tailWord_3043132 prefixEnd_3043132 1041726274052061977169931 := by
  unfold tailWord_3043132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55496071205629982206621825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73994761607506642942162433 55496071205629982206621825)
  ·
    refine ⟨41622053404222486654966369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55496071205629982206621825 41622053404222486654966369)
    ·
      refine ⟨31216540053166864991224777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41622053404222486654966369 31216540053166864991224777)
      ·
        refine ⟨23412405039875148743418583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31216540053166864991224777 23412405039875148743418583)
        ·
          refine ⟨35118607559812723115127875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23412405039875148743418583 35118607559812723115127875)
          ·
            refine ⟨52677911339719084672691813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35118607559812723115127875 52677911339719084672691813)
            ·
              refine ⟨9877108376197328376129715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52677911339719084672691813 9877108376197328376129715)
              ·
                refine ⟨14815662564295992564194573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9877108376197328376129715 14815662564295992564194573)
                ·
                  refine ⟨5555873461610997211572965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14815662564295992564194573 5555873461610997211572965)
                  ·
                    refine ⟨1041726274052061977169931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5555873461610997211572965 1041726274052061977169931)
                    ·
                      rfl

theorem cell22_3043132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3043132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043132 prefixEnd_3043132 := by exact prefixLift 3043132
  have htrace : WordTrace (prefixWord ++ tailWord_3043132) baseStart_3043132 baseEnd_3043132 := by
    simpa [prefixWord, tailWord_3043132, baseEnd_3043132] using wordTrace_append hprefix tailTrace_3043132
  have hstable : (prefixWord ++ tailWord_3043132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043132).length < 2 ^ (prefixWord ++ tailWord_3043132).sum := by decide
  have hdescent : baseEnd_3043132 < baseStart_3043132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043198 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3043198 : Nat := 118140960795 + 3043198 * 2 ^ 59
def prefixEnd_3043198 : Nat := 4983230072969 + 3 ^ 40 * 3043198 * 2
def baseEnd_3043198 : Nat := 347249622400286601673243

theorem tailTrace_3043198 : CollatzResearch.WordTrace tailWord_3043198 prefixEnd_3043198 347249622400286601673243 := by
  unfold tailWord_3043198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874318703627607210643281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73996366419347238456764165 13874318703627607210643281)
  ·
    refine ⟨10405739027720705407982461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13874318703627607210643281 10405739027720705407982461)
    ·
      refine ⟨3902152135395264527993423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10405739027720705407982461 3902152135395264527993423)
      ·
        refine ⟨5853228203092896791990135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902152135395264527993423 5853228203092896791990135)
        ·
          refine ⟨8779842304639345187985203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853228203092896791990135 8779842304639345187985203)
          ·
            refine ⟨13169763456959017781977805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779842304639345187985203 13169763456959017781977805)
            ·
              refine ⟨4938661296359631668241677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13169763456959017781977805 4938661296359631668241677)
              ·
                refine ⟨1851997986134861875590629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4938661296359631668241677 1851997986134861875590629)
                ·
                  refine ⟨347249622400286601673243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1851997986134861875590629 347249622400286601673243)
                  ·
                    rfl

theorem cell22_3043198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3043198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043198 prefixEnd_3043198 := by exact prefixLift 3043198
  have htrace : WordTrace (prefixWord ++ tailWord_3043198) baseStart_3043198 baseEnd_3043198 := by
    simpa [prefixWord, tailWord_3043198, baseEnd_3043198] using wordTrace_append hprefix tailTrace_3043198
  have hstable : (prefixWord ++ tailWord_3043198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043198).length < 2 ^ (prefixWord ++ tailWord_3043198).sum := by decide
  have hdescent : baseEnd_3043198 < baseStart_3043198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043230 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3043230 : Nat := 118140960795 + 3043230 * 2 ^ 59
def prefixEnd_3043230 : Nat := 4983230072969 + 3 ^ 40 * 3043230 * 2
def baseEnd_3043230 : Nat := 1041759821454822388219631

theorem tailTrace_3043230 : CollatzResearch.WordTrace tailWord_3043230 prefixEnd_3043230 1041759821454822388219631 := by
  unfold tailWord_3043230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874464595613115893788893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73997144509936618100207429 13874464595613115893788893)
  ·
    refine ⟨5202924223354918460170835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13874464595613115893788893 5202924223354918460170835)
    ·
      refine ⟨7804386335032377690256253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5202924223354918460170835 7804386335032377690256253)
      ·
        refine ⟨2926644875637141633846095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7804386335032377690256253 2926644875637141633846095)
        ·
          refine ⟨4389967313455712450769143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926644875637141633846095 4389967313455712450769143)
          ·
            refine ⟨6584950970183568676153715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4389967313455712450769143 6584950970183568676153715)
            ·
              refine ⟨9877426455275353014230573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6584950970183568676153715 9877426455275353014230573)
              ·
                refine ⟨3704034920728257380336465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9877426455275353014230573 3704034920728257380336465)
                ·
                  refine ⟨2778026190546193035252349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704034920728257380336465 2778026190546193035252349)
                  ·
                    refine ⟨1041759821454822388219631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778026190546193035252349 1041759821454822388219631)
                    ·
                      rfl

theorem cell22_3043230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3043230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043230 prefixEnd_3043230 := by exact prefixLift 3043230
  have htrace : WordTrace (prefixWord ++ tailWord_3043230) baseStart_3043230 baseEnd_3043230 := by
    simpa [prefixWord, tailWord_3043230, baseEnd_3043230] using wordTrace_append hprefix tailTrace_3043230
  have hstable : (prefixWord ++ tailWord_3043230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043230).length < 2 ^ (prefixWord ++ tailWord_3043230).sum := by decide
  have hdescent : baseEnd_3043230 < baseStart_3043230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_3043267 : Nat := 118140960795 + 3043267 * 2 ^ 59
def prefixEnd_3043267 : Nat := 4983230072969 + 3 ^ 40 * 3043267 * 2
def baseEnd_3043267 : Nat := 1041772487310966625044517

theorem tailTrace_3043267 : CollatzResearch.WordTrace tailWord_3043267 prefixEnd_3043267 1041772487310966625044517 := by
  unfold tailWord_3043267
  simp only [CollatzResearch.WordTrace]
  refine ⟨110997066265770882469408055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73998044177180588312938703 110997066265770882469408055)
  ·
    refine ⟨166495599398656323704112083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110997066265770882469408055 166495599398656323704112083)
    ·
      refine ⟨249743399097984485556168125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166495599398656323704112083 249743399097984485556168125)
      ·
        refine ⟨93653774661744182083563047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249743399097984485556168125 93653774661744182083563047)
        ·
          refine ⟨140480661992616273125344571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93653774661744182083563047 140480661992616273125344571)
          ·
            refine ⟨210720992988924409688016857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140480661992616273125344571 210720992988924409688016857)
            ·
              refine ⟨158040744741693307266012643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210720992988924409688016857 158040744741693307266012643)
              ·
                refine ⟨237061117112539960899018965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158040744741693307266012643 237061117112539960899018965)
                ·
                  refine ⟨5556119932325155333570757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 237061117112539960899018965 5556119932325155333570757)
                  ·
                    refine ⟨1041772487310966625044517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556119932325155333570757 1041772487310966625044517)
                    ·
                      rfl

theorem cell22_3043267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_3043267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043267 prefixEnd_3043267 := by exact prefixLift 3043267
  have htrace : WordTrace (prefixWord ++ tailWord_3043267) baseStart_3043267 baseEnd_3043267 := by
    simpa [prefixWord, tailWord_3043267, baseEnd_3043267] using wordTrace_append hprefix tailTrace_3043267
  have hstable : (prefixWord ++ tailWord_3043267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043267).length < 2 ^ (prefixWord ++ tailWord_3043267).sum := by decide
  have hdescent : baseEnd_3043267 < baseStart_3043267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043284 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3043284 : Nat := 118140960795 + 3043284 * 2 ^ 59
def prefixEnd_3043284 : Nat := 4983230072969 + 3 ^ 40 * 3043284 * 2
def baseEnd_3043284 : Nat := 1041778306758384247369465

theorem tailTrace_3043284 : CollatzResearch.WordTrace tailWord_3043284 prefixEnd_3043284 1041778306758384247369465 := by
  unfold tailWord_3043284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55498843153354647186388453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73998457537806196248517937 55498843153354647186388453)
  ·
    refine ⟨10406033091253996347447835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55498843153354647186388453 10406033091253996347447835)
    ·
      refine ⟨15609049636880994521171753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406033091253996347447835 15609049636880994521171753)
      ·
        refine ⟨11706787227660745890878815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15609049636880994521171753 11706787227660745890878815)
        ·
          refine ⟨17560180841491118836318223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11706787227660745890878815 17560180841491118836318223)
          ·
            refine ⟨26340271262236678254477335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17560180841491118836318223 26340271262236678254477335)
            ·
              refine ⟨39510406893355017381716003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26340271262236678254477335 39510406893355017381716003)
              ·
                refine ⟨59265610340032526072574005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39510406893355017381716003 59265610340032526072574005)
                ·
                  refine ⟨5556150969378049319303813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59265610340032526072574005 5556150969378049319303813)
                  ·
                    refine ⟨1041778306758384247369465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556150969378049319303813 1041778306758384247369465)
                    ·
                      rfl

theorem cell22_3043284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3043284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043284 prefixEnd_3043284 := by exact prefixLift 3043284
  have htrace : WordTrace (prefixWord ++ tailWord_3043284) baseStart_3043284 baseEnd_3043284 := by
    simpa [prefixWord, tailWord_3043284, baseEnd_3043284] using wordTrace_append hprefix tailTrace_3043284
  have hstable : (prefixWord ++ tailWord_3043284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043284).length < 2 ^ (prefixWord ++ tailWord_3043284).sum := by decide
  have hdescent : baseEnd_3043284 < baseStart_3043284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043299 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 6]
def baseStart_3043299 : Nat := 118140960795 + 3043299 * 2 ^ 59
def prefixEnd_3043299 : Nat := 4983230072969 + 3 ^ 40 * 3043299 * 2
def baseEnd_3043299 : Nat := 347261147188309736081473

theorem tailTrace_3043299 : CollatzResearch.WordTrace tailWord_3043299 prefixEnd_3043299 347261147188309736081473 := by
  unfold tailWord_3043299
  simp only [CollatzResearch.WordTrace]
  refine ⟨110998233401654951934572951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73998822267769967956381967 110998233401654951934572951)
  ·
    refine ⟨166497350102482427901859427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110998233401654951934572951 166497350102482427901859427)
    ·
      refine ⟨249746025153723641852789141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166497350102482427901859427 249746025153723641852789141)
      ·
        refine ⟨11706844929080795711849491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249746025153723641852789141 11706844929080795711849491)
        ·
          refine ⟨17560267393621193567774237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11706844929080795711849491 17560267393621193567774237)
          ·
            refine ⟨6585100272607947587915339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17560267393621193567774237 6585100272607947587915339)
            ·
              refine ⟨9877650408911921381873009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585100272607947587915339 9877650408911921381873009)
              ·
                refine ⟨7408237806683941036404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9877650408911921381873009 7408237806683941036404757)
                ·
                  refine ⟨347261147188309736081473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7408237806683941036404757 347261147188309736081473)
                  ·
                    rfl

theorem cell22_3043299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_3043299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043299 prefixEnd_3043299 := by exact prefixLift 3043299
  have htrace : WordTrace (prefixWord ++ tailWord_3043299) baseStart_3043299 baseEnd_3043299 := by
    simpa [prefixWord, tailWord_3043299, baseEnd_3043299] using wordTrace_append hprefix tailTrace_3043299
  have hstable : (prefixWord ++ tailWord_3043299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043299).length < 2 ^ (prefixWord ++ tailWord_3043299).sum := by decide
  have hdescent : baseEnd_3043299 < baseStart_3043299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043318 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3043318 : Nat := 118140960795 + 3043318 * 2 ^ 59
def prefixEnd_3043318 : Nat := 4983230072969 + 3 ^ 40 * 3043318 * 2
def baseEnd_3043318 : Nat := 1041789945653219492019361

theorem tailTrace_3043318 : CollatzResearch.WordTrace tailWord_3043318 prefixEnd_3043318 1041789945653219492019361 := by
  unfold tailWord_3043318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937432899286632386219663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73999284259057412119676405 6937432899286632386219663)
  ·
    refine ⟨10406149348929948579329495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937432899286632386219663 10406149348929948579329495)
    ·
      refine ⟨15609224023394922868994243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406149348929948579329495 15609224023394922868994243)
      ·
        refine ⟨23413836035092384303491365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15609224023394922868994243 23413836035092384303491365)
        ·
          refine ⟨4390094256579822056904631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23413836035092384303491365 4390094256579822056904631)
          ·
            refine ⟨6585141384869733085356947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390094256579822056904631 6585141384869733085356947)
            ·
              refine ⟨9877712077304599628035421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585141384869733085356947 9877712077304599628035421)
              ·
                refine ⟨3704142028989224860513283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9877712077304599628035421 3704142028989224860513283)
                ·
                  refine ⟨5556213043483837290769925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3704142028989224860513283 5556213043483837290769925)
                  ·
                    refine ⟨1041789945653219492019361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556213043483837290769925 1041789945653219492019361)
                    ·
                      rfl

theorem cell22_3043318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3043318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043318 prefixEnd_3043318 := by exact prefixLift 3043318
  have htrace : WordTrace (prefixWord ++ tailWord_3043318) baseStart_3043318 baseEnd_3043318 := by
    simpa [prefixWord, tailWord_3043318, baseEnd_3043318] using wordTrace_append hprefix tailTrace_3043318
  have hstable : (prefixWord ++ tailWord_3043318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043318).length < 2 ^ (prefixWord ++ tailWord_3043318).sum := by decide
  have hdescent : baseEnd_3043318 < baseStart_3043318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043329 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3043329 : Nat := 118140960795 + 3043329 * 2 ^ 59
def prefixEnd_3043329 : Nat := 4983230072969 + 3 ^ 40 * 3043329 * 2
def baseEnd_3043329 : Nat := 1041793711178019129994327

theorem tailTrace_3043329 : CollatzResearch.WordTrace tailWord_3043329 prefixEnd_3043329 1041793711178019129994327 := by
  unfold tailWord_3043329
  simp only [CollatzResearch.WordTrace]
  refine ⟨110999327591546267058165041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73999551727697511372110027 110999327591546267058165041)
  ·
    refine ⟨83249495693659700293623781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110999327591546267058165041 83249495693659700293623781)
    ·
      refine ⟨15609280442561193805054459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83249495693659700293623781 15609280442561193805054459)
      ·
        refine ⟨23413920663841790707581689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15609280442561193805054459 23413920663841790707581689)
        ·
          refine ⟨17560440497881343030686267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23413920663841790707581689 17560440497881343030686267)
          ·
            refine ⟨26340660746822014546029401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17560440497881343030686267 26340660746822014546029401)
            ·
              refine ⟨19755495560116510909522051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26340660746822014546029401 19755495560116510909522051)
              ·
                refine ⟨29633243340174766364283077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19755495560116510909522051 29633243340174766364283077)
                ·
                  refine ⟨5556233126282768693303077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29633243340174766364283077 5556233126282768693303077)
                  ·
                    refine ⟨1041793711178019129994327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556233126282768693303077 1041793711178019129994327)
                    ·
                      rfl

theorem cell22_3043329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3043329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043329 prefixEnd_3043329 := by exact prefixLift 3043329
  have htrace : WordTrace (prefixWord ++ tailWord_3043329) baseStart_3043329 baseEnd_3043329 := by
    simpa [prefixWord, tailWord_3043329, baseEnd_3043329] using wordTrace_append hprefix tailTrace_3043329
  have hstable : (prefixWord ++ tailWord_3043329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043329).length < 2 ^ (prefixWord ++ tailWord_3043329).sum := by decide
  have hdescent : baseEnd_3043329 < baseStart_3043329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043367 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 4]
def baseStart_3043367 : Nat := 118140960795 + 3043367 * 2 ^ 59
def prefixEnd_3043367 : Nat := 4983230072969 + 3 ^ 40 * 3043367 * 2
def baseEnd_3043367 : Nat := 347268906451533232514737

theorem tailTrace_3043367 : CollatzResearch.WordTrace tailWord_3043367 prefixEnd_3043367 347268906451533232514737 := by
  unfold tailWord_3043367
  simp only [CollatzResearch.WordTrace]
  refine ⟨111000713565408599548048355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74000475710272399698698903 111000713565408599548048355)
  ·
    refine ⟨166501070348112899322072533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111000713565408599548048355 166501070348112899322072533)
    ·
      refine ⟨3902368836283896077861075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166501070348112899322072533 3902368836283896077861075)
      ·
        refine ⟨5853553254425844116791613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902368836283896077861075 5853553254425844116791613)
        ·
          refine ⟨2195082470409691543796855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5853553254425844116791613 2195082470409691543796855)
          ·
            refine ⟨3292623705614537315695283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195082470409691543796855 3292623705614537315695283)
            ·
              refine ⟨4938935558421805973542925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292623705614537315695283 4938935558421805973542925)
              ·
                refine ⟨1852100834408177240078597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4938935558421805973542925 1852100834408177240078597)
                ·
                  refine ⟨347268906451533232514737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852100834408177240078597 347268906451533232514737)
                  ·
                    rfl

theorem cell22_3043367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 4].length) (baseStart_3043367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043367 prefixEnd_3043367 := by exact prefixLift 3043367
  have htrace : WordTrace (prefixWord ++ tailWord_3043367) baseStart_3043367 baseEnd_3043367 := by
    simpa [prefixWord, tailWord_3043367, baseEnd_3043367] using wordTrace_append hprefix tailTrace_3043367
  have hstable : (prefixWord ++ tailWord_3043367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043367).length < 2 ^ (prefixWord ++ tailWord_3043367).sum := by decide
  have hdescent : baseEnd_3043367 < baseStart_3043367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043389 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3043389 : Nat := 118140960795 + 3043389 * 2 ^ 59
def prefixEnd_3043389 : Nat := 4983230072969 + 3 ^ 40 * 3043389 * 2
def baseEnd_3043389 : Nat := 347271416801399657831381

theorem tailTrace_3043389 : CollatzResearch.WordTrace tailWord_3043389 prefixEnd_3043389 347271416801399657831381 := by
  unfold tailWord_3043389
  simp only [CollatzResearch.WordTrace]
  refine ⟨111001515971328897305349221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74001010647552598203566147 111001515971328897305349221)
  ·
    refine ⟨20812784244624168244752979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111001515971328897305349221 20812784244624168244752979)
    ·
      refine ⟨31219176366936252367129469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20812784244624168244752979 31219176366936252367129469)
      ·
        refine ⟨11707191137601094637673551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31219176366936252367129469 11707191137601094637673551)
        ·
          refine ⟨17560786706401641956510327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11707191137601094637673551 17560786706401641956510327)
          ·
            refine ⟨26341180059602462934765491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17560786706401641956510327 26341180059602462934765491)
            ·
              refine ⟨39511770089403694402148237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26341180059602462934765491 39511770089403694402148237)
              ·
                refine ⟨14816913783526385400805589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39511770089403694402148237 14816913783526385400805589)
                ·
                  refine ⟨347271416801399657831381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14816913783526385400805589 347271416801399657831381)
                  ·
                    rfl

theorem cell22_3043389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3043389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043389 prefixEnd_3043389 := by exact prefixLift 3043389
  have htrace : WordTrace (prefixWord ++ tailWord_3043389) baseStart_3043389 baseEnd_3043389 := by
    simpa [prefixWord, tailWord_3043389, baseEnd_3043389] using wordTrace_append hprefix tailTrace_3043389
  have hstable : (prefixWord ++ tailWord_3043389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043389).length < 2 ^ (prefixWord ++ tailWord_3043389).sum := by decide
  have hdescent : baseEnd_3043389 < baseStart_3043389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043393 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3043393 : Nat := 118140960795 + 3043393 * 2 ^ 59
def prefixEnd_3043393 : Nat := 4983230072969 + 3 ^ 40 * 3043393 * 2
def baseEnd_3043393 : Nat := 1041815619685944296394131

theorem tailTrace_3043393 : CollatzResearch.WordTrace tailWord_3043393 prefixEnd_3043393 1041815619685944296394131 := by
  unfold tailWord_3043393
  simp only [CollatzResearch.WordTrace]
  refine ⟨111001661863314405988494833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74001107908876270658996555 111001661863314405988494833)
  ·
    refine ⟨83251246397485804491371125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111001661863314405988494833 83251246397485804491371125)
    ·
      refine ⟨7804804349764294171066043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83251246397485804491371125 7804804349764294171066043)
      ·
        refine ⟨11707206524646441256599065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7804804349764294171066043 11707206524646441256599065)
        ·
          refine ⟨8780404893484830942449299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11707206524646441256599065 8780404893484830942449299)
          ·
            refine ⟨13170607340227246413673949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8780404893484830942449299 13170607340227246413673949)
            ·
              refine ⟨4938977752585217405127731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13170607340227246413673949 4938977752585217405127731)
              ·
                refine ⟨7408466628877826107691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938977752585217405127731 7408466628877826107691597)
                ·
                  refine ⟨2778174985829184790384349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7408466628877826107691597 2778174985829184790384349)
                  ·
                    refine ⟨1041815619685944296394131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778174985829184790384349 1041815619685944296394131)
                    ·
                      rfl

theorem cell22_3043393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3043393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043393 prefixEnd_3043393 := by exact prefixLift 3043393
  have htrace : WordTrace (prefixWord ++ tailWord_3043393) baseStart_3043393 baseEnd_3043393 := by
    simpa [prefixWord, tailWord_3043393, baseEnd_3043393] using wordTrace_append hprefix tailTrace_3043393
  have hstable : (prefixWord ++ tailWord_3043393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043393).length < 2 ^ (prefixWord ++ tailWord_3043393).sum := by decide
  have hdescent : baseEnd_3043393 < baseStart_3043393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043404 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_3043404 : Nat := 118140960795 + 3043404 * 2 ^ 59
def prefixEnd_3043404 : Nat := 4983230072969 + 3 ^ 40 * 3043404 * 2
def baseEnd_3043404 : Nat := 1041819385210743934369097

theorem tailTrace_3043404 : CollatzResearch.WordTrace tailWord_3043404 prefixEnd_3043404 1041819385210743934369097 := by
  unfold tailWord_3043404
  simp only [CollatzResearch.WordTrace]
  refine ⟨55501031533137277433572633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74001375377516369911430177 55501031533137277433572633)
  ·
    refine ⟨41625773649852958075179475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55501031533137277433572633 41625773649852958075179475)
    ·
      refine ⟨62438660474779437112769213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41625773649852958075179475 62438660474779437112769213)
      ·
        refine ⟨23414497678042288917288455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62438660474779437112769213 23414497678042288917288455)
        ·
          refine ⟨35121746517063433375932683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23414497678042288917288455 35121746517063433375932683)
          ·
            refine ⟨52682619775595150063899025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35121746517063433375932683 52682619775595150063899025)
            ·
              refine ⟨39511964831696362547924269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52682619775595150063899025 39511964831696362547924269)
              ·
                refine ⟨14816986811886135955471601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39511964831696362547924269 14816986811886135955471601)
                ·
                  refine ⟨11112740108914601966603701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14816986811886135955471601 11112740108914601966603701)
                  ·
                    refine ⟨1041819385210743934369097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11112740108914601966603701 1041819385210743934369097)
                    ·
                      rfl

theorem cell22_3043404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_3043404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043404 prefixEnd_3043404 := by exact prefixLift 3043404
  have htrace : WordTrace (prefixWord ++ tailWord_3043404) baseStart_3043404 baseEnd_3043404 := by
    simpa [prefixWord, tailWord_3043404, baseEnd_3043404] using wordTrace_append hprefix tailTrace_3043404
  have hstable : (prefixWord ++ tailWord_3043404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043404).length < 2 ^ (prefixWord ++ tailWord_3043404).sum := by decide
  have hdescent : baseEnd_3043404 < baseStart_3043404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043406 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_3043406 : Nat := 118140960795 + 3043406 * 2 ^ 59
def prefixEnd_3043406 : Nat := 4983230072969 + 3 ^ 40 * 3043406 * 2
def baseEnd_3043406 : Nat := 347273356617205531939697

theorem tailTrace_3043406 : CollatzResearch.WordTrace tailWord_3043406 prefixEnd_3043406 347273356617205531939697 := by
  unfold tailWord_3043406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13875267001533413651089759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74001424008178206139145381 13875267001533413651089759)
  ·
    refine ⟨20812900502300120476634639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13875267001533413651089759 20812900502300120476634639)
    ·
      refine ⟨31219350753450180714951959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20812900502300120476634639 31219350753450180714951959)
      ·
        refine ⟨46829026130175271072427939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31219350753450180714951959 46829026130175271072427939)
        ·
          refine ⟨70243539195262906608641909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46829026130175271072427939 70243539195262906608641909)
          ·
            refine ⟨6585331799555897494560179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70243539195262906608641909 6585331799555897494560179)
            ·
              refine ⟨9877997699333846241840269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585331799555897494560179 9877997699333846241840269)
              ·
                refine ⟨3704249137250192340690101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9877997699333846241840269 3704249137250192340690101)
                ·
                  refine ⟨347273356617205531939697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3704249137250192340690101 347273356617205531939697)
                  ·
                    rfl

theorem cell22_3043406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_3043406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043406 prefixEnd_3043406 := by exact prefixLift 3043406
  have htrace : WordTrace (prefixWord ++ tailWord_3043406) baseStart_3043406 baseEnd_3043406 := by
    simpa [prefixWord, tailWord_3043406, baseEnd_3043406] using wordTrace_append hprefix tailTrace_3043406
  have hstable : (prefixWord ++ tailWord_3043406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043406).length < 2 ^ (prefixWord ++ tailWord_3043406).sum := by decide
  have hdescent : baseEnd_3043406 < baseStart_3043406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043466 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3043466 : Nat := 118140960795 + 3043466 * 2 ^ 59
def prefixEnd_3043466 : Nat := 4983230072969 + 3 ^ 40 * 3043466 * 2
def baseEnd_3043466 : Nat := 1041840609077796439318907

theorem tailTrace_3043466 : CollatzResearch.WordTrace tailWord_3043466 prefixEnd_3043466 1041840609077796439318907 := by
  unfold tailWord_3043466
  simp only [CollatzResearch.WordTrace]
  refine ⟨27751081098012484863975563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74002882928033292970601501 27751081098012484863975563)
  ·
    refine ⟨41626621647018727295963345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27751081098012484863975563 41626621647018727295963345)
    ·
      refine ⟨31219966235264045471972509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41626621647018727295963345 31219966235264045471972509)
      ·
        refine ⟨11707487338224017051989691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31219966235264045471972509 11707487338224017051989691)
        ·
          refine ⟨17561231007336025577984537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11707487338224017051989691 17561231007336025577984537)
          ·
            refine ⟨13170923255502019183488403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17561231007336025577984537 13170923255502019183488403)
            ·
              refine ⟨19756384883253028775232605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13170923255502019183488403 19756384883253028775232605)
              ·
                refine ⟨7408644331219885790712227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19756384883253028775232605 7408644331219885790712227)
                ·
                  refine ⟨11112966496829828686068341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408644331219885790712227 11112966496829828686068341)
                  ·
                    refine ⟨1041840609077796439318907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11112966496829828686068341 1041840609077796439318907)
                    ·
                      rfl

theorem cell22_3043466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3043466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043466 prefixEnd_3043466 := by exact prefixLift 3043466
  have htrace : WordTrace (prefixWord ++ tailWord_3043466) baseStart_3043466 baseEnd_3043466 := by
    simpa [prefixWord, tailWord_3043466, baseEnd_3043466] using wordTrace_append hprefix tailTrace_3043466
  have hstable : (prefixWord ++ tailWord_3043466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043466).length < 2 ^ (prefixWord ++ tailWord_3043466).sum := by decide
  have hdescent : baseEnd_3043466 < baseStart_3043466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043478 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3043478 : Nat := 118140960795 + 3043478 * 2 ^ 59
def prefixEnd_3043478 : Nat := 4983230072969 + 3 ^ 40 * 3043478 * 2
def baseEnd_3043478 : Nat := 1041844716923032408018871

theorem tailTrace_3043478 : CollatzResearch.WordTrace tailWord_3043478 prefixEnd_3043478 1041844716923032408018871 := by
  unfold tailWord_3043478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937797629250404094083693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74003174712004310336892725 6937797629250404094083693)
  ·
    refine ⟨2601674110968901535281385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6937797629250404094083693 2601674110968901535281385)
    ·
      refine ⟨1951255583226676151461039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2601674110968901535281385 1951255583226676151461039)
      ·
        refine ⟨2926883374840014227191559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951255583226676151461039 2926883374840014227191559)
        ·
          refine ⟨4390325062260021340787339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2926883374840014227191559 4390325062260021340787339)
          ·
            refine ⟨6585487593390032011181009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390325062260021340787339 6585487593390032011181009)
            ·
              refine ⟨4939115695042524008385757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585487593390032011181009 4939115695042524008385757)
              ·
                refine ⟨1852168385640946503144659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4939115695042524008385757 1852168385640946503144659)
                ·
                  refine ⟨2778252578461419754716989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852168385640946503144659 2778252578461419754716989)
                  ·
                    refine ⟨1041844716923032408018871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778252578461419754716989 1041844716923032408018871)
                    ·
                      rfl

theorem cell22_3043478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3043478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043478 prefixEnd_3043478 := by exact prefixLift 3043478
  have htrace : WordTrace (prefixWord ++ tailWord_3043478) baseStart_3043478 baseEnd_3043478 := by
    simpa [prefixWord, tailWord_3043478, baseEnd_3043478] using wordTrace_append hprefix tailTrace_3043478
  have hstable : (prefixWord ++ tailWord_3043478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043478).length < 2 ^ (prefixWord ++ tailWord_3043478).sum := by decide
  have hdescent : baseEnd_3043478 < baseStart_3043478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043545 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 1, 3]
def baseStart_3043545 : Nat := 118140960795 + 3043545 * 2 ^ 59
def prefixEnd_3043545 : Nat := 4983230072969 + 3 ^ 40 * 3043545 * 2
def baseEnd_3043545 : Nat := 1041867652392266566593665

theorem tailTrace_3043545 : CollatzResearch.WordTrace tailWord_3043545 prefixEnd_3043545 1041867652392266566593665 := by
  unfold tailWord_3043545
  simp only [CollatzResearch.WordTrace]
  refine ⟨111007205758763735948028089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74004803839175823965352059 111007205758763735948028089)
  ·
    refine ⟨83255404319072801961021067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111007205758763735948028089 83255404319072801961021067)
    ·
      refine ⟨124883106478609202941531601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83255404319072801961021067 124883106478609202941531601)
      ·
        refine ⟨93662329858956902206148701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124883106478609202941531601 93662329858956902206148701)
        ·
          refine ⟨35123373697108838327305763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93662329858956902206148701 35123373697108838327305763)
          ·
            refine ⟨52685060545663257490958645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35123373697108838327305763 52685060545663257490958645)
            ·
              refine ⟨4939224426155930389777373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52685060545663257490958645 4939224426155930389777373)
              ·
                refine ⟨1852209159808473896166515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4939224426155930389777373 1852209159808473896166515)
                ·
                  refine ⟨2778313739712710844249773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852209159808473896166515 2778313739712710844249773)
                  ·
                    refine ⟨1041867652392266566593665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778313739712710844249773 1041867652392266566593665)
                    ·
                      rfl

theorem cell22_3043545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_3043545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043545 prefixEnd_3043545 := by exact prefixLift 3043545
  have htrace : WordTrace (prefixWord ++ tailWord_3043545) baseStart_3043545 baseEnd_3043545 := by
    simpa [prefixWord, tailWord_3043545, baseEnd_3043545] using wordTrace_append hprefix tailTrace_3043545
  have hstable : (prefixWord ++ tailWord_3043545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043545).length < 2 ^ (prefixWord ++ tailWord_3043545).sum := by decide
  have hdescent : baseEnd_3043545 < baseStart_3043545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043562 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3043562 : Nat := 118140960795 + 3043562 * 2 ^ 59
def prefixEnd_3043562 : Nat := 4983230072969 + 3 ^ 40 * 3043562 * 2
def baseEnd_3043562 : Nat := 1041873471839684188918613

theorem tailTrace_3043562 : CollatzResearch.WordTrace tailWord_3043562 prefixEnd_3043562 1041873471839684188918613 := by
  unfold tailWord_3043562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27751956449925536962849235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74005217199801431900931293 27751956449925536962849235)
  ·
    refine ⟨41627934674888305444273853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27751956449925536962849235 41627934674888305444273853)
    ·
      refine ⟨15610475503083114541602695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41627934674888305444273853 15610475503083114541602695)
      ·
        refine ⟨23415713254624671812404043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15610475503083114541602695 23415713254624671812404043)
        ·
          refine ⟨35123569881937007718606065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23415713254624671812404043 35123569881937007718606065)
          ·
            refine ⟨26342677411452755788954549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35123569881937007718606065 26342677411452755788954549)
            ·
              refine ⟨2469626007323695855214489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26342677411452755788954549 2469626007323695855214489)
              ·
                refine ⟨1852219505492771891410867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469626007323695855214489 1852219505492771891410867)
                ·
                  refine ⟨2778329258239157837116301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852219505492771891410867 2778329258239157837116301)
                  ·
                    refine ⟨1041873471839684188918613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778329258239157837116301 1041873471839684188918613)
                    ·
                      rfl

theorem cell22_3043562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3043562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043562 prefixEnd_3043562 := by exact prefixLift 3043562
  have htrace : WordTrace (prefixWord ++ tailWord_3043562) baseStart_3043562 baseEnd_3043562 := by
    simpa [prefixWord, tailWord_3043562, baseEnd_3043562] using wordTrace_append hprefix tailTrace_3043562
  have hstable : (prefixWord ++ tailWord_3043562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043562).length < 2 ^ (prefixWord ++ tailWord_3043562).sum := by decide
  have hdescent : baseEnd_3043562 < baseStart_3043562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043571 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_3043571 : Nat := 118140960795 + 3043571 * 2 ^ 59
def prefixEnd_3043571 : Nat := 4983230072969 + 3 ^ 40 * 3043571 * 2
def baseEnd_3043571 : Nat := 1041876552723611165443585

theorem tailTrace_3043571 : CollatzResearch.WordTrace tailWord_3043571 prefixEnd_3043571 1041876552723611165443585 := by
  unfold tailWord_3043571
  simp only [CollatzResearch.WordTrace]
  refine ⟨111008154056669542388474567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74005436037779694925649711 111008154056669542388474567)
  ·
    refine ⟨166512231085004313582711851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111008154056669542388474567 166512231085004313582711851)
    ·
      refine ⟨249768346627506470374067777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166512231085004313582711851 249768346627506470374067777)
      ·
        refine ⟨187326259970629852780550833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249768346627506470374067777 187326259970629852780550833)
        ·
          refine ⟨140494694977972389585413125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187326259970629852780550833 140494694977972389585413125)
          ·
            refine ⟨26342755308369823047264961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140494694977972389585413125 26342755308369823047264961)
            ·
              refine ⟨19757066481277367285448721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26342755308369823047264961 19757066481277367285448721)
              ·
                refine ⟨14817799860958025464086541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19757066481277367285448721 14817799860958025464086541)
                ·
                  refine ⟨5556674947859259549032453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14817799860958025464086541 5556674947859259549032453)
                  ·
                    refine ⟨1041876552723611165443585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556674947859259549032453 1041876552723611165443585)
                    ·
                      rfl

theorem cell22_3043571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_3043571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043571 prefixEnd_3043571 := by exact prefixLift 3043571
  have htrace : WordTrace (prefixWord ++ tailWord_3043571) baseStart_3043571 baseEnd_3043571 := by
    simpa [prefixWord, tailWord_3043571, baseEnd_3043571] using wordTrace_append hprefix tailTrace_3043571
  have hstable : (prefixWord ++ tailWord_3043571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043571).length < 2 ^ (prefixWord ++ tailWord_3043571).sum := by decide
  have hdescent : baseEnd_3043571 < baseStart_3043571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043601 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3043601 : Nat := 118140960795 + 3043601 * 2 ^ 59
def prefixEnd_3043601 : Nat := 4983230072969 + 3 ^ 40 * 3043601 * 2
def baseEnd_3043601 : Nat := 1041886822336701087193493

theorem tailTrace_3043601 : CollatzResearch.WordTrace tailWord_3043601 prefixEnd_3043601 1041886822336701087193493 := by
  unfold tailWord_3043601
  simp only [CollatzResearch.WordTrace]
  refine ⟨111009248246560857512066657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74006165497707238341377771 111009248246560857512066657)
  ·
    refine ⟨83256936184920643134049993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111009248246560857512066657 83256936184920643134049993)
    ·
      refine ⟨62442702138690482350537495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83256936184920643134049993 62442702138690482350537495)
      ·
        refine ⟨93664053208035723525806243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62442702138690482350537495 93664053208035723525806243)
        ·
          refine ⟨140496079812053585288709365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93664053208035723525806243 140496079812053585288709365)
          ·
            refine ⟨13171507482380023620816503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140496079812053585288709365 13171507482380023620816503)
            ·
              refine ⟨19757261223570035431224755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13171507482380023620816503 19757261223570035431224755)
              ·
                refine ⟨29635891835355053146837133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19757261223570035431224755 29635891835355053146837133)
                ·
                  refine ⟨11113459438258144930063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29635891835355053146837133 11113459438258144930063925)
                  ·
                    refine ⟨1041886822336701087193493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11113459438258144930063925 1041886822336701087193493)
                    ·
                      rfl

theorem cell22_3043601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3043601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043601 prefixEnd_3043601 := by exact prefixLift 3043601
  have htrace : WordTrace (prefixWord ++ tailWord_3043601) baseStart_3043601 baseEnd_3043601 := by
    simpa [prefixWord, tailWord_3043601, baseEnd_3043601] using wordTrace_append hprefix tailTrace_3043601
  have hstable : (prefixWord ++ tailWord_3043601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043601).length < 2 ^ (prefixWord ++ tailWord_3043601).sum := by decide
  have hdescent : baseEnd_3043601 < baseStart_3043601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043620 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3043620 : Nat := 118140960795 + 3043620 * 2 ^ 59
def prefixEnd_3043620 : Nat := 4983230072969 + 3 ^ 40 * 3043620 * 2
def baseEnd_3043620 : Nat := 347297775474997123656145

theorem tailTrace_3043620 : CollatzResearch.WordTrace tailWord_3043620 prefixEnd_3043620 347297775474997123656145 := by
  unfold tailWord_3043620
  simp only [CollatzResearch.WordTrace]
  refine ⟨55504970616746011878504157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74006627488994682504672209 55504970616746011878504157)
  ·
    refine ⟨20814363981279754454439059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55504970616746011878504157 20814363981279754454439059)
    ·
      refine ⟨31221545971919631681658589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20814363981279754454439059 31221545971919631681658589)
      ·
        refine ⟨11708079739469861880621971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31221545971919631681658589 11708079739469861880621971)
        ·
          refine ⟨17562119609204792820932957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708079739469861880621971 17562119609204792820932957)
          ·
            refine ⟨6585794853451797307849859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17562119609204792820932957 6585794853451797307849859)
            ·
              refine ⟨9878692280177695961774789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585794853451797307849859 9878692280177695961774789)
              ·
                refine ⟨1852254802533317992832773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9878692280177695961774789 1852254802533317992832773)
                ·
                  refine ⟨347297775474997123656145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852254802533317992832773 347297775474997123656145)
                  ·
                    rfl

theorem cell22_3043620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3043620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043620 prefixEnd_3043620 := by exact prefixLift 3043620
  have htrace : WordTrace (prefixWord ++ tailWord_3043620) baseStart_3043620 baseEnd_3043620 := by
    simpa [prefixWord, tailWord_3043620, baseEnd_3043620] using wordTrace_append hprefix tailTrace_3043620
  have hstable : (prefixWord ++ tailWord_3043620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043620).length < 2 ^ (prefixWord ++ tailWord_3043620).sum := by decide
  have hdescent : baseEnd_3043620 < baseStart_3043620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043631 : List Nat := [1, 1, 2, 1, 2, 1, 7, 7]
def baseStart_3043631 : Nat := 118140960795 + 3043631 * 2 ^ 59
def prefixEnd_3043631 : Nat := 4983230072969 + 3 ^ 40 * 3043631 * 2
def baseEnd_3043631 : Nat := 115766343549976778771489

theorem tailTrace_3043631 : CollatzResearch.WordTrace tailWord_3043631 prefixEnd_3043631 115766343549976778771489 := by
  unfold tailWord_3043631
  simp only [CollatzResearch.WordTrace]
  refine ⟨111010342436452172635658747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74006894957634781757105831 111010342436452172635658747)
  ·
    refine ⟨166515513654678258953488121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111010342436452172635658747 166515513654678258953488121)
    ·
      refine ⟨124886635241008694215116091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166515513654678258953488121 124886635241008694215116091)
      ·
        refine ⟨187329952861513041322674137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124886635241008694215116091 187329952861513041322674137)
        ·
          refine ⟨140497464646134780992005603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187329952861513041322674137 140497464646134780992005603)
          ·
            refine ⟨210746196969202171488008405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140497464646134780992005603 210746196969202171488008405)
            ·
              refine ⟨4939363991465675894250197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 210746196969202171488008405 4939363991465675894250197)
              ·
                refine ⟨115766343549976778771489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4939363991465675894250197 115766343549976778771489)
                ·
                  rfl

theorem cell22_3043631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 7].length) (baseStart_3043631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043631 prefixEnd_3043631 := by exact prefixLift 3043631
  have htrace : WordTrace (prefixWord ++ tailWord_3043631) baseStart_3043631 baseEnd_3043631 := by
    simpa [prefixWord, tailWord_3043631, baseEnd_3043631] using wordTrace_append hprefix tailTrace_3043631
  have hstable : (prefixWord ++ tailWord_3043631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043631).length < 2 ^ (prefixWord ++ tailWord_3043631).sum := by decide
  have hdescent : baseEnd_3043631 < baseStart_3043631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043669 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_3043669 : Nat := 118140960795 + 3043669 * 2 ^ 59
def prefixEnd_3043669 : Nat := 4983230072969 + 3 ^ 40 * 3043669 * 2
def baseEnd_3043669 : Nat := 1041910100126371576493285

theorem tailTrace_3043669 : CollatzResearch.WordTrace tailWord_3043669 prefixEnd_3043669 1041910100126371576493285 := by
  unfold tailWord_3043669
  simp only [CollatzResearch.WordTrace]
  refine ⟨111011728410314505125542061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74007818940209670083694707 111011728410314505125542061)
  ·
    refine ⟨41629398153867939422078273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111011728410314505125542061 41629398153867939422078273)
    ·
      refine ⟨31222048615400954566558705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41629398153867939422078273 31222048615400954566558705)
      ·
        refine ⟨23416536461550715924919029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31222048615400954566558705 23416536461550715924919029)
        ·
          refine ⟨2195300293270379617961159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23416536461550715924919029 2195300293270379617961159)
          ·
            refine ⟨3292950439905569426941739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195300293270379617961159 3292950439905569426941739)
            ·
              refine ⟨4939425659858354140412609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292950439905569426941739 4939425659858354140412609)
              ·
                refine ⟨3704569244893765605309457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4939425659858354140412609 3704569244893765605309457)
                ·
                  refine ⟨2778426933670324203982093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704569244893765605309457 2778426933670324203982093)
                  ·
                    refine ⟨1041910100126371576493285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778426933670324203982093 1041910100126371576493285)
                    ·
                      rfl

theorem cell22_3043669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_3043669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043669 prefixEnd_3043669 := by exact prefixLift 3043669
  have htrace : WordTrace (prefixWord ++ tailWord_3043669) baseStart_3043669 baseEnd_3043669 := by
    simpa [prefixWord, tailWord_3043669, baseEnd_3043669] using wordTrace_append hprefix tailTrace_3043669
  have hstable : (prefixWord ++ tailWord_3043669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043669).length < 2 ^ (prefixWord ++ tailWord_3043669).sum := by decide
  have hdescent : baseEnd_3043669 < baseStart_3043669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043757 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3043757 : Nat := 118140960795 + 3043757 * 2 ^ 59
def prefixEnd_3043757 : Nat := 4983230072969 + 3 ^ 40 * 3043757 * 2
def baseEnd_3043757 : Nat := 1041940224324768680293015

theorem tailTrace_3043757 : CollatzResearch.WordTrace tailWord_3043757 prefixEnd_3043757 1041940224324768680293015 := by
  unfold tailWord_3043757
  simp only [CollatzResearch.WordTrace]
  refine ⟨111014938033995696154745525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74009958689330464103163683 111014938033995696154745525)
  ·
    refine ⟨10407650440687096514507393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111014938033995696154745525 10407650440687096514507393)
    ·
      refine ⟨7805737830515322385880545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10407650440687096514507393 7805737830515322385880545)
      ·
        refine ⟨5854303372886491789410409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7805737830515322385880545 5854303372886491789410409)
        ·
          refine ⟨4390727529664868842057807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5854303372886491789410409 4390727529664868842057807)
          ·
            refine ⟨6586091294497303263086711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390727529664868842057807 6586091294497303263086711)
            ·
              refine ⟨9879136941745954894630067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586091294497303263086711 9879136941745954894630067)
              ·
                refine ⟨14818705412618932341945101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9879136941745954894630067 14818705412618932341945101)
                ·
                  refine ⟨5557014529732099628229413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14818705412618932341945101 5557014529732099628229413)
                  ·
                    refine ⟨1041940224324768680293015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5557014529732099628229413 1041940224324768680293015)
                    ·
                      rfl

theorem cell22_3043757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3043757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043757 prefixEnd_3043757 := by exact prefixLift 3043757
  have htrace : WordTrace (prefixWord ++ tailWord_3043757) baseStart_3043757 baseEnd_3043757 := by
    simpa [prefixWord, tailWord_3043757, baseEnd_3043757] using wordTrace_append hprefix tailTrace_3043757
  have hstable : (prefixWord ++ tailWord_3043757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043757).length < 2 ^ (prefixWord ++ tailWord_3043757).sum := by decide
  have hdescent : baseEnd_3043757 < baseStart_3043757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043843 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_3043843 : Nat := 118140960795 + 3043843 * 2 ^ 59
def prefixEnd_3043843 : Nat := 4983230072969 + 3 ^ 40 * 3043843 * 2
def baseEnd_3043843 : Nat := 1041969663882293122642751

theorem tailTrace_3043843 : CollatzResearch.WordTrace tailWord_3043843 prefixEnd_3043843 1041969663882293122642751 := by
  unfold tailWord_3043843
  simp only [CollatzResearch.WordTrace]
  refine ⟨111018074711684132842376183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74012049807789421894917455 111018074711684132842376183)
  ·
    refine ⟨166527112067526199263564275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111018074711684132842376183 166527112067526199263564275)
    ·
      refine ⟨249790668101289298895346413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166527112067526199263564275 249790668101289298895346413)
      ·
        refine ⟨93671500537983487085754905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249790668101289298895346413 93671500537983487085754905)
        ·
          refine ⟨70253625403487615314316179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93671500537983487085754905 70253625403487615314316179)
          ·
            refine ⟨105380438105231422971474269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70253625403487615314316179 105380438105231422971474269)
            ·
              refine ⟨39517664289461783614302851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105380438105231422971474269 39517664289461783614302851)
              ·
                refine ⟨59276496434192675421454277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39517664289461783614302851 59276496434192675421454277)
                ·
                  refine ⟨11114343081411126641522677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59276496434192675421454277 11114343081411126641522677)
                  ·
                    refine ⟨1041969663882293122642751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11114343081411126641522677 1041969663882293122642751)
                    ·
                      rfl

theorem cell22_3043843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_3043843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043843 prefixEnd_3043843 := by exact prefixLift 3043843
  have htrace : WordTrace (prefixWord ++ tailWord_3043843) baseStart_3043843 baseEnd_3043843 := by
    simpa [prefixWord, tailWord_3043843, baseEnd_3043843] using wordTrace_append hprefix tailTrace_3043843
  have hstable : (prefixWord ++ tailWord_3043843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043843).length < 2 ^ (prefixWord ++ tailWord_3043843).sum := by decide
  have hdescent : baseEnd_3043843 < baseStart_3043843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043845 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 5]
def baseStart_3043845 : Nat := 118140960795 + 3043845 * 2 ^ 59
def prefixEnd_3043845 : Nat := 4983230072969 + 3 ^ 40 * 3043845 * 2
def baseEnd_3043845 : Nat := 347323449507721928030915

theorem tailTrace_3043845 : CollatzResearch.WordTrace tailWord_3043845 prefixEnd_3043845 347323449507721928030915 := by
  unfold tailWord_3043845
  simp only [CollatzResearch.WordTrace]
  refine ⟨111018147657676887183948989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74012098438451258122632659 111018147657676887183948989)
  ·
    refine ⟨41631805371628832693980871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111018147657676887183948989 41631805371628832693980871)
    ·
      refine ⟨62447708057443249040971307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41631805371628832693980871 62447708057443249040971307)
      ·
        refine ⟨93671562086164873561456961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62447708057443249040971307 93671562086164873561456961)
        ·
          refine ⟨70253671564623655171092721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93671562086164873561456961 70253671564623655171092721)
          ·
            refine ⟨52690253673467741378319541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70253671564623655171092721 52690253673467741378319541)
            ·
              refine ⟨4939711281887600754217457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52690253673467741378319541 4939711281887600754217457)
              ·
                refine ⟨3704783461415700565663093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4939711281887600754217457 3704783461415700565663093)
                ·
                  refine ⟨347323449507721928030915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3704783461415700565663093 347323449507721928030915)
                  ·
                    rfl

theorem cell22_3043845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_3043845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043845 prefixEnd_3043845 := by exact prefixLift 3043845
  have htrace : WordTrace (prefixWord ++ tailWord_3043845) baseStart_3043845 baseEnd_3043845 := by
    simpa [prefixWord, tailWord_3043845, baseEnd_3043845] using wordTrace_append hprefix tailTrace_3043845
  have hstable : (prefixWord ++ tailWord_3043845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043845).length < 2 ^ (prefixWord ++ tailWord_3043845).sum := by decide
  have hdescent : baseEnd_3043845 < baseStart_3043845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043937 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3043937 : Nat := 118140960795 + 3043937 * 2 ^ 59
def prefixEnd_3043937 : Nat := 4983230072969 + 3 ^ 40 * 3043937 * 2
def baseEnd_3043937 : Nat := 1042001842003308210792463

theorem tailTrace_3043937 : CollatzResearch.WordTrace tailWord_3043937 prefixEnd_3043937 1042001842003308210792463 := by
  unfold tailWord_3043937
  simp only [CollatzResearch.WordTrace]
  refine ⟨111021503173343586896298065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74014335448895724597532043 111021503173343586896298065)
  ·
    refine ⟨83266127380007690172223549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111021503173343586896298065 83266127380007690172223549)
    ·
      refine ⟨31224797767502883814583831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83266127380007690172223549 31224797767502883814583831)
      ·
        refine ⟨46837196651254325721875747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31224797767502883814583831 46837196651254325721875747)
        ·
          refine ⟨70255794976881488582813621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46837196651254325721875747 70255794976881488582813621)
          ·
            refine ⟨6586480779082639554638777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70255794976881488582813621 6586480779082639554638777)
            ·
              refine ⟨4939860584311979665979083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6586480779082639554638777 4939860584311979665979083)
              ·
                refine ⟨7409790876467969498968625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939860584311979665979083 7409790876467969498968625)
                ·
                  refine ⟨5557343157350977124226469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7409790876467969498968625 5557343157350977124226469)
                  ·
                    refine ⟨1042001842003308210792463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5557343157350977124226469 1042001842003308210792463)
                    ·
                      rfl

theorem cell22_3043937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3043937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043937 prefixEnd_3043937 := by exact prefixLift 3043937
  have htrace : WordTrace (prefixWord ++ tailWord_3043937) baseStart_3043937 baseEnd_3043937 := by
    simpa [prefixWord, tailWord_3043937, baseEnd_3043937] using wordTrace_append hprefix tailTrace_3043937
  have hstable : (prefixWord ++ tailWord_3043937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043937).length < 2 ^ (prefixWord ++ tailWord_3043937).sum := by decide
  have hdescent : baseEnd_3043937 < baseStart_3043937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3043958 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_3043958 : Nat := 118140960795 + 3043958 * 2 ^ 59
def prefixEnd_3043958 : Nat := 4983230072969 + 3 ^ 40 * 3043958 * 2
def baseEnd_3043958 : Nat := 347336343577490385339133

theorem tailTrace_3043958 : CollatzResearch.WordTrace tailWord_3043958 prefixEnd_3043958 347336343577490385339133 := by
  unfold tailWord_3043958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938891819141719217675783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74014846070845004988541685 6938891819141719217675783)
  ·
    refine ⟨10408337728712578826513675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938891819141719217675783 10408337728712578826513675)
    ·
      refine ⟨15612506593068868239770513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10408337728712578826513675 15612506593068868239770513)
      ·
        refine ⟨11709379944801651179827885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15612506593068868239770513 11709379944801651179827885)
        ·
          refine ⟨4391017479300619192435457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11709379944801651179827885 4391017479300619192435457)
          ·
            refine ⟨3293263109475464394326593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4391017479300619192435457 3293263109475464394326593)
            ·
              refine ⟨2469947332106598295744945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3293263109475464394326593 2469947332106598295744945)
              ·
                refine ⟨1852460499079948721808709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469947332106598295744945 1852460499079948721808709)
                ·
                  refine ⟨347336343577490385339133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852460499079948721808709 347336343577490385339133)
                  ·
                    rfl

theorem cell22_3043958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_3043958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3043958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3043958 prefixEnd_3043958 := by exact prefixLift 3043958
  have htrace : WordTrace (prefixWord ++ tailWord_3043958) baseStart_3043958 baseEnd_3043958 := by
    simpa [prefixWord, tailWord_3043958, baseEnd_3043958] using wordTrace_append hprefix tailTrace_3043958
  have hstable : (prefixWord ++ tailWord_3043958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3043958).length < 2 ^ (prefixWord ++ tailWord_3043958).sum := by decide
  have hdescent : baseEnd_3043958 < baseStart_3043958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3043958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044014 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3044014 : Nat := 118140960795 + 3044014 * 2 ^ 59
def prefixEnd_3044014 : Nat := 4983230072969 + 3 ^ 40 * 3044014 * 2
def baseEnd_3044014 : Nat := 347342733558968558872409

theorem tailTrace_3044014 : CollatzResearch.WordTrace tailWord_3044014 prefixEnd_3044014 347342733558968558872409 := by
  unfold tailWord_3044014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878038949258078630856387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74016207729376419364567397 13878038949258078630856387)
  ·
    refine ⟨20817058423887117946284581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13878038949258078630856387 20817058423887117946284581)
    ·
      refine ⟨3903198454478834614928359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20817058423887117946284581 3903198454478834614928359)
      ·
        refine ⟨5854797681718251922392539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903198454478834614928359 5854797681718251922392539)
        ·
          refine ⟨8782196522577377883588809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854797681718251922392539 8782196522577377883588809)
          ·
            refine ⟨6586647391933033412691607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8782196522577377883588809 6586647391933033412691607)
            ·
              refine ⟨9879971087899550119037411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586647391933033412691607 9879971087899550119037411)
              ·
                refine ⟨14819956631849325178556117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9879971087899550119037411 14819956631849325178556117)
                ·
                  refine ⟨347342733558968558872409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14819956631849325178556117 347342733558968558872409)
                  ·
                    rfl

theorem cell22_3044014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3044014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044014 prefixEnd_3044014 := by exact prefixLift 3044014
  have htrace : WordTrace (prefixWord ++ tailWord_3044014) baseStart_3044014 baseEnd_3044014 := by
    simpa [prefixWord, tailWord_3044014, baseEnd_3044014] using wordTrace_append hprefix tailTrace_3044014
  have hstable : (prefixWord ++ tailWord_3044014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044014).length < 2 ^ (prefixWord ++ tailWord_3044014).sum := by decide
  have hdescent : baseEnd_3044014 < baseStart_3044014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044042 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_3044042 : Nat := 118140960795 + 3044042 * 2 ^ 59
def prefixEnd_3044042 : Nat := 4983230072969 + 3 ^ 40 * 3044042 * 2
def baseEnd_3044042 : Nat := 347345928549707645639047

theorem tailTrace_3044042 : CollatzResearch.WordTrace tailWord_3044042 prefixEnd_3044042 347345928549707645639047 := by
  unfold tailWord_3044042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27756333209490797457217595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74016888558642126552580253 27756333209490797457217595)
  ·
    refine ⟨41634499814236196185826393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27756333209490797457217595 41634499814236196185826393)
    ·
      refine ⟨31225874860677147139369795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41634499814236196185826393 31225874860677147139369795)
      ·
        refine ⟨46838812291015720709054693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31225874860677147139369795 46838812291015720709054693)
        ·
          refine ⟨8782277304565447632947755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46838812291015720709054693 8782277304565447632947755)
          ·
            refine ⟨13173415956848171449421633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782277304565447632947755 13173415956848171449421633)
            ·
              refine ⟨9880061967636128587066225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13173415956848171449421633 9880061967636128587066225)
              ·
                refine ⟨7410046475727096440299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9880061967636128587066225 7410046475727096440299669)
                ·
                  refine ⟨347345928549707645639047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7410046475727096440299669 347345928549707645639047)
                  ·
                    rfl

theorem cell22_3044042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_3044042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044042 prefixEnd_3044042 := by exact prefixLift 3044042
  have htrace : WordTrace (prefixWord ++ tailWord_3044042) baseStart_3044042 baseEnd_3044042 := by
    simpa [prefixWord, tailWord_3044042, baseEnd_3044042] using wordTrace_append hprefix tailTrace_3044042
  have hstable : (prefixWord ++ tailWord_3044042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044042).length < 2 ^ (prefixWord ++ tailWord_3044042).sum := by decide
  have hdescent : baseEnd_3044042 < baseStart_3044042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044044 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_3044044 : Nat := 118140960795 + 3044044 * 2 ^ 59
def prefixEnd_3044044 : Nat := 4983230072969 + 3 ^ 40 * 3044044 * 2
def baseEnd_3044044 : Nat := 1042038470289995598367135

theorem tailTrace_3044044 : CollatzResearch.WordTrace tailWord_3044044 prefixEnd_3044044 1042038470289995598367135 := by
  unfold tailWord_3044044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55512702891977972085221593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74016937189303962780295457 55512702891977972085221593)
  ·
    refine ⟨41634527168983479063916195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55512702891977972085221593 41634527168983479063916195)
    ·
      refine ⟨62451790753475218595874293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41634527168983479063916195 62451790753475218595874293)
      ·
        refine ⟨5854855383138301743363215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62451790753475218595874293 5854855383138301743363215)
        ·
          refine ⟨8782283074707452615044823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5854855383138301743363215 8782283074707452615044823)
          ·
            refine ⟨13173424612061178922567235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782283074707452615044823 13173424612061178922567235)
            ·
              refine ⟨19760136918091768383850853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13173424612061178922567235 19760136918091768383850853)
              ·
                refine ⟨3705025672142206571972035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19760136918091768383850853 3705025672142206571972035)
                ·
                  refine ⟨5557538508213309857958053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705025672142206571972035 5557538508213309857958053)
                  ·
                    refine ⟨1042038470289995598367135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5557538508213309857958053 1042038470289995598367135)
                    ·
                      rfl

theorem cell22_3044044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_3044044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044044 prefixEnd_3044044 := by exact prefixLift 3044044
  have htrace : WordTrace (prefixWord ++ tailWord_3044044) baseStart_3044044 baseEnd_3044044 := by
    simpa [prefixWord, tailWord_3044044, baseEnd_3044044] using wordTrace_append hprefix tailTrace_3044044
  have hstable : (prefixWord ++ tailWord_3044044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044044).length < 2 ^ (prefixWord ++ tailWord_3044044).sum := by decide
  have hdescent : baseEnd_3044044 < baseStart_3044044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044057 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_3044057 : Nat := 118140960795 + 3044057 * 2 ^ 59
def prefixEnd_3044057 : Nat := 4983230072969 + 3 ^ 40 * 3044057 * 2
def baseEnd_3044057 : Nat := 1042042920455667897792095

theorem tailTrace_3044057 : CollatzResearch.WordTrace tailWord_3044057 prefixEnd_3044057 1042042920455667897792095 := by
  unfold tailWord_3044057
  simp only [CollatzResearch.WordTrace]
  refine ⟨111025879932908847390666425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74017253288605898260444283 111025879932908847390666425)
  ·
    refine ⟨83269409949681635542999819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111025879932908847390666425 83269409949681635542999819)
    ·
      refine ⟨124904114924522453314499729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83269409949681635542999819 124904114924522453314499729)
      ·
        refine ⟨93678086193391839985874797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124904114924522453314499729 93678086193391839985874797)
        ·
          refine ⟨35129282322521939994703049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93678086193391839985874797 35129282322521939994703049)
          ·
            refine ⟨26346961741891454996027287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35129282322521939994703049 26346961741891454996027287)
            ·
              refine ⟨39520442612837182494040931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26346961741891454996027287 39520442612837182494040931)
              ·
                refine ⟨59280663919255773741061397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39520442612837182494040931 59280663919255773741061397)
                ·
                  refine ⟨2778781121215114394112253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59280663919255773741061397 2778781121215114394112253)
                  ·
                    refine ⟨1042042920455667897792095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778781121215114394112253 1042042920455667897792095)
                    ·
                      rfl

theorem cell22_3044057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_3044057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044057 prefixEnd_3044057 := by exact prefixLift 3044057
  have htrace : WordTrace (prefixWord ++ tailWord_3044057) baseStart_3044057 baseEnd_3044057 := by
    simpa [prefixWord, tailWord_3044057, baseEnd_3044057] using wordTrace_append hprefix tailTrace_3044057
  have hstable : (prefixWord ++ tailWord_3044057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044057).length < 2 ^ (prefixWord ++ tailWord_3044057).sum := by decide
  have hdescent : baseEnd_3044057 < baseStart_3044057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044074 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_3044074 : Nat := 118140960795 + 3044074 * 2 ^ 59
def prefixEnd_3044074 : Nat := 4983230072969 + 3 ^ 40 * 3044074 * 2
def baseEnd_3044074 : Nat := 1042048739903085520117043

theorem tailTrace_3044074 : CollatzResearch.WordTrace tailWord_3044074 prefixEnd_3044074 1042048739903085520117043 := by
  unfold tailWord_3044074
  simp only [CollatzResearch.WordTrace]
  refine ⟨27756624993461814823508819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74017666649231506196023517 27756624993461814823508819)
  ·
    refine ⟨41634937490192722235263229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27756624993461814823508819 41634937490192722235263229)
    ·
      refine ⟨15613101558822270838223711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41634937490192722235263229 15613101558822270838223711)
      ·
        refine ⟨23419652338233406257335567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15613101558822270838223711 23419652338233406257335567)
        ·
          refine ⟨35129478507350109386003351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23419652338233406257335567 35129478507350109386003351)
          ·
            refine ⟨52694217761025164079005027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35129478507350109386003351 52694217761025164079005027)
            ·
              refine ⟨79041326641537746118507541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52694217761025164079005027 79041326641537746118507541)
              ·
                refine ⟨3705062186322081849305041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79041326641537746118507541 3705062186322081849305041)
                ·
                  refine ⟨2778796639741561386978781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705062186322081849305041 2778796639741561386978781)
                  ·
                    refine ⟨1042048739903085520117043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2778796639741561386978781 1042048739903085520117043)
                    ·
                      rfl

theorem cell22_3044074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_3044074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044074 prefixEnd_3044074 := by exact prefixLift 3044074
  have htrace : WordTrace (prefixWord ++ tailWord_3044074) baseStart_3044074 baseEnd_3044074 := by
    simpa [prefixWord, tailWord_3044074, baseEnd_3044074] using wordTrace_append hprefix tailTrace_3044074
  have hstable : (prefixWord ++ tailWord_3044074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044074).length < 2 ^ (prefixWord ++ tailWord_3044074).sum := by decide
  have hdescent : baseEnd_3044074 < baseStart_3044074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044138 : List Nat := [3, 1, 4, 3, 2, 1, 1, 7]
def baseStart_3044138 : Nat := 118140960795 + 3044138 * 2 ^ 59
def prefixEnd_3044138 : Nat := 4983230072969 + 3 ^ 40 * 3044138 * 2
def baseEnd_3044138 : Nat := 115785627601223409612983

theorem tailTrace_3044138 : CollatzResearch.WordTrace tailWord_3044138 prefixEnd_3044138 115785627601223409612983 := by
  unfold tailWord_3044138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757208561403849556091267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74019222830410265482910045 27757208561403849556091267)
  ·
    refine ⟨41635812842105774334136901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27757208561403849556091267 41635812842105774334136901)
    ·
      refine ⟨7806714907894832687650669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41635812842105774334136901 7806714907894832687650669)
      ·
        refine ⟨2927518090460562257869001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7806714907894832687650669 2927518090460562257869001)
        ·
          refine ⟨2195638567845421693401751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2927518090460562257869001 2195638567845421693401751)
          ·
            refine ⟨3293457851768132540102627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195638567845421693401751 3293457851768132540102627)
            ·
              refine ⟨4940186777652198810153941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293457851768132540102627 4940186777652198810153941)
              ·
                refine ⟨115785627601223409612983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4940186777652198810153941 115785627601223409612983)
                ·
                  rfl

theorem cell22_3044138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_3044138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044138 prefixEnd_3044138 := by exact prefixLift 3044138
  have htrace : WordTrace (prefixWord ++ tailWord_3044138) baseStart_3044138 baseEnd_3044138 := by
    simpa [prefixWord, tailWord_3044138, baseEnd_3044138] using wordTrace_append hprefix tailTrace_3044138
  have hstable : (prefixWord ++ tailWord_3044138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044138).length < 2 ^ (prefixWord ++ tailWord_3044138).sum := by decide
  have hdescent : baseEnd_3044138 < baseStart_3044138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044147 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_3044147 : Nat := 118140960795 + 3044147 * 2 ^ 59
def prefixEnd_3044147 : Nat := 4983230072969 + 3 ^ 40 * 3044147 * 2
def baseEnd_3044147 : Nat := 1042073729294937663041819

theorem tailTrace_3044147 : CollatzResearch.WordTrace tailWord_3044147 prefixEnd_3044147 1042073729294937663041819 := by
  unfold tailWord_3044147
  simp only [CollatzResearch.WordTrace]
  refine ⟨111029162502582792761442695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74019441668388528507628463 111029162502582792761442695)
  ·
    refine ⟨166543743753874189142164043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111029162502582792761442695 166543743753874189142164043)
    ·
      refine ⟨249815615630811283713246065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166543743753874189142164043 249815615630811283713246065)
      ·
        refine ⟨187361711723108462784934549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249815615630811283713246065 187361711723108462784934549)
        ·
          refine ⟨8782580237020709193043807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187361711723108462784934549 8782580237020709193043807)
          ·
            refine ⟨13173870355531063789565711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782580237020709193043807 13173870355531063789565711)
            ·
              refine ⟨19760805533296595684348567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13173870355531063789565711 19760805533296595684348567)
              ·
                refine ⟨29641208299944893526522851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19760805533296595684348567 29641208299944893526522851)
                ·
                  refine ⟨44461812449917340289784277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29641208299944893526522851 44461812449917340289784277)
                  ·
                    refine ⟨1042073729294937663041819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44461812449917340289784277 1042073729294937663041819)
                    ·
                      rfl

theorem cell22_3044147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_3044147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044147 prefixEnd_3044147 := by exact prefixLift 3044147
  have htrace : WordTrace (prefixWord ++ tailWord_3044147) baseStart_3044147 baseEnd_3044147 := by
    simpa [prefixWord, tailWord_3044147, baseEnd_3044147] using wordTrace_append hprefix tailTrace_3044147
  have hstable : (prefixWord ++ tailWord_3044147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044147).length < 2 ^ (prefixWord ++ tailWord_3044147).sum := by decide
  have hdescent : baseEnd_3044147 < baseStart_3044147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044149 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 5]
def baseStart_3044149 : Nat := 118140960795 + 3044149 * 2 ^ 59
def prefixEnd_3044149 : Nat := 4983230072969 + 3 ^ 40 * 3044149 * 2
def baseEnd_3044149 : Nat := 347358137978603441497271

theorem tailTrace_3044149 : CollatzResearch.WordTrace tailWord_3044149 prefixEnd_3044149 347358137978603441497271 := by
  unfold tailWord_3044149
  simp only [CollatzResearch.WordTrace]
  refine ⟨111029235448575547103015501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74019490299050364735343667 111029235448575547103015501)
  ·
    refine ⟨41635963293215830163630813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111029235448575547103015501 41635963293215830163630813)
    ·
      refine ⟨15613486234955936311361555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41635963293215830163630813 15613486234955936311361555)
      ·
        refine ⟨23420229352433904467042333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15613486234955936311361555 23420229352433904467042333)
        ·
          refine ⟨8782586007162714175140875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23420229352433904467042333 8782586007162714175140875)
          ·
            refine ⟨13173879010744071262711313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782586007162714175140875 13173879010744071262711313)
            ·
              refine ⟨9880409258058053447033485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13173879010744071262711313 9880409258058053447033485)
              ·
                refine ⟨3705153471771770042637557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9880409258058053447033485 3705153471771770042637557)
                ·
                  refine ⟨347358137978603441497271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3705153471771770042637557 347358137978603441497271)
                  ·
                    rfl

theorem cell22_3044149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_3044149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044149 prefixEnd_3044149 := by exact prefixLift 3044149
  have htrace : WordTrace (prefixWord ++ tailWord_3044149) baseStart_3044149 baseEnd_3044149 := by
    simpa [prefixWord, tailWord_3044149, baseEnd_3044149] using wordTrace_append hprefix tailTrace_3044149
  have hstable : (prefixWord ++ tailWord_3044149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044149).length < 2 ^ (prefixWord ++ tailWord_3044149).sum := by decide
  have hdescent : baseEnd_3044149 < baseStart_3044149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044209 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_3044209 : Nat := 118140960795 + 3044209 * 2 ^ 59
def prefixEnd_3044209 : Nat := 4983230072969 + 3 ^ 40 * 3044209 * 2
def baseEnd_3044209 : Nat := 1042094953161990167991629

theorem tailTrace_3044209 : CollatzResearch.WordTrace tailWord_3044209 prefixEnd_3044209 1042094953161990167991629 := by
  unfold tailWord_3044209
  simp only [CollatzResearch.WordTrace]
  refine ⟨111031423828358177350199681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74020949218905451566799787 111031423828358177350199681)
  ·
    refine ⟨83273567871268633012649761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111031423828358177350199681 83273567871268633012649761)
    ·
      refine ⟨62455175903451474759487321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83273567871268633012649761 62455175903451474759487321)
      ·
        refine ⟨46841381927588606069615491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62455175903451474759487321 46841381927588606069615491)
        ·
          refine ⟨70262072891382909104423237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46841381927588606069615491 70262072891382909104423237)
          ·
            refine ⟨13174138667134295457079357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70262072891382909104423237 13174138667134295457079357)
            ·
              refine ⟨4940302000175360796404759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13174138667134295457079357 4940302000175360796404759)
              ·
                refine ⟨7410453000263041194607139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940302000175360796404759 7410453000263041194607139)
                ·
                  refine ⟨11115679500394561791910709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410453000263041194607139 11115679500394561791910709)
                  ·
                    refine ⟨1042094953161990167991629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11115679500394561791910709 1042094953161990167991629)
                    ·
                      rfl

theorem cell22_3044209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_3044209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044209 prefixEnd_3044209 := by exact prefixLift 3044209
  have htrace : WordTrace (prefixWord ++ tailWord_3044209) baseStart_3044209 baseEnd_3044209 := by
    simpa [prefixWord, tailWord_3044209, baseEnd_3044209] using wordTrace_append hprefix tailTrace_3044209
  have hstable : (prefixWord ++ tailWord_3044209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044209).length < 2 ^ (prefixWord ++ tailWord_3044209).sum := by decide
  have hdescent : baseEnd_3044209 < baseStart_3044209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044348 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3044348 : Nat := 118140960795 + 3044348 * 2 ^ 59
def prefixEnd_3044348 : Nat := 4983230072969 + 3 ^ 40 * 3044348 * 2
def baseEnd_3044348 : Nat := 1042142535702640138766203

theorem tailTrace_3044348 : CollatzResearch.WordTrace tailWord_3044348 prefixEnd_3044348 1042142535702640138766203 := by
  unfold tailWord_3044348
  simp only [CollatzResearch.WordTrace]
  refine ⟨55518246787427302044754849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74024329049903069393006465 55518246787427302044754849)
  ·
    refine ⟨41638685090570476533566137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55518246787427302044754849 41638685090570476533566137)
    ·
      refine ⟨31229013817927857400174603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41638685090570476533566137 31229013817927857400174603)
      ·
        refine ⟨46843520726891786100261905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31229013817927857400174603 46843520726891786100261905)
        ·
          refine ⟨35132640545168839575196429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46843520726891786100261905 35132640545168839575196429)
          ·
            refine ⟨13174740204438314840698661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35132640545168839575196429 13174740204438314840698661)
            ·
              refine ⟨2470263788332184032630999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13174740204438314840698661 2470263788332184032630999)
              ·
                refine ⟨3705395682498276048946499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470263788332184032630999 3705395682498276048946499)
                ·
                  refine ⟨5558093523747414073419749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705395682498276048946499 5558093523747414073419749)
                  ·
                    refine ⟨1042142535702640138766203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5558093523747414073419749 1042142535702640138766203)
                    ·
                      rfl

theorem cell22_3044348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3044348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044348 prefixEnd_3044348 := by exact prefixLift 3044348
  have htrace : WordTrace (prefixWord ++ tailWord_3044348) baseStart_3044348 baseEnd_3044348 := by
    simpa [prefixWord, tailWord_3044348, baseEnd_3044348] using wordTrace_append hprefix tailTrace_3044348
  have hstable : (prefixWord ++ tailWord_3044348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044348).length < 2 ^ (prefixWord ++ tailWord_3044348).sum := by decide
  have hdescent : baseEnd_3044348 < baseStart_3044348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044389 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_3044389 : Nat := 118140960795 + 3044389 * 2 ^ 59
def prefixEnd_3044389 : Nat := 4983230072969 + 3 ^ 40 * 3044389 * 2
def baseEnd_3044389 : Nat := 1042156570840529698491077

theorem tailTrace_3044389 : CollatzResearch.WordTrace tailWord_3044389 prefixEnd_3044389 1042156570840529698491077 := by
  unfold tailWord_3044389
  simp only [CollatzResearch.WordTrace]
  refine ⟨111037988967706068091752221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74025325978470712061168147 111037988967706068091752221)
  ·
    refine ⟨41639245862889775534407083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111037988967706068091752221 41639245862889775534407083)
    ·
      refine ⟨62458868794334663301610625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41639245862889775534407083 62458868794334663301610625)
      ·
        refine ⟨46844151595750997476207969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62458868794334663301610625 46844151595750997476207969)
        ·
          refine ⟨35133113696813248107155977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46844151595750997476207969 35133113696813248107155977)
          ·
            refine ⟨26349835272609936080366983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35133113696813248107155977 26349835272609936080366983)
            ·
              refine ⟨39524752908914904120550475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26349835272609936080366983 39524752908914904120550475)
              ·
                refine ⟨59287129363372356180825713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39524752908914904120550475 59287129363372356180825713)
                ·
                  refine ⟨44465347022529267135619285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59287129363372356180825713 44465347022529267135619285)
                  ·
                    refine ⟨1042156570840529698491077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44465347022529267135619285 1042156570840529698491077)
                    ·
                      rfl

theorem cell22_3044389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_3044389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044389 prefixEnd_3044389 := by exact prefixLift 3044389
  have htrace : WordTrace (prefixWord ++ tailWord_3044389) baseStart_3044389 baseEnd_3044389 := by
    simpa [prefixWord, tailWord_3044389, baseEnd_3044389] using wordTrace_append hprefix tailTrace_3044389
  have hstable : (prefixWord ++ tailWord_3044389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044389).length < 2 ^ (prefixWord ++ tailWord_3044389).sum := by decide
  have hdescent : baseEnd_3044389 < baseStart_3044389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044419 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 7]
def baseStart_3044419 : Nat := 118140960795 + 3044419 * 2 ^ 59
def prefixEnd_3044419 : Nat := 4983230072969 + 3 ^ 40 * 3044419 * 2
def baseEnd_3044419 : Nat := 347388946817873206746995

theorem tailTrace_3044419 : CollatzResearch.WordTrace tailWord_3044419 prefixEnd_3044419 347388946817873206746995 := by
  unfold tailWord_3044419
  simp only [CollatzResearch.WordTrace]
  refine ⟨111039083157597383215344311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74026055438398255476896207 111039083157597383215344311)
  ·
    refine ⟨166558624736396074823016467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111039083157597383215344311 166558624736396074823016467)
    ·
      refine ⟨249837937104594112234524701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166558624736396074823016467 249837937104594112234524701)
      ·
        refine ⟨93689226414222792087946763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249837937104594112234524701 93689226414222792087946763)
        ·
          refine ⟨140533839621334188131920145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93689226414222792087946763 140533839621334188131920145)
          ·
            refine ⟨105400379716000641098940109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140533839621334188131920145 105400379716000641098940109)
            ·
              refine ⟨39525142393500240412102541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105400379716000641098940109 39525142393500240412102541)
              ·
                refine ⟨14821928397562590154538453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39525142393500240412102541 14821928397562590154538453)
                ·
                  refine ⟨347388946817873206746995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14821928397562590154538453 347388946817873206746995)
                  ·
                    rfl

theorem cell22_3044419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_3044419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044419 prefixEnd_3044419 := by exact prefixLift 3044419
  have htrace : WordTrace (prefixWord ++ tailWord_3044419) baseStart_3044419 baseEnd_3044419 := by
    simpa [prefixWord, tailWord_3044419, baseEnd_3044419] using wordTrace_append hprefix tailTrace_3044419
  have hstable : (prefixWord ++ tailWord_3044419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044419).length < 2 ^ (prefixWord ++ tailWord_3044419).sum := by decide
  have hdescent : baseEnd_3044419 < baseStart_3044419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044423 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3044423 : Nat := 118140960795 + 3044423 * 2 ^ 59
def prefixEnd_3044423 : Nat := 4983230072969 + 3 ^ 40 * 3044423 * 2
def baseEnd_3044423 : Nat := 1042168209735364943140973

theorem tailTrace_3044423 : CollatzResearch.WordTrace tailWord_3044423 prefixEnd_3044423 1042168209735364943140973 := by
  unfold tailWord_3044423
  simp only [CollatzResearch.WordTrace]
  refine ⟨111039229049582891898489923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74026152699721927932326615 111039229049582891898489923)
  ·
    refine ⟨166558843574374337847734885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111039229049582891898489923 166558843574374337847734885)
    ·
      refine ⟨31229783170195188346450291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166558843574374337847734885 31229783170195188346450291)
      ·
        refine ⟨46844674755292782519675437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31229783170195188346450291 46844674755292782519675437)
        ·
          refine ⟨17566753033234793444878289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46844674755292782519675437 17566753033234793444878289)
          ·
            refine ⟨13175064774926095083658717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566753033234793444878289 13175064774926095083658717)
            ·
              refine ⟨4940649290597285656372019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13175064774926095083658717 4940649290597285656372019)
              ·
                refine ⟨7410973935895928484558029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940649290597285656372019 7410973935895928484558029)
                ·
                  refine ⟨2779115225960973181709261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7410973935895928484558029 2779115225960973181709261)
                  ·
                    refine ⟨1042168209735364943140973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779115225960973181709261 1042168209735364943140973)
                    ·
                      rfl

theorem cell22_3044423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3044423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044423 prefixEnd_3044423 := by exact prefixLift 3044423
  have htrace : WordTrace (prefixWord ++ tailWord_3044423) baseStart_3044423 baseEnd_3044423 := by
    simpa [prefixWord, tailWord_3044423, baseEnd_3044423] using wordTrace_append hprefix tailTrace_3044423
  have hstable : (prefixWord ++ tailWord_3044423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044423).length < 2 ^ (prefixWord ++ tailWord_3044423).sum := by decide
  have hdescent : baseEnd_3044423 < baseStart_3044423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044498 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_3044498 : Nat := 118140960795 + 3044498 * 2 ^ 59
def prefixEnd_3044498 : Nat := 4983230072969 + 3 ^ 40 * 3044498 * 2
def baseEnd_3044498 : Nat := 347397961256029915838581

theorem tailTrace_3044498 : CollatzResearch.WordTrace tailWord_3044498 prefixEnd_3044498 347397961256029915838581 := by
  unfold tailWord_3044498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27760491131077794926867537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74027976349540786471646765 27760491131077794926867537)
  ·
    refine ⟨20820368348308346195150653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27760491131077794926867537 20820368348308346195150653)
    ·
      refine ⟨7807638130615629823181495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20820368348308346195150653 7807638130615629823181495)
      ·
        refine ⟨11711457195923444734772243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7807638130615629823181495 11711457195923444734772243)
        ·
          refine ⟨17567185793885167102158365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11711457195923444734772243 17567185793885167102158365)
          ·
            refine ⟨6587694672706937663309387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17567185793885167102158365 6587694672706937663309387)
            ·
              refine ⟨9881542009060406494964081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587694672706937663309387 9881542009060406494964081)
              ·
                refine ⟨7411156506795304871223061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9881542009060406494964081 7411156506795304871223061)
                ·
                  refine ⟨347397961256029915838581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7411156506795304871223061 347397961256029915838581)
                  ·
                    rfl

theorem cell22_3044498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_3044498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044498 prefixEnd_3044498 := by exact prefixLift 3044498
  have htrace : WordTrace (prefixWord ++ tailWord_3044498) baseStart_3044498 baseEnd_3044498 := by
    simpa [prefixWord, tailWord_3044498, baseEnd_3044498] using wordTrace_append hprefix tailTrace_3044498
  have hstable : (prefixWord ++ tailWord_3044498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044498).length < 2 ^ (prefixWord ++ tailWord_3044498).sum := by decide
  have hdescent : baseEnd_3044498 < baseStart_3044498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044513 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_3044513 : Nat := 118140960795 + 3044513 * 2 ^ 59
def prefixEnd_3044513 : Nat := 4983230072969 + 3 ^ 40 * 3044513 * 2
def baseEnd_3044513 : Nat := 1042199018574634708390697

theorem tailTrace_3044513 : CollatzResearch.WordTrace tailWord_3044513 prefixEnd_3044513 1042199018574634708390697 := by
  unfold tailWord_3044513
  simp only [CollatzResearch.WordTrace]
  refine ⟨111042511619256837269266193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74028341079504558179510795 111042511619256837269266193)
  ·
    refine ⟨83281883714442627951949645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111042511619256837269266193 83281883714442627951949645)
    ·
      refine ⟨31230706392915985481981117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83281883714442627951949645 31230706392915985481981117)
      ·
        refine ⟨11711514897343494555742919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31230706392915985481981117 11711514897343494555742919)
        ·
          refine ⟨17567272346015241833614379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11711514897343494555742919 17567272346015241833614379)
          ·
            refine ⟨26350908519022862750421569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17567272346015241833614379 26350908519022862750421569)
            ·
              refine ⟨19763181389267147062816177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26350908519022862750421569 19763181389267147062816177)
              ·
                refine ⟨14822386041950360297112133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19763181389267147062816177 14822386041950360297112133)
                ·
                  refine ⟨2779197382865692555708525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14822386041950360297112133 2779197382865692555708525)
                  ·
                    refine ⟨1042199018574634708390697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779197382865692555708525 1042199018574634708390697)
                    ·
                      rfl

theorem cell22_3044513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_3044513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044513 prefixEnd_3044513 := by exact prefixLift 3044513
  have htrace : WordTrace (prefixWord ++ tailWord_3044513) baseStart_3044513 baseEnd_3044513 := by
    simpa [prefixWord, tailWord_3044513, baseEnd_3044513] using wordTrace_append hprefix tailTrace_3044513
  have hstable : (prefixWord ++ tailWord_3044513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044513).length < 2 ^ (prefixWord ++ tailWord_3044513).sum := by decide
  have hdescent : baseEnd_3044513 < baseStart_3044513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044530 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3044530 : Nat := 118140960795 + 3044530 * 2 ^ 59
def prefixEnd_3044530 : Nat := 4983230072969 + 3 ^ 40 * 3044530 * 2
def baseEnd_3044530 : Nat := 1042204838022052330715645

theorem tailTrace_3044530 : CollatzResearch.WordTrace tailWord_3044530 prefixEnd_3044530 1042204838022052330715645 := by
  unfold tailWord_3044530
  simp only [CollatzResearch.WordTrace]
  refine ⟨27760782915048812293158761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74028754440130166115090029 27760782915048812293158761)
  ·
    refine ⟨20820587186286609219869071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27760782915048812293158761 20820587186286609219869071)
    ·
      refine ⟨31230880779429913829803607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20820587186286609219869071 31230880779429913829803607)
      ·
        refine ⟨46846321169144870744705411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31230880779429913829803607 46846321169144870744705411)
        ·
          refine ⟨70269481753717306117058117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46846321169144870744705411 70269481753717306117058117)
          ·
            refine ⟨13175527828821994896948397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70269481753717306117058117 13175527828821994896948397)
            ·
              refine ⟨4940822935808248086355649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13175527828821994896948397 4940822935808248086355649)
              ·
                refine ⟨3705617201856186064766737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4940822935808248086355649 3705617201856186064766737)
                ·
                  refine ⟨2779212901392139548575053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705617201856186064766737 2779212901392139548575053)
                  ·
                    refine ⟨1042204838022052330715645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779212901392139548575053 1042204838022052330715645)
                    ·
                      rfl

theorem cell22_3044530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3044530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044530 prefixEnd_3044530 := by exact prefixLift 3044530
  have htrace : WordTrace (prefixWord ++ tailWord_3044530) baseStart_3044530 baseEnd_3044530 := by
    simpa [prefixWord, tailWord_3044530, baseEnd_3044530] using wordTrace_append hprefix tailTrace_3044530
  have hstable : (prefixWord ++ tailWord_3044530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044530).length < 2 ^ (prefixWord ++ tailWord_3044530).sum := by decide
  have hdescent : baseEnd_3044530 < baseStart_3044530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044566 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3044566 : Nat := 118140960795 + 3044566 * 2 ^ 59
def prefixEnd_3044566 : Nat := 4983230072969 + 3 ^ 40 * 3044566 * 2
def baseEnd_3044566 : Nat := 347405720519253412271845

theorem tailTrace_3044566 : CollatzResearch.WordTrace tailWord_3044566 prefixEnd_3044566 347405720519253412271845 := by
  unfold tailWord_3044566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940277793004051707559097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74029629792043218213963701 6940277793004051707559097)
  ·
    refine ⟨5205208344753038780669323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6940277793004051707559097 5205208344753038780669323)
    ·
      refine ⟨7807812517129558171003985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205208344753038780669323 7807812517129558171003985)
      ·
        refine ⟨5855859387847168628252989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7807812517129558171003985 5855859387847168628252989)
        ·
          refine ⟨2195947270442688235594871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5855859387847168628252989 2195947270442688235594871)
          ·
            refine ⟨3293920905664032353392307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195947270442688235594871 3293920905664032353392307)
            ·
              refine ⟨4940881358496048530088461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3293920905664032353392307 4940881358496048530088461)
              ·
                refine ⟨1852830509436018198783173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4940881358496048530088461 1852830509436018198783173)
                ·
                  refine ⟨347405720519253412271845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852830509436018198783173 347405720519253412271845)
                  ·
                    rfl

theorem cell22_3044566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3044566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044566 prefixEnd_3044566 := by exact prefixLift 3044566
  have htrace : WordTrace (prefixWord ++ tailWord_3044566) baseStart_3044566 baseEnd_3044566 := by
    simpa [prefixWord, tailWord_3044566, baseEnd_3044566] using wordTrace_append hprefix tailTrace_3044566
  have hstable : (prefixWord ++ tailWord_3044566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044566).length < 2 ^ (prefixWord ++ tailWord_3044566).sum := by decide
  have hdescent : baseEnd_3044566 < baseStart_3044566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044744 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 1, 3]
def baseStart_3044744 : Nat := 118140960795 + 3044744 * 2 ^ 59
def prefixEnd_3044744 : Nat := 4983230072969 + 3 ^ 40 * 3044744 * 2
def baseEnd_3044744 : Nat := 1042278094595427105864989

theorem tailTrace_3044744 : CollatzResearch.WordTrace tailWord_3044744 prefixEnd_3044744 1042278094595427105864989 := by
  unfold tailWord_3044744
  simp only [CollatzResearch.WordTrace]
  refine ⟨55525468440709981860462643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74033957920946642480616857 55525468440709981860462643)
  ·
    refine ⟨83288202661064972790693965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55525468440709981860462643 83288202661064972790693965)
    ·
      refine ⟨31233075997899364796510237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83288202661064972790693965 31233075997899364796510237)
      ·
        refine ⟨11712403499212261798691339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31233075997899364796510237 11712403499212261798691339)
        ·
          refine ⟨17568605248818392698037009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11712403499212261798691339 17568605248818392698037009)
          ·
            refine ⟨13176453936613794523527757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17568605248818392698037009 13176453936613794523527757)
            ·
              refine ⟨4941170226230172946322909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13176453936613794523527757 4941170226230172946322909)
              ·
                refine ⟨1852938834836314854871091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4941170226230172946322909 1852938834836314854871091)
                ·
                  refine ⟨2779408252254472282306637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852938834836314854871091 2779408252254472282306637)
                  ·
                    refine ⟨1042278094595427105864989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779408252254472282306637 1042278094595427105864989)
                    ·
                      rfl

theorem cell22_3044744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_3044744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044744 prefixEnd_3044744 := by exact prefixLift 3044744
  have htrace : WordTrace (prefixWord ++ tailWord_3044744) baseStart_3044744 baseEnd_3044744 := by
    simpa [prefixWord, tailWord_3044744, baseEnd_3044744] using wordTrace_append hprefix tailTrace_3044744
  have hstable : (prefixWord ++ tailWord_3044744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044744).length < 2 ^ (prefixWord ++ tailWord_3044744).sum := by decide
  have hdescent : baseEnd_3044744 < baseStart_3044744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044783 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_3044783 : Nat := 118140960795 + 3044783 * 2 ^ 59
def prefixEnd_3044783 : Nat := 4983230072969 + 3 ^ 40 * 3044783 * 2
def baseEnd_3044783 : Nat := 1042291445092444004139869

theorem tailTrace_3044783 : CollatzResearch.WordTrace tailWord_3044783 prefixEnd_3044783 1042291445092444004139869 := by
  unfold tailWord_3044783
  simp only [CollatzResearch.WordTrace]
  refine ⟨111052359328278673381595003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74034906218852448921063335 111052359328278673381595003)
  ·
    refine ⟨166578538992418010072392505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111052359328278673381595003 166578538992418010072392505)
    ·
      refine ⟨124933904244313507554294379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166578538992418010072392505 124933904244313507554294379)
      ·
        refine ⟨187400856366470261331441569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124933904244313507554294379 187400856366470261331441569)
        ·
          refine ⟨140550642274852695998581177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187400856366470261331441569 140550642274852695998581177)
          ·
            refine ⟨105412981706139521998935883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140550642274852695998581177 105412981706139521998935883)
            ·
              refine ⟨158119472559209282998403825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105412981706139521998935883 158119472559209282998403825)
              ·
                refine ⟨118589604419406962248802869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158119472559209282998403825 118589604419406962248802869)
                ·
                  refine ⟨11117775414319402710825269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118589604419406962248802869 11117775414319402710825269)
                  ·
                    refine ⟨1042291445092444004139869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11117775414319402710825269 1042291445092444004139869)
                    ·
                      rfl

theorem cell22_3044783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_3044783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044783 prefixEnd_3044783 := by exact prefixLift 3044783
  have htrace : WordTrace (prefixWord ++ tailWord_3044783) baseStart_3044783 baseEnd_3044783 := by
    simpa [prefixWord, tailWord_3044783, baseEnd_3044783] using wordTrace_append hprefix tailTrace_3044783
  have hstable : (prefixWord ++ tailWord_3044783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044783).length < 2 ^ (prefixWord ++ tailWord_3044783).sum := by decide
  have hdescent : baseEnd_3044783 < baseStart_3044783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044800 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_3044800 : Nat := 118140960795 + 3044800 * 2 ^ 59
def prefixEnd_3044800 : Nat := 4983230072969 + 3 ^ 40 * 3044800 * 2
def baseEnd_3044800 : Nat := 1042297264539861626464817

theorem tailTrace_3044800 : CollatzResearch.WordTrace tailWord_3044800 prefixEnd_3044800 1042297264539861626464817 := by
  unfold tailWord_3044800
  simp only [CollatzResearch.WordTrace]
  refine ⟨55526489684608542642481927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74035319579478056856642569 55526489684608542642481927)
  ·
    refine ⟨83289734526912813963722891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55526489684608542642481927 83289734526912813963722891)
    ·
      refine ⟨124934601790369220945584337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83289734526912813963722891 124934601790369220945584337)
      ·
        refine ⟨93700951342776915709188253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124934601790369220945584337 93700951342776915709188253)
        ·
          refine ⟨35137856753541343390945595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93700951342776915709188253 35137856753541343390945595)
          ·
            refine ⟨52706785130312015086418393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35137856753541343390945595 52706785130312015086418393)
            ·
              refine ⟨39530088847734011314813795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52706785130312015086418393 39530088847734011314813795)
              ·
                refine ⟨59295133271601016972220693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39530088847734011314813795 59295133271601016972220693)
                ·
                  refine ⟨2779459372106297670572845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59295133271601016972220693 2779459372106297670572845)
                  ·
                    refine ⟨1042297264539861626464817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779459372106297670572845 1042297264539861626464817)
                    ·
                      rfl

theorem cell22_3044800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_3044800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044800 prefixEnd_3044800 := by exact prefixLift 3044800
  have htrace : WordTrace (prefixWord ++ tailWord_3044800) baseStart_3044800 baseEnd_3044800 := by
    simpa [prefixWord, tailWord_3044800, baseEnd_3044800] using wordTrace_append hprefix tailTrace_3044800
  have hstable : (prefixWord ++ tailWord_3044800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044800).length < 2 ^ (prefixWord ++ tailWord_3044800).sum := by decide
  have hdescent : baseEnd_3044800 < baseStart_3044800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044815 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_3044815 : Nat := 118140960795 + 3044815 * 2 ^ 59
def prefixEnd_3044815 : Nat := 4983230072969 + 3 ^ 40 * 3044815 * 2
def baseEnd_3044815 : Nat := 1042302399346406587339771

theorem tailTrace_3044815 : CollatzResearch.WordTrace tailWord_3044815 prefixEnd_3044815 1042302399346406587339771 := by
  unfold tailWord_3044815
  simp only [CollatzResearch.WordTrace]
  refine ⟨111053526464162742846759899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74035684309441828564506599 111053526464162742846759899)
  ·
    refine ⟨166580289696244114270139849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111053526464162742846759899 166580289696244114270139849)
    ·
      refine ⟨124935217272183085702604887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166580289696244114270139849 124935217272183085702604887)
      ·
        refine ⟨187402825908274628553907331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124935217272183085702604887 187402825908274628553907331)
        ·
          refine ⟨281104238862411942830860997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187402825908274628553907331 281104238862411942830860997)
          ·
            refine ⟨52707044786702239280786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281104238862411942830860997 52707044786702239280786437)
            ·
              refine ⟨9882570897506669865147457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52707044786702239280786437 9882570897506669865147457)
              ·
                refine ⟨7411928173130002398860593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9882570897506669865147457 7411928173130002398860593)
                ·
                  refine ⟨5558946129847501799145445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7411928173130002398860593 5558946129847501799145445)
                  ·
                    refine ⟨1042302399346406587339771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5558946129847501799145445 1042302399346406587339771)
                    ·
                      rfl

theorem cell22_3044815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_3044815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044815 prefixEnd_3044815 := by exact prefixLift 3044815
  have htrace : WordTrace (prefixWord ++ tailWord_3044815) baseStart_3044815 baseEnd_3044815 := by
    simpa [prefixWord, tailWord_3044815, baseEnd_3044815] using wordTrace_append hprefix tailTrace_3044815
  have hstable : (prefixWord ++ tailWord_3044815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044815).length < 2 ^ (prefixWord ++ tailWord_3044815).sum := by decide
  have hdescent : baseEnd_3044815 < baseStart_3044815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044868 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_3044868 : Nat := 118140960795 + 3044868 * 2 ^ 59
def prefixEnd_3044868 : Nat := 4983230072969 + 3 ^ 40 * 3044868 * 2
def baseEnd_3044868 : Nat := 1042320542329532115764609

theorem tailTrace_3044868 : CollatzResearch.WordTrace tailWord_3044868 prefixEnd_3044868 1042320542329532115764609 := by
  unfold tailWord_3044868
  simp only [CollatzResearch.WordTrace]
  refine ⟨55527729766485366449219629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74036973021980488598959505 55527729766485366449219629)
  ·
    refine ⟨20822898662432012418457361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55527729766485366449219629 20822898662432012418457361)
    ·
      refine ⟨15617173996824009313843021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20822898662432012418457361 15617173996824009313843021)
      ·
        refine ⟨5856440248809003492691133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15617173996824009313843021 5856440248809003492691133)
        ·
          refine ⟨2196165093303376309759175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5856440248809003492691133 2196165093303376309759175)
          ·
            refine ⟨3294247639955064464638763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196165093303376309759175 3294247639955064464638763)
            ·
              refine ⟨4941371459932596696958145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294247639955064464638763 4941371459932596696958145)
              ·
                refine ⟨3706028594949447522718609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941371459932596696958145 3706028594949447522718609)
                ·
                  refine ⟨2779521446212085642038957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3706028594949447522718609 2779521446212085642038957)
                  ·
                    refine ⟨1042320542329532115764609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2779521446212085642038957 1042320542329532115764609)
                    ·
                      rfl

theorem cell22_3044868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_3044868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044868 prefixEnd_3044868 := by exact prefixLift 3044868
  have htrace : WordTrace (prefixWord ++ tailWord_3044868) baseStart_3044868 baseEnd_3044868 := by
    simpa [prefixWord, tailWord_3044868, baseEnd_3044868] using wordTrace_append hprefix tailTrace_3044868
  have hstable : (prefixWord ++ tailWord_3044868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044868).length < 2 ^ (prefixWord ++ tailWord_3044868).sum := by decide
  have hdescent : baseEnd_3044868 < baseStart_3044868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044922 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_3044922 : Nat := 118140960795 + 3044922 * 2 ^ 59
def prefixEnd_3044922 : Nat := 4983230072969 + 3 ^ 40 * 3044922 * 2
def baseEnd_3044922 : Nat := 1042339027633093974914443

theorem tailTrace_3044922 : CollatzResearch.WordTrace tailWord_3044922 prefixEnd_3044922 1042339027633093974914443 := by
  unfold tailWord_3044922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764357268693775030226255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74038286049850066747270013 27764357268693775030226255)
  ·
    refine ⟨41646535903040662545339383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27764357268693775030226255 41646535903040662545339383)
    ·
      refine ⟨62469803854560993818009075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41646535903040662545339383 62469803854560993818009075)
      ·
        refine ⟨93704705781841490727013613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62469803854560993818009075 93704705781841490727013613)
        ·
          refine ⟨35139264668190559022630105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93704705781841490727013613 35139264668190559022630105)
          ·
            refine ⟨26354448501142919266972579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35139264668190559022630105 26354448501142919266972579)
            ·
              refine ⟨39531672751714378900458869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26354448501142919266972579 39531672751714378900458869)
              ·
                refine ⟨3706094320473223021918019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39531672751714378900458869 3706094320473223021918019)
                ·
                  refine ⟨5559141480709834532877029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706094320473223021918019 5559141480709834532877029)
                  ·
                    refine ⟨1042339027633093974914443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559141480709834532877029 1042339027633093974914443)
                    ·
                      rfl

theorem cell22_3044922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_3044922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044922 prefixEnd_3044922 := by exact prefixLift 3044922
  have htrace : WordTrace (prefixWord ++ tailWord_3044922) baseStart_3044922 baseEnd_3044922 := by
    simpa [prefixWord, tailWord_3044922, baseEnd_3044922] using wordTrace_append hprefix tailTrace_3044922
  have hstable : (prefixWord ++ tailWord_3044922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044922).length < 2 ^ (prefixWord ++ tailWord_3044922).sum := by decide
  have hdescent : baseEnd_3044922 < baseStart_3044922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044937 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 4]
def baseStart_3044937 : Nat := 118140960795 + 3044937 * 2 ^ 59
def prefixEnd_3044937 : Nat := 4983230072969 + 3 ^ 40 * 3044937 * 2
def baseEnd_3044937 : Nat := 347448054146546311929799

theorem tailTrace_3044937 : CollatzResearch.WordTrace tailWord_3044937 prefixEnd_3044937 347448054146546311929799 := by
  unfold tailWord_3044937
  simp only [CollatzResearch.WordTrace]
  refine ⟨111057976169720757682701065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74038650779813838455134043 111057976169720757682701065)
  ·
    refine ⟨83293482127290568262025799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111057976169720757682701065 83293482127290568262025799)
    ·
      refine ⟨124940223190935852393038699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83293482127290568262025799 124940223190935852393038699)
      ·
        refine ⟨187410334786403778589558049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124940223190935852393038699 187410334786403778589558049)
        ·
          refine ⟨140557751089802833942168537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187410334786403778589558049 140557751089802833942168537)
          ·
            refine ⟨105418313317352125456626403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140557751089802833942168537 105418313317352125456626403)
            ·
              refine ⟨158127469976028188184939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105418313317352125456626403 158127469976028188184939605)
              ·
                refine ⟨1853056288781580330292261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 158127469976028188184939605 1853056288781580330292261)
                ·
                  refine ⟨347448054146546311929799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853056288781580330292261 347448054146546311929799)
                  ·
                    rfl

theorem cell22_3044937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_3044937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044937 prefixEnd_3044937 := by exact prefixLift 3044937
  have htrace : WordTrace (prefixWord ++ tailWord_3044937) baseStart_3044937 baseEnd_3044937 := by
    simpa [prefixWord, tailWord_3044937, baseEnd_3044937] using wordTrace_append hprefix tailTrace_3044937
  have hstable : (prefixWord ++ tailWord_3044937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044937).length < 2 ^ (prefixWord ++ tailWord_3044937).sum := by decide
  have hdescent : baseEnd_3044937 < baseStart_3044937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044956 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3044956 : Nat := 118140960795 + 3044956 * 2 ^ 59
def prefixEnd_3044956 : Nat := 4983230072969 + 3 ^ 40 * 3044956 * 2
def baseEnd_3044956 : Nat := 1042350666527929219564339

theorem tailTrace_3044956 : CollatzResearch.WordTrace tailWord_3044956 prefixEnd_3044956 1042350666527929219564339 := by
  unfold tailWord_3044956
  simp only [CollatzResearch.WordTrace]
  refine ⟨55529334578325961963821361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74039112771101282618428481 55529334578325961963821361)
  ·
    refine ⟨41647000933744471472866021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55529334578325961963821361 41647000933744471472866021)
    ·
      refine ⟨7808812675077088401162379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41647000933744471472866021 7808812675077088401162379)
      ·
        refine ⟨11713219012615632601743569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7808812675077088401162379 11713219012615632601743569)
        ·
          refine ⟨8784914259461724451307677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11713219012615632601743569 8784914259461724451307677)
          ·
            refine ⟨3294342847298146669240379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8784914259461724451307677 3294342847298146669240379)
            ·
              refine ⟨4941514270947220003860569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294342847298146669240379 4941514270947220003860569)
              ·
                refine ⟨3706135703210415002895427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941514270947220003860569 3706135703210415002895427)
                ·
                  refine ⟨5559203554815622504343141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706135703210415002895427 5559203554815622504343141)
                  ·
                    refine ⟨1042350666527929219564339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559203554815622504343141 1042350666527929219564339)
                    ·
                      rfl

theorem cell22_3044956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3044956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044956 prefixEnd_3044956 := by exact prefixLift 3044956
  have htrace : WordTrace (prefixWord ++ tailWord_3044956) baseStart_3044956 baseEnd_3044956 := by
    simpa [prefixWord, tailWord_3044956, baseEnd_3044956] using wordTrace_append hprefix tailTrace_3044956
  have hstable : (prefixWord ++ tailWord_3044956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044956).length < 2 ^ (prefixWord ++ tailWord_3044956).sum := by decide
  have hdescent : baseEnd_3044956 < baseStart_3044956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044967 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3044967 : Nat := 118140960795 + 3044967 * 2 ^ 59
def prefixEnd_3044967 : Nat := 4983230072969 + 3 ^ 40 * 3044967 * 2
def baseEnd_3044967 : Nat := 1042354432052728857539305

theorem tailTrace_3044967 : CollatzResearch.WordTrace tailWord_3044967 prefixEnd_3044967 1042354432052728857539305 := by
  unfold tailWord_3044967
  simp only [CollatzResearch.WordTrace]
  refine ⟨111059070359612072806293155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74039380239741381870862103 111059070359612072806293155)
  ·
    refine ⟨166588605539418109209439733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111059070359612072806293155 166588605539418109209439733)
    ·
      refine ⟨15617681769320447738384975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166588605539418109209439733 15617681769320447738384975)
      ·
        refine ⟨23426522653980671607577463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15617681769320447738384975 23426522653980671607577463)
        ·
          refine ⟨35139783980971007411366195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23426522653980671607577463 35139783980971007411366195)
          ·
            refine ⟨52709675971456511117049293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35139783980971007411366195 52709675971456511117049293)
            ·
              refine ⟨19766128489296191668893485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52709675971456511117049293 19766128489296191668893485)
              ·
                refine ⟨7412298183486071875835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19766128489296191668893485 7412298183486071875835057)
                ·
                  refine ⟨5559223637614553906876293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412298183486071875835057 5559223637614553906876293)
                  ·
                    refine ⟨1042354432052728857539305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559223637614553906876293 1042354432052728857539305)
                    ·
                      rfl

theorem cell22_3044967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3044967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044967 prefixEnd_3044967 := by exact prefixLift 3044967
  have htrace : WordTrace (prefixWord ++ tailWord_3044967) baseStart_3044967 baseEnd_3044967 := by
    simpa [prefixWord, tailWord_3044967, baseEnd_3044967] using wordTrace_append hprefix tailTrace_3044967
  have hstable : (prefixWord ++ tailWord_3044967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044967).length < 2 ^ (prefixWord ++ tailWord_3044967).sum := by decide
  have hdescent : baseEnd_3044967 < baseStart_3044967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3044982 : List Nat := [5, 1, 1, 2, 2, 11]
def baseStart_3044982 : Nat := 118140960795 + 3044982 * 2 ^ 59
def prefixEnd_3044982 : Nat := 4983230072969 + 3 ^ 40 * 3044982 * 2
def baseEnd_3044982 : Nat := 12868636627892269363139

theorem tailTrace_3044982 : CollatzResearch.WordTrace tailWord_3044982 prefixEnd_3044982 12868636627892269363139 := by
  unfold tailWord_3044982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941226090909858148005575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74039744969705153578726133 6941226090909858148005575)
  ·
    refine ⟨10411839136364787222008363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6941226090909858148005575 10411839136364787222008363)
    ·
      refine ⟨15617758704547180833012545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411839136364787222008363 15617758704547180833012545)
      ·
        refine ⟨11713319028410385624759409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15617758704547180833012545 11713319028410385624759409)
        ·
          refine ⟨8784989271307789218569557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11713319028410385624759409 8784989271307789218569557)
          ·
            refine ⟨12868636627892269363139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8784989271307789218569557 12868636627892269363139)
            ·
              rfl

theorem cell22_3044982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 11].length) (baseStart_3044982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3044982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3044982 prefixEnd_3044982 := by exact prefixLift 3044982
  have htrace : WordTrace (prefixWord ++ tailWord_3044982) baseStart_3044982 baseEnd_3044982 := by
    simpa [prefixWord, tailWord_3044982, baseEnd_3044982] using wordTrace_append hprefix tailTrace_3044982
  have hstable : (prefixWord ++ tailWord_3044982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3044982).length < 2 ^ (prefixWord ++ tailWord_3044982).sum := by decide
  have hdescent : baseEnd_3044982 < baseStart_3044982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3044982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045042 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_3045042 : Nat := 118140960795 + 3045042 * 2 ^ 59
def prefixEnd_3045042 : Nat := 4983230072969 + 3 ^ 40 * 3045042 * 2
def baseEnd_3045042 : Nat := 1042380106085453661914075

theorem tailTrace_3045042 : CollatzResearch.WordTrace tailWord_3045042 prefixEnd_3045042 1042380106085453661914075 := by
  unfold tailWord_3045042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27765451458585090153818345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74041203889560240410182253 27765451458585090153818345)
  ·
    refine ⟨20824088593938817615363759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27765451458585090153818345 20824088593938817615363759)
    ·
      refine ⟨31236132890908226423045639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20824088593938817615363759 31236132890908226423045639)
      ·
        refine ⟨46854199336362339634568459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31236132890908226423045639 46854199336362339634568459)
        ·
          refine ⟨70281299004543509451852689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46854199336362339634568459 70281299004543509451852689)
          ·
            refine ⟨52710974253407632088889517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70281299004543509451852689 52710974253407632088889517)
            ·
              refine ⟨19766615345027862033333569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52710974253407632088889517 19766615345027862033333569)
              ·
                refine ⟨14824961508770896525000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19766615345027862033333569 14824961508770896525000177)
                ·
                  refine ⟨11118721131578172393750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14824961508770896525000177 11118721131578172393750133)
                  ·
                    refine ⟨1042380106085453661914075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11118721131578172393750133 1042380106085453661914075)
                    ·
                      rfl

theorem cell22_3045042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_3045042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045042 prefixEnd_3045042 := by exact prefixLift 3045042
  have htrace : WordTrace (prefixWord ++ tailWord_3045042) baseStart_3045042 baseEnd_3045042 := by
    simpa [prefixWord, tailWord_3045042, baseEnd_3045042] using wordTrace_append hprefix tailTrace_3045042
  have hstable : (prefixWord ++ tailWord_3045042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045042).length < 2 ^ (prefixWord ++ tailWord_3045042).sum := by decide
  have hdescent : baseEnd_3045042 < baseStart_3045042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045087 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_3045087 : Nat := 118140960795 + 3045087 * 2 ^ 59
def prefixEnd_3045087 : Nat := 4983230072969 + 3 ^ 40 * 3045087 * 2
def baseEnd_3045087 : Nat := 1042395510505088544538937

theorem tailTrace_3045087 : CollatzResearch.WordTrace tailWord_3045087 prefixEnd_3045087 1042395510505088544538937 := by
  unfold tailWord_3045087
  simp only [CollatzResearch.WordTrace]
  refine ⟨111063447119177333300661515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74042298079451555533774343 111063447119177333300661515)
  ·
    refine ⟨166595170678765999950992273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111063447119177333300661515 166595170678765999950992273)
    ·
      refine ⟨124946378009074499963244205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166595170678765999950992273 124946378009074499963244205)
      ·
        refine ⟨46854891753402937486216577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124946378009074499963244205 46854891753402937486216577)
        ·
          refine ⟨35141168815052203114662433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46854891753402937486216577 35141168815052203114662433)
          ·
            refine ⟨26355876611289152335996825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35141168815052203114662433 26355876611289152335996825)
            ·
              refine ⟨19766907458466864251997619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26355876611289152335996825 19766907458466864251997619)
              ·
                refine ⟨29650361187700296377996429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19766907458466864251997619 29650361187700296377996429)
                ·
                  refine ⟨11118885445387611141748661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29650361187700296377996429 11118885445387611141748661)
                  ·
                    refine ⟨1042395510505088544538937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11118885445387611141748661 1042395510505088544538937)
                    ·
                      rfl

theorem cell22_3045087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_3045087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045087 prefixEnd_3045087 := by exact prefixLift 3045087
  have htrace : WordTrace (prefixWord ++ tailWord_3045087) baseStart_3045087 baseEnd_3045087 := by
    simpa [prefixWord, tailWord_3045087, baseEnd_3045087] using wordTrace_append hprefix tailTrace_3045087
  have hstable : (prefixWord ++ tailWord_3045087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045087).length < 2 ^ (prefixWord ++ tailWord_3045087).sum := by decide
  have hdescent : baseEnd_3045087 < baseStart_3045087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045132 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_3045132 : Nat := 118140960795 + 3045132 * 2 ^ 59
def prefixEnd_3045132 : Nat := 4983230072969 + 3 ^ 40 * 3045132 * 2
def baseEnd_3045132 : Nat := 1042410914924723427163799

theorem tailTrace_3045132 : CollatzResearch.WordTrace tailWord_3045132 prefixEnd_3045132 1042410914924723427163799 := by
  unfold tailWord_3045132
  simp only [CollatzResearch.WordTrace]
  refine ⟨55532544202007152993024825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74043392269342870657366433 55532544202007152993024825)
  ·
    refine ⟨41649408151505364744768619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55532544202007152993024825 41649408151505364744768619)
    ·
      refine ⟨62474112227258047117152929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41649408151505364744768619 62474112227258047117152929)
      ·
        refine ⟨46855584170443535337864697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62474112227258047117152929 46855584170443535337864697)
        ·
          refine ⟨35141688127832651503398523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46855584170443535337864697 35141688127832651503398523)
          ·
            refine ⟨52712532191748977255097785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35141688127832651503398523 52712532191748977255097785)
            ·
              refine ⟨39534399143811732941323339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52712532191748977255097785 39534399143811732941323339)
              ·
                refine ⟨59301598715717599411985009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39534399143811732941323339 59301598715717599411985009)
                ·
                  refine ⟨44476199036788199558988757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59301598715717599411985009 44476199036788199558988757)
                  ·
                    refine ⟨1042410914924723427163799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44476199036788199558988757 1042410914924723427163799)
                    ·
                      rfl

theorem cell22_3045132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_3045132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045132 prefixEnd_3045132 := by exact prefixLift 3045132
  have htrace : WordTrace (prefixWord ++ tailWord_3045132) baseStart_3045132 baseEnd_3045132 := by
    simpa [prefixWord, tailWord_3045132, baseEnd_3045132] using wordTrace_append hprefix tailTrace_3045132
  have hstable : (prefixWord ++ tailWord_3045132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045132).length < 2 ^ (prefixWord ++ tailWord_3045132).sum := by decide
  have hdescent : baseEnd_3045132 < baseStart_3045132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045271 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3045271 : Nat := 118140960795 + 3045271 * 2 ^ 59
def prefixEnd_3045271 : Nat := 4983230072969 + 3 ^ 40 * 3045271 * 2
def baseEnd_3045271 : Nat := 1042458497465373397938373

theorem tailTrace_3045271 : CollatzResearch.WordTrace tailWord_3045271 prefixEnd_3045271 1042458497465373397938373 := by
  unfold tailWord_3045271
  simp only [CollatzResearch.WordTrace]
  refine ⟨111070158150510732725359667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74046772100340488483573111 111070158150510732725359667)
  ·
    refine ⟨166605237225766099088039501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111070158150510732725359667 166605237225766099088039501)
    ·
      refine ⟨62476963959662287158014813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166605237225766099088039501 62476963959662287158014813)
      ·
        refine ⟨23428861484873357684255555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62476963959662287158014813 23428861484873357684255555)
        ·
          refine ⟨35143292227310036526383333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23428861484873357684255555 35143292227310036526383333)
          ·
            refine ⟨6589367292620631848696875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35143292227310036526383333 6589367292620631848696875)
            ·
              refine ⟨9884050938930947773045313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589367292620631848696875 9884050938930947773045313)
              ·
                refine ⟨7413038204198210829783985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9884050938930947773045313 7413038204198210829783985)
                ·
                  refine ⟨5559778653148658122337989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413038204198210829783985 5559778653148658122337989)
                  ·
                    refine ⟨1042458497465373397938373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559778653148658122337989 1042458497465373397938373)
                    ·
                      rfl

theorem cell22_3045271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3045271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045271 prefixEnd_3045271 := by exact prefixLift 3045271
  have htrace : WordTrace (prefixWord ++ tailWord_3045271) baseStart_3045271 baseEnd_3045271 := by
    simpa [prefixWord, tailWord_3045271, baseEnd_3045271] using wordTrace_append hprefix tailTrace_3045271
  have hstable : (prefixWord ++ tailWord_3045271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045271).length < 2 ^ (prefixWord ++ tailWord_3045271).sum := by decide
  have hdescent : baseEnd_3045271 < baseStart_3045271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045294 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3045294 : Nat := 118140960795 + 3045294 * 2 ^ 59
def prefixEnd_3045294 : Nat := 4983230072969 + 3 ^ 40 * 3045294 * 2
def baseEnd_3045294 : Nat := 1042466370835409004613303

theorem tailTrace_3045294 : CollatzResearch.WordTrace tailWord_3045294 prefixEnd_3045294 1042466370835409004613303 := by
  unfold tailWord_3045294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883874628678425956680867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74047331352951605102297957 13883874628678425956680867)
  ·
    refine ⟨20825811943017638935021301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883874628678425956680867 20825811943017638935021301)
    ·
      refine ⟨1952419869657903650158247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20825811943017638935021301 1952419869657903650158247)
      ·
        refine ⟨2928629804486855475237371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952419869657903650158247 2928629804486855475237371)
        ·
          refine ⟨4392944706730283212856057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928629804486855475237371 4392944706730283212856057)
          ·
            refine ⟨3294708530047712409642043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4392944706730283212856057 3294708530047712409642043)
            ·
              refine ⟨4942062795071568614463065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294708530047712409642043 4942062795071568614463065)
              ·
                refine ⟨3706547096303676460847299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4942062795071568614463065 3706547096303676460847299)
                ·
                  refine ⟨5559820644455514691270949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706547096303676460847299 5559820644455514691270949)
                  ·
                    refine ⟨1042466370835409004613303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559820644455514691270949 1042466370835409004613303)
                    ·
                      rfl

theorem cell22_3045294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3045294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045294 prefixEnd_3045294 := by exact prefixLift 3045294
  have htrace : WordTrace (prefixWord ++ tailWord_3045294) baseStart_3045294 baseEnd_3045294 := by
    simpa [prefixWord, tailWord_3045294, baseEnd_3045294] using wordTrace_append hprefix tailTrace_3045294
  have hstable : (prefixWord ++ tailWord_3045294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045294).length < 2 ^ (prefixWord ++ tailWord_3045294).sum := by decide
  have hdescent : baseEnd_3045294 < baseStart_3045294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045596 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 4]
def baseStart_3045596 : Nat := 118140960795 + 3045596 * 2 ^ 59
def prefixEnd_3045596 : Nat := 4983230072969 + 3 ^ 40 * 3045596 * 2
def baseEnd_3045596 : Nat := 347523250535726961187459

theorem tailTrace_3045596 : CollatzResearch.WordTrace tailWord_3045596 prefixEnd_3045596 347523250535726961187459 := by
  unfold tailWord_3045596
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541005937166656615470321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74054674582888875487293761 55541005937166656615470321)
  ·
    refine ⟨41655754452874992461602741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55541005937166656615470321 41655754452874992461602741)
    ·
      refine ⟨3905226979957030543275257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41655754452874992461602741 3905226979957030543275257)
      ·
        refine ⟨2928920234967772907456443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905226979957030543275257 2928920234967772907456443)
        ·
          refine ⟨4393380352451659361184665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928920234967772907456443 4393380352451659361184665)
          ·
            refine ⟨3295035264338744520888499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4393380352451659361184665 3295035264338744520888499)
            ·
              refine ⟨4942552896508116781332749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295035264338744520888499 4942552896508116781332749)
              ·
                refine ⟨1853457336190543792999781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4942552896508116781332749 1853457336190543792999781)
                ·
                  refine ⟨347523250535726961187459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853457336190543792999781 347523250535726961187459)
                  ·
                    rfl

theorem cell22_3045596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_3045596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045596 prefixEnd_3045596 := by exact prefixLift 3045596
  have htrace : WordTrace (prefixWord ++ tailWord_3045596) baseStart_3045596 baseEnd_3045596 := by
    simpa [prefixWord, tailWord_3045596, baseEnd_3045596] using wordTrace_append hprefix tailTrace_3045596
  have hstable : (prefixWord ++ tailWord_3045596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045596).length < 2 ^ (prefixWord ++ tailWord_3045596).sum := by decide
  have hdescent : baseEnd_3045596 < baseStart_3045596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045622 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3045622 : Nat := 118140960795 + 3045622 * 2 ^ 59
def prefixEnd_3045622 : Nat := 4983230072969 + 3 ^ 40 * 3045622 * 2
def baseEnd_3045622 : Nat := 1042578651938525482412297

theorem tailTrace_3045622 : CollatzResearch.WordTrace tailWord_3045622 prefixEnd_3045622 1042578651938525482412297 := by
  unfold tailWord_3045622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942685010764944979461695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74055306781492746447591413 6942685010764944979461695)
  ·
    refine ⟨10414027516147417469192543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942685010764944979461695 10414027516147417469192543)
    ·
      refine ⟨15621041274221126203788815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10414027516147417469192543 15621041274221126203788815)
      ·
        refine ⟨23431561911331689305683223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15621041274221126203788815 23431561911331689305683223)
        ·
          refine ⟨35147342866997533958524835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431561911331689305683223 35147342866997533958524835)
          ·
            refine ⟨52721014300496300937787253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35147342866997533958524835 52721014300496300937787253)
            ·
              refine ⟨4942595090671528212917555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52721014300496300937787253 4942595090671528212917555)
              ·
                refine ⟨7413892636007292319376333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942595090671528212917555 7413892636007292319376333)
                ·
                  refine ⟨2780209738502734619766125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7413892636007292319376333 2780209738502734619766125)
                  ·
                    refine ⟨1042578651938525482412297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780209738502734619766125 1042578651938525482412297)
                    ·
                      rfl

theorem cell22_3045622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3045622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045622 prefixEnd_3045622 := by exact prefixLift 3045622
  have htrace : WordTrace (prefixWord ++ tailWord_3045622) baseStart_3045622 baseEnd_3045622 := by
    simpa [prefixWord, tailWord_3045622, baseEnd_3045622] using wordTrace_append hprefix tailTrace_3045622
  have hstable : (prefixWord ++ tailWord_3045622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045622).length < 2 ^ (prefixWord ++ tailWord_3045622).sum := by decide
  have hdescent : baseEnd_3045622 < baseStart_3045622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045633 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3045633 : Nat := 118140960795 + 3045633 * 2 ^ 59
def prefixEnd_3045633 : Nat := 4983230072969 + 3 ^ 40 * 3045633 * 2
def baseEnd_3045633 : Nat := 1042582417463325120387263

theorem tailTrace_3045633 : CollatzResearch.WordTrace tailWord_3045633 prefixEnd_3045633 1042582417463325120387263 := by
  unfold tailWord_3045633
  simp only [CollatzResearch.WordTrace]
  refine ⟨111083361375199268550037553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74055574250132845700025035 111083361375199268550037553)
  ·
    refine ⟨83312521031399451412528165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111083361375199268550037553 83312521031399451412528165)
    ·
      refine ⟨15621097693387397139849031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83312521031399451412528165 15621097693387397139849031)
      ·
        refine ⟨23431646540081095709773547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15621097693387397139849031 23431646540081095709773547)
        ·
          refine ⟨35147469810121643564660321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431646540081095709773547 35147469810121643564660321)
          ·
            refine ⟨26360602357591232673495241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35147469810121643564660321 26360602357591232673495241)
            ·
              refine ⟨19770451768193424505121431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26360602357591232673495241 19770451768193424505121431)
              ·
                refine ⟨29655677652290136757682147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19770451768193424505121431 29655677652290136757682147)
                ·
                  refine ⟨44483516478435205136523221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29655677652290136757682147 44483516478435205136523221)
                  ·
                    refine ⟨1042582417463325120387263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44483516478435205136523221 1042582417463325120387263)
                    ·
                      rfl

theorem cell22_3045633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3045633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045633 prefixEnd_3045633 := by exact prefixLift 3045633
  have htrace : WordTrace (prefixWord ++ tailWord_3045633) baseStart_3045633 baseEnd_3045633 := by
    simpa [prefixWord, tailWord_3045633, baseEnd_3045633] using wordTrace_append hprefix tailTrace_3045633
  have hstable : (prefixWord ++ tailWord_3045633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045633).length < 2 ^ (prefixWord ++ tailWord_3045633).sum := by decide
  have hdescent : baseEnd_3045633 < baseStart_3045633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045665 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3045665 : Nat := 118140960795 + 3045665 * 2 ^ 59
def prefixEnd_3045665 : Nat := 4983230072969 + 3 ^ 40 * 3045665 * 2
def baseEnd_3045665 : Nat := 1042593371717287703587165

theorem tailTrace_3045665 : CollatzResearch.WordTrace tailWord_3045665 prefixEnd_3045665 1042593371717287703587165 := by
  unfold tailWord_3045665
  simp only [CollatzResearch.WordTrace]
  refine ⟨111084528511083338015202449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74056352340722225343468299 111084528511083338015202449)
  ·
    refine ⟨83313396383312503511401837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111084528511083338015202449 83313396383312503511401837)
    ·
      refine ⟨31242523643742188816775689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83313396383312503511401837 31242523643742188816775689)
      ·
        refine ⟨23431892732806641612581767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31242523643742188816775689 23431892732806641612581767)
        ·
          refine ⟨35147839099209962418872651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431892732806641612581767 35147839099209962418872651)
          ·
            refine ⟨52721758648814943628308977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35147839099209962418872651 52721758648814943628308977)
            ·
              refine ⟨39541318986611207721231733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52721758648814943628308977 39541318986611207721231733)
              ·
                refine ⟨3706998654994800723865475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39541318986611207721231733 3706998654994800723865475)
                ·
                  refine ⟨5560497982492201085798213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706998654994800723865475 5560497982492201085798213)
                  ·
                    refine ⟨1042593371717287703587165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560497982492201085798213 1042593371717287703587165)
                    ·
                      rfl

theorem cell22_3045665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3045665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045665 prefixEnd_3045665 := by exact prefixLift 3045665
  have htrace : WordTrace (prefixWord ++ tailWord_3045665) baseStart_3045665 baseEnd_3045665 := by
    simpa [prefixWord, tailWord_3045665, baseEnd_3045665] using wordTrace_append hprefix tailTrace_3045665
  have hstable : (prefixWord ++ tailWord_3045665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045665).length < 2 ^ (prefixWord ++ tailWord_3045665).sum := by decide
  have hdescent : baseEnd_3045665 < baseStart_3045665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045695 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 1, 5]
def baseStart_3045695 : Nat := 118140960795 + 3045695 * 2 ^ 59
def prefixEnd_3045695 : Nat := 4983230072969 + 3 ^ 40 * 3045695 * 2
def baseEnd_3045695 : Nat := 1042603641330377625337073

theorem tailTrace_3045695 : CollatzResearch.WordTrace tailWord_3045695 prefixEnd_3045695 1042603641330377625337073 := by
  unfold tailWord_3045695
  simp only [CollatzResearch.WordTrace]
  refine ⟨111085622700974653138794539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74057081800649768759196359 111085622700974653138794539)
  ·
    refine ⟨166628434051461979708191809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111085622700974653138794539 166628434051461979708191809)
    ·
      refine ⟨124971325538596484781143857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166628434051461979708191809 124971325538596484781143857)
      ·
        refine ⟨93728494153947363585857893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124971325538596484781143857 93728494153947363585857893)
        ·
          refine ⟨17574092653865130672348355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93728494153947363585857893 17574092653865130672348355)
          ·
            refine ⟨26361138980797696008522533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17574092653865130672348355 26361138980797696008522533)
            ·
              refine ⟨4942713558899568001597975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26361138980797696008522533 4942713558899568001597975)
              ·
                refine ⟨7414070338349352002396963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942713558899568001597975 7414070338349352002396963)
                ·
                  refine ⟨11121105507524028003595445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7414070338349352002396963 11121105507524028003595445)
                  ·
                    refine ⟨1042603641330377625337073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11121105507524028003595445 1042603641330377625337073)
                    ·
                      rfl

theorem cell22_3045695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_3045695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045695 prefixEnd_3045695 := by exact prefixLift 3045695
  have htrace : WordTrace (prefixWord ++ tailWord_3045695) baseStart_3045695 baseEnd_3045695 := by
    simpa [prefixWord, tailWord_3045695, baseEnd_3045695] using wordTrace_append hprefix tailTrace_3045695
  have hstable : (prefixWord ++ tailWord_3045695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045695).length < 2 ^ (prefixWord ++ tailWord_3045695).sum := by decide
  have hdescent : baseEnd_3045695 < baseStart_3045695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045697 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 6]
def baseStart_3045697 : Nat := 118140960795 + 3045697 * 2 ^ 59
def prefixEnd_3045697 : Nat := 4983230072969 + 3 ^ 40 * 3045697 * 2
def baseEnd_3045697 : Nat := 347534775323750095595689

theorem tailTrace_3045697 : CollatzResearch.WordTrace tailWord_3045697 prefixEnd_3045697 347534775323750095595689 := by
  unfold tailWord_3045697
  simp only [CollatzResearch.WordTrace]
  refine ⟨111085695646967407480367345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74057130431311604986911563 111085695646967407480367345)
  ·
    refine ⟨83314271735225555610275509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111085695646967407480367345 83314271735225555610275509)
    ·
      refine ⟨7810712975177395838463329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83314271735225555610275509 7810712975177395838463329)
      ·
        refine ⟨5858034731383046878847497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7810712975177395838463329 5858034731383046878847497)
        ·
          refine ⟨4393526048537285159135623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5858034731383046878847497 4393526048537285159135623)
          ·
            refine ⟨6590289072805927738703435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393526048537285159135623 6590289072805927738703435)
            ·
              refine ⟨9885433609208891608055153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6590289072805927738703435 9885433609208891608055153)
              ·
                refine ⟨7414075206906668706041365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9885433609208891608055153 7414075206906668706041365)
                ·
                  refine ⟨347534775323750095595689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7414075206906668706041365 347534775323750095595689)
                  ·
                    rfl

theorem cell22_3045697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_3045697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045697 prefixEnd_3045697 := by exact prefixLift 3045697
  have htrace : WordTrace (prefixWord ++ tailWord_3045697) baseStart_3045697 baseEnd_3045697 := by
    simpa [prefixWord, tailWord_3045697, baseEnd_3045697] using wordTrace_append hprefix tailTrace_3045697
  have hstable : (prefixWord ++ tailWord_3045697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045697).length < 2 ^ (prefixWord ++ tailWord_3045697).sum := by decide
  have hdescent : baseEnd_3045697 < baseStart_3045697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045710 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3045710 : Nat := 118140960795 + 3045710 * 2 ^ 59
def prefixEnd_3045710 : Nat := 4983230072969 + 3 ^ 40 * 3045710 * 2
def baseEnd_3045710 : Nat := 1042608776136922586212027

theorem tailTrace_3045710 : CollatzResearch.WordTrace tailWord_3045710 prefixEnd_3045710 1042608776136922586212027 := by
  unfold tailWord_3045710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13885771224490038837573823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74057446530613540467060389 13885771224490038837573823)
  ·
    refine ⟨20828656836735058256360735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13885771224490038837573823 20828656836735058256360735)
    ·
      refine ⟨31242985255102587384541103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20828656836735058256360735 31242985255102587384541103)
      ·
        refine ⟨46864477882653881076811655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31242985255102587384541103 46864477882653881076811655)
        ·
          refine ⟨70296716823980821615217483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46864477882653881076811655 70296716823980821615217483)
          ·
            refine ⟨105445075235971232422826225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70296716823980821615217483 105445075235971232422826225)
            ·
              refine ⟨79083806426978424317119669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105445075235971232422826225 79083806426978424317119669)
              ·
                refine ⟨7414106852529227279729969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79083806426978424317119669 7414106852529227279729969)
                ·
                  refine ⟨5560580139396920459797477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7414106852529227279729969 5560580139396920459797477)
                  ·
                    refine ⟨1042608776136922586212027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560580139396920459797477 1042608776136922586212027)
                    ·
                      rfl

theorem cell22_3045710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3045710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045710 prefixEnd_3045710 := by exact prefixLift 3045710
  have htrace : WordTrace (prefixWord ++ tailWord_3045710) baseStart_3045710 baseEnd_3045710 := by
    simpa [prefixWord, tailWord_3045710, baseEnd_3045710] using wordTrace_append hprefix tailTrace_3045710
  have hstable : (prefixWord ++ tailWord_3045710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045710).length < 2 ^ (prefixWord ++ tailWord_3045710).sum := by decide
  have hdescent : baseEnd_3045710 < baseStart_3045710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045757 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_3045757 : Nat := 118140960795 + 3045757 * 2 ^ 59
def prefixEnd_3045757 : Nat := 4983230072969 + 3 ^ 40 * 3045757 * 2
def baseEnd_3045757 : Nat := 1042624865197430130286883

theorem tailTrace_3045757 : CollatzResearch.WordTrace tailWord_3045757 prefixEnd_3045757 1042624865197430130286883 := by
  unfold tailWord_3045757
  simp only [CollatzResearch.WordTrace]
  refine ⟨111087884026750037727551525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74058589351166691818367683 111087884026750037727551525)
  ·
    refine ⟨20828978255015632073915911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111087884026750037727551525 20828978255015632073915911)
    ·
      refine ⟨31243467382523448110873867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20828978255015632073915911 31243467382523448110873867)
      ·
        refine ⟨46865201073785172166310801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31243467382523448110873867 46865201073785172166310801)
        ·
          refine ⟨35148900805338879124733101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46865201073785172166310801 35148900805338879124733101)
          ·
            refine ⟨13180837802002079671774913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35148900805338879124733101 13180837802002079671774913)
            ·
              refine ⟨9885628351501559753831185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13180837802002079671774913 9885628351501559753831185)
              ·
                refine ⟨7414221263626169815373389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9885628351501559753831185 7414221263626169815373389)
                ·
                  refine ⟨2780332973859813680765021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7414221263626169815373389 2780332973859813680765021)
                  ·
                    refine ⟨1042624865197430130286883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780332973859813680765021 1042624865197430130286883)
                    ·
                      rfl

theorem cell22_3045757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_3045757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045757 prefixEnd_3045757 := by exact prefixLift 3045757
  have htrace : WordTrace (prefixWord ++ tailWord_3045757) baseStart_3045757 baseEnd_3045757 := by
    simpa [prefixWord, tailWord_3045757, baseEnd_3045757] using wordTrace_append hprefix tailTrace_3045757
  have hstable : (prefixWord ++ tailWord_3045757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045757).length < 2 ^ (prefixWord ++ tailWord_3045757).sum := by decide
  have hdescent : baseEnd_3045757 < baseStart_3045757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045791 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 1, 3]
def baseStart_3045791 : Nat := 118140960795 + 3045791 * 2 ^ 59
def prefixEnd_3045791 : Nat := 4983230072969 + 3 ^ 40 * 3045791 * 2
def baseEnd_3045791 : Nat := 1042636504092265374936779

theorem tailTrace_3045791 : CollatzResearch.WordTrace tailWord_3045791 prefixEnd_3045791 1042636504092265374936779 := by
  unfold tailWord_3045791
  simp only [CollatzResearch.WordTrace]
  refine ⟨111089124108626861534289227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74059416072417907689526151 111089124108626861534289227)
  ·
    refine ⟨166633686162940292301433841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111089124108626861534289227 166633686162940292301433841)
    ·
      refine ⟨124975264622205219226075381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166633686162940292301433841 124975264622205219226075381)
      ·
        refine ⟨11716431058331739302444567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124975264622205219226075381 11716431058331739302444567)
        ·
          refine ⟨17574646587497608953666851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11716431058331739302444567 17574646587497608953666851)
          ·
            refine ⟨26361969881246413430500277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17574646587497608953666851 26361969881246413430500277)
            ·
              refine ⟨2471434676366851259109401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26361969881246413430500277 2471434676366851259109401)
              ·
                refine ⟨1853576007275138444332051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471434676366851259109401 1853576007275138444332051)
                ·
                  refine ⟨2780364010912707666498077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853576007275138444332051 2780364010912707666498077)
                  ·
                    refine ⟨1042636504092265374936779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780364010912707666498077 1042636504092265374936779)
                    ·
                      rfl

theorem cell22_3045791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_3045791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045791 prefixEnd_3045791 := by exact prefixLift 3045791
  have htrace : WordTrace (prefixWord ++ tailWord_3045791) baseStart_3045791 baseEnd_3045791 := by
    simpa [prefixWord, tailWord_3045791, baseEnd_3045791] using wordTrace_append hprefix tailTrace_3045791
  have hstable : (prefixWord ++ tailWord_3045791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045791).length < 2 ^ (prefixWord ++ tailWord_3045791).sum := by decide
  have hdescent : baseEnd_3045791 < baseStart_3045791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045817 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_3045817 : Nat := 118140960795 + 3045817 * 2 ^ 59
def prefixEnd_3045817 : Nat := 4983230072969 + 3 ^ 40 * 3045817 * 2
def baseEnd_3045817 : Nat := 1042645404423609973786699

theorem tailTrace_3045817 : CollatzResearch.WordTrace tailWord_3045817 prefixEnd_3045817 1042645404423609973786699 := by
  unfold tailWord_3045817
  simp only [CollatzResearch.WordTrace]
  refine ⟨111090072406532667974735705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74060048271021778649823803 111090072406532667974735705)
  ·
    refine ⟨83317554304899500981051779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111090072406532667974735705 83317554304899500981051779)
    ·
      refine ⟨124976331457349251471577669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83317554304899500981051779 124976331457349251471577669)
      ·
        refine ⟨23433062148252984650920813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124976331457349251471577669 23433062148252984650920813)
        ·
          refine ⟨8787398305594869244095305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23433062148252984650920813 8787398305594869244095305)
          ·
            refine ⟨6590548729196151933071479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8787398305594869244095305 6590548729196151933071479)
            ·
              refine ⟨9885823093794227899607219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6590548729196151933071479 9885823093794227899607219)
              ·
                refine ⟨14828734640691341849410829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885823093794227899607219 14828734640691341849410829)
                ·
                  refine ⟨5560775490259253193529061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14828734640691341849410829 5560775490259253193529061)
                  ·
                    refine ⟨1042645404423609973786699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560775490259253193529061 1042645404423609973786699)
                    ·
                      rfl

theorem cell22_3045817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_3045817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045817 prefixEnd_3045817 := by exact prefixLift 3045817
  have htrace : WordTrace (prefixWord ++ tailWord_3045817) baseStart_3045817 baseEnd_3045817 := by
    simpa [prefixWord, tailWord_3045817, baseEnd_3045817] using wordTrace_append hprefix tailTrace_3045817
  have hstable : (prefixWord ++ tailWord_3045817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045817).length < 2 ^ (prefixWord ++ tailWord_3045817).sum := by decide
  have hdescent : baseEnd_3045817 < baseStart_3045817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045834 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_3045834 : Nat := 118140960795 + 3045834 * 2 ^ 59
def prefixEnd_3045834 : Nat := 4983230072969 + 3 ^ 40 * 3045834 * 2
def baseEnd_3045834 : Nat := 1042651223871027596111647

theorem tailTrace_3045834 : CollatzResearch.WordTrace tailWord_3045834 prefixEnd_3045834 1042651223871027596111647 := by
  unfold tailWord_3045834
  simp only [CollatzResearch.WordTrace]
  refine ⟨27772673111867769969526139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74060461631647386585403037 27772673111867769969526139)
  ·
    refine ⟨41659009667801654954289209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27772673111867769969526139 41659009667801654954289209)
    ·
      refine ⟨31244257250851241215716907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41659009667801654954289209 31244257250851241215716907)
      ·
        refine ⟨46866385876276861823575361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31244257250851241215716907 46866385876276861823575361)
        ·
          refine ⟨35149789407207646367681521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46866385876276861823575361 35149789407207646367681521)
          ·
            refine ⟨26362342055405734775761141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35149789407207646367681521 26362342055405734775761141)
            ·
              refine ⟨2471469567694287635227607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26362342055405734775761141 2471469567694287635227607)
              ·
                refine ⟨3707204351541431452841411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471469567694287635227607 3707204351541431452841411)
                ·
                  refine ⟨5560806527312147179262117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707204351541431452841411 5560806527312147179262117)
                  ·
                    refine ⟨1042651223871027596111647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560806527312147179262117 1042651223871027596111647)
                    ·
                      rfl

theorem cell22_3045834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_3045834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045834 prefixEnd_3045834 := by exact prefixLift 3045834
  have htrace : WordTrace (prefixWord ++ tailWord_3045834) baseStart_3045834 baseEnd_3045834 := by
    simpa [prefixWord, tailWord_3045834, baseEnd_3045834] using wordTrace_append hprefix tailTrace_3045834
  have hstable : (prefixWord ++ tailWord_3045834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045834).length < 2 ^ (prefixWord ++ tailWord_3045834).sum := by decide
  have hdescent : baseEnd_3045834 < baseStart_3045834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045842 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3045842 : Nat := 118140960795 + 3045842 * 2 ^ 59
def prefixEnd_3045842 : Nat := 4983230072969 + 3 ^ 40 * 3045842 * 2
def baseEnd_3045842 : Nat := 1042653962434518241911623

theorem tailTrace_3045842 : CollatzResearch.WordTrace tailWord_3045842 prefixEnd_3045842 1042653962434518241911623 := by
  unfold tailWord_3045842
  simp only [CollatzResearch.WordTrace]
  refine ⟨27772746057860524311098945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74060656154294731496263853 27772746057860524311098945)
  ·
    refine ⟨20829559543395393233324209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27772746057860524311098945 20829559543395393233324209)
    ·
      refine ⟨15622169657546544924993157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20829559543395393233324209 15622169657546544924993157)
      ·
        refine ⟨2929156810789977173436217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15622169657546544924993157 2929156810789977173436217)
        ·
          refine ⟨2196867608092482880077163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2929156810789977173436217 2196867608092482880077163)
          ·
            refine ⟨3295301412138724320115745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196867608092482880077163 3295301412138724320115745)
            ·
              refine ⟨2471476059104043240086809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3295301412138724320115745 2471476059104043240086809)
              ·
                refine ⟨1853607044328032430065107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471476059104043240086809 1853607044328032430065107)
                ·
                  refine ⟨2780410566492048645097661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853607044328032430065107 2780410566492048645097661)
                  ·
                    refine ⟨1042653962434518241911623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780410566492048645097661 1042653962434518241911623)
                    ·
                      rfl

theorem cell22_3045842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3045842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045842 prefixEnd_3045842 := by exact prefixLift 3045842
  have htrace : WordTrace (prefixWord ++ tailWord_3045842) baseStart_3045842 baseEnd_3045842 := by
    simpa [prefixWord, tailWord_3045842, baseEnd_3045842] using wordTrace_append hprefix tailTrace_3045842
  have hstable : (prefixWord ++ tailWord_3045842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045842).length < 2 ^ (prefixWord ++ tailWord_3045842).sum := by decide
  have hdescent : baseEnd_3045842 < baseStart_3045842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045864 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_3045864 : Nat := 118140960795 + 3045864 * 2 ^ 59
def prefixEnd_3045864 : Nat := 4983230072969 + 3 ^ 40 * 3045864 * 2
def baseEnd_3045864 : Nat := 1042661493484117517861555

theorem tailTrace_3045864 : CollatzResearch.WordTrace tailWord_3045864 prefixEnd_3045864 1042661493484117517861555 := by
  unfold tailWord_3045864
  simp only [CollatzResearch.WordTrace]
  refine ⟨55545893318681197500848323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74061191091574930001131097 55545893318681197500848323)
  ·
    refine ⟨83318839978021796251272485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55545893318681197500848323 83318839978021796251272485)
    ·
      refine ⟨15622282495879086797113591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83318839978021796251272485 15622282495879086797113591)
      ·
        refine ⟨23433423743818630195670387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15622282495879086797113591 23433423743818630195670387)
        ·
          refine ⟨35150135615727945293505581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23433423743818630195670387 35150135615727945293505581)
          ·
            refine ⟨13181300855897979485064593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35150135615727945293505581 13181300855897979485064593)
            ·
              refine ⟨9885975641923484613798445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13181300855897979485064593 9885975641923484613798445)
              ·
                refine ⟨3707240865721306730174417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9885975641923484613798445 3707240865721306730174417)
                ·
                  refine ⟨2780430649290980047630813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3707240865721306730174417 2780430649290980047630813)
                  ·
                    refine ⟨1042661493484117517861555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780430649290980047630813 1042661493484117517861555)
                    ·
                      rfl

theorem cell22_3045864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_3045864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045864 prefixEnd_3045864 := by exact prefixLift 3045864
  have htrace : WordTrace (prefixWord ++ tailWord_3045864) baseStart_3045864 baseEnd_3045864 := by
    simpa [prefixWord, tailWord_3045864, baseEnd_3045864] using wordTrace_append hprefix tailTrace_3045864
  have hstable : (prefixWord ++ tailWord_3045864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045864).length < 2 ^ (prefixWord ++ tailWord_3045864).sum := by decide
  have hdescent : baseEnd_3045864 < baseStart_3045864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045909 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_3045909 : Nat := 118140960795 + 3045909 * 2 ^ 59
def prefixEnd_3045909 : Nat := 4983230072969 + 3 ^ 40 * 3045909 * 2
def baseEnd_3045909 : Nat := 1042676897903752400486417

theorem tailTrace_3045909 : CollatzResearch.WordTrace tailWord_3045909 prefixEnd_3045909 1042676897903752400486417 := by
  unfold tailWord_3045909
  simp only [CollatzResearch.WordTrace]
  refine ⟨111093427922199367687084781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74062285281466245124723187 111093427922199367687084781)
  ·
    refine ⟨41660035470824762882656793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111093427922199367687084781 41660035470824762882656793)
    ·
      refine ⟨31245026603118572161992595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41660035470824762882656793 31245026603118572161992595)
      ·
        refine ⟨46867539904677858242988893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31245026603118572161992595 46867539904677858242988893)
        ·
          refine ⟨17575327464254196841120835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46867539904677858242988893 17575327464254196841120835)
          ·
            refine ⟨26362991196381295261681253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17575327464254196841120835 26362991196381295261681253)
            ·
              refine ⟨4943060849321492861565235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26362991196381295261681253 4943060849321492861565235)
              ·
                refine ⟨7414591273982239292347853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943060849321492861565235 7414591273982239292347853)
                ·
                  refine ⟨2780471727743339734630445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7414591273982239292347853 2780471727743339734630445)
                  ·
                    refine ⟨1042676897903752400486417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780471727743339734630445 1042676897903752400486417)
                    ·
                      rfl

theorem cell22_3045909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_3045909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045909 prefixEnd_3045909 := by exact prefixLift 3045909
  have htrace : WordTrace (prefixWord ++ tailWord_3045909) baseStart_3045909 baseEnd_3045909 := by
    simpa [prefixWord, tailWord_3045909, baseEnd_3045909] using wordTrace_append hprefix tailTrace_3045909
  have hstable : (prefixWord ++ tailWord_3045909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045909).length < 2 ^ (prefixWord ++ tailWord_3045909).sum := by decide
  have hdescent : baseEnd_3045909 < baseStart_3045909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045935 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3045935 : Nat := 118140960795 + 3045935 * 2 ^ 59
def prefixEnd_3045935 : Nat := 4983230072969 + 3 ^ 40 * 3045935 * 2
def baseEnd_3045935 : Nat := 1042685798235096999336337

theorem tailTrace_3045935 : CollatzResearch.WordTrace tailWord_3045935 prefixEnd_3045935 1042685798235096999336337 := by
  unfold tailWord_3045935
  simp only [CollatzResearch.WordTrace]
  refine ⟨111094376220105174127531259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74062917480070116085020839 111094376220105174127531259)
  ·
    refine ⟨166641564330157761191296889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111094376220105174127531259 166641564330157761191296889)
    ·
      refine ⟨124981173247618320893472667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166641564330157761191296889 124981173247618320893472667)
      ·
        refine ⟨187471759871427481340209001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124981173247618320893472667 187471759871427481340209001)
        ·
          refine ⟨140603819903570611005156751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187471759871427481340209001 140603819903570611005156751)
          ·
            refine ⟨210905729855355916507735127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140603819903570611005156751 210905729855355916507735127)
            ·
              refine ⟨316358594783033874761602691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210905729855355916507735127 316358594783033874761602691)
              ·
                refine ⟨474537892174550812142404037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316358594783033874761602691 474537892174550812142404037)
                ·
                  refine ⟨88975854782728277276700757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474537892174550812142404037 88975854782728277276700757)
                  ·
                    refine ⟨1042685798235096999336337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88975854782728277276700757 1042685798235096999336337)
                    ·
                      rfl

theorem cell22_3045935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3045935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045935 prefixEnd_3045935 := by exact prefixLift 3045935
  have htrace : WordTrace (prefixWord ++ tailWord_3045935) baseStart_3045935 baseEnd_3045935 := by
    simpa [prefixWord, tailWord_3045935, baseEnd_3045935] using wordTrace_append hprefix tailTrace_3045935
  have hstable : (prefixWord ++ tailWord_3045935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045935).length < 2 ^ (prefixWord ++ tailWord_3045935).sum := by decide
  have hdescent : baseEnd_3045935 < baseStart_3045935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3045967 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 6]
def baseStart_3045967 : Nat := 118140960795 + 3045967 * 2 ^ 59
def prefixEnd_3045967 : Nat := 4983230072969 + 3 ^ 40 * 3045967 * 2
def baseEnd_3045967 : Nat := 347565584163019860845413

theorem tailTrace_3045967 : CollatzResearch.WordTrace tailWord_3045967 prefixEnd_3045967 347565584163019860845413 := by
  unfold tailWord_3045967
  simp only [CollatzResearch.WordTrace]
  refine ⟨111095543355989243592696155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74063695570659495728464103 111095543355989243592696155)
  ·
    refine ⟨166643315033983865389044233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111095543355989243592696155 166643315033983865389044233)
    ·
      refine ⟨124982486275487899041783175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166643315033983865389044233 124982486275487899041783175)
      ·
        refine ⟨187473729413231848562674763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124982486275487899041783175 187473729413231848562674763)
        ·
          refine ⟨281210594119847772844012145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187473729413231848562674763 281210594119847772844012145)
          ·
            refine ⟨210907945589885829633009109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281210594119847772844012145 210907945589885829633009109)
            ·
              refine ⟨4943154974762949132023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 210907945589885829633009109 4943154974762949132023651)
              ·
                refine ⟨7414732462144423698035477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943154974762949132023651 7414732462144423698035477)
                ·
                  refine ⟨347565584163019860845413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7414732462144423698035477 347565584163019860845413)
                  ·
                    rfl

theorem cell22_3045967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 6].length) (baseStart_3045967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3045967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3045967 prefixEnd_3045967 := by exact prefixLift 3045967
  have htrace : WordTrace (prefixWord ++ tailWord_3045967) baseStart_3045967 baseEnd_3045967 := by
    simpa [prefixWord, tailWord_3045967, baseEnd_3045967] using wordTrace_append hprefix tailTrace_3045967
  have hstable : (prefixWord ++ tailWord_3045967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3045967).length < 2 ^ (prefixWord ++ tailWord_3045967).sum := by decide
  have hdescent : baseEnd_3045967 < baseStart_3045967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3045967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046016 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_3046016 : Nat := 118140960795 + 3046016 * 2 ^ 59
def prefixEnd_3046016 : Nat := 4983230072969 + 3 ^ 40 * 3046016 * 2
def baseEnd_3046016 : Nat := 1042713526190439788061089

theorem tailTrace_3046016 : CollatzResearch.WordTrace tailWord_3046016 prefixEnd_3046016 1042713526190439788061089 := by
  unfold tailWord_3046016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55548665266405862480614951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74064887021874483307486601 55548665266405862480614951)
  ·
    refine ⟨83322997899608793720922427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55548665266405862480614951 83322997899608793720922427)
    ·
      refine ⟨124984496849413190581383641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83322997899608793720922427 124984496849413190581383641)
      ·
        refine ⟨93738372637059892936037731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124984496849413190581383641 93738372637059892936037731)
        ·
          refine ⟨140607558955589839404056597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93738372637059892936037731 140607558955589839404056597)
          ·
            refine ⟨6590979326043273722065153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140607558955589839404056597 6590979326043273722065153)
            ·
              refine ⟨4943234494532455291548865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6590979326043273722065153 4943234494532455291548865)
              ·
                refine ⟨3707425870899341468661649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4943234494532455291548865 3707425870899341468661649)
                ·
                  refine ⟨2780569403174506101496237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3707425870899341468661649 2780569403174506101496237)
                  ·
                    refine ⟨1042713526190439788061089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780569403174506101496237 1042713526190439788061089)
                    ·
                      rfl

theorem cell22_3046016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_3046016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046016 prefixEnd_3046016 := by exact prefixLift 3046016
  have htrace : WordTrace (prefixWord ++ tailWord_3046016) baseStart_3046016 baseEnd_3046016 := by
    simpa [prefixWord, tailWord_3046016, baseEnd_3046016] using wordTrace_append hprefix tailTrace_3046016
  have hstable : (prefixWord ++ tailWord_3046016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046016).length < 2 ^ (prefixWord ++ tailWord_3046016).sum := by decide
  have hdescent : baseEnd_3046016 < baseStart_3046016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046046 : List Nat := [4, 3, 1, 1, 1, 1, 5, 6]
def baseStart_3046046 : Nat := 118140960795 + 3046046 * 2 ^ 59
def prefixEnd_3046046 : Nat := 4983230072969 + 3 ^ 40 * 3046046 * 2
def baseEnd_3046046 : Nat := 115858199533725523312333

theorem tailTrace_3046046 : CollatzResearch.WordTrace tailWord_3046046 prefixEnd_3046046 115858199533725523312333 := by
  unfold tailWord_3046046
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887303090337880010602749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74065616481802026723214661 13887303090337880010602749)
  ·
    refine ⟨5207738658876705003976031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13887303090337880010602749 5207738658876705003976031)
    ·
      refine ⟨7811607988315057505964047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5207738658876705003976031 7811607988315057505964047)
      ·
        refine ⟨11717411982472586258946071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811607988315057505964047 11717411982472586258946071)
        ·
          refine ⟨17576117973708879388419107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11717411982472586258946071 17576117973708879388419107)
          ·
            refine ⟨26364176960563319082628661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17576117973708879388419107 26364176960563319082628661)
            ·
              refine ⟨2471641590052811163996437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26364176960563319082628661 2471641590052811163996437)
              ·
                refine ⟨115858199533725523312333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2471641590052811163996437 115858199533725523312333)
                ·
                  rfl

theorem cell22_3046046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_3046046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046046 prefixEnd_3046046 := by exact prefixLift 3046046
  have htrace : WordTrace (prefixWord ++ tailWord_3046046) baseStart_3046046 baseEnd_3046046 := by
    simpa [prefixWord, tailWord_3046046, baseEnd_3046046] using wordTrace_append hprefix tailTrace_3046046
  have hstable : (prefixWord ++ tailWord_3046046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046046).length < 2 ^ (prefixWord ++ tailWord_3046046).sum := by decide
  have hdescent : baseEnd_3046046 < baseStart_3046046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046048 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_3046048 : Nat := 118140960795 + 3046048 * 2 ^ 59
def prefixEnd_3046048 : Nat := 4983230072969 + 3 ^ 40 * 3046048 * 2
def baseEnd_3046048 : Nat := 1042724480444402371260991

theorem tailTrace_3046048 : CollatzResearch.WordTrace tailWord_3046048 prefixEnd_3046048 1042724480444402371260991 := by
  unfold tailWord_3046048
  simp only [CollatzResearch.WordTrace]
  refine ⟨55549248834347897213197399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74065665112463862950929865 55549248834347897213197399)
  ·
    refine ⟨83323873251521845819796099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55549248834347897213197399 83323873251521845819796099)
    ·
      refine ⟨124985809877282768729694149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83323873251521845819796099 124985809877282768729694149)
      ·
        refine ⟨23434839351990519136817653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124985809877282768729694149 23434839351990519136817653)
        ·
          refine ⟨2197016189249111169076655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23434839351990519136817653 2197016189249111169076655)
          ·
            refine ⟨3295524283873666753614983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2197016189249111169076655 3295524283873666753614983)
            ·
              refine ⟨4943286425810500130422475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295524283873666753614983 4943286425810500130422475)
              ·
                refine ⟨7414929638715750195633713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4943286425810500130422475 7414929638715750195633713)
                ·
                  refine ⟨5561197229036812646725285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7414929638715750195633713 5561197229036812646725285)
                  ·
                    refine ⟨1042724480444402371260991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5561197229036812646725285 1042724480444402371260991)
                    ·
                      rfl

theorem cell22_3046048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_3046048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046048 prefixEnd_3046048 := by exact prefixLift 3046048
  have htrace : WordTrace (prefixWord ++ tailWord_3046048) baseStart_3046048 baseEnd_3046048 := by
    simpa [prefixWord, tailWord_3046048, baseEnd_3046048] using wordTrace_append hprefix tailTrace_3046048
  have hstable : (prefixWord ++ tailWord_3046048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046048).length < 2 ^ (prefixWord ++ tailWord_3046048).sum := by decide
  have hdescent : baseEnd_3046048 < baseStart_3046048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046078 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3046078 : Nat := 118140960795 + 3046078 * 2 ^ 59
def prefixEnd_3046078 : Nat := 4983230072969 + 3 ^ 40 * 3046078 * 2
def baseEnd_3046078 : Nat := 1042734750057492293010899

theorem tailTrace_3046078 : CollatzResearch.WordTrace tailWord_3046078 prefixEnd_3046078 1042734750057492293010899 := by
  unfold tailWord_3046078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887448982323388693748361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74066394572391406366657925 13887448982323388693748361)
  ·
    refine ⟨10415586736742541520311271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13887448982323388693748361 10415586736742541520311271)
    ·
      refine ⟨15623380105113812280466907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10415586736742541520311271 15623380105113812280466907)
      ·
        refine ⟨23435070157670718420700361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15623380105113812280466907 23435070157670718420700361)
        ·
          refine ⟨17576302618253038815525271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23435070157670718420700361 17576302618253038815525271)
          ·
            refine ⟨26364453927379558223287907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17576302618253038815525271 26364453927379558223287907)
            ·
              refine ⟨39546680891069337334931861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26364453927379558223287907 39546680891069337334931861)
              ·
                refine ⟨1853750666768875187574931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39546680891069337334931861 1853750666768875187574931)
                ·
                  refine ⟨2780626000153312781362397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1853750666768875187574931 2780626000153312781362397)
                  ·
                    refine ⟨1042734750057492293010899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780626000153312781362397 1042734750057492293010899)
                    ·
                      rfl

theorem cell22_3046078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3046078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046078 prefixEnd_3046078 := by exact prefixLift 3046078
  have htrace : WordTrace (prefixWord ++ tailWord_3046078) baseStart_3046078 baseEnd_3046078 := by
    simpa [prefixWord, tailWord_3046078, baseEnd_3046078] using wordTrace_append hprefix tailTrace_3046078
  have hstable : (prefixWord ++ tailWord_3046078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046078).length < 2 ^ (prefixWord ++ tailWord_3046078).sum := by decide
  have hdescent : baseEnd_3046078 < baseStart_3046078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046087 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3046087 : Nat := 118140960795 + 3046087 * 2 ^ 59
def prefixEnd_3046087 : Nat := 4983230072969 + 3 ^ 40 * 3046087 * 2
def baseEnd_3046087 : Nat := 1042737830941419269535871

theorem tailTrace_3046087 : CollatzResearch.WordTrace tailWord_3046087 prefixEnd_3046087 1042737830941419269535871 := by
  unfold tailWord_3046087
  simp only [CollatzResearch.WordTrace]
  refine ⟨111099920115554504087064515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74066613410369669391376343 111099920115554504087064515)
  ·
    refine ⟨166649880173331756130596773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111099920115554504087064515 166649880173331756130596773)
    ·
      refine ⟨31246852532499704274486895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166649880173331756130596773 31246852532499704274486895)
      ·
        refine ⟨46870278798749556411730343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31246852532499704274486895 46870278798749556411730343)
        ·
          refine ⟨70305418198124334617595515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46870278798749556411730343 70305418198124334617595515)
          ·
            refine ⟨105458127297186501926393273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70305418198124334617595515 105458127297186501926393273)
            ·
              refine ⟨79093595472889876444794955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105458127297186501926393273 79093595472889876444794955)
              ·
                refine ⟨118640393209334814667192433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79093595472889876444794955 118640393209334814667192433)
                ·
                  refine ⟨88980294907001111000394325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118640393209334814667192433 88980294907001111000394325)
                  ·
                    refine ⟨1042737830941419269535871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88980294907001111000394325 1042737830941419269535871)
                    ·
                      rfl

theorem cell22_3046087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3046087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046087 prefixEnd_3046087 := by exact prefixLift 3046087
  have htrace : WordTrace (prefixWord ++ tailWord_3046087) baseStart_3046087 baseEnd_3046087 := by
    simpa [prefixWord, tailWord_3046087, baseEnd_3046087] using wordTrace_append hprefix tailTrace_3046087
  have hstable : (prefixWord ++ tailWord_3046087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046087).length < 2 ^ (prefixWord ++ tailWord_3046087).sum := by decide
  have hdescent : baseEnd_3046087 < baseStart_3046087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046194 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_3046194 : Nat := 118140960795 + 3046194 * 2 ^ 59
def prefixEnd_3046194 : Nat := 4983230072969 + 3 ^ 40 * 3046194 * 2
def baseEnd_3046194 : Nat := 1042774459228106657110543

theorem tailTrace_3046194 : CollatzResearch.WordTrace tailWord_3046194 prefixEnd_3046194 1042774459228106657110543 := by
  unfold tailWord_3046194
  simp only [CollatzResearch.WordTrace]
  refine ⟨27775955681541715340302409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74069215150777907574139757 27775955681541715340302409)
  ·
    refine ⟨20831966761156286505226807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27775955681541715340302409 20831966761156286505226807)
    ·
      refine ⟨31247950141734429757840211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20831966761156286505226807 31247950141734429757840211)
      ·
        refine ⟨46871925212601644636760317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31247950141734429757840211 46871925212601644636760317)
        ·
          refine ⟨17576971954725616738785119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46871925212601644636760317 17576971954725616738785119)
          ·
            refine ⟨26365457932088425108177679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17576971954725616738785119 26365457932088425108177679)
            ·
              refine ⟨39548186898132637662266519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26365457932088425108177679 39548186898132637662266519)
              ·
                refine ⟨59322280347198956493399779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39548186898132637662266519 59322280347198956493399779)
                ·
                  refine ⟨88983420520798434740099669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59322280347198956493399779 88983420520798434740099669)
                  ·
                    refine ⟨1042774459228106657110543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88983420520798434740099669 1042774459228106657110543)
                    ·
                      rfl

theorem cell22_3046194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_3046194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046194 prefixEnd_3046194 := by exact prefixLift 3046194
  have htrace : WordTrace (prefixWord ++ tailWord_3046194) baseStart_3046194 baseEnd_3046194 := by
    simpa [prefixWord, tailWord_3046194, baseEnd_3046194] using wordTrace_append hprefix tailTrace_3046194
  have hstable : (prefixWord ++ tailWord_3046194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046194).length < 2 ^ (prefixWord ++ tailWord_3046194).sum := by decide
  have hdescent : baseEnd_3046194 < baseStart_3046194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046243 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 5]
def baseStart_3046243 : Nat := 118140960795 + 3046243 * 2 ^ 59
def prefixEnd_3046243 : Nat := 4983230072969 + 3 ^ 40 * 3046243 * 2
def baseEnd_3046243 : Nat := 347597077643162287545131

theorem tailTrace_3046243 : CollatzResearch.WordTrace tailWord_3046243 prefixEnd_3046243 347597077643162287545131 := by
  unfold tailWord_3046243
  simp only [CollatzResearch.WordTrace]
  refine ⟨111105609902989342729743383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74070406601992895153162255 111105609902989342729743383)
  ·
    refine ⟨166658414854484014094615075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111105609902989342729743383 166658414854484014094615075)
    ·
      refine ⟨249987622281726021141922613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166658414854484014094615075 249987622281726021141922613)
      ·
        refine ⟨23436339588911814482055245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249987622281726021141922613 23436339588911814482055245)
        ·
          refine ⟨8788627345841930430770717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23436339588911814482055245 8788627345841930430770717)
          ·
            refine ⟨3295735254690723911539019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8788627345841930430770717 3295735254690723911539019)
            ·
              refine ⟨4943602882036085867308529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295735254690723911539019 4943602882036085867308529)
              ·
                refine ⟨3707702161527064400481397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4943602882036085867308529 3707702161527064400481397)
                ·
                  refine ⟨347597077643162287545131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3707702161527064400481397 347597077643162287545131)
                  ·
                    rfl

theorem cell22_3046243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 5].length) (baseStart_3046243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046243 prefixEnd_3046243 := by exact prefixLift 3046243
  have htrace : WordTrace (prefixWord ++ tailWord_3046243) baseStart_3046243 baseEnd_3046243 := by
    simpa [prefixWord, tailWord_3046243, baseEnd_3046243] using wordTrace_append hprefix tailTrace_3046243
  have hstable : (prefixWord ++ tailWord_3046243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046243).length < 2 ^ (prefixWord ++ tailWord_3046243).sum := by decide
  have hdescent : baseEnd_3046243 < baseStart_3046243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046303 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 4, 3]
def baseStart_3046303 : Nat := 118140960795 + 3046303 * 2 ^ 59
def prefixEnd_3046303 : Nat := 4983230072969 + 3 ^ 40 * 3046303 * 2
def baseEnd_3046303 : Nat := 1042811772155666706135209

theorem tailTrace_3046303 : CollatzResearch.WordTrace tailWord_3046303 prefixEnd_3046303 1042811772155666706135209 := by
  unfold tailWord_3046303
  simp only [CollatzResearch.WordTrace]
  refine ⟨111107798282771972976927563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74071865521847981984618375 111107798282771972976927563)
  ·
    refine ⟨166661697424157959465391345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111107798282771972976927563 166661697424157959465391345)
    ·
      refine ⟨124996273068118469599043509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166661697424157959465391345 124996273068118469599043509)
      ·
        refine ⟨11718400600136106524910329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124996273068118469599043509 11718400600136106524910329)
        ·
          refine ⟨8788800450102079893682747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11718400600136106524910329 8788800450102079893682747)
          ·
            refine ⟨13183200675153119840524121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8788800450102079893682747 13183200675153119840524121)
            ·
              refine ⟨9887400506364839880393091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13183200675153119840524121 9887400506364839880393091)
              ·
                refine ⟨14831100759547259820589637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887400506364839880393091 14831100759547259820589637)
                ·
                  refine ⟨2780831392415111216360557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14831100759547259820589637 2780831392415111216360557)
                  ·
                    refine ⟨1042811772155666706135209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2780831392415111216360557 1042811772155666706135209)
                    ·
                      rfl

theorem cell22_3046303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_3046303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046303 prefixEnd_3046303 := by exact prefixLift 3046303
  have htrace : WordTrace (prefixWord ++ tailWord_3046303) baseStart_3046303 baseEnd_3046303 := by
    simpa [prefixWord, tailWord_3046303, baseEnd_3046303] using wordTrace_append hprefix tailTrace_3046303
  have hstable : (prefixWord ++ tailWord_3046303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046303).length < 2 ^ (prefixWord ++ tailWord_3046303).sum := by decide
  have hdescent : baseEnd_3046303 < baseStart_3046303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046376 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3046376 : Nat := 118140960795 + 3046376 * 2 ^ 59
def prefixEnd_3046376 : Nat := 4983230072969 + 3 ^ 40 * 3046376 * 2
def baseEnd_3046376 : Nat := 1042836761547518849059985

theorem tailTrace_3046376 : CollatzResearch.WordTrace tailWord_3046376 prefixEnd_3046376 1042836761547518849059985 := by
  unfold tailWord_3046376
  simp only [CollatzResearch.WordTrace]
  refine ⟨55555230405753753222167491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74073640541005004296223321 55555230405753753222167491)
  ·
    refine ⟨83332845608630629833251237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55555230405753753222167491 83332845608630629833251237)
    ·
      refine ⟨15624908551618243093734607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83332845608630629833251237 15624908551618243093734607)
      ·
        refine ⟨23437362827427364640601911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15624908551618243093734607 23437362827427364640601911)
        ·
          refine ⟨35156044241141046960902867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23437362827427364640601911 35156044241141046960902867)
          ·
            refine ⟨52734066361711570441354301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35156044241141046960902867 52734066361711570441354301)
            ·
              refine ⟨19775274885641838915507863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52734066361711570441354301 19775274885641838915507863)
              ·
                refine ⟨29662912328462758373261795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19775274885641838915507863 29662912328462758373261795)
                ·
                  refine ⟨44494368492694137559892693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29662912328462758373261795 44494368492694137559892693)
                  ·
                    refine ⟨1042836761547518849059985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44494368492694137559892693 1042836761547518849059985)
                    ·
                      rfl

theorem cell22_3046376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3046376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046376 prefixEnd_3046376 := by exact prefixLift 3046376
  have htrace : WordTrace (prefixWord ++ tailWord_3046376) baseStart_3046376 baseEnd_3046376 := by
    simpa [prefixWord, tailWord_3046376, baseEnd_3046376] using wordTrace_append hprefix tailTrace_3046376
  have hstable : (prefixWord ++ tailWord_3046376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046376).length < 2 ^ (prefixWord ++ tailWord_3046376).sum := by decide
  have hdescent : baseEnd_3046376 < baseStart_3046376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046378 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_3046378 : Nat := 118140960795 + 3046378 * 2 ^ 59
def prefixEnd_3046378 : Nat := 4983230072969 + 3 ^ 40 * 3046378 * 2
def baseEnd_3046378 : Nat := 347612482062797170169993

theorem tailTrace_3046378 : CollatzResearch.WordTrace tailWord_3046378 prefixEnd_3046378 347612482062797170169993 := by
  unfold tailWord_3046378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27777633439375065196476947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74073689171666840523938525 27777633439375065196476947)
  ·
    refine ⟨41666450159062597794715421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27777633439375065196476947 41666450159062597794715421)
    ·
      refine ⟨15624918809648474173018283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41666450159062597794715421 15624918809648474173018283)
      ·
        refine ⟨23437378214472711259527425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15624918809648474173018283 23437378214472711259527425)
        ·
          refine ⟨17578033660854533444645569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23437378214472711259527425 17578033660854533444645569)
          ·
            refine ⟨13183525245640900083484177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17578033660854533444645569 13183525245640900083484177)
            ·
              refine ⟨9887643934230675062613133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13183525245640900083484177 9887643934230675062613133)
              ·
                refine ⟨3707866475336503148479925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9887643934230675062613133 3707866475336503148479925)
                ·
                  refine ⟨347612482062797170169993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3707866475336503148479925 347612482062797170169993)
                  ·
                    rfl

theorem cell22_3046378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_3046378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046378 prefixEnd_3046378 := by exact prefixLift 3046378
  have htrace : WordTrace (prefixWord ++ tailWord_3046378) baseStart_3046378 baseEnd_3046378 := by
    simpa [prefixWord, tailWord_3046378, baseEnd_3046378] using wordTrace_append hprefix tailTrace_3046378
  have hstable : (prefixWord ++ tailWord_3046378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046378).length < 2 ^ (prefixWord ++ tailWord_3046378).sum := by decide
  have hdescent : baseEnd_3046378 < baseStart_3046378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046423 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 6]
def baseStart_3046423 : Nat := 118140960795 + 3046423 * 2 ^ 59
def prefixEnd_3046423 : Nat := 4983230072969 + 3 ^ 40 * 3046423 * 2
def baseEnd_3046423 : Nat := 347617616869342131044947

theorem tailTrace_3046423 : CollatzResearch.WordTrace tailWord_3046423 prefixEnd_3046423 347617616869342131044947 := by
  unfold tailWord_3046423
  simp only [CollatzResearch.WordTrace]
  refine ⟨111112175042337233471295923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74074783361558155647530615 111112175042337233471295923)
  ·
    refine ⟨166668262563505850206943885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111112175042337233471295923 166668262563505850206943885)
    ·
      refine ⟨62500598461314693827603957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166668262563505850206943885 62500598461314693827603957)
      ·
        refine ⟨5859431105748252546337871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62500598461314693827603957 5859431105748252546337871)
        ·
          refine ⟨8789146658622378819506807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859431105748252546337871 8789146658622378819506807)
          ·
            refine ⟨13183719987933568229260211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789146658622378819506807 13183719987933568229260211)
            ·
              refine ⟨19775579981900352343890317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13183719987933568229260211 19775579981900352343890317)
              ·
                refine ⟨7415842493212632128958869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19775579981900352343890317 7415842493212632128958869)
                ·
                  refine ⟨347617616869342131044947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7415842493212632128958869 347617616869342131044947)
                  ·
                    rfl

theorem cell22_3046423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_3046423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046423 prefixEnd_3046423 := by exact prefixLift 3046423
  have htrace : WordTrace (prefixWord ++ tailWord_3046423) baseStart_3046423 baseEnd_3046423 := by
    simpa [prefixWord, tailWord_3046423, baseEnd_3046423] using wordTrace_append hprefix tailTrace_3046423
  have hstable : (prefixWord ++ tailWord_3046423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046423).length < 2 ^ (prefixWord ++ tailWord_3046423).sum := by decide
  have hdescent : baseEnd_3046423 < baseStart_3046423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046442 : List Nat := [3, 1, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3046442 : Nat := 118140960795 + 3046442 * 2 ^ 59
def prefixEnd_3046442 : Nat := 4983230072969 + 3 ^ 40 * 3046442 * 2
def baseEnd_3046442 : Nat := 1042859354696316676909783

theorem tailTrace_3046442 : CollatzResearch.WordTrace tailWord_3046442 prefixEnd_3046442 1042859354696316676909783 := by
  unfold tailWord_3046442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27778217007317099929059395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74075245352845599810825053 27778217007317099929059395)
  ·
    refine ⟨41667325510975649893589093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27778217007317099929059395 41667325510975649893589093)
    ·
      refine ⟨7812623533307934355047955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41667325510975649893589093 7812623533307934355047955)
      ·
        refine ⟨11718935299961901532571933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7812623533307934355047955 11718935299961901532571933)
        ·
          refine ⟨4394600737485713074714475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11718935299961901532571933 4394600737485713074714475)
          ·
            refine ⟨6591901106228569612071713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394600737485713074714475 6591901106228569612071713)
            ·
              refine ⟨4943925829671427209053785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6591901106228569612071713 4943925829671427209053785)
              ·
                refine ⟨3707944372253570406790339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4943925829671427209053785 3707944372253570406790339)
                ·
                  refine ⟨5561916558380355610185509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707944372253570406790339 5561916558380355610185509)
                  ·
                    refine ⟨1042859354696316676909783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5561916558380355610185509 1042859354696316676909783)
                    ·
                      rfl

theorem cell22_3046442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3046442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046442 prefixEnd_3046442 := by exact prefixLift 3046442
  have htrace : WordTrace (prefixWord ++ tailWord_3046442) baseStart_3046442 baseEnd_3046442 := by
    simpa [prefixWord, tailWord_3046442, baseEnd_3046442] using wordTrace_append hprefix tailTrace_3046442
  have hstable : (prefixWord ++ tailWord_3046442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046442).length < 2 ^ (prefixWord ++ tailWord_3046442).sum := by decide
  have hdescent : baseEnd_3046442 < baseStart_3046442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046453 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3046453 : Nat := 118140960795 + 3046453 * 2 ^ 59
def prefixEnd_3046453 : Nat := 4983230072969 + 3 ^ 40 * 3046453 * 2
def baseEnd_3046453 : Nat := 1042863120221116314884749

theorem tailTrace_3046453 : CollatzResearch.WordTrace tailWord_3046453 prefixEnd_3046453 1042863120221116314884749 := by
  unfold tailWord_3046453
  simp only [CollatzResearch.WordTrace]
  refine ⟨111113269232228548594888013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74075512821485699063258675 111113269232228548594888013)
  ·
    refine ⟨41667475962085705723083005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111113269232228548594888013 41667475962085705723083005)
    ·
      refine ⟨15625303485782139646156127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41667475962085705723083005 15625303485782139646156127)
      ·
        refine ⟨23437955228673209469234191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15625303485782139646156127 23437955228673209469234191)
        ·
          refine ⟨35156932843009814203851287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23437955228673209469234191 35156932843009814203851287)
          ·
            refine ⟨52735399264514721305776931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35156932843009814203851287 52735399264514721305776931)
            ·
              refine ⟨79103098896772081958665397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52735399264514721305776931 79103098896772081958665397)
              ·
                refine ⟨7415915521572382683624881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79103098896772081958665397 7415915521572382683624881)
                ·
                  refine ⟨5561936641179287012718661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7415915521572382683624881 5561936641179287012718661)
                  ·
                    refine ⟨1042863120221116314884749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5561936641179287012718661 1042863120221116314884749)
                    ·
                      rfl

theorem cell22_3046453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3046453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046453 prefixEnd_3046453 := by exact prefixLift 3046453
  have htrace : WordTrace (prefixWord ++ tailWord_3046453) baseStart_3046453 baseEnd_3046453 := by
    simpa [prefixWord, tailWord_3046453, baseEnd_3046453] using wordTrace_append hprefix tailTrace_3046453
  have hstable : (prefixWord ++ tailWord_3046453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046453).length < 2 ^ (prefixWord ++ tailWord_3046453).sum := by decide
  have hdescent : baseEnd_3046453 < baseStart_3046453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046457 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 4]
def baseStart_3046457 : Nat := 118140960795 + 3046457 * 2 ^ 59
def prefixEnd_3046457 : Nat := 4983230072969 + 3 ^ 40 * 3046457 * 2
def baseEnd_3046457 : Nat := 347621496500953879261579

theorem tailTrace_3046457 : CollatzResearch.WordTrace tailWord_3046457 prefixEnd_3046457 347621496500953879261579 := by
  unfold tailWord_3046457
  simp only [CollatzResearch.WordTrace]
  refine ⟨111113415124214057278033625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74075610082809371518689083 111113415124214057278033625)
  ·
    refine ⟨83335061343160542958525219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111113415124214057278033625 83335061343160542958525219)
    ·
      refine ⟨125002592014740814437787829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83335061343160542958525219 125002592014740814437787829)
      ·
        refine ⟨11718993001381951353542609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125002592014740814437787829 11718993001381951353542609)
        ·
          refine ⟨8789244751036463515156957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11718993001381951353542609 8789244751036463515156957)
          ·
            refine ⟨3295966781638673818183859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8789244751036463515156957 3295966781638673818183859)
            ·
              refine ⟨4943950172458010727275789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3295966781638673818183859 4943950172458010727275789)
              ·
                refine ⟨1853981314671754022728421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4943950172458010727275789 1853981314671754022728421)
                ·
                  refine ⟨347621496500953879261579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853981314671754022728421 347621496500953879261579)
                  ·
                    rfl

theorem cell22_3046457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_3046457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046457 prefixEnd_3046457 := by exact prefixLift 3046457
  have htrace : WordTrace (prefixWord ++ tailWord_3046457) baseStart_3046457 baseEnd_3046457 := by
    simpa [prefixWord, tailWord_3046457, baseEnd_3046457] using wordTrace_append hprefix tailTrace_3046457
  have hstable : (prefixWord ++ tailWord_3046457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046457).length < 2 ^ (prefixWord ++ tailWord_3046457).sum := by decide
  have hdescent : baseEnd_3046457 < baseStart_3046457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046560 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_3046560 : Nat := 118140960795 + 3046560 * 2 ^ 59
def prefixEnd_3046560 : Nat := 4983230072969 + 3 ^ 40 * 3046560 * 2
def baseEnd_3046560 : Nat := 1042899748507803702459421

theorem tailTrace_3046560 : CollatzResearch.WordTrace tailWord_3046560 prefixEnd_3046560 1042899748507803702459421 := by
  unfold tailWord_3046560
  simp only [CollatzResearch.WordTrace]
  refine ⟨55558585921420452934516567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74078114561893937246022089 55558585921420452934516567)
  ·
    refine ⟨83337878882130679401774851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55558585921420452934516567 83337878882130679401774851)
    ·
      refine ⟨125006818323196019102662277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83337878882130679401774851 125006818323196019102662277)
      ·
        refine ⟨23438778435599253581749177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125006818323196019102662277 23438778435599253581749177)
        ·
          refine ⟨17579083826699440186311883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23438778435599253581749177 17579083826699440186311883)
          ·
            refine ⟨26368625740049160279467825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17579083826699440186311883 26368625740049160279467825)
            ·
              refine ⟨19776469305036870209600869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26368625740049160279467825 19776469305036870209600869)
              ·
                refine ⟨3708087994694413164300163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19776469305036870209600869 3708087994694413164300163)
                ·
                  refine ⟨5562131992041619746450245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708087994694413164300163 5562131992041619746450245)
                  ·
                    refine ⟨1042899748507803702459421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562131992041619746450245 1042899748507803702459421)
                    ·
                      rfl

theorem cell22_3046560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_3046560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046560 prefixEnd_3046560 := by exact prefixLift 3046560
  have htrace : WordTrace (prefixWord ++ tailWord_3046560) baseStart_3046560 baseEnd_3046560 := by
    simpa [prefixWord, tailWord_3046560, baseEnd_3046560] using wordTrace_append hprefix tailTrace_3046560
  have hstable : (prefixWord ++ tailWord_3046560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046560).length < 2 ^ (prefixWord ++ tailWord_3046560).sum := by decide
  have hdescent : baseEnd_3046560 < baseStart_3046560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046575 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 4]
def baseStart_3046575 : Nat := 118140960795 + 3046575 * 2 ^ 59
def prefixEnd_3046575 : Nat := 4983230072969 + 3 ^ 40 * 3046575 * 2
def baseEnd_3046575 : Nat := 347634961104782887778125

theorem tailTrace_3046575 : CollatzResearch.WordTrace tailWord_3046575 prefixEnd_3046575 347634961104782887778125 := by
  unfold tailWord_3046575
  simp only [CollatzResearch.WordTrace]
  refine ⟨111117718937786563430829179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74078479291857708953886119 111117718937786563430829179)
  ·
    refine ⟨166676578406679845146243769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111117718937786563430829179 166676578406679845146243769)
    ·
      refine ⟨125007433805009883859682827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166676578406679845146243769 125007433805009883859682827)
      ·
        refine ⟨187511150707514825789524241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125007433805009883859682827 187511150707514825789524241)
        ·
          refine ⟨140633363030636119342143181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187511150707514825789524241 140633363030636119342143181)
          ·
            refine ⟨52737511136488544753303693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140633363030636119342143181 52737511136488544753303693)
            ·
              refine ⟨19776566676183204282488885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52737511136488544753303693 19776566676183204282488885)
              ·
                refine ⟨1854053125892175401483333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19776566676183204282488885 1854053125892175401483333)
                ·
                  refine ⟨347634961104782887778125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854053125892175401483333 347634961104782887778125)
                  ·
                    rfl

theorem cell22_3046575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 4].length) (baseStart_3046575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046575 prefixEnd_3046575 := by exact prefixLift 3046575
  have htrace : WordTrace (prefixWord ++ tailWord_3046575) baseStart_3046575 baseEnd_3046575 := by
    simpa [prefixWord, tailWord_3046575, baseEnd_3046575] using wordTrace_append hprefix tailTrace_3046575
  have hstable : (prefixWord ++ tailWord_3046575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046575).length < 2 ^ (prefixWord ++ tailWord_3046575).sum := by decide
  have hdescent : baseEnd_3046575 < baseStart_3046575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046577 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3046577 : Nat := 118140960795 + 3046577 * 2 ^ 59
def prefixEnd_3046577 : Nat := 4983230072969 + 3 ^ 40 * 3046577 * 2
def baseEnd_3046577 : Nat := 1042905567955221324784369

theorem tailTrace_3046577 : CollatzResearch.WordTrace tailWord_3046577 prefixEnd_3046577 1042905567955221324784369 := by
  unfold tailWord_3046577
  simp only [CollatzResearch.WordTrace]
  refine ⟨111117791883779317772401985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74078527922519545181601323 111117791883779317772401985)
  ·
    refine ⟨83338343912834488329301489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111117791883779317772401985 83338343912834488329301489)
    ·
      refine ⟨62503757934625866246976117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83338343912834488329301489 62503757934625866246976117)
      ·
        refine ⟨5859727306371174960654011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62503757934625866246976117 5859727306371174960654011)
        ·
          refine ⟨8789590959556762440981017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5859727306371174960654011 8789590959556762440981017)
          ·
            refine ⟨6592193219667571830735763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8789590959556762440981017 6592193219667571830735763)
            ·
              refine ⟨9888289829501357746103645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6592193219667571830735763 9888289829501357746103645)
              ·
                refine ⟨3708108686063009154788867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9888289829501357746103645 3708108686063009154788867)
                ·
                  refine ⟨5562163029094513732183301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708108686063009154788867 5562163029094513732183301)
                  ·
                    refine ⟨1042905567955221324784369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562163029094513732183301 1042905567955221324784369)
                    ·
                      rfl

theorem cell22_3046577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3046577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046577 prefixEnd_3046577 := by exact prefixLift 3046577
  have htrace : WordTrace (prefixWord ++ tailWord_3046577) baseStart_3046577 baseEnd_3046577 := by
    simpa [prefixWord, tailWord_3046577, baseEnd_3046577] using wordTrace_append hprefix tailTrace_3046577
  have hstable : (prefixWord ++ tailWord_3046577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046577).length < 2 ^ (prefixWord ++ tailWord_3046577).sum := by decide
  have hdescent : baseEnd_3046577 < baseStart_3046577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046598 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3046598 : Nat := 118140960795 + 3046598 * 2 ^ 59
def prefixEnd_3046598 : Nat := 4983230072969 + 3 ^ 40 * 3046598 * 2
def baseEnd_3046598 : Nat := 347637585561461423336435

theorem tailTrace_3046598 : CollatzResearch.WordTrace tailWord_3046598 prefixEnd_3046598 347637585561461423336435 := by
  unfold tailWord_3046598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472454931771976198716139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74079038544468825572610965 3472454931771976198716139)
  ·
    refine ⟨5208682397657964298074209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3472454931771976198716139 5208682397657964298074209)
    ·
      refine ⟨3906511798243473223555657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5208682397657964298074209 3906511798243473223555657)
      ·
        refine ⟨2929883848682604917666743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3906511798243473223555657 2929883848682604917666743)
        ·
          refine ⟨4394825773023907376500115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929883848682604917666743 4394825773023907376500115)
          ·
            refine ⟨6592238659535861064750173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394825773023907376500115 6592238659535861064750173)
            ·
              refine ⟨2472089497325947899281315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6592238659535861064750173 2472089497325947899281315)
              ·
                refine ⟨3708134245988921848921973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472089497325947899281315 3708134245988921848921973)
                ·
                  refine ⟨347637585561461423336435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3708134245988921848921973 347637585561461423336435)
                  ·
                    rfl

theorem cell22_3046598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3046598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046598 prefixEnd_3046598 := by exact prefixLift 3046598
  have htrace : WordTrace (prefixWord ++ tailWord_3046598) baseStart_3046598 baseEnd_3046598 := by
    simpa [prefixWord, tailWord_3046598, baseEnd_3046598] using wordTrace_append hprefix tailTrace_3046598
  have hstable : (prefixWord ++ tailWord_3046598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046598).length < 2 ^ (prefixWord ++ tailWord_3046598).sum := by decide
  have hdescent : baseEnd_3046598 < baseStart_3046598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046618 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_3046618 : Nat := 118140960795 + 3046618 * 2 ^ 59
def prefixEnd_3046618 : Nat := 4983230072969 + 3 ^ 40 * 3046618 * 2
def baseEnd_3046618 : Nat := 1042919603093110884509243

theorem tailTrace_3046618 : CollatzResearch.WordTrace tailWord_3046618 prefixEnd_3046618 1042919603093110884509243 := by
  unfold tailWord_3046618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27779821819157695443661127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74079524851087187849763005 27779821819157695443661127)
  ·
    refine ⟨41669732728736543165491691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27779821819157695443661127 41669732728736543165491691)
    ·
      refine ⟨62504599093104814748237537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41669732728736543165491691 62504599093104814748237537)
      ·
        refine ⟨46878449319828611061178153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62504599093104814748237537 46878449319828611061178153)
        ·
          refine ⟨35158836989871458295883615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46878449319828611061178153 35158836989871458295883615)
          ·
            refine ⟨52738255484807187443825423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35158836989871458295883615 52738255484807187443825423)
            ·
              refine ⟨79107383227210781165738135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52738255484807187443825423 79107383227210781165738135)
              ·
                refine ⟨118661074840816171748607203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79107383227210781165738135 118661074840816171748607203)
                ·
                  refine ⟨177991612261224257622910805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118661074840816171748607203 177991612261224257622910805)
                  ·
                    refine ⟨1042919603093110884509243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177991612261224257622910805 1042919603093110884509243)
                    ·
                      rfl

theorem cell22_3046618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_3046618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046618 prefixEnd_3046618 := by exact prefixLift 3046618
  have htrace : WordTrace (prefixWord ++ tailWord_3046618) baseStart_3046618 baseEnd_3046618 := by
    simpa [prefixWord, tailWord_3046618, baseEnd_3046618] using wordTrace_append hprefix tailTrace_3046618
  have hstable : (prefixWord ++ tailWord_3046618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046618).length < 2 ^ (prefixWord ++ tailWord_3046618).sum := by decide
  have hdescent : baseEnd_3046618 < baseStart_3046618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046658 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3046658 : Nat := 118140960795 + 3046658 * 2 ^ 59
def prefixEnd_3046658 : Nat := 4983230072969 + 3 ^ 40 * 3046658 * 2
def baseEnd_3046658 : Nat := 1042933295910564113509121

theorem tailTrace_3046658 : CollatzResearch.WordTrace tailWord_3046658 prefixEnd_3046658 1042933295910564113509121 := by
  unfold tailWord_3046658
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780186549121467151525157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74080497464323912404067085 27780186549121467151525157)
  ·
    refine ⟨5208784977960275090910967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27780186549121467151525157 5208784977960275090910967)
    ·
      refine ⟨7813177466940412636366451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5208784977960275090910967 7813177466940412636366451)
      ·
        refine ⟨11719766200410618954549677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813177466940412636366451 11719766200410618954549677)
        ·
          refine ⟨4394912325153982107956129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11719766200410618954549677 4394912325153982107956129)
          ·
            refine ⟨3296184243865486580967097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4394912325153982107956129 3296184243865486580967097)
            ·
              refine ⟨2472138182899114935725323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296184243865486580967097 2472138182899114935725323)
              ·
                refine ⟨3708207274348672403587985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472138182899114935725323 3708207274348672403587985)
                ·
                  refine ⟨2781155455761504302690989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708207274348672403587985 2781155455761504302690989)
                  ·
                    refine ⟨1042933295910564113509121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2781155455761504302690989 1042933295910564113509121)
                    ·
                      rfl

theorem cell22_3046658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3046658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046658 prefixEnd_3046658 := by exact prefixLift 3046658
  have htrace : WordTrace (prefixWord ++ tailWord_3046658) baseStart_3046658 baseEnd_3046658 := by
    simpa [prefixWord, tailWord_3046658, baseEnd_3046658] using wordTrace_append hprefix tailTrace_3046658
  have hstable : (prefixWord ++ tailWord_3046658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046658).length < 2 ^ (prefixWord ++ tailWord_3046658).sum := by decide
  have hdescent : baseEnd_3046658 < baseStart_3046658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046665 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 5]
def baseStart_3046665 : Nat := 118140960795 + 3046665 * 2 ^ 59
def prefixEnd_3046665 : Nat := 4983230072969 + 3 ^ 40 * 3046665 * 2
def baseEnd_3046665 : Nat := 347645230717872809528033

theorem tailTrace_3046665 : CollatzResearch.WordTrace tailWord_3046665 prefixEnd_3046665 347645230717872809528033 := by
  unfold tailWord_3046665
  simp only [CollatzResearch.WordTrace]
  refine ⟨111121001507460508801605449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74080667671640339201070299 111121001507460508801605449)
  ·
    refine ⟨83340751130595381601204087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111121001507460508801605449 83340751130595381601204087)
    ·
      refine ⟨125011126695893072401806131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83340751130595381601204087 125011126695893072401806131)
      ·
        refine ⟨187516690043839608602709197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125011126695893072401806131 187516690043839608602709197)
        ·
          refine ⟨70318758766439853226015949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187516690043839608602709197 70318758766439853226015949)
          ·
            refine ⟨26369534537414944959755981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70318758766439853226015949 26369534537414944959755981)
            ·
              refine ⟨9888575451530604359908493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26369534537414944959755981 9888575451530604359908493)
              ·
                refine ⟨3708215794323976634965685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9888575451530604359908493 3708215794323976634965685)
                ·
                  refine ⟨347645230717872809528033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3708215794323976634965685 347645230717872809528033)
                  ·
                    rfl

theorem cell22_3046665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_3046665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046665 prefixEnd_3046665 := by exact prefixLift 3046665
  have htrace : WordTrace (prefixWord ++ tailWord_3046665) baseStart_3046665 baseEnd_3046665 := by
    simpa [prefixWord, tailWord_3046665, baseEnd_3046665] using wordTrace_append hprefix tailTrace_3046665
  have hstable : (prefixWord ++ tailWord_3046665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046665).length < 2 ^ (prefixWord ++ tailWord_3046665).sum := by decide
  have hdescent : baseEnd_3046665 < baseStart_3046665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046755 : List Nat := [1, 1, 1, 5, 2, 3, 9]
def baseStart_3046755 : Nat := 118140960795 + 3046755 * 2 ^ 59
def prefixEnd_3046755 : Nat := 4983230072969 + 3 ^ 40 * 3046755 * 2
def baseEnd_3046755 : Nat := 38628388925662525697549

theorem tailTrace_3046755 : CollatzResearch.WordTrace tailWord_3046755 prefixEnd_3046755 38628388925662525697549 := by
  unfold tailWord_3046755
  simp only [CollatzResearch.WordTrace]
  refine ⟨111124284077134454172381719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74082856051422969448254479 111124284077134454172381719)
  ·
    refine ⟨166686426115701681258572579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111124284077134454172381719 166686426115701681258572579)
    ·
      refine ⟨250029639173552521887858869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166686426115701681258572579 250029639173552521887858869)
      ·
        refine ⟨23440278672520548926986769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250029639173552521887858869 23440278672520548926986769)
        ·
          refine ⟨17580209004390411695240077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23440278672520548926986769 17580209004390411695240077)
          ·
            refine ⟨6592578376646404385715029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17580209004390411695240077 6592578376646404385715029)
            ·
              refine ⟨38628388925662525697549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6592578376646404385715029 38628388925662525697549)
              ·
                rfl

theorem cell22_3046755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 9].length) (baseStart_3046755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046755 prefixEnd_3046755 := by exact prefixLift 3046755
  have htrace : WordTrace (prefixWord ++ tailWord_3046755) baseStart_3046755 baseEnd_3046755 := by
    simpa [prefixWord, tailWord_3046755, baseEnd_3046755] using wordTrace_append hprefix tailTrace_3046755
  have hstable : (prefixWord ++ tailWord_3046755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046755).length < 2 ^ (prefixWord ++ tailWord_3046755).sum := by decide
  have hdescent : baseEnd_3046755 < baseStart_3046755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046759 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3046759 : Nat := 118140960795 + 3046759 * 2 ^ 59
def prefixEnd_3046759 : Nat := 4983230072969 + 3 ^ 40 * 3046759 * 2
def baseEnd_3046759 : Nat := 1042967870274633516733811

theorem tailTrace_3046759 : CollatzResearch.WordTrace tailWord_3046759 prefixEnd_3046759 1042967870274633516733811 := by
  unfold tailWord_3046759
  simp only [CollatzResearch.WordTrace]
  refine ⟨111124429969119962855527331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74082953312746641903684887 111124429969119962855527331)
  ·
    refine ⟨166686644953679944283290997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111124429969119962855527331 166686644953679944283290997)
    ·
      refine ⟨15626872964407494776558531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166686644953679944283290997 15626872964407494776558531)
      ·
        refine ⟨23440309446611242164837797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15626872964407494776558531 23440309446611242164837797)
        ·
          refine ⟨4395058021239607905907087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23440309446611242164837797 4395058021239607905907087)
          ·
            refine ⟨6592587031859411858860631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4395058021239607905907087 6592587031859411858860631)
            ·
              refine ⟨9888880547789117788290947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6592587031859411858860631 9888880547789117788290947)
              ·
                refine ⟨14833320821683676682436421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9888880547789117788290947 14833320821683676682436421)
                ·
                  refine ⟨2781247654065689377956829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14833320821683676682436421 2781247654065689377956829)
                  ·
                    refine ⟨1042967870274633516733811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2781247654065689377956829 1042967870274633516733811)
                    ·
                      rfl

theorem cell22_3046759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3046759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046759 prefixEnd_3046759 := by exact prefixLift 3046759
  have htrace : WordTrace (prefixWord ++ tailWord_3046759) baseStart_3046759 baseEnd_3046759 := by
    simpa [prefixWord, tailWord_3046759, baseEnd_3046759] using wordTrace_append hprefix tailTrace_3046759
  have hstable : (prefixWord ++ tailWord_3046759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046759).length < 2 ^ (prefixWord ++ tailWord_3046759).sum := by decide
  have hdescent : baseEnd_3046759 < baseStart_3046759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046879 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 4]
def baseStart_3046879 : Nat := 118140960795 + 3046879 * 2 ^ 59
def prefixEnd_3046879 : Nat := 4983230072969 + 3 ^ 40 * 3046879 * 2
def baseEnd_3046879 : Nat := 347669649575664401244481

theorem tailTrace_3046879 : CollatzResearch.WordTrace tailWord_3046879 prefixEnd_3046879 347669649575664401244481 := by
  unfold tailWord_3046879
  simp only [CollatzResearch.WordTrace]
  refine ⟨111128806728685223349895691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74085871152456815566597127 111128806728685223349895691)
  ·
    refine ⟨166693210093027835024843537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111128806728685223349895691 166693210093027835024843537)
    ·
      refine ⟨125019907569770876268632653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166693210093027835024843537 125019907569770876268632653)
      ·
        refine ⟨46882465338664078600737245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125019907569770876268632653 46882465338664078600737245)
        ·
          refine ⟨17580924501999029475276467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46882465338664078600737245 17580924501999029475276467)
          ·
            refine ⟨26371386752998544212914701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17580924501999029475276467 26371386752998544212914701)
            ·
              refine ⟨9889270032374454079843013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26371386752998544212914701 9889270032374454079843013)
              ·
                refine ⟨1854238131070210139970565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9889270032374454079843013 1854238131070210139970565)
                ·
                  refine ⟨347669649575664401244481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854238131070210139970565 347669649575664401244481)
                  ·
                    rfl

theorem cell22_3046879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 4].length) (baseStart_3046879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046879 prefixEnd_3046879 := by exact prefixLift 3046879
  have htrace : WordTrace (prefixWord ++ tailWord_3046879) baseStart_3046879 baseEnd_3046879 := by
    simpa [prefixWord, tailWord_3046879, baseEnd_3046879] using wordTrace_append hprefix tailTrace_3046879
  have hstable : (prefixWord ++ tailWord_3046879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046879).length < 2 ^ (prefixWord ++ tailWord_3046879).sum := by decide
  have hdescent : baseEnd_3046879 < baseStart_3046879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046894 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3046894 : Nat := 118140960795 + 3046894 * 2 ^ 59
def prefixEnd_3046894 : Nat := 4983230072969 + 3 ^ 40 * 3046894 * 2
def baseEnd_3046894 : Nat := 1043014083533538164608397

theorem tailTrace_3046894 : CollatzResearch.WordTrace tailWord_3046894 prefixEnd_3046894 1043014083533538164608397 := by
  unfold tailWord_3046894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891169227953860113961467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74086235882420587274461157 13891169227953860113961467)
  ·
    refine ⟨20836753841930790170942201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891169227953860113961467 20836753841930790170942201)
    ·
      refine ⟨15627565381448092628206651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20836753841930790170942201 15627565381448092628206651)
      ·
        refine ⟨23441348072172138942309977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15627565381448092628206651 23441348072172138942309977)
        ·
          refine ⟨17581011054129104206732483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23441348072172138942309977 17581011054129104206732483)
          ·
            refine ⟨26371516581193656310098725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17581011054129104206732483 26371516581193656310098725)
            ·
              refine ⟨4944659358973810558143511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26371516581193656310098725 4944659358973810558143511)
              ·
                refine ⟨7416989038460715837215267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4944659358973810558143511 7416989038460715837215267)
                ·
                  refine ⟨11125483557691073755822901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7416989038460715837215267 11125483557691073755822901)
                  ·
                    refine ⟨1043014083533538164608397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11125483557691073755822901 1043014083533538164608397)
                    ·
                      rfl

theorem cell22_3046894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3046894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046894 prefixEnd_3046894 := by exact prefixLift 3046894
  have htrace : WordTrace (prefixWord ++ tailWord_3046894) baseStart_3046894 baseEnd_3046894 := by
    simpa [prefixWord, tailWord_3046894, baseEnd_3046894] using wordTrace_append hprefix tailTrace_3046894
  have hstable : (prefixWord ++ tailWord_3046894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046894).length < 2 ^ (prefixWord ++ tailWord_3046894).sum := by decide
  have hdescent : baseEnd_3046894 < baseStart_3046894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3046909 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_3046909 : Nat := 118140960795 + 3046909 * 2 ^ 59
def prefixEnd_3046909 : Nat := 4983230072969 + 3 ^ 40 * 3046909 * 2
def baseEnd_3046909 : Nat := 1043019218340083125483351

theorem tailTrace_3046909 : CollatzResearch.WordTrace tailWord_3046909 prefixEnd_3046909 1043019218340083125483351 := by
  unfold tailWord_3046909
  simp only [CollatzResearch.WordTrace]
  refine ⟨111129900918576538473487781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74086600612384358982325187 111129900918576538473487781)
  ·
    refine ⟨20836856422233100963778959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111129900918576538473487781 20836856422233100963778959)
    ·
      refine ⟨31255284633349651445668439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20836856422233100963778959 31255284633349651445668439)
      ·
        refine ⟨46882926950024477168502659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31255284633349651445668439 46882926950024477168502659)
        ·
          refine ⟨70324390425036715752753989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46882926950024477168502659 70324390425036715752753989)
          ·
            refine ⟨13185823204694384203641373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70324390425036715752753989 13185823204694384203641373)
            ·
              refine ⟨4944683701760394076365515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13185823204694384203641373 4944683701760394076365515)
              ·
                refine ⟨7417025552640591114548273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4944683701760394076365515 7417025552640591114548273)
                ·
                  refine ⟨5562769164480443335911205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7417025552640591114548273 5562769164480443335911205)
                  ·
                    refine ⟨1043019218340083125483351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562769164480443335911205 1043019218340083125483351)
                    ·
                      rfl

theorem cell22_3046909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_3046909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3046909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3046909 prefixEnd_3046909 := by exact prefixLift 3046909
  have htrace : WordTrace (prefixWord ++ tailWord_3046909) baseStart_3046909 baseEnd_3046909 := by
    simpa [prefixWord, tailWord_3046909, baseEnd_3046909] using wordTrace_append hprefix tailTrace_3046909
  have hstable : (prefixWord ++ tailWord_3046909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3046909).length < 2 ^ (prefixWord ++ tailWord_3046909).sum := by decide
  have hdescent : baseEnd_3046909 < baseStart_3046909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3046909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047016 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3047016 : Nat := 118140960795 + 3047016 * 2 ^ 59
def prefixEnd_3047016 : Nat := 4983230072969 + 3 ^ 40 * 3047016 * 2
def baseEnd_3047016 : Nat := 1043055846626770513058023

theorem tailTrace_3047016 : CollatzResearch.WordTrace tailWord_3047016 prefixEnd_3047016 1043055846626770513058023 := by
  unfold tailWord_3047016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55566901764594447873816451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74089202352792597165088601 55566901764594447873816451)
  ·
    refine ⟨83350352646891671810724677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55566901764594447873816451 83350352646891671810724677)
    ·
      refine ⟨15628191121292188464510877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83350352646891671810724677 15628191121292188464510877)
      ·
        refine ⟨5860571670484570674191579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15628191121292188464510877 5860571670484570674191579)
        ·
          refine ⟨8790857505726856011287369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860571670484570674191579 8790857505726856011287369)
          ·
            refine ⟨6593143129295142008465527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8790857505726856011287369 6593143129295142008465527)
            ·
              refine ⟨9889714693942713012698291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6593143129295142008465527 9889714693942713012698291)
              ·
                refine ⟨14834572040914069519047437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9889714693942713012698291 14834572040914069519047437)
                ·
                  refine ⟨5562964515342776069642789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14834572040914069519047437 5562964515342776069642789)
                  ·
                    refine ⟨1043055846626770513058023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5562964515342776069642789 1043055846626770513058023)
                    ·
                      rfl

theorem cell22_3047016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3047016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047016 prefixEnd_3047016 := by exact prefixLift 3047016
  have htrace : WordTrace (prefixWord ++ tailWord_3047016) baseStart_3047016 baseEnd_3047016 := by
    simpa [prefixWord, tailWord_3047016, baseEnd_3047016] using wordTrace_append hprefix tailTrace_3047016
  have hstable : (prefixWord ++ tailWord_3047016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047016).length < 2 ^ (prefixWord ++ tailWord_3047016).sum := by decide
  have hdescent : baseEnd_3047016 < baseStart_3047016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047027 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_3047027 : Nat := 118140960795 + 3047027 * 2 ^ 59
def prefixEnd_3047027 : Nat := 4983230072969 + 3 ^ 40 * 3047027 * 2
def baseEnd_3047027 : Nat := 1043059612151570151032989

theorem tailTrace_3047027 : CollatzResearch.WordTrace tailWord_3047027 prefixEnd_3047027 1043059612151570151032989 := by
  unfold tailWord_3047027
  simp only [CollatzResearch.WordTrace]
  refine ⟨111134204732149044626283335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74089469821432696417522223 111134204732149044626283335)
  ·
    refine ⟨166701307098223566939425003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111134204732149044626283335 166701307098223566939425003)
    ·
      refine ⟨250051960647335350409137505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166701307098223566939425003 250051960647335350409137505)
      ·
        refine ⟨187538970485501512806853129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250051960647335350409137505 187538970485501512806853129)
        ·
          refine ⟨140654227864126134605139847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187538970485501512806853129 140654227864126134605139847)
          ·
            refine ⟨210981341796189201907709771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140654227864126134605139847 210981341796189201907709771)
            ·
              refine ⟨316472012694283802861564657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210981341796189201907709771 316472012694283802861564657)
              ·
                refine ⟨237354009520712852146173493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316472012694283802861564657 237354009520712852146173493)
                ·
                  refine ⟨22251938392566829888703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237354009520712852146173493 22251938392566829888703765)
                  ·
                    refine ⟨1043059612151570151032989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22251938392566829888703765 1043059612151570151032989)
                    ·
                      rfl

theorem cell22_3047027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_3047027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047027 prefixEnd_3047027 := by exact prefixLift 3047027
  have htrace : WordTrace (prefixWord ++ tailWord_3047027) baseStart_3047027 baseEnd_3047027 := by
    simpa [prefixWord, tailWord_3047027, baseEnd_3047027] using wordTrace_append hprefix tailTrace_3047027
  have hstable : (prefixWord ++ tailWord_3047027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047027).length < 2 ^ (prefixWord ++ tailWord_3047027).sum := by decide
  have hdescent : baseEnd_3047027 < baseStart_3047027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047076 : List Nat := [2, 3, 1, 2, 2, 3, 3, 6]
def baseStart_3047076 : Nat := 118140960795 + 3047076 * 2 ^ 59
def prefixEnd_3047076 : Nat := 4983230072969 + 3 ^ 40 * 3047076 * 2
def baseEnd_3047076 : Nat := 115897376205883372950871

theorem tailTrace_3047076 : CollatzResearch.WordTrace tailWord_3047076 prefixEnd_3047076 115897376205883372950871 := by
  unfold tailWord_3047076
  simp only [CollatzResearch.WordTrace]
  refine ⟨55567995954485762997408541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74090661272647683996544721 55567995954485762997408541)
  ·
    refine ⟨20837998482932161124028203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55567995954485762997408541 20837998482932161124028203)
    ·
      refine ⟨31256997724398241686042305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20837998482932161124028203 31256997724398241686042305)
      ·
        refine ⟨23442748293298681264531729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31256997724398241686042305 23442748293298681264531729)
        ·
          refine ⟨17582061219974010948398797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23442748293298681264531729 17582061219974010948398797)
          ·
            refine ⟨6593272957490254105649549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17582061219974010948398797 6593272957490254105649549)
            ·
              refine ⟨2472477359058845289618581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6593272957490254105649549 2472477359058845289618581)
              ·
                refine ⟨115897376205883372950871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2472477359058845289618581 115897376205883372950871)
                ·
                  rfl

theorem cell22_3047076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_3047076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047076 prefixEnd_3047076 := by exact prefixLift 3047076
  have htrace : WordTrace (prefixWord ++ tailWord_3047076) baseStart_3047076 baseEnd_3047076 := by
    simpa [prefixWord, tailWord_3047076, baseEnd_3047076] using wordTrace_append hprefix tailTrace_3047076
  have hstable : (prefixWord ++ tailWord_3047076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047076).length < 2 ^ (prefixWord ++ tailWord_3047076).sum := by decide
  have hdescent : baseEnd_3047076 < baseStart_3047076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047104 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_3047104 : Nat := 118140960795 + 3047104 * 2 ^ 59
def prefixEnd_3047104 : Nat := 4983230072969 + 3 ^ 40 * 3047104 * 2
def baseEnd_3047104 : Nat := 347695323608389205619251

theorem tailTrace_3047104 : CollatzResearch.WordTrace tailWord_3047104 prefixEnd_3047104 347695323608389205619251 := by
  unfold tailWord_3047104
  simp only [CollatzResearch.WordTrace]
  refine ⟨55568506576435043388418183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74091342101913391184557577 55568506576435043388418183)
  ·
    refine ⟨83352759864652565082627275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55568506576435043388418183 83352759864652565082627275)
    ·
      refine ⟨125029139796978847623940913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83352759864652565082627275 125029139796978847623940913)
      ·
        refine ⟨93771854847734135717955685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125029139796978847623940913 93771854847734135717955685)
        ·
          refine ⟨17582222783950150447116691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93771854847734135717955685 17582222783950150447116691)
          ·
            refine ⟨26373334175925225670675037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17582222783950150447116691 26373334175925225670675037)
            ·
              refine ⟨9890000315971959626503139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26373334175925225670675037 9890000315971959626503139)
              ·
                refine ⟨14835000473957939439754709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9890000315971959626503139 14835000473957939439754709)
                ·
                  refine ⟨347695323608389205619251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14835000473957939439754709 347695323608389205619251)
                  ·
                    rfl

theorem cell22_3047104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_3047104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047104 prefixEnd_3047104 := by exact prefixLift 3047104
  have htrace : WordTrace (prefixWord ++ tailWord_3047104) baseStart_3047104 baseEnd_3047104 := by
    simpa [prefixWord, tailWord_3047104, baseEnd_3047104] using wordTrace_append hprefix tailTrace_3047104
  have hstable : (prefixWord ++ tailWord_3047104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047104).length < 2 ^ (prefixWord ++ tailWord_3047104).sum := by decide
  have hdescent : baseEnd_3047104 < baseStart_3047104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047108 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3047108 : Nat := 118140960795 + 3047108 * 2 ^ 59
def prefixEnd_3047108 : Nat := 4983230072969 + 3 ^ 40 * 3047108 * 2
def baseEnd_3047108 : Nat := 1043087340106912939757741

theorem tailTrace_3047108 : CollatzResearch.WordTrace tailWord_3047108 prefixEnd_3047108 1043087340106912939757741 := by
  unfold tailWord_3047108
  simp only [CollatzResearch.WordTrace]
  refine ⟨55568579522427797729990989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74091439363237063639987985 55568579522427797729990989)
  ·
    refine ⟨20838217320910424148746621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55568579522427797729990989 20838217320910424148746621)
    ·
      refine ⟨7814331495341409055779983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20838217320910424148746621 7814331495341409055779983)
      ·
        refine ⟨11721497243012113583669975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7814331495341409055779983 11721497243012113583669975)
        ·
          refine ⟨17582245864518170375504963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11721497243012113583669975 17582245864518170375504963)
          ·
            refine ⟨26373368796777255563257445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17582245864518170375504963 26373368796777255563257445)
            ·
              refine ⟨4945006649395735418110771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26373368796777255563257445 4945006649395735418110771)
              ·
                refine ⟨7417509974093603127166157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945006649395735418110771 7417509974093603127166157)
                ·
                  refine ⟨2781566240285101172687309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7417509974093603127166157 2781566240285101172687309)
                  ·
                    refine ⟨1043087340106912939757741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2781566240285101172687309 1043087340106912939757741)
                    ·
                      rfl

theorem cell22_3047108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3047108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047108 prefixEnd_3047108 := by exact prefixLift 3047108
  have htrace : WordTrace (prefixWord ++ tailWord_3047108) baseStart_3047108 baseEnd_3047108 := by
    simpa [prefixWord, tailWord_3047108, baseEnd_3047108] using wordTrace_append hprefix tailTrace_3047108
  have hstable : (prefixWord ++ tailWord_3047108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047108).length < 2 ^ (prefixWord ++ tailWord_3047108).sum := by decide
  have hdescent : baseEnd_3047108 < baseStart_3047108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047151 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 1, 4]
def baseStart_3047151 : Nat := 118140960795 + 3047151 * 2 ^ 59
def prefixEnd_3047151 : Nat := 4983230072969 + 3 ^ 40 * 3047151 * 2
def baseEnd_3047151 : Nat := 1043102059885675160932609

theorem tailTrace_3047151 : CollatzResearch.WordTrace tailWord_3047151 prefixEnd_3047151 1043102059885675160932609 := by
  unfold tailWord_3047151
  simp only [CollatzResearch.WordTrace]
  refine ⟨111138727383699813803797307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74092484922466542535864871 111138727383699813803797307)
  ·
    refine ⟨166708091075549720705695961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111138727383699813803797307 166708091075549720705695961)
    ·
      refine ⟨125031068306662290529271971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166708091075549720705695961 125031068306662290529271971)
      ·
        refine ⟨187546602459993435793907957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125031068306662290529271971 187546602459993435793907957)
        ·
          refine ⟨17582493980624384605678871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187546602459993435793907957 17582493980624384605678871)
          ·
            refine ⟨26373740970936576908518307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17582493980624384605678871 26373740970936576908518307)
            ·
              refine ⟨39560611456404865362777461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26373740970936576908518307 39560611456404865362777461)
              ·
                refine ⟨3708807324037956127760387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39560611456404865362777461 3708807324037956127760387)
                ·
                  refine ⟨5563210986056934191640581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3708807324037956127760387 5563210986056934191640581)
                  ·
                    refine ⟨1043102059885675160932609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5563210986056934191640581 1043102059885675160932609)
                    ·
                      rfl

theorem cell22_3047151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_3047151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047151 prefixEnd_3047151 := by exact prefixLift 3047151
  have htrace : WordTrace (prefixWord ++ tailWord_3047151) baseStart_3047151 baseEnd_3047151 := by
    simpa [prefixWord, tailWord_3047151, baseEnd_3047151] using wordTrace_append hprefix tailTrace_3047151
  have hstable : (prefixWord ++ tailWord_3047151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047151).length < 2 ^ (prefixWord ++ tailWord_3047151).sum := by decide
  have hdescent : baseEnd_3047151 < baseStart_3047151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047179 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_3047179 : Nat := 118140960795 + 3047179 * 2 ^ 59
def prefixEnd_3047179 : Nat := 4983230072969 + 3 ^ 40 * 3047179 * 2
def baseEnd_3047179 : Nat := 1043111644857892421232523

theorem tailTrace_3047179 : CollatzResearch.WordTrace tailWord_3047179 prefixEnd_3047179 1043111644857892421232523 := by
  unfold tailWord_3047179
  simp only [CollatzResearch.WordTrace]
  refine ⟨111139748627598374585816591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74093165751732249723877727 111139748627598374585816591)
  ·
    refine ⟨166709622941397561878724887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111139748627598374585816591 166709622941397561878724887)
    ·
      refine ⟨250064434412096342818087331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166709622941397561878724887 250064434412096342818087331)
      ·
        refine ⟨375096651618144514227130997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250064434412096342818087331 375096651618144514227130997)
        ·
          refine ⟨35165311089201048208793531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375096651618144514227130997 35165311089201048208793531)
          ·
            refine ⟨52747966633801572313190297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35165311089201048208793531 52747966633801572313190297)
            ·
              refine ⟨39560974975351179234892723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52747966633801572313190297 39560974975351179234892723)
              ·
                refine ⟨59341462463026768852339085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39560974975351179234892723 59341462463026768852339085)
                ·
                  refine ⟨22253048423635038319627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59341462463026768852339085 22253048423635038319627157)
                  ·
                    refine ⟨1043111644857892421232523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22253048423635038319627157 1043111644857892421232523)
                    ·
                      rfl

theorem cell22_3047179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_3047179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047179 prefixEnd_3047179 := by exact prefixLift 3047179
  have htrace : WordTrace (prefixWord ++ tailWord_3047179) baseStart_3047179 baseEnd_3047179 := by
    simpa [prefixWord, tailWord_3047179, baseEnd_3047179] using wordTrace_append hprefix tailTrace_3047179
  have hstable : (prefixWord ++ tailWord_3047179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047179).length < 2 ^ (prefixWord ++ tailWord_3047179).sum := by decide
  have hdescent : baseEnd_3047179 < baseStart_3047179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047245 : List Nat := [1, 6, 1, 2, 1, 2, 3, 6]
def baseStart_3047245 : Nat := 118140960795 + 3047245 * 2 ^ 59
def prefixEnd_3047245 : Nat := 4983230072969 + 3 ^ 40 * 3047245 * 2
def baseEnd_3047245 : Nat := 115903804222965583231369

theorem tailTrace_3047245 : CollatzResearch.WordTrace tailWord_3047245 prefixEnd_3047245 115903804222965583231369 := by
  unfold tailWord_3047245
  simp only [CollatzResearch.WordTrace]
  refine ⟨111142155845359267857719189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74094770563572845238479459 111142155845359267857719189)
  ·
    refine ⟨5209788555251215680830587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111142155845359267857719189 5209788555251215680830587)
    ·
      refine ⟨7814682832876823521245881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209788555251215680830587 7814682832876823521245881)
      ·
        refine ⟨5861012124657617640934411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7814682832876823521245881 5861012124657617640934411)
        ·
          refine ⟨8791518186986426461401617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861012124657617640934411 8791518186986426461401617)
          ·
            refine ⟨6593638640239819846051213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8791518186986426461401617 6593638640239819846051213)
            ·
              refine ⟨2472614490089932442269205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6593638640239819846051213 2472614490089932442269205)
              ·
                refine ⟨115903804222965583231369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2472614490089932442269205 115903804222965583231369)
                ·
                  rfl

theorem cell22_3047245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 6].length) (baseStart_3047245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047245 prefixEnd_3047245 := by exact prefixLift 3047245
  have htrace : WordTrace (prefixWord ++ tailWord_3047245) baseStart_3047245 baseEnd_3047245 := by
    simpa [prefixWord, tailWord_3047245, baseEnd_3047245] using wordTrace_append hprefix tailTrace_3047245
  have hstable : (prefixWord ++ tailWord_3047245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047245).length < 2 ^ (prefixWord ++ tailWord_3047245).sum := by decide
  have hdescent : baseEnd_3047245 < baseStart_3047245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047271 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3047271 : Nat := 118140960795 + 3047271 * 2 ^ 59
def prefixEnd_3047271 : Nat := 4983230072969 + 3 ^ 40 * 3047271 * 2
def baseEnd_3047271 : Nat := 1043143138338034847932241

theorem tailTrace_3047271 : CollatzResearch.WordTrace tailWord_3047271 prefixEnd_3047271 1043143138338034847932241 := by
  unfold tailWord_3047271
  simp only [CollatzResearch.WordTrace]
  refine ⟨111143104143265074298165667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74095402762176716198777111 111143104143265074298165667)
  ·
    refine ⟨166714656214897611447248501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111143104143265074298165667 166714656214897611447248501)
    ·
      refine ⟨15629499020146651073179547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166714656214897611447248501 15629499020146651073179547)
      ·
        refine ⟨23444248530219976609769321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15629499020146651073179547 23444248530219976609769321)
        ·
          refine ⟨17583186397664982457326991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23444248530219976609769321 17583186397664982457326991)
          ·
            refine ⟨26374779596497473685990487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17583186397664982457326991 26374779596497473685990487)
            ·
              refine ⟨39562169394746210528985731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26374779596497473685990487 39562169394746210528985731)
              ·
                refine ⟨59343254092119315793478597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39562169394746210528985731 59343254092119315793478597)
                ·
                  refine ⟨11126860142272371711277237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59343254092119315793478597 11126860142272371711277237)
                  ·
                    refine ⟨1043143138338034847932241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11126860142272371711277237 1043143138338034847932241)
                    ·
                      rfl

theorem cell22_3047271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3047271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047271 prefixEnd_3047271 := by exact prefixLift 3047271
  have htrace : WordTrace (prefixWord ++ tailWord_3047271) baseStart_3047271 baseEnd_3047271 := by
    simpa [prefixWord, tailWord_3047271, baseEnd_3047271] using wordTrace_append hprefix tailTrace_3047271
  have hstable : (prefixWord ++ tailWord_3047271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047271).length < 2 ^ (prefixWord ++ tailWord_3047271).sum := by decide
  have hdescent : baseEnd_3047271 < baseStart_3047271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047301 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 6]
def baseStart_3047301 : Nat := 118140960795 + 3047301 * 2 ^ 59
def prefixEnd_3047301 : Nat := 4983230072969 + 3 ^ 40 * 3047301 * 2
def baseEnd_3047301 : Nat := 347717802650374923227383

theorem tailTrace_3047301 : CollatzResearch.WordTrace tailWord_3047301 prefixEnd_3047301 347717802650374923227383 := by
  unfold tailWord_3047301
  simp only [CollatzResearch.WordTrace]
  refine ⟨111144198333156389421757757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74096132222104259614505171 111144198333156389421757757)
  ·
    refine ⟨41679074374933646033159159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111144198333156389421757757 41679074374933646033159159)
    ·
      refine ⟨62518611562400469049738739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41679074374933646033159159 62518611562400469049738739)
      ·
        refine ⟨93777917343600703574608109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62518611562400469049738739 93777917343600703574608109)
        ·
          refine ⟨35166719003850263840478041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93777917343600703574608109 35166719003850263840478041)
          ·
            refine ⟨26375039252887697880358531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35166719003850263840478041 26375039252887697880358531)
            ·
              refine ⟨39562558879331546820537797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26375039252887697880358531 39562558879331546820537797)
              ·
                refine ⟨7417979789874665028850837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39562558879331546820537797 7417979789874665028850837)
                ·
                  refine ⟨347717802650374923227383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7417979789874665028850837 347717802650374923227383)
                  ·
                    rfl

theorem cell22_3047301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_3047301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047301 prefixEnd_3047301 := by exact prefixLift 3047301
  have htrace : WordTrace (prefixWord ++ tailWord_3047301) baseStart_3047301 baseEnd_3047301 := by
    simpa [prefixWord, tailWord_3047301, baseEnd_3047301] using wordTrace_append hprefix tailTrace_3047301
  have hstable : (prefixWord ++ tailWord_3047301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047301).length < 2 ^ (prefixWord ++ tailWord_3047301).sum := by decide
  have hdescent : baseEnd_3047301 < baseStart_3047301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047335 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 6]
def baseStart_3047335 : Nat := 118140960795 + 3047335 * 2 ^ 59
def prefixEnd_3047335 : Nat := 4983230072969 + 3 ^ 40 * 3047335 * 2
def baseEnd_3047335 : Nat := 347721682281986671444015

theorem tailTrace_3047335 : CollatzResearch.WordTrace tailWord_3047335 prefixEnd_3047335 347721682281986671444015 := by
  unfold tailWord_3047335
  simp only [CollatzResearch.WordTrace]
  refine ⟨111145438415033213228495459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74096958943355475485663639 111145438415033213228495459)
  ·
    refine ⟨166718157622549819842743189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111145438415033213228495459 166718157622549819842743189)
    ·
      refine ⟨7814913638557022805128587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166718157622549819842743189 7814913638557022805128587)
      ·
        refine ⟨11722370457835534207692881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7814913638557022805128587 11722370457835534207692881)
        ·
          refine ⟨8791777843376650655769661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11722370457835534207692881 8791777843376650655769661)
          ·
            refine ⟨3296916691266243995913623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8791777843376650655769661 3296916691266243995913623)
            ·
              refine ⟨4945375036899365993870435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296916691266243995913623 4945375036899365993870435)
              ·
                refine ⟨7418062555349048990805653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945375036899365993870435 7418062555349048990805653)
                ·
                  refine ⟨347721682281986671444015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7418062555349048990805653 347721682281986671444015)
                  ·
                    rfl

theorem cell22_3047335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 6].length) (baseStart_3047335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047335 prefixEnd_3047335 := by exact prefixLift 3047335
  have htrace : WordTrace (prefixWord ++ tailWord_3047335) baseStart_3047335 baseEnd_3047335 := by
    simpa [prefixWord, tailWord_3047335, baseEnd_3047335] using wordTrace_append hprefix tailTrace_3047335
  have hstable : (prefixWord ++ tailWord_3047335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047335).length < 2 ^ (prefixWord ++ tailWord_3047335).sum := by decide
  have hdescent : baseEnd_3047335 < baseStart_3047335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047408 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_3047408 : Nat := 118140960795 + 3047408 * 2 ^ 59
def prefixEnd_3047408 : Nat := 4983230072969 + 3 ^ 40 * 3047408 * 2
def baseEnd_3047408 : Nat := 347730012079270719085607

theorem tailTrace_3047408 : CollatzResearch.WordTrace tailWord_3047408 prefixEnd_3047408 347730012079270719085607 := by
  unfold tailWord_3047408
  simp only [CollatzResearch.WordTrace]
  refine ⟨55574050471884373347951439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74098733962512497797268585 55574050471884373347951439)
  ·
    refine ⟨83361075707826560021927159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55574050471884373347951439 83361075707826560021927159)
    ·
      refine ⟨125041613561739840032890739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83361075707826560021927159 125041613561739840032890739)
      ·
        refine ⟨187562420342609760049336109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125041613561739840032890739 187562420342609760049336109)
        ·
          refine ⟨70335907628478660018501041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187562420342609760049336109 70335907628478660018501041)
          ·
            refine ⟨52751930721358995013875781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70335907628478660018501041 52751930721358995013875781)
            ·
              refine ⟨9890987010254811565101709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52751930721358995013875781 9890987010254811565101709)
              ·
                refine ⟨3709120128845554336913141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9890987010254811565101709 3709120128845554336913141)
                ·
                  refine ⟨347730012079270719085607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709120128845554336913141 347730012079270719085607)
                  ·
                    rfl

theorem cell22_3047408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_3047408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047408 prefixEnd_3047408 := by exact prefixLift 3047408
  have htrace : WordTrace (prefixWord ++ tailWord_3047408) baseStart_3047408 baseEnd_3047408 := by
    simpa [prefixWord, tailWord_3047408, baseEnd_3047408] using wordTrace_append hprefix tailTrace_3047408
  have hstable : (prefixWord ++ tailWord_3047408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047408).length < 2 ^ (prefixWord ++ tailWord_3047408).sum := by decide
  have hdescent : baseEnd_3047408 < baseStart_3047408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047468 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_3047468 : Nat := 118140960795 + 3047468 * 2 ^ 59
def prefixEnd_3047468 : Nat := 4983230072969 + 3 ^ 40 * 3047468 * 2
def baseEnd_3047468 : Nat := 1043210575463992000756637

theorem tailTrace_3047468 : CollatzResearch.WordTrace tailWord_3047468 prefixEnd_3047468 1043210575463992000756637 := by
  unfold tailWord_3047468
  simp only [CollatzResearch.WordTrace]
  refine ⟨55575144661775688471543529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74100192882367584628724705 55575144661775688471543529)
  ·
    refine ⟨41681358496331766353657647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55575144661775688471543529 41681358496331766353657647)
    ·
      refine ⟨62522037744497649530486471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41681358496331766353657647 62522037744497649530486471)
      ·
        refine ⟨93783056616746474295729707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62522037744497649530486471 93783056616746474295729707)
        ·
          refine ⟨140674584925119711443594561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93783056616746474295729707 140674584925119711443594561)
          ·
            refine ⟨105505938693839783582695921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140674584925119711443594561 105505938693839783582695921)
            ·
              refine ⟨79129454020379837687021941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105505938693839783582695921 79129454020379837687021941)
              ·
                refine ⟨7418386314410609783158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79129454020379837687021941 7418386314410609783158307)
                ·
                  refine ⟨11127579471615914674737461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7418386314410609783158307 11127579471615914674737461)
                  ·
                    refine ⟨1043210575463992000756637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11127579471615914674737461 1043210575463992000756637)
                    ·
                      rfl

theorem cell22_3047468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_3047468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047468 prefixEnd_3047468 := by exact prefixLift 3047468
  have htrace : WordTrace (prefixWord ++ tailWord_3047468) baseStart_3047468 baseEnd_3047468 := by
    simpa [prefixWord, tailWord_3047468, baseEnd_3047468] using wordTrace_append hprefix tailTrace_3047468
  have hstable : (prefixWord ++ tailWord_3047468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047468).length < 2 ^ (prefixWord ++ tailWord_3047468).sum := by decide
  have hdescent : baseEnd_3047468 < baseStart_3047468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047470 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3047470 : Nat := 118140960795 + 3047470 * 2 ^ 59
def prefixEnd_3047470 : Nat := 4983230072969 + 3 ^ 40 * 3047470 * 2
def baseEnd_3047470 : Nat := 347737086701621554068877

theorem tailTrace_3047470 : CollatzResearch.WordTrace tailWord_3047470 prefixEnd_3047470 347737086701621554068877 := by
  unfold tailWord_3047470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893795283693016410582483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74100241513029420856439909 13893795283693016410582483)
  ·
    refine ⟨20840692925539524615873725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13893795283693016410582483 20840692925539524615873725)
    ·
      refine ⟨7815259847077321730952647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20840692925539524615873725 7815259847077321730952647)
      ·
        refine ⟨11722889770615982596428971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7815259847077321730952647 11722889770615982596428971)
        ·
          refine ⟨17584334655923973894643457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722889770615982596428971 17584334655923973894643457)
          ·
            refine ⟨13188250991942980420982593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17584334655923973894643457 13188250991942980420982593)
            ·
              refine ⟨9891188243957235315736945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13188250991942980420982593 9891188243957235315736945)
              ·
                refine ⟨7418391182967926486802709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9891188243957235315736945 7418391182967926486802709)
                ·
                  refine ⟨347737086701621554068877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7418391182967926486802709 347737086701621554068877)
                  ·
                    rfl

theorem cell22_3047470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3047470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047470 prefixEnd_3047470 := by exact prefixLift 3047470
  have htrace : WordTrace (prefixWord ++ tailWord_3047470) baseStart_3047470 baseEnd_3047470 := by
    simpa [prefixWord, tailWord_3047470, baseEnd_3047470] using wordTrace_append hprefix tailTrace_3047470
  have hstable : (prefixWord ++ tailWord_3047470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047470).length < 2 ^ (prefixWord ++ tailWord_3047470).sum := by decide
  have hdescent : baseEnd_3047470 < baseStart_3047470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047485 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_3047485 : Nat := 118140960795 + 3047485 * 2 ^ 59
def prefixEnd_3047485 : Nat := 4983230072969 + 3 ^ 40 * 3047485 * 2
def baseEnd_3047485 : Nat := 1043216394911409623081585

theorem tailTrace_3047485 : CollatzResearch.WordTrace tailWord_3047485 prefixEnd_3047485 1043216394911409623081585 := by
  unfold tailWord_3047485
  simp only [CollatzResearch.WordTrace]
  refine ⟨111150909364489788846455909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74100606242993192564303939 111150909364489788846455909)
  ·
    refine ⟨20840795505841835408710483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111150909364489788846455909 20840795505841835408710483)
    ·
      refine ⟨31261193258762753113065725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20840795505841835408710483 31261193258762753113065725)
      ·
        refine ⟨11722947472036032417399647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31261193258762753113065725 11722947472036032417399647)
        ·
          refine ⟨17584421208054048626099471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11722947472036032417399647 17584421208054048626099471)
          ·
            refine ⟨26376631812081072939149207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17584421208054048626099471 26376631812081072939149207)
            ·
              refine ⟨39564947718121609408723811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26376631812081072939149207 39564947718121609408723811)
              ·
                refine ⟨59347421577182414113085717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39564947718121609408723811 59347421577182414113085717)
                ·
                  refine ⟨2781910386430425661550893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59347421577182414113085717 2781910386430425661550893)
                  ·
                    refine ⟨1043216394911409623081585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2781910386430425661550893 1043216394911409623081585)
                    ·
                      rfl

theorem cell22_3047485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_3047485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047485 prefixEnd_3047485 := by exact prefixLift 3047485
  have htrace : WordTrace (prefixWord ++ tailWord_3047485) baseStart_3047485 baseEnd_3047485 := by
    simpa [prefixWord, tailWord_3047485, baseEnd_3047485] using wordTrace_append hprefix tailTrace_3047485
  have hstable : (prefixWord ++ tailWord_3047485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047485).length < 2 ^ (prefixWord ++ tailWord_3047485).sum := by decide
  have hdescent : baseEnd_3047485 < baseStart_3047485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047607 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3047607 : Nat := 118140960795 + 3047607 * 2 ^ 59
def prefixEnd_3047607 : Nat := 4983230072969 + 3 ^ 40 * 3047607 * 2
def baseEnd_3047607 : Nat := 1043258158004641971531211

theorem tailTrace_3047607 : CollatzResearch.WordTrace tailWord_3047607 prefixEnd_3047607 1043258158004641971531211 := by
  unfold tailWord_3047607
  simp only [CollatzResearch.WordTrace]
  refine ⟨111155359070047803682397075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74103572713365202454931383 111155359070047803682397075)
  ·
    refine ⟨166733038605071705523595613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111155359070047803682397075 166733038605071705523595613)
    ·
      refine ⟨62524889476901889571348355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166733038605071705523595613 62524889476901889571348355)
      ·
        refine ⟨93787334215352834357022533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62524889476901889571348355 93787334215352834357022533)
        ·
          refine ⟨17585125165378656441941725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93787334215352834357022533 17585125165378656441941725)
          ·
            refine ⟨6594421937016996165728147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17585125165378656441941725 6594421937016996165728147)
            ·
              refine ⟨9891632905525494248592221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6594421937016996165728147 9891632905525494248592221)
              ·
                refine ⟨3709362339572060343222083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9891632905525494248592221 3709362339572060343222083)
                ·
                  refine ⟨5564043509358090514833125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3709362339572060343222083 5564043509358090514833125)
                  ·
                    refine ⟨1043258158004641971531211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5564043509358090514833125 1043258158004641971531211)
                    ·
                      rfl

theorem cell22_3047607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3047607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047607 prefixEnd_3047607 := by exact prefixLift 3047607
  have htrace : WordTrace (prefixWord ++ tailWord_3047607) baseStart_3047607 baseEnd_3047607 := by
    simpa [prefixWord, tailWord_3047607, baseEnd_3047607] using wordTrace_append hprefix tailTrace_3047607
  have hstable : (prefixWord ++ tailWord_3047607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047607).length < 2 ^ (prefixWord ++ tailWord_3047607).sum := by decide
  have hdescent : baseEnd_3047607 < baseStart_3047607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047729 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 5]
def baseStart_3047729 : Nat := 118140960795 + 3047729 * 2 ^ 59
def prefixEnd_3047729 : Nat := 4983230072969 + 3 ^ 40 * 3047729 * 2
def baseEnd_3047729 : Nat := 347766640365958106660279

theorem tailTrace_3047729 : CollatzResearch.WordTrace tailWord_3047729 prefixEnd_3047729 347766640365958106660279 := by
  unfold tailWord_3047729
  simp only [CollatzResearch.WordTrace]
  refine ⟨111159808775605818518338241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74106539183737212345558827 111159808775605818518338241)
  ·
    refine ⟨83369856581704363888753681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111159808775605818518338241 83369856581704363888753681)
    ·
      refine ⟨62527392436278272916565261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83369856581704363888753681 62527392436278272916565261)
      ·
        refine ⟨23447772163604352343711973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62527392436278272916565261 23447772163604352343711973)
        ·
          refine ⟨4396457280675816064445995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23447772163604352343711973 4396457280675816064445995)
          ·
            refine ⟨6594685921013724096668993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396457280675816064445995 6594685921013724096668993)
            ·
              refine ⟨4946014440760293072501745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594685921013724096668993 4946014440760293072501745)
              ·
                refine ⟨3709510830570219804376309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4946014440760293072501745 3709510830570219804376309)
                ·
                  refine ⟨347766640365958106660279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709510830570219804376309 347766640365958106660279)
                  ·
                    rfl

theorem cell22_3047729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_3047729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047729 prefixEnd_3047729 := by exact prefixLift 3047729
  have htrace : WordTrace (prefixWord ++ tailWord_3047729) baseStart_3047729 baseEnd_3047729 := by
    simpa [prefixWord, tailWord_3047729, baseEnd_3047729] using wordTrace_append hprefix tailTrace_3047729
  have hstable : (prefixWord ++ tailWord_3047729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047729).length < 2 ^ (prefixWord ++ tailWord_3047729).sum := by decide
  have hdescent : baseEnd_3047729 < baseStart_3047729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047785 : List Nat := [1, 2, 1, 1, 1, 3, 13]
def baseStart_3047785 : Nat := 118140960795 + 3047785 * 2 ^ 59
def prefixEnd_3047785 : Nat := 4983230072969 + 3 ^ 40 * 3047785 * 2
def baseEnd_3047785 : Nat := 38641447816381808910395

theorem tailTrace_3047785 : CollatzResearch.WordTrace tailWord_3047785 prefixEnd_3047785 38641447816381808910395 := by
  unfold tailWord_3047785
  simp only [CollatzResearch.WordTrace]
  refine ⟨111161851263402940082376809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74107900842268626721584539 111161851263402940082376809)
  ·
    refine ⟨83371388447552205061782607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111161851263402940082376809 83371388447552205061782607)
    ·
      refine ⟨125057082671328307592673911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83371388447552205061782607 125057082671328307592673911)
      ·
        refine ⟨187585624006992461389010867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125057082671328307592673911 187585624006992461389010867)
        ·
          refine ⟨281378436010488692083516301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187585624006992461389010867 281378436010488692083516301)
          ·
            refine ⟨105516913503933259531318613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281378436010488692083516301 105516913503933259531318613)
            ·
              refine ⟨38641447816381808910395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 105516913503933259531318613 38641447816381808910395)
              ·
                rfl

theorem cell22_3047785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 13].length) (baseStart_3047785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047785 prefixEnd_3047785 := by exact prefixLift 3047785
  have htrace : WordTrace (prefixWord ++ tailWord_3047785) baseStart_3047785 baseEnd_3047785 := by
    simpa [prefixWord, tailWord_3047785, baseEnd_3047785] using wordTrace_append hprefix tailTrace_3047785
  have hstable : (prefixWord ++ tailWord_3047785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047785).length < 2 ^ (prefixWord ++ tailWord_3047785).sum := by decide
  have hdescent : baseEnd_3047785 < baseStart_3047785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047789 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_3047789 : Nat := 118140960795 + 3047789 * 2 ^ 59
def prefixEnd_3047789 : Nat := 4983230072969 + 3 ^ 40 * 3047789 * 2
def baseEnd_3047789 : Nat := 1043320460324054163480653

theorem tailTrace_3047789 : CollatzResearch.WordTrace tailWord_3047789 prefixEnd_3047789 1043320460324054163480653 := by
  unfold tailWord_3047789
  simp only [CollatzResearch.WordTrace]
  refine ⟨111161997155388448765522421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74107998103592299177014947 111161997155388448765522421)
  ·
    refine ⟨10421437233317667071767727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111161997155388448765522421 10421437233317667071767727)
    ·
      refine ⟨15632155849976500607651591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421437233317667071767727 15632155849976500607651591)
      ·
        refine ⟨23448233774964750911477387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15632155849976500607651591 23448233774964750911477387)
        ·
          refine ⟨35172350662447126367216081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23448233774964750911477387 35172350662447126367216081)
          ·
            refine ⟨26379262996835344775412061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35172350662447126367216081 26379262996835344775412061)
            ·
              refine ⟨9892223623813254290779523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26379262996835344775412061 9892223623813254290779523)
              ·
                refine ⟨14838335435719881436169285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9892223623813254290779523 14838335435719881436169285)
                ·
                  refine ⟨2782187894197477769281741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14838335435719881436169285 2782187894197477769281741)
                  ·
                    refine ⟨1043320460324054163480653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782187894197477769281741 1043320460324054163480653)
                    ·
                      rfl

theorem cell22_3047789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_3047789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047789 prefixEnd_3047789 := by exact prefixLift 3047789
  have htrace : WordTrace (prefixWord ++ tailWord_3047789) baseStart_3047789 baseEnd_3047789 := by
    simpa [prefixWord, tailWord_3047789, baseEnd_3047789] using wordTrace_append hprefix tailTrace_3047789
  have hstable : (prefixWord ++ tailWord_3047789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047789).length < 2 ^ (prefixWord ++ tailWord_3047789).sum := by decide
  have hdescent : baseEnd_3047789 < baseStart_3047789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047819 : List Nat := [1, 1, 1, 1, 4, 6, 2, 6]
def baseStart_3047819 : Nat := 118140960795 + 3047819 * 2 ^ 59
def prefixEnd_3047819 : Nat := 4983230072969 + 3 ^ 40 * 3047819 * 2
def baseEnd_3047819 : Nat := 115925636659682676136729

theorem tailTrace_3047819 : CollatzResearch.WordTrace tailWord_3047819 prefixEnd_3047819 115925636659682676136729 := by
  unfold tailWord_3047819
  simp only [CollatzResearch.WordTrace]
  refine ⟨111163091345279763889114511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74108727563519842592743007 111163091345279763889114511)
  ·
    refine ⟨166744637017919645833671767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111163091345279763889114511 166744637017919645833671767)
    ·
      refine ⟨250116955526879468750507651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166744637017919645833671767 250116955526879468750507651)
      ·
        refine ⟨375175433290319203125761477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250116955526879468750507651 375175433290319203125761477)
        ·
          refine ⟨70345393741934850586080277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375175433290319203125761477 70345393741934850586080277)
          ·
            refine ⟨3297440331653196121222513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70345393741934850586080277 3297440331653196121222513)
            ·
              refine ⟨2473080248739897090916885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297440331653196121222513 2473080248739897090916885)
              ·
                refine ⟨115925636659682676136729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2473080248739897090916885 115925636659682676136729)
                ·
                  rfl

theorem cell22_3047819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 6].length) (baseStart_3047819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047819 prefixEnd_3047819 := by exact prefixLift 3047819
  have htrace : WordTrace (prefixWord ++ tailWord_3047819) baseStart_3047819 baseEnd_3047819 := by
    simpa [prefixWord, tailWord_3047819, baseEnd_3047819] using wordTrace_append hprefix tailTrace_3047819
  have hstable : (prefixWord ++ tailWord_3047819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047819).length < 2 ^ (prefixWord ++ tailWord_3047819).sum := by decide
  have hdescent : baseEnd_3047819 < baseStart_3047819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047943 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 4]
def baseStart_3047943 : Nat := 118140960795 + 3047943 * 2 ^ 59
def prefixEnd_3047943 : Nat := 4983230072969 + 3 ^ 40 * 3047943 * 2
def baseEnd_3047943 : Nat := 347791059223749698376727

theorem tailTrace_3047943 : CollatzResearch.WordTrace tailWord_3047943 prefixEnd_3047943 347791059223749698376727 := by
  unfold tailWord_3047943
  simp only [CollatzResearch.WordTrace]
  refine ⟨111167613996830533066628483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74111742664553688711085655 111167613996830533066628483)
  ·
    refine ⟨166751420995245799599942725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111167613996830533066628483 166751420995245799599942725)
    ·
      refine ⟨31265891436608587424989261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166751420995245799599942725 31265891436608587424989261)
      ·
        refine ⟨11724709288728220284370973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31265891436608587424989261 11724709288728220284370973)
        ·
          refine ⟨4396765983273082606639115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11724709288728220284370973 4396765983273082606639115)
          ·
            refine ⟨6595148974909623909958673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396765983273082606639115 6595148974909623909958673)
            ·
              refine ⟨4946361731182217932469005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6595148974909623909958673 4946361731182217932469005)
              ·
                refine ⟨1854885649193331724675877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4946361731182217932469005 1854885649193331724675877)
                ·
                  refine ⟨347791059223749698376727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854885649193331724675877 347791059223749698376727)
                  ·
                    rfl

theorem cell22_3047943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 4].length) (baseStart_3047943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047943 prefixEnd_3047943 := by exact prefixLift 3047943
  have htrace : WordTrace (prefixWord ++ tailWord_3047943) baseStart_3047943 baseEnd_3047943 := by
    simpa [prefixWord, tailWord_3047943, baseEnd_3047943] using wordTrace_append hprefix tailTrace_3047943
  have hstable : (prefixWord ++ tailWord_3047943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047943).length < 2 ^ (prefixWord ++ tailWord_3047943).sum := by decide
  have hdescent : baseEnd_3047943 < baseStart_3047943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047975 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3047975 : Nat := 118140960795 + 3047975 * 2 ^ 59
def prefixEnd_3047975 : Nat := 4983230072969 + 3 ^ 40 * 3047975 * 2
def baseEnd_3047975 : Nat := 1043384131925211678330083

theorem tailTrace_3047975 : CollatzResearch.WordTrace tailWord_3047975 prefixEnd_3047975 1043384131925211678330083 := by
  unfold tailWord_3047975
  simp only [CollatzResearch.WordTrace]
  refine ⟨111168781132714602531793379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74112520755143068354528919 111168781132714602531793379)
  ·
    refine ⟨166753171699071903797690069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111168781132714602531793379 166753171699071903797690069)
    ·
      refine ⟨3908277461696997745258361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166753171699071903797690069 3908277461696997745258361)
      ·
        refine ⟨2931208096272748308943771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3908277461696997745258361 2931208096272748308943771)
        ·
          refine ⟨4396812144409122463415657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931208096272748308943771 4396812144409122463415657)
          ·
            refine ⟨3297609108306841847561743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4396812144409122463415657 3297609108306841847561743)
            ·
              refine ⟨4946413662460262771342615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297609108306841847561743 4946413662460262771342615)
              ·
                refine ⟨7419620493690394157013923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4946413662460262771342615 7419620493690394157013923)
                ·
                  refine ⟨11129430740535591235520885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7419620493690394157013923 11129430740535591235520885)
                  ·
                    refine ⟨1043384131925211678330083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11129430740535591235520885 1043384131925211678330083)
                    ·
                      rfl

theorem cell22_3047975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3047975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047975 prefixEnd_3047975 := by exact prefixLift 3047975
  have htrace : WordTrace (prefixWord ++ tailWord_3047975) baseStart_3047975 baseEnd_3047975 := by
    simpa [prefixWord, tailWord_3047975, baseEnd_3047975] using wordTrace_append hprefix tailTrace_3047975
  have hstable : (prefixWord ++ tailWord_3047975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047975).length < 2 ^ (prefixWord ++ tailWord_3047975).sum := by decide
  have hdescent : baseEnd_3047975 < baseStart_3047975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047986 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3047986 : Nat := 118140960795 + 3047986 * 2 ^ 59
def prefixEnd_3047986 : Nat := 4983230072969 + 3 ^ 40 * 3047986 * 2
def baseEnd_3047986 : Nat := 1043387897450011316305049

theorem tailTrace_3047986 : CollatzResearch.WordTrace tailWord_3047986 prefixEnd_3047986 1043387897450011316305049 := by
  unfold tailWord_3047986
  simp only [CollatzResearch.WordTrace]
  refine ⟨27792295583918687852610953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74112788223783167606962541 27792295583918687852610953)
  ·
    refine ⟨20844221687939015889458215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27792295583918687852610953 20844221687939015889458215)
    ·
      refine ⟨31266332531908523834187323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20844221687939015889458215 31266332531908523834187323)
      ·
        refine ⟨46899498797862785751280985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31266332531908523834187323 46899498797862785751280985)
        ·
          refine ⟨35174624098397089313460739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46899498797862785751280985 35174624098397089313460739)
          ·
            refine ⟨52761936147595633970191109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35174624098397089313460739 52761936147595633970191109)
            ·
              refine ⟨9892863027674181369410833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52761936147595633970191109 9892863027674181369410833)
              ·
                refine ⟨7419647270755636027058125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9892863027674181369410833 7419647270755636027058125)
                ·
                  refine ⟨2782367726533363510146797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7419647270755636027058125 2782367726533363510146797)
                  ·
                    refine ⟨1043387897450011316305049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782367726533363510146797 1043387897450011316305049)
                    ·
                      rfl

theorem cell22_3047986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3047986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047986 prefixEnd_3047986 := by exact prefixLift 3047986
  have htrace : WordTrace (prefixWord ++ tailWord_3047986) baseStart_3047986 baseEnd_3047986 := by
    simpa [prefixWord, tailWord_3047986, baseEnd_3047986] using wordTrace_append hprefix tailTrace_3047986
  have hstable : (prefixWord ++ tailWord_3047986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047986).length < 2 ^ (prefixWord ++ tailWord_3047986).sum := by decide
  have hdescent : baseEnd_3047986 < baseStart_3047986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3047988 : List Nat := [2, 5, 1, 3, 1, 1, 1, 8]
def baseStart_3047988 : Nat := 118140960795 + 3047988 * 2 ^ 59
def prefixEnd_3047988 : Nat := 4983230072969 + 3 ^ 40 * 3047988 * 2
def baseEnd_3047988 : Nat := 115932064676764886417227

theorem tailTrace_3047988 : CollatzResearch.WordTrace tailWord_3047988 prefixEnd_3047988 115932064676764886417227 := by
  unfold tailWord_3047988
  simp only [CollatzResearch.WordTrace]
  refine ⟨55584627640833752876008309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74112836854445003834677745 55584627640833752876008309)
  ·
    refine ⟨5211058841328164332125779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55584627640833752876008309 5211058841328164332125779)
    ·
      refine ⟨7816588261992246498188669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5211058841328164332125779 7816588261992246498188669)
      ·
        refine ⟨2931220598247092436820751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7816588261992246498188669 2931220598247092436820751)
        ·
          refine ⟨4396830897370638655231127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931220598247092436820751 4396830897370638655231127)
          ·
            refine ⟨6595246346055957982846691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396830897370638655231127 6595246346055957982846691)
            ·
              refine ⟨9892869519083936974270037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6595246346055957982846691 9892869519083936974270037)
              ·
                refine ⟨115932064676764886417227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9892869519083936974270037 115932064676764886417227)
                ·
                  rfl

theorem cell22_3047988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_3047988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3047988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3047988 prefixEnd_3047988 := by exact prefixLift 3047988
  have htrace : WordTrace (prefixWord ++ tailWord_3047988) baseStart_3047988 baseEnd_3047988 := by
    simpa [prefixWord, tailWord_3047988, baseEnd_3047988] using wordTrace_append hprefix tailTrace_3047988
  have hstable : (prefixWord ++ tailWord_3047988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3047988).length < 2 ^ (prefixWord ++ tailWord_3047988).sum := by decide
  have hdescent : baseEnd_3047988 < baseStart_3047988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3047988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048014 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3048014 : Nat := 118140960795 + 3048014 * 2 ^ 59
def prefixEnd_3048014 : Nat := 4983230072969 + 3 ^ 40 * 3048014 * 2
def baseEnd_3048014 : Nat := 1043397482422228576604963

theorem tailTrace_3048014 : CollatzResearch.WordTrace tailWord_3048014 prefixEnd_3048014 1043397482422228576604963 := by
  unfold tailWord_3048014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13896275447446664024057887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74113469053048874794975397 13896275447446664024057887)
  ·
    refine ⟨20844413171169996036086831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13896275447446664024057887 20844413171169996036086831)
    ·
      refine ⟨31266619756754994054130247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20844413171169996036086831 31266619756754994054130247)
      ·
        refine ⟨46899929635132491081195371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31266619756754994054130247 46899929635132491081195371)
        ·
          refine ⟨70349894452698736621793057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46899929635132491081195371 70349894452698736621793057)
          ·
            refine ⟨52762420839524052466344793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70349894452698736621793057 52762420839524052466344793)
            ·
              refine ⟨39571815629643039349758595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52762420839524052466344793 39571815629643039349758595)
              ·
                refine ⟨59357723444464559024637893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39571815629643039349758595 59357723444464559024637893)
                ·
                  refine ⟨11129573145837104817119605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59357723444464559024637893 11129573145837104817119605)
                  ·
                    refine ⟨1043397482422228576604963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11129573145837104817119605 1043397482422228576604963)
                    ·
                      rfl

theorem cell22_3048014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3048014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048014 prefixEnd_3048014 := by exact prefixLift 3048014
  have htrace : WordTrace (prefixWord ++ tailWord_3048014) baseStart_3048014 baseEnd_3048014 := by
    simpa [prefixWord, tailWord_3048014, baseEnd_3048014] using wordTrace_append hprefix tailTrace_3048014
  have hstable : (prefixWord ++ tailWord_3048014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048014).length < 2 ^ (prefixWord ++ tailWord_3048014).sum := by decide
  have hdescent : baseEnd_3048014 < baseStart_3048014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048033 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 5]
def baseStart_3048033 : Nat := 118140960795 + 3048033 * 2 ^ 59
def prefixEnd_3048033 : Nat := 4983230072969 + 3 ^ 40 * 3048033 * 2
def baseEnd_3048033 : Nat := 347801328836839620126635

theorem tailTrace_3048033 : CollatzResearch.WordTrace tailWord_3048033 prefixEnd_3048033 347801328836839620126635 := by
  unfold tailWord_3048033
  simp only [CollatzResearch.WordTrace]
  refine ⟨111170896566504478437404753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74113931044336318958269835 111170896566504478437404753)
  ·
    refine ⟨83378172424878358828053565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111170896566504478437404753 83378172424878358828053565)
    ·
      refine ⟨31266814659329384560520087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83378172424878358828053565 31266814659329384560520087)
      ·
        refine ⟨46900221988994076840780131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31266814659329384560520087 46900221988994076840780131)
        ·
          refine ⟨70350332983491115261170197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46900221988994076840780131 70350332983491115261170197)
          ·
            refine ⟨3297671858601146027867353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70350332983491115261170197 3297671858601146027867353)
            ·
              refine ⟨2473253893950859520900515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3297671858601146027867353 2473253893950859520900515)
              ·
                refine ⟨3709880840926289281350773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473253893950859520900515 3709880840926289281350773)
                ·
                  refine ⟨347801328836839620126635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3709880840926289281350773 347801328836839620126635)
                  ·
                    rfl

theorem cell22_3048033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_3048033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048033 prefixEnd_3048033 := by exact prefixLift 3048033
  have htrace : WordTrace (prefixWord ++ tailWord_3048033) baseStart_3048033 baseEnd_3048033 := by
    simpa [prefixWord, tailWord_3048033, baseEnd_3048033] using wordTrace_append hprefix tailTrace_3048033
  have hstable : (prefixWord ++ tailWord_3048033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048033).length < 2 ^ (prefixWord ++ tailWord_3048033).sum := by decide
  have hdescent : baseEnd_3048033 < baseStart_3048033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048044 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_3048044 : Nat := 118140960795 + 3048044 * 2 ^ 59
def prefixEnd_3048044 : Nat := 4983230072969 + 3 ^ 40 * 3048044 * 2
def baseEnd_3048044 : Nat := 347802584011772832784957

theorem tailTrace_3048044 : CollatzResearch.WordTrace tailWord_3048044 prefixEnd_3048044 347802584011772832784957 := by
  unfold tailWord_3048044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55585648884732313658027593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74114198512976418210703457 55585648884732313658027593)
  ·
    refine ⟨41689236663549235243520695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55585648884732313658027593 41689236663549235243520695)
    ·
      refine ⟨62533854995323852865281043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41689236663549235243520695 62533854995323852865281043)
      ·
        refine ⟨93800782492985779297921565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62533854995323852865281043 93800782492985779297921565)
        ·
          refine ⟨35175293434869667236720587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93800782492985779297921565 35175293434869667236720587)
          ·
            refine ⟨52762940152304500855080881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35175293434869667236720587 52762940152304500855080881)
            ·
              refine ⟨39572205114228375641310661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52762940152304500855080881 39572205114228375641310661)
              ·
                refine ⟨7419788458917820432745749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39572205114228375641310661 7419788458917820432745749)
                ·
                  refine ⟨347802584011772832784957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7419788458917820432745749 347802584011772832784957)
                  ·
                    rfl

theorem cell22_3048044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_3048044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048044 prefixEnd_3048044 := by exact prefixLift 3048044
  have htrace : WordTrace (prefixWord ++ tailWord_3048044) baseStart_3048044 baseEnd_3048044 := by
    simpa [prefixWord, tailWord_3048044, baseEnd_3048044] using wordTrace_append hprefix tailTrace_3048044
  have hstable : (prefixWord ++ tailWord_3048044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048044).length < 2 ^ (prefixWord ++ tailWord_3048044).sum := by decide
  have hdescent : baseEnd_3048044 < baseStart_3048044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048078 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_3048078 : Nat := 118140960795 + 3048078 * 2 ^ 59
def prefixEnd_3048078 : Nat := 4983230072969 + 3 ^ 40 * 3048078 * 2
def baseEnd_3048078 : Nat := 347806463643384581001589

theorem tailTrace_3048078 : CollatzResearch.WordTrace tailWord_3048078 prefixEnd_3048078 347806463643384581001589 := by
  unfold tailWord_3048078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13896567231417681390349111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74115025234227634081861925 13896567231417681390349111)
  ·
    refine ⟨20844850847126522085523667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13896567231417681390349111 20844850847126522085523667)
    ·
      refine ⟨31267276270689783128285501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20844850847126522085523667 31267276270689783128285501)
      ·
        refine ⟨11725228601508668673107063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31267276270689783128285501 11725228601508668673107063)
        ·
          refine ⟨17587842902263003009660595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11725228601508668673107063 17587842902263003009660595)
          ·
            refine ⟨26381764353394504514490893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17587842902263003009660595 26381764353394504514490893)
            ·
              refine ⟨9893161632522939192934085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26381764353394504514490893 9893161632522939192934085)
              ·
                refine ⟨1854967806098051098675141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9893161632522939192934085 1854967806098051098675141)
                ·
                  refine ⟨347806463643384581001589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1854967806098051098675141 347806463643384581001589)
                  ·
                    rfl

theorem cell22_3048078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_3048078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048078 prefixEnd_3048078 := by exact prefixLift 3048078
  have htrace : WordTrace (prefixWord ++ tailWord_3048078) baseStart_3048078 baseEnd_3048078 := by
    simpa [prefixWord, tailWord_3048078, baseEnd_3048078] using wordTrace_append hprefix tailTrace_3048078
  have hstable : (prefixWord ++ tailWord_3048078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048078).length < 2 ^ (prefixWord ++ tailWord_3048078).sum := by decide
  have hdescent : baseEnd_3048078 < baseStart_3048078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048093 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3048093 : Nat := 118140960795 + 3048093 * 2 ^ 59
def prefixEnd_3048093 : Nat := 4983230072969 + 3 ^ 40 * 3048093 * 2
def baseEnd_3048093 : Nat := 1043424525736698703879721

theorem tailTrace_3048093 : CollatzResearch.WordTrace tailWord_3048093 prefixEnd_3048093 1043424525736698703879721 := by
  unfold tailWord_3048093
  simp only [CollatzResearch.WordTrace]
  refine ⟨111173084946287108684588933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74115389964191405789725955 111173084946287108684588933)
  ·
    refine ⟨20844953427428832878360425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111173084946287108684588933 20844953427428832878360425)
    ·
      refine ⟨15633715070571624658770319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20844953427428832878360425 15633715070571624658770319)
      ·
        refine ⟨23450572605857436988155479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15633715070571624658770319 23450572605857436988155479)
        ·
          refine ⟨35175858908786155482233219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23450572605857436988155479 35175858908786155482233219)
          ·
            refine ⟨52763788363179233223349829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35175858908786155482233219 52763788363179233223349829)
            ·
              refine ⟨9893210318096106229378093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52763788363179233223349829 9893210318096106229378093)
              ·
                refine ⟨3709953869286039836016785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9893210318096106229378093 3709953869286039836016785)
                ·
                  refine ⟨2782465401964529877012589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3709953869286039836016785 2782465401964529877012589)
                  ·
                    refine ⟨1043424525736698703879721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782465401964529877012589 1043424525736698703879721)
                    ·
                      rfl

theorem cell22_3048093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3048093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048093 prefixEnd_3048093 := by exact prefixLift 3048093
  have htrace : WordTrace (prefixWord ++ tailWord_3048093) baseStart_3048093 baseEnd_3048093 := by
    simpa [prefixWord, tailWord_3048093, baseEnd_3048093] using wordTrace_append hprefix tailTrace_3048093
  have hstable : (prefixWord ++ tailWord_3048093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048093).length < 2 ^ (prefixWord ++ tailWord_3048093).sum := by decide
  have hdescent : baseEnd_3048093 < baseStart_3048093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048121 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_3048121 : Nat := 118140960795 + 3048121 * 2 ^ 59
def prefixEnd_3048121 : Nat := 4983230072969 + 3 ^ 40 * 3048121 * 2
def baseEnd_3048121 : Nat := 1043434110708915964179635

theorem tailTrace_3048121 : CollatzResearch.WordTrace tailWord_3048121 prefixEnd_3048121 1043434110708915964179635 := by
  unfold tailWord_3048121
  simp only [CollatzResearch.WordTrace]
  refine ⟨111174106190185669466608217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74116070793457112977738811 111174106190185669466608217)
  ·
    refine ⟨83380579642639252099956163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111174106190185669466608217 83380579642639252099956163)
    ·
      refine ⟨125070869463958878149934245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83380579642639252099956163 125070869463958878149934245)
      ·
        refine ⟨23450788024492289653112671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125070869463958878149934245 23450788024492289653112671)
        ·
          refine ⟨35176182036738434479669007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23450788024492289653112671 35176182036738434479669007)
          ·
            refine ⟨52764273055107651719503511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35176182036738434479669007 52764273055107651719503511)
            ·
              refine ⟨79146409582661477579255267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52764273055107651719503511 79146409582661477579255267)
              ·
                refine ⟨118719614373992216368882901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79146409582661477579255267 118719614373992216368882901)
                ·
                  refine ⟨2782490961890442571145693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 118719614373992216368882901 2782490961890442571145693)
                  ·
                    refine ⟨1043434110708915964179635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782490961890442571145693 1043434110708915964179635)
                    ·
                      rfl

theorem cell22_3048121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_3048121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048121 prefixEnd_3048121 := by exact prefixLift 3048121
  have htrace : WordTrace (prefixWord ++ tailWord_3048121) baseStart_3048121 baseEnd_3048121 := by
    simpa [prefixWord, tailWord_3048121, baseEnd_3048121] using wordTrace_append hprefix tailTrace_3048121
  have hstable : (prefixWord ++ tailWord_3048121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048121).length < 2 ^ (prefixWord ++ tailWord_3048121).sum := by decide
  have hdescent : baseEnd_3048121 < baseStart_3048121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048138 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_3048138 : Nat := 118140960795 + 3048138 * 2 ^ 59
def prefixEnd_3048138 : Nat := 4983230072969 + 3 ^ 40 * 3048138 * 2
def baseEnd_3048138 : Nat := 1043439930156333586504583

theorem tailTrace_3048138 : CollatzResearch.WordTrace tailWord_3048138 prefixEnd_3048138 1043439930156333586504583 := by
  unfold tailWord_3048138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27793681557781020342494267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74116484154082720913318045 27793681557781020342494267)
  ·
    refine ⟨41690522336671530513741401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27793681557781020342494267 41690522336671530513741401)
    ·
      refine ⟨31267891752503647885306051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41690522336671530513741401 31267891752503647885306051)
      ·
        refine ⟨46901837628755471827959077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31267891752503647885306051 46901837628755471827959077)
        ·
          refine ⟨8794094555391650967742327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46901837628755471827959077 8794094555391650967742327)
          ·
            refine ⟨13191141833087476451613491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794094555391650967742327 13191141833087476451613491)
            ·
              refine ⟨19786712749631214677420237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13191141833087476451613491 19786712749631214677420237)
              ·
                refine ⟨7420017281111705504032589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19786712749631214677420237 7420017281111705504032589)
                ·
                  refine ⟨2782506480416889564012221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7420017281111705504032589 2782506480416889564012221)
                  ·
                    refine ⟨1043439930156333586504583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782506480416889564012221 1043439930156333586504583)
                    ·
                      rfl

theorem cell22_3048138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_3048138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048138 prefixEnd_3048138 := by exact prefixLift 3048138
  have htrace : WordTrace (prefixWord ++ tailWord_3048138) baseStart_3048138 baseEnd_3048138 := by
    simpa [prefixWord, tailWord_3048138, baseEnd_3048138] using wordTrace_append hprefix tailTrace_3048138
  have hstable : (prefixWord ++ tailWord_3048138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048138).length < 2 ^ (prefixWord ++ tailWord_3048138).sum := by decide
  have hdescent : baseEnd_3048138 < baseStart_3048138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048211 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_3048211 : Nat := 118140960795 + 3048211 * 2 ^ 59
def prefixEnd_3048211 : Nat := 4983230072969 + 3 ^ 40 * 3048211 * 2
def baseEnd_3048211 : Nat := 1043464919548185729429359

theorem tailTrace_3048211 : CollatzResearch.WordTrace tailWord_3048211 prefixEnd_3048211 1043464919548185729429359 := by
  unfold tailWord_3048211
  simp only [CollatzResearch.WordTrace]
  refine ⟨111177388759859614837384487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74118259173239743224922991 111177388759859614837384487)
  ·
    refine ⟨166766083139789422256076731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111177388759859614837384487 166766083139789422256076731)
    ·
      refine ⟨250149124709684133384115097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166766083139789422256076731 250149124709684133384115097)
      ·
        refine ⟨187611843532263100038086323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250149124709684133384115097 187611843532263100038086323)
        ·
          refine ⟨281417765298394650057129485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187611843532263100038086323 281417765298394650057129485)
          ·
            refine ⟨105531661986897993771423557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281417765298394650057129485 105531661986897993771423557)
            ·
              refine ⟨19787186622543373832141917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105531661986897993771423557 19787186622543373832141917)
              ·
                refine ⟨7420194983453765187053219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19787186622543373832141917 7420194983453765187053219)
                ·
                  refine ⟨11130292475180647780579829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7420194983453765187053219 11130292475180647780579829)
                  ·
                    refine ⟨1043464919548185729429359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11130292475180647780579829 1043464919548185729429359)
                    ·
                      rfl

theorem cell22_3048211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_3048211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048211 prefixEnd_3048211 := by exact prefixLift 3048211
  have htrace : WordTrace (prefixWord ++ tailWord_3048211) baseStart_3048211 baseEnd_3048211 := by
    simpa [prefixWord, tailWord_3048211, baseEnd_3048211] using wordTrace_append hprefix tailTrace_3048211
  have hstable : (prefixWord ++ tailWord_3048211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048211).length < 2 ^ (prefixWord ++ tailWord_3048211).sum := by decide
  have hdescent : baseEnd_3048211 < baseStart_3048211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048243 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_3048243 : Nat := 118140960795 + 3048243 * 2 ^ 59
def prefixEnd_3048243 : Nat := 4983230072969 + 3 ^ 40 * 3048243 * 2
def baseEnd_3048243 : Nat := 1043475873802148312629261

theorem tailTrace_3048243 : CollatzResearch.WordTrace tailWord_3048243 prefixEnd_3048243 1043475873802148312629261 := by
  unfold tailWord_3048243
  simp only [CollatzResearch.WordTrace]
  refine ⟨111178555895743684302549383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74119037263829122868366255 111178555895743684302549383)
  ·
    refine ⟨166767833843615526453824075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111178555895743684302549383 166767833843615526453824075)
    ·
      refine ⟨250151750765423289680736113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166767833843615526453824075 250151750765423289680736113)
      ·
        refine ⟨187613813074067467260552085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250151750765423289680736113 187613813074067467260552085)
        ·
          refine ⟨8794397487846912527838379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187613813074067467260552085 8794397487846912527838379)
          ·
            refine ⟨13191596231770368791757569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794397487846912527838379 13191596231770368791757569)
            ·
              refine ⟨9893697173827776593818177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13191596231770368791757569 9893697173827776593818177)
              ·
                refine ⟨7420272880370832445363633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9893697173827776593818177 7420272880370832445363633)
                ·
                  refine ⟨5565204660278124334022725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420272880370832445363633 5565204660278124334022725)
                  ·
                    refine ⟨1043475873802148312629261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5565204660278124334022725 1043475873802148312629261)
                    ·
                      rfl

theorem cell22_3048243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_3048243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048243 prefixEnd_3048243 := by exact prefixLift 3048243
  have htrace : WordTrace (prefixWord ++ tailWord_3048243) baseStart_3048243 baseEnd_3048243 := by
    simpa [prefixWord, tailWord_3048243, baseEnd_3048243] using wordTrace_append hprefix tailTrace_3048243
  have hstable : (prefixWord ++ tailWord_3048243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048243).length < 2 ^ (prefixWord ++ tailWord_3048243).sum := by decide
  have hdescent : baseEnd_3048243 < baseStart_3048243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048245 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_3048245 : Nat := 118140960795 + 3048245 * 2 ^ 59
def prefixEnd_3048245 : Nat := 4983230072969 + 3 ^ 40 * 3048245 * 2
def baseEnd_3048245 : Nat := 1043476558443020974079255

theorem tailTrace_3048245 : CollatzResearch.WordTrace tailWord_3048245 prefixEnd_3048245 1043476558443020974079255 := by
  unfold tailWord_3048245
  simp only [CollatzResearch.WordTrace]
  refine ⟨111178628841736438644122189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74119085894490959096081459 111178628841736438644122189)
  ·
    refine ⟨41691985815651164491545821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111178628841736438644122189 41691985815651164491545821)
    ·
      refine ⟨15634494680869186684329683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41691985815651164491545821 15634494680869186684329683)
      ·
        refine ⟨23451742021303780026494525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15634494680869186684329683 23451742021303780026494525)
        ·
          refine ⟨8794403257988917509935447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23451742021303780026494525 8794403257988917509935447)
          ·
            refine ⟨13191604886983376264903171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8794403257988917509935447 13191604886983376264903171)
            ·
              refine ⟨19787407330475064397354757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13191604886983376264903171 19787407330475064397354757)
              ·
                refine ⟨3710138874464074574504017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19787407330475064397354757 3710138874464074574504017)
                ·
                  refine ⟨2782604155848055930878013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710138874464074574504017 2782604155848055930878013)
                  ·
                    refine ⟨1043476558443020974079255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782604155848055930878013 1043476558443020974079255)
                    ·
                      rfl

theorem cell22_3048245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_3048245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048245 prefixEnd_3048245 := by exact prefixLift 3048245
  have htrace : WordTrace (prefixWord ++ tailWord_3048245) baseStart_3048245 baseEnd_3048245 := by
    simpa [prefixWord, tailWord_3048245, baseEnd_3048245] using wordTrace_append hprefix tailTrace_3048245
  have hstable : (prefixWord ++ tailWord_3048245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048245).length < 2 ^ (prefixWord ++ tailWord_3048245).sum := by decide
  have hdescent : baseEnd_3048245 < baseStart_3048245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048378 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_3048378 : Nat := 118140960795 + 3048378 * 2 ^ 59
def prefixEnd_3048378 : Nat := 4983230072969 + 3 ^ 40 * 3048378 * 2
def baseEnd_3048378 : Nat := 1043522087061052960503847

theorem tailTrace_3048378 : CollatzResearch.WordTrace tailWord_3048378 prefixEnd_3048378 1043522087061052960503847 := by
  unfold tailWord_3048378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27795869937563650589678447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74122319833503068239142525 27795869937563650589678447)
  ·
    refine ⟨41693804906345475884517671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27795869937563650589678447 41693804906345475884517671)
    ·
      refine ⟨62540707359518213826776507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41693804906345475884517671 62540707359518213826776507)
      ·
        refine ⟨93811061039277320740164761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62540707359518213826776507 93811061039277320740164761)
        ·
          refine ⟨70358295779457990555123571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93811061039277320740164761 70358295779457990555123571)
          ·
            refine ⟨105537443669186985832685357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70358295779457990555123571 105537443669186985832685357)
            ·
              refine ⟨39576541375945119687257009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105537443669186985832685357 39576541375945119687257009)
              ·
                refine ⟨29682406031958839765442757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39576541375945119687257009 29682406031958839765442757)
                ·
                  refine ⟨5565451130992282456020517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29682406031958839765442757 5565451130992282456020517)
                  ·
                    refine ⟨1043522087061052960503847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5565451130992282456020517 1043522087061052960503847)
                    ·
                      rfl

theorem cell22_3048378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_3048378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048378 prefixEnd_3048378 := by exact prefixLift 3048378
  have htrace : WordTrace (prefixWord ++ tailWord_3048378) baseStart_3048378 baseEnd_3048378 := by
    simpa [prefixWord, tailWord_3048378, baseEnd_3048378] using wordTrace_append hprefix tailTrace_3048378
  have hstable : (prefixWord ++ tailWord_3048378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048378).length < 2 ^ (prefixWord ++ tailWord_3048378).sum := by decide
  have hdescent : baseEnd_3048378 < baseStart_3048378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048395 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 2, 4]
def baseStart_3048395 : Nat := 118140960795 + 3048395 * 2 ^ 59
def prefixEnd_3048395 : Nat := 4983230072969 + 3 ^ 40 * 3048395 * 2
def baseEnd_3048395 : Nat := 1043527906508470582828795

theorem tailTrace_3048395 : CollatzResearch.WordTrace tailWord_3048395 prefixEnd_3048395 1043527906508470582828795 := by
  unfold tailWord_3048395
  simp only [CollatzResearch.WordTrace]
  refine ⟨111184099791193014262082639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74122733194128676174721759 111184099791193014262082639)
  ·
    refine ⟨166776149686789521393123959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111184099791193014262082639 166776149686789521393123959)
    ·
      refine ⟨250164224530184282089685939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166776149686789521393123959 250164224530184282089685939)
      ·
        refine ⟨375246336795276423134528909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250164224530184282089685939 375246336795276423134528909)
        ·
          refine ⟨140717376298228658675448341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375246336795276423134528909 140717376298228658675448341)
          ·
            refine ⟨6596127013979468375411641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140717376298228658675448341 6596127013979468375411641)
            ·
              refine ⟨4947095260484601281558731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596127013979468375411641 4947095260484601281558731)
              ·
                refine ⟨7420642890726901922338097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947095260484601281558731 7420642890726901922338097)
                ·
                  refine ⟨5565482168045176441753573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420642890726901922338097 5565482168045176441753573)
                  ·
                    refine ⟨1043527906508470582828795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5565482168045176441753573 1043527906508470582828795)
                    ·
                      rfl

theorem cell22_3048395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_3048395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048395 prefixEnd_3048395 := by exact prefixLift 3048395
  have htrace : WordTrace (prefixWord ++ tailWord_3048395) baseStart_3048395 baseEnd_3048395 := by
    simpa [prefixWord, tailWord_3048395, baseEnd_3048395] using wordTrace_append hprefix tailTrace_3048395
  have hstable : (prefixWord ++ tailWord_3048395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048395).length < 2 ^ (prefixWord ++ tailWord_3048395).sum := by decide
  have hdescent : baseEnd_3048395 < baseStart_3048395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048446 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3048446 : Nat := 118140960795 + 3048446 * 2 ^ 59
def prefixEnd_3048446 : Nat := 4983230072969 + 3 ^ 40 * 3048446 * 2
def baseEnd_3048446 : Nat := 1043545364850723449803639

theorem tailTrace_3048446 : CollatzResearch.WordTrace tailWord_3048446 prefixEnd_3048446 1043545364850723449803639 := by
  unfold tailWord_3048446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13898244989251031246523649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74123973276005499981459461 13898244989251031246523649)
  ·
    refine ⟨10423683741938273434892737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13898244989251031246523649 10423683741938273434892737)
    ·
      refine ⟨7817762806453705076169553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10423683741938273434892737 7817762806453705076169553)
      ·
        refine ⟨5863322104840278807127165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7817762806453705076169553 5863322104840278807127165)
        ·
          refine ⟨2198745789315104552672687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5863322104840278807127165 2198745789315104552672687)
          ·
            refine ⟨3298118683972656829009031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198745789315104552672687 3298118683972656829009031)
            ·
              refine ⟨4947178025958985243513547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298118683972656829009031 4947178025958985243513547)
              ·
                refine ⟨7420767038938477865270321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947178025958985243513547 7420767038938477865270321)
                ·
                  refine ⟨5565575279203858398952741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7420767038938477865270321 5565575279203858398952741)
                  ·
                    refine ⟨1043545364850723449803639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5565575279203858398952741 1043545364850723449803639)
                    ·
                      rfl

theorem cell22_3048446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3048446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048446 prefixEnd_3048446 := by exact prefixLift 3048446
  have htrace : WordTrace (prefixWord ++ tailWord_3048446) baseStart_3048446 baseEnd_3048446 := by
    simpa [prefixWord, tailWord_3048446, baseEnd_3048446] using wordTrace_append hprefix tailTrace_3048446
  have hstable : (prefixWord ++ tailWord_3048446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048446).length < 2 ^ (prefixWord ++ tailWord_3048446).sum := by decide
  have hdescent : baseEnd_3048446 < baseStart_3048446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048453 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_3048453 : Nat := 118140960795 + 3048453 * 2 ^ 59
def prefixEnd_3048453 : Nat := 4983230072969 + 3 ^ 40 * 3048453 * 2
def baseEnd_3048453 : Nat := 1043547761093777764878617

theorem tailTrace_3048453 : CollatzResearch.WordTrace tailWord_3048453 prefixEnd_3048453 1043547761093777764878617 := by
  unfold tailWord_3048453
  simp only [CollatzResearch.WordTrace]
  refine ⟨111186215224982890167694013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74124143483321926778462675 111186215224982890167694013)
  ·
    refine ⟨41694830709368583812885255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111186215224982890167694013 41694830709368583812885255)
    ·
      refine ⟨62542246064052875719327883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41694830709368583812885255 62542246064052875719327883)
      ·
        refine ⟨93813369096079313578991825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62542246064052875719327883 93813369096079313578991825)
        ·
          refine ⟨70360026822059485184243869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93813369096079313578991825 70360026822059485184243869)
          ·
            refine ⟨26385010058272306944091451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70360026822059485184243869 26385010058272306944091451)
            ·
              refine ⟨39577515087408460416137177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26385010058272306944091451 39577515087408460416137177)
              ·
                refine ⟨29683136315556345312102883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39577515087408460416137177 29683136315556345312102883)
                ·
                  refine ⟨44524704473334517968154325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29683136315556345312102883 44524704473334517968154325)
                  ·
                    refine ⟨1043547761093777764878617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44524704473334517968154325 1043547761093777764878617)
                    ·
                      rfl

theorem cell22_3048453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_3048453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048453 prefixEnd_3048453 := by exact prefixLift 3048453
  have htrace : WordTrace (prefixWord ++ tailWord_3048453) baseStart_3048453 baseEnd_3048453 := by
    simpa [prefixWord, tailWord_3048453, baseEnd_3048453] using wordTrace_append hprefix tailTrace_3048453
  have hstable : (prefixWord ++ tailWord_3048453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048453).length < 2 ^ (prefixWord ++ tailWord_3048453).sum := by decide
  have hdescent : baseEnd_3048453 < baseStart_3048453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048459 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 1, 3]
def baseStart_3048459 : Nat := 118140960795 + 3048459 * 2 ^ 59
def prefixEnd_3048459 : Nat := 4983230072969 + 3 ^ 40 * 3048459 * 2
def baseEnd_3048459 : Nat := 1043549815016395749228599

theorem tailTrace_3048459 : CollatzResearch.WordTrace tailWord_3048459 prefixEnd_3048459 1043549815016395749228599 := by
  unfold tailWord_3048459
  simp only [CollatzResearch.WordTrace]
  refine ⟨111186434062961153192412431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74124289375307435461608287 111186434062961153192412431)
  ·
    refine ⟨166779651094441729788618647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111186434062961153192412431 166779651094441729788618647)
    ·
      refine ⟨250169476641662594682927971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166779651094441729788618647 250169476641662594682927971)
      ·
        refine ⟨375254214962493892024391957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250169476641662594682927971 375254214962493892024391957)
        ·
          refine ⟨17590041326366901188643373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 375254214962493892024391957 17590041326366901188643373)
          ·
            refine ⟨6596265497387587945741265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17590041326366901188643373 6596265497387587945741265)
            ·
              refine ⟨4947199123040690959305949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6596265497387587945741265 4947199123040690959305949)
              ·
                refine ⟨1855199671140259109739731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4947199123040690959305949 1855199671140259109739731)
                ·
                  refine ⟨2782799506710388664609597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855199671140259109739731 2782799506710388664609597)
                  ·
                    refine ⟨1043549815016395749228599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782799506710388664609597 1043549815016395749228599)
                    ·
                      rfl

theorem cell22_3048459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 1, 3].length) (baseStart_3048459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048459 prefixEnd_3048459 := by exact prefixLift 3048459
  have htrace : WordTrace (prefixWord ++ tailWord_3048459) baseStart_3048459 baseEnd_3048459 := by
    simpa [prefixWord, tailWord_3048459, baseEnd_3048459] using wordTrace_append hprefix tailTrace_3048459
  have hstable : (prefixWord ++ tailWord_3048459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048459).length < 2 ^ (prefixWord ++ tailWord_3048459).sum := by decide
  have hdescent : baseEnd_3048459 < baseStart_3048459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048472 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_3048472 : Nat := 118140960795 + 3048472 * 2 ^ 59
def prefixEnd_3048472 : Nat := 4983230072969 + 3 ^ 40 * 3048472 * 2
def baseEnd_3048472 : Nat := 347851421727356016217853

theorem tailTrace_3048472 : CollatzResearch.WordTrace tailWord_3048472 prefixEnd_3048472 347851421727356016217853 := by
  unfold tailWord_3048472
  simp only [CollatzResearch.WordTrace]
  refine ⟨55593454105957028206317835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74124605474609370941757113 55593454105957028206317835)
  ·
    refine ⟨83390181158935542309476753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55593454105957028206317835 83390181158935542309476753)
    ·
      refine ⟨62542635869201656732107565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83390181158935542309476753 62542635869201656732107565)
      ·
        refine ⟨23453488450950621274540337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62542635869201656732107565 23453488450950621274540337)
        ·
          refine ⟨17590116338212965955905253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23453488450950621274540337 17590116338212965955905253)
          ·
            refine ⟨3298146813414931116732235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17590116338212965955905253 3298146813414931116732235)
            ·
              refine ⟨4947220220122396675098353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298146813414931116732235 4947220220122396675098353)
              ·
                refine ⟨3710415165091797506323765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4947220220122396675098353 3710415165091797506323765)
                ·
                  refine ⟨347851421727356016217853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3710415165091797506323765 347851421727356016217853)
                  ·
                    rfl

theorem cell22_3048472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_3048472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048472 prefixEnd_3048472 := by exact prefixLift 3048472
  have htrace : WordTrace (prefixWord ++ tailWord_3048472) baseStart_3048472 baseEnd_3048472 := by
    simpa [prefixWord, tailWord_3048472, baseEnd_3048472] using wordTrace_append hprefix tailTrace_3048472
  have hstable : (prefixWord ++ tailWord_3048472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048472).length < 2 ^ (prefixWord ++ tailWord_3048472).sum := by decide
  have hdescent : baseEnd_3048472 < baseStart_3048472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048487 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3048487 : Nat := 118140960795 + 3048487 * 2 ^ 59
def prefixEnd_3048487 : Nat := 4983230072969 + 3 ^ 40 * 3048487 * 2
def baseEnd_3048487 : Nat := 1043559399988613009528513

theorem tailTrace_3048487 : CollatzResearch.WordTrace tailWord_3048487 prefixEnd_3048487 1043559399988613009528513 := by
  unfold tailWord_3048487
  simp only [CollatzResearch.WordTrace]
  refine ⟨111187455306859713974431715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74124970204573142649621143 111187455306859713974431715)
  ·
    refine ⟨166781182960289570961647573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111187455306859713974431715 166781182960289570961647573)
    ·
      refine ⟨3908933975631786819413615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166781182960289570961647573 3908933975631786819413615)
      ·
        refine ⟨5863400963447680229120423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3908933975631786819413615 5863400963447680229120423)
        ·
          refine ⟨8795101445171520343680635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863400963447680229120423 8795101445171520343680635)
          ·
            refine ⟨13192652167757280515520953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8795101445171520343680635 13192652167757280515520953)
            ·
              refine ⟨9894489125817960386640715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13192652167757280515520953 9894489125817960386640715)
              ·
                refine ⟨14841733688726940579961073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894489125817960386640715 14841733688726940579961073)
                ·
                  refine ⟨11131300266545205434970805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14841733688726940579961073 11131300266545205434970805)
                  ·
                    refine ⟨1043559399988613009528513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11131300266545205434970805 1043559399988613009528513)
                    ·
                      rfl

theorem cell22_3048487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3048487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048487 prefixEnd_3048487 := by exact prefixLift 3048487
  have htrace : WordTrace (prefixWord ++ tailWord_3048487) baseStart_3048487 baseEnd_3048487 := by
    simpa [prefixWord, tailWord_3048487, baseEnd_3048487] using wordTrace_append hprefix tailTrace_3048487
  have hstable : (prefixWord ++ tailWord_3048487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048487).length < 2 ^ (prefixWord ++ tailWord_3048487).sum := by decide
  have hdescent : baseEnd_3048487 < baseStart_3048487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048515 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 6, 3]
def baseStart_3048515 : Nat := 118140960795 + 3048515 * 2 ^ 59
def prefixEnd_3048515 : Nat := 4983230072969 + 3 ^ 40 * 3048515 * 2
def baseEnd_3048515 : Nat := 1043568984960830269828427

theorem tailTrace_3048515 : CollatzResearch.WordTrace tailWord_3048515 prefixEnd_3048515 1043568984960830269828427 := by
  unfold tailWord_3048515
  simp only [CollatzResearch.WordTrace]
  refine ⟨111188476550758274756450999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74125651033838849837633999 111188476550758274756450999)
  ·
    refine ⟨166782714826137412134676499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111188476550758274756450999 166782714826137412134676499)
    ·
      refine ⟨250174072239206118202014749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166782714826137412134676499 250174072239206118202014749)
      ·
        refine ⟨93815277089702294325755531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250174072239206118202014749 93815277089702294325755531)
        ·
          refine ⟨140722915634553441488633297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93815277089702294325755531 140722915634553441488633297)
          ·
            refine ⟨105542186725915081116474973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140722915634553441488633297 105542186725915081116474973)
            ·
              refine ⟨39578320022218155418678115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105542186725915081116474973 39578320022218155418678115)
              ·
                refine ⟨59367480033327233128017173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39578320022218155418678115 59367480033327233128017173)
                ·
                  refine ⟨2782850626562214052875805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59367480033327233128017173 2782850626562214052875805)
                  ·
                    refine ⟨1043568984960830269828427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782850626562214052875805 1043568984960830269828427)
                    ·
                      rfl

theorem cell22_3048515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3].length) (baseStart_3048515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048515 prefixEnd_3048515 := by exact prefixLift 3048515
  have htrace : WordTrace (prefixWord ++ tailWord_3048515) baseStart_3048515 baseEnd_3048515 := by
    simpa [prefixWord, tailWord_3048515, baseEnd_3048515] using wordTrace_append hprefix tailTrace_3048515
  have hstable : (prefixWord ++ tailWord_3048515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048515).length < 2 ^ (prefixWord ++ tailWord_3048515).sum := by decide
  have hdescent : baseEnd_3048515 < baseStart_3048515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048517 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 4]
def baseStart_3048517 : Nat := 118140960795 + 3048517 * 2 ^ 59
def prefixEnd_3048517 : Nat := 4983230072969 + 3 ^ 40 * 3048517 * 2
def baseEnd_3048517 : Nat := 347856556533900977092807

theorem tailTrace_3048517 : CollatzResearch.WordTrace tailWord_3048517 prefixEnd_3048517 347856556533900977092807 := by
  unfold tailWord_3048517
  simp only [CollatzResearch.WordTrace]
  refine ⟨111188549496751029098023805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74125699664500686065349203 111188549496751029098023805)
  ·
    refine ⟨41695706061281635911758927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111188549496751029098023805 41695706061281635911758927)
    ·
      refine ⟨62543559091922453867638391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41695706061281635911758927 62543559091922453867638391)
      ·
        refine ⟨93815338637883680801457587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62543559091922453867638391 93815338637883680801457587)
        ·
          refine ⟨140723007956825521202186381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93815338637883680801457587 140723007956825521202186381)
          ·
            refine ⟨52771127983809570450819893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140723007956825521202186381 52771127983809570450819893)
            ·
              refine ⟨4947293248482147229764365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52771127983809570450819893 4947293248482147229764365)
              ·
                refine ⟨1855234968180805211161637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4947293248482147229764365 1855234968180805211161637)
                ·
                  refine ⟨347856556533900977092807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855234968180805211161637 347856556533900977092807)
                  ·
                    rfl

theorem cell22_3048517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_3048517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048517 prefixEnd_3048517 := by exact prefixLift 3048517
  have htrace : WordTrace (prefixWord ++ tailWord_3048517) baseStart_3048517 baseEnd_3048517 := by
    simpa [prefixWord, tailWord_3048517, baseEnd_3048517] using wordTrace_append hprefix tailTrace_3048517
  have hstable : (prefixWord ++ tailWord_3048517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048517).length < 2 ^ (prefixWord ++ tailWord_3048517).sum := by decide
  have hdescent : baseEnd_3048517 < baseStart_3048517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048532 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3048532 : Nat := 118140960795 + 3048532 * 2 ^ 59
def prefixEnd_3048532 : Nat := 4983230072969 + 3 ^ 40 * 3048532 * 2
def baseEnd_3048532 : Nat := 1043574804408247892153375

theorem tailTrace_3048532 : CollatzResearch.WordTrace tailWord_3048532 prefixEnd_3048532 1043574804408247892153375 := by
  unfold tailWord_3048532
  simp only [CollatzResearch.WordTrace]
  refine ⟨55594548295848343329909925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74126064394464457773213233 55594548295848343329909925)
  ·
    refine ⟨10423977805471564374358111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55594548295848343329909925 10423977805471564374358111)
    ·
      refine ⟨15635966708207346561537167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10423977805471564374358111 15635966708207346561537167)
      ·
        refine ⟨23453950062311019842305751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15635966708207346561537167 23453950062311019842305751)
        ·
          refine ⟨35180925093466529763458627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23453950062311019842305751 35180925093466529763458627)
          ·
            refine ⟨52771387640199794645187941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35180925093466529763458627 52771387640199794645187941)
            ·
              refine ⟨9894635182537461495972739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52771387640199794645187941 9894635182537461495972739)
              ·
                refine ⟨14841952773806192243959109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9894635182537461495972739 14841952773806192243959109)
                ·
                  refine ⟨2782866145088661045742333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14841952773806192243959109 2782866145088661045742333)
                  ·
                    refine ⟨1043574804408247892153375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2782866145088661045742333 1043574804408247892153375)
                    ·
                      rfl

theorem cell22_3048532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3048532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048532 prefixEnd_3048532 := by exact prefixLift 3048532
  have htrace : WordTrace (prefixWord ++ tailWord_3048532) baseStart_3048532 baseEnd_3048532 := by
    simpa [prefixWord, tailWord_3048532, baseEnd_3048532] using wordTrace_append hprefix tailTrace_3048532
  have hstable : (prefixWord ++ tailWord_3048532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048532).length < 2 ^ (prefixWord ++ tailWord_3048532).sum := by decide
  have hdescent : baseEnd_3048532 < baseStart_3048532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048641 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 5]
def baseStart_3048641 : Nat := 118140960795 + 3048641 * 2 ^ 59
def prefixEnd_3048641 : Nat := 4983230072969 + 3 ^ 40 * 3048641 * 2
def baseEnd_3048641 : Nat := 347870705778602647059347

theorem tailTrace_3048641 : CollatzResearch.WordTrace tailWord_3048641 prefixEnd_3048641 347870705778602647059347 := by
  unfold tailWord_3048641
  simp only [CollatzResearch.WordTrace]
  refine ⟨111193072148301798275537777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74128714765534532183691851 111193072148301798275537777)
  ·
    refine ⟨83394804111226348706653333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111193072148301798275537777 83394804111226348706653333)
    ·
      refine ⟨3909131442713735095624375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83394804111226348706653333 3909131442713735095624375)
      ·
        refine ⟨5863697164070602643436563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909131442713735095624375 5863697164070602643436563)
        ·
          refine ⟨8795545746105903965154845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863697164070602643436563 8795545746105903965154845)
          ·
            refine ⟨3298329654789713986933067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8795545746105903965154845 3298329654789713986933067)
            ·
              refine ⟨4947494482184570980399601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298329654789713986933067 4947494482184570980399601)
              ·
                refine ⟨3710620861638428235299701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4947494482184570980399601 3710620861638428235299701)
                ·
                  refine ⟨347870705778602647059347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3710620861638428235299701 347870705778602647059347)
                  ·
                    rfl

theorem cell22_3048641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_3048641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048641 prefixEnd_3048641 := by exact prefixLift 3048641
  have htrace : WordTrace (prefixWord ++ tailWord_3048641) baseStart_3048641 baseEnd_3048641 := by
    simpa [prefixWord, tailWord_3048641, baseEnd_3048641] using wordTrace_append hprefix tailTrace_3048641
  have hstable : (prefixWord ++ tailWord_3048641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048641).length < 2 ^ (prefixWord ++ tailWord_3048641).sum := by decide
  have hdescent : baseEnd_3048641 < baseStart_3048641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048682 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3048682 : Nat := 118140960795 + 3048682 * 2 ^ 59
def prefixEnd_3048682 : Nat := 4983230072969 + 3 ^ 40 * 3048682 * 2
def baseEnd_3048682 : Nat := 1043626152473697500902915

theorem tailTrace_3048682 : CollatzResearch.WordTrace tailWord_3048682 prefixEnd_3048682 1043626152473697500902915 := by
  unfold tailWord_3048682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27798641885288315569445075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74129711694102174851853533 27798641885288315569445075)
  ·
    refine ⟨41697962827932473354167613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27798641885288315569445075 41697962827932473354167613)
    ·
      refine ⟨15636736060474677507812855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41697962827932473354167613 15636736060474677507812855)
      ·
        refine ⟨23455104090712016261719283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15636736060474677507812855 23455104090712016261719283)
        ·
          refine ⟨35182656136068024392578925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23455104090712016261719283 35182656136068024392578925)
          ·
            refine ⟨13193496051025509147217097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35182656136068024392578925 13193496051025509147217097)
            ·
              refine ⟨9895122038269131860412823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13193496051025509147217097 9895122038269131860412823)
              ·
                refine ⟨14842683057403697790619235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895122038269131860412823 14842683057403697790619235)
                ·
                  refine ⟨22264024586105546685928853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14842683057403697790619235 22264024586105546685928853)
                  ·
                    refine ⟨1043626152473697500902915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22264024586105546685928853 1043626152473697500902915)
                    ·
                      rfl

theorem cell22_3048682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3048682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048682 prefixEnd_3048682 := by exact prefixLift 3048682
  have htrace : WordTrace (prefixWord ++ tailWord_3048682) baseStart_3048682 baseEnd_3048682 := by
    simpa [prefixWord, tailWord_3048682, baseEnd_3048682] using wordTrace_append hprefix tailTrace_3048682
  have hstable : (prefixWord ++ tailWord_3048682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048682).length < 2 ^ (prefixWord ++ tailWord_3048682).sum := by decide
  have hdescent : baseEnd_3048682 < baseStart_3048682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048695 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3048695 : Nat := 118140960795 + 3048695 * 2 ^ 59
def prefixEnd_3048695 : Nat := 4983230072969 + 3 ^ 40 * 3048695 * 2
def baseEnd_3048695 : Nat := 1043630602639369800327875

theorem tailTrace_3048695 : CollatzResearch.WordTrace tailWord_3048695 prefixEnd_3048695 1043630602639369800327875 := by
  unfold tailWord_3048695
  simp only [CollatzResearch.WordTrace]
  refine ⟨111195041690106165498003539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74130027793404110332002359 111195041690106165498003539)
  ·
    refine ⟨166792562535159248247005309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111195041690106165498003539 166792562535159248247005309)
    ·
      refine ⟨62547210950684718092626991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166792562535159248247005309 62547210950684718092626991)
      ·
        refine ⟨93820816426027077138940487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62547210950684718092626991 93820816426027077138940487)
        ·
          refine ⟨140731224639040615708410731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93820816426027077138940487 140731224639040615708410731)
          ·
            refine ⟨211096836958560923562616097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140731224639040615708410731 211096836958560923562616097)
            ·
              refine ⟨158322627718920692671962073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211096836958560923562616097 158322627718920692671962073)
              ·
                refine ⟨118741970789190519503971555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158322627718920692671962073 118741970789190519503971555)
                ·
                  refine ⟨178112956183785779255957333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118741970789190519503971555 178112956183785779255957333)
                  ·
                    refine ⟨1043630602639369800327875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178112956183785779255957333 1043630602639369800327875)
                    ·
                      rfl

theorem cell22_3048695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3048695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048695 prefixEnd_3048695 := by exact prefixLift 3048695
  have htrace : WordTrace (prefixWord ++ tailWord_3048695) baseStart_3048695 baseEnd_3048695 := by
    simpa [prefixWord, tailWord_3048695, baseEnd_3048695] using wordTrace_append hprefix tailTrace_3048695
  have hstable : (prefixWord ++ tailWord_3048695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048695).length < 2 ^ (prefixWord ++ tailWord_3048695).sum := by decide
  have hdescent : baseEnd_3048695 < baseStart_3048695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048718 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3048718 : Nat := 118140960795 + 3048718 * 2 ^ 59
def prefixEnd_3048718 : Nat := 4983230072969 + 3 ^ 40 * 3048718 * 2
def baseEnd_3048718 : Nat := 1043638476009405407002805

theorem tailTrace_3048718 : CollatzResearch.WordTrace tailWord_3048718 prefixEnd_3048718 1043638476009405407002805 := by
  unfold tailWord_3048718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899485071127855053261351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74130587046015226950727205 13899485071127855053261351)
  ·
    refine ⟨20849227606691782579892027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13899485071127855053261351 20849227606691782579892027)
    ·
      refine ⟨31273841410037673869838041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20849227606691782579892027 31273841410037673869838041)
      ·
        refine ⟨23455381057528255402378531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31273841410037673869838041 23455381057528255402378531)
        ·
          refine ⟨35183071586292383103567797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23455381057528255402378531 35183071586292383103567797)
          ·
            refine ⟨3298412961214910915959481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35183071586292383103567797 3298412961214910915959481)
            ·
              refine ⟨2473809720911183186969611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298412961214910915959481 2473809720911183186969611)
              ·
                refine ⟨3710714581366774780454417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473809720911183186969611 3710714581366774780454417)
                ·
                  refine ⟨2783035936025081085340813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3710714581366774780454417 2783035936025081085340813)
                  ·
                    refine ⟨1043638476009405407002805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783035936025081085340813 1043638476009405407002805)
                    ·
                      rfl

theorem cell22_3048718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3048718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048718 prefixEnd_3048718 := by exact prefixLift 3048718
  have htrace : WordTrace (prefixWord ++ tailWord_3048718) baseStart_3048718 baseEnd_3048718 := by
    simpa [prefixWord, tailWord_3048718, baseEnd_3048718] using wordTrace_append hprefix tailTrace_3048718
  have hstable : (prefixWord ++ tailWord_3048718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048718).length < 2 ^ (prefixWord ++ tailWord_3048718).sum := by decide
  have hdescent : baseEnd_3048718 < baseStart_3048718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048787 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 6]
def baseStart_3048787 : Nat := 118140960795 + 3048787 * 2 ^ 59
def prefixEnd_3048787 : Nat := 4983230072969 + 3 ^ 40 * 3048787 * 2
def baseEnd_3048787 : Nat := 347887365373170742342531

theorem tailTrace_3048787 : CollatzResearch.WordTrace tailWord_3048787 prefixEnd_3048787 347887365373170742342531 := by
  unfold tailWord_3048787
  simp only [CollatzResearch.WordTrace]
  refine ⟨111198397205772865210352615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74132264803848576806901743 111198397205772865210352615)
  ·
    refine ⟨166797595808659297815528923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111198397205772865210352615 166797595808659297815528923)
    ·
      refine ⟨250196393712988946723293385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166797595808659297815528923 250196393712988946723293385)
      ·
        refine ⟨187647295284741710042470039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250196393712988946723293385 187647295284741710042470039)
        ·
          refine ⟨281470942927112565063705059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187647295284741710042470039 281470942927112565063705059)
          ·
            refine ⟨422206414390668847595557589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281470942927112565063705059 422206414390668847595557589)
            ·
              refine ⟨9895462837281301115520881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 422206414390668847595557589 9895462837281301115520881)
              ·
                refine ⟨7421597127960975836640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9895462837281301115520881 7421597127960975836640661)
                ·
                  refine ⟨347887365373170742342531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7421597127960975836640661 347887365373170742342531)
                  ·
                    rfl

theorem cell22_3048787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_3048787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048787 prefixEnd_3048787 := by exact prefixLift 3048787
  have htrace : WordTrace (prefixWord ++ tailWord_3048787) baseStart_3048787 baseEnd_3048787 := by
    simpa [prefixWord, tailWord_3048787, baseEnd_3048787] using wordTrace_append hprefix tailTrace_3048787
  have hstable : (prefixWord ++ tailWord_3048787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048787).length < 2 ^ (prefixWord ++ tailWord_3048787).sum := by decide
  have hdescent : baseEnd_3048787 < baseStart_3048787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048789 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3048789 : Nat := 118140960795 + 3048789 * 2 ^ 59
def prefixEnd_3048789 : Nat := 4983230072969 + 3 ^ 40 * 3048789 * 2
def baseEnd_3048789 : Nat := 1043662780760384888477587

theorem tailTrace_3048789 : CollatzResearch.WordTrace tailWord_3048789 prefixEnd_3048789 1043662780760384888477587 := by
  unfold tailWord_3048789
  simp only [CollatzResearch.WordTrace]
  refine ⟨111198470151765619551925421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74132313434510413034616947 111198470151765619551925421)
  ·
    refine ⟨41699426306912107331972033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111198470151765619551925421 41699426306912107331972033)
    ·
      refine ⟨31274569730184080498979025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41699426306912107331972033 31274569730184080498979025)
      ·
        refine ⟨23455927297638060374234269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31274569730184080498979025 23455927297638060374234269)
        ·
          refine ⟨8795972736614272640337851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23455927297638060374234269 8795972736614272640337851)
          ·
            refine ⟨13193959104921408960506777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8795972736614272640337851 13193959104921408960506777)
            ·
              refine ⟨9895469328691056720380083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13193959104921408960506777 9895469328691056720380083)
              ·
                refine ⟨14843203993036585080570125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9895469328691056720380083 14843203993036585080570125)
                ·
                  refine ⟨5566201497388719405213797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14843203993036585080570125 5566201497388719405213797)
                  ·
                    refine ⟨1043662780760384888477587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566201497388719405213797 1043662780760384888477587)
                    ·
                      rfl

theorem cell22_3048789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3048789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048789 prefixEnd_3048789 := by exact prefixLift 3048789
  have htrace : WordTrace (prefixWord ++ tailWord_3048789) baseStart_3048789 baseEnd_3048789 := by
    simpa [prefixWord, tailWord_3048789, baseEnd_3048789] using wordTrace_append hprefix tailTrace_3048789
  have hstable : (prefixWord ++ tailWord_3048789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048789).length < 2 ^ (prefixWord ++ tailWord_3048789).sum := by decide
  have hdescent : baseEnd_3048789 < baseStart_3048789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048821 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 6]
def baseStart_3048821 : Nat := 118140960795 + 3048821 * 2 ^ 59
def prefixEnd_3048821 : Nat := 4983230072969 + 3 ^ 40 * 3048821 * 2
def baseEnd_3048821 : Nat := 347891245004782490559163

theorem tailTrace_3048821 : CollatzResearch.WordTrace tailWord_3048821 prefixEnd_3048821 347891245004782490559163 := by
  unfold tailWord_3048821
  simp only [CollatzResearch.WordTrace]
  refine ⟨111199637287649689017090317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74133091525099792678060211 111199637287649689017090317)
  ·
    refine ⟨41699863982868633381408869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111199637287649689017090317 41699863982868633381408869)
    ·
      refine ⟨7818724496787868759014163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41699863982868633381408869 7818724496787868759014163)
      ·
        refine ⟨11728086745181803138521245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7818724496787868759014163 11728086745181803138521245)
        ·
          refine ⟨4398032529443176176945467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11728086745181803138521245 4398032529443176176945467)
          ·
            refine ⟨6597048794164764265418201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398032529443176176945467 6597048794164764265418201)
            ·
              refine ⟨4947786595623573199063651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6597048794164764265418201 4947786595623573199063651)
              ·
                refine ⟨7421679893435359798595477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947786595623573199063651 7421679893435359798595477)
                ·
                  refine ⟨347891245004782490559163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7421679893435359798595477 347891245004782490559163)
                  ·
                    rfl

theorem cell22_3048821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_3048821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048821 prefixEnd_3048821 := by exact prefixLift 3048821
  have htrace : WordTrace (prefixWord ++ tailWord_3048821) baseStart_3048821 baseEnd_3048821 := by
    simpa [prefixWord, tailWord_3048821, baseEnd_3048821] using wordTrace_append hprefix tailTrace_3048821
  have hstable : (prefixWord ++ tailWord_3048821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048821).length < 2 ^ (prefixWord ++ tailWord_3048821).sum := by decide
  have hdescent : baseEnd_3048821 < baseStart_3048821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048836 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3048836 : Nat := 118140960795 + 3048836 * 2 ^ 59
def prefixEnd_3048836 : Nat := 4983230072969 + 3 ^ 40 * 3048836 * 2
def baseEnd_3048836 : Nat := 1043678869820892432552443

theorem tailTrace_3048836 : CollatzResearch.WordTrace tailWord_3048836 prefixEnd_3048836 1043678869820892432552443 := by
  unfold tailWord_3048836
  simp only [CollatzResearch.WordTrace]
  refine ⟨55600092191297673289443181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74133456255063564385924241 55600092191297673289443181)
  ·
    refine ⟨20850034571736627483541193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55600092191297673289443181 20850034571736627483541193)
    ·
      refine ⟨15637525928802470612655895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20850034571736627483541193 15637525928802470612655895)
      ·
        refine ⟨23456288893203705918983843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15637525928802470612655895 23456288893203705918983843)
        ·
          refine ⟨35184433339805558878475765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23456288893203705918983843 35184433339805558878475765)
          ·
            refine ⟨3298540625606771144857103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35184433339805558878475765 3298540625606771144857103)
            ·
              refine ⟨4947810938410156717285655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298540625606771144857103 4947810938410156717285655)
              ·
                refine ⟨7421716407615235075928483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4947810938410156717285655 7421716407615235075928483)
                ·
                  refine ⟨11132574611422852613892725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7421716407615235075928483 11132574611422852613892725)
                  ·
                    refine ⟨1043678869820892432552443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11132574611422852613892725 1043678869820892432552443)
                    ·
                      rfl

theorem cell22_3048836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3048836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048836 prefixEnd_3048836 := by exact prefixLift 3048836
  have htrace : WordTrace (prefixWord ++ tailWord_3048836) baseStart_3048836 baseEnd_3048836 := by
    simpa [prefixWord, tailWord_3048836, baseEnd_3048836] using wordTrace_append hprefix tailTrace_3048836
  have hstable : (prefixWord ++ tailWord_3048836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048836).length < 2 ^ (prefixWord ++ tailWord_3048836).sum := by decide
  have hdescent : baseEnd_3048836 < baseStart_3048836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048966 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3048966 : Nat := 118140960795 + 3048966 * 2 ^ 59
def prefixEnd_3048966 : Nat := 4983230072969 + 3 ^ 40 * 3048966 * 2
def baseEnd_3048966 : Nat := 1043723371477615426802045

theorem tailTrace_3048966 : CollatzResearch.WordTrace tailWord_3048966 prefixEnd_3048966 1043723371477615426802045 := by
  unfold tailWord_3048966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475153933503886836909961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74136617248082919187412501 3475153933503886836909961)
  ·
    refine ⟨2606365450127915127682471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3475153933503886836909961 2606365450127915127682471)
    ·
      refine ⟨3909548175191872691523707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606365450127915127682471 3909548175191872691523707)
      ·
        refine ⟨5864322262787809037285561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909548175191872691523707 5864322262787809037285561)
        ·
          refine ⟨4398241697090856777964171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5864322262787809037285561 4398241697090856777964171)
          ·
            refine ⟨6597362545636285166946257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4398241697090856777964171 6597362545636285166946257)
            ·
              refine ⟨4948021909227213875209693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6597362545636285166946257 4948021909227213875209693)
              ·
                refine ⟨1855508215960205203203635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4948021909227213875209693 1855508215960205203203635)
                ·
                  refine ⟨2783262323940307804805453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855508215960205203203635 2783262323940307804805453)
                  ·
                    refine ⟨1043723371477615426802045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783262323940307804805453 1043723371477615426802045)
                    ·
                      rfl

theorem cell22_3048966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3048966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048966 prefixEnd_3048966 := by exact prefixLift 3048966
  have htrace : WordTrace (prefixWord ++ tailWord_3048966) baseStart_3048966 baseEnd_3048966 := by
    simpa [prefixWord, tailWord_3048966, baseEnd_3048966] using wordTrace_append hprefix tailTrace_3048966
  have hstable : (prefixWord ++ tailWord_3048966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048966).length < 2 ^ (prefixWord ++ tailWord_3048966).sum := by decide
  have hdescent : baseEnd_3048966 < baseStart_3048966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3048969 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_3048969 : Nat := 118140960795 + 3048969 * 2 ^ 59
def prefixEnd_3048969 : Nat := 4983230072969 + 3 ^ 40 * 3048969 * 2
def baseEnd_3048969 : Nat := 1043724398438924418977035

theorem tailTrace_3048969 : CollatzResearch.WordTrace tailWord_3048969 prefixEnd_3048969 1043724398438924418977035 := by
  unfold tailWord_3048969
  simp only [CollatzResearch.WordTrace]
  refine ⟨111205035291113510293477961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74136690194075673528985307 111205035291113510293477961)
  ·
    refine ⟨83403776468335132720108471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111205035291113510293477961 83403776468335132720108471)
    ·
      refine ⟨125105664702502699080162707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83403776468335132720108471 125105664702502699080162707)
      ·
        refine ⟨187658497053754048620244061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125105664702502699080162707 187658497053754048620244061)
        ·
          refine ⟨70371936395157768232591523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187658497053754048620244061 70371936395157768232591523)
          ·
            refine ⟨105557904592736652348887285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70371936395157768232591523 105557904592736652348887285)
            ·
              refine ⟨9896053555569061157708183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105557904592736652348887285 9896053555569061157708183)
              ·
                refine ⟨14844080333353591736562275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9896053555569061157708183 14844080333353591736562275)
                ·
                  refine ⟨22266120500030387604843413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14844080333353591736562275 22266120500030387604843413)
                  ·
                    refine ⟨1043724398438924418977035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22266120500030387604843413 1043724398438924418977035)
                    ·
                      rfl

theorem cell22_3048969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_3048969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3048969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3048969 prefixEnd_3048969 := by exact prefixLift 3048969
  have htrace : WordTrace (prefixWord ++ tailWord_3048969) baseStart_3048969 baseEnd_3048969 := by
    simpa [prefixWord, tailWord_3048969, baseEnd_3048969] using wordTrace_append hprefix tailTrace_3048969
  have hstable : (prefixWord ++ tailWord_3048969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3048969).length < 2 ^ (prefixWord ++ tailWord_3048969).sum := by decide
  have hdescent : baseEnd_3048969 < baseStart_3048969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3048969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049029 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 9]
def baseStart_3049029 : Nat := 118140960795 + 3049029 * 2 ^ 59
def prefixEnd_3049029 : Nat := 4983230072969 + 3 ^ 40 * 3049029 * 2
def baseEnd_3049029 : Nat := 347914979221701420825617

theorem tailTrace_3049029 : CollatzResearch.WordTrace tailWord_3049029 prefixEnd_3049029 347914979221701420825617 := by
  unfold tailWord_3049029
  simp only [CollatzResearch.WordTrace]
  refine ⟨111207223670896140540662141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74138149113930760360441427 111207223670896140540662141)
  ·
    refine ⟨41702708876586052702748303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111207223670896140540662141 41702708876586052702748303)
    ·
      refine ⟨62554063314879079054122455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41702708876586052702748303 62554063314879079054122455)
      ·
        refine ⟨93831094972318618581183683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62554063314879079054122455 93831094972318618581183683)
        ·
          refine ⟨140746642458477927871775525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93831094972318618581183683 140746642458477927871775525)
          ·
            refine ⟨26389995460964611475957911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140746642458477927871775525 26389995460964611475957911)
            ·
              refine ⟨39584993191446917213936867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26389995460964611475957911 39584993191446917213936867)
              ·
                refine ⟨59377489787170375820905301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39584993191446917213936867 59377489787170375820905301)
                ·
                  refine ⟨347914979221701420825617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59377489787170375820905301 347914979221701420825617)
                  ·
                    rfl

theorem cell22_3049029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_3049029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049029 prefixEnd_3049029 := by exact prefixLift 3049029
  have htrace : WordTrace (prefixWord ++ tailWord_3049029) baseStart_3049029 baseEnd_3049029 := by
    simpa [prefixWord, tailWord_3049029, baseEnd_3049029] using wordTrace_append hprefix tailTrace_3049029
  have hstable : (prefixWord ++ tailWord_3049029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049029).length < 2 ^ (prefixWord ++ tailWord_3049029).sum := by decide
  have hdescent : baseEnd_3049029 < baseStart_3049029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049063 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 5]
def baseStart_3049063 : Nat := 118140960795 + 3049063 * 2 ^ 59
def prefixEnd_3049063 : Nat := 4983230072969 + 3 ^ 40 * 3049063 * 2
def baseEnd_3049063 : Nat := 347918858853313169042249

theorem tailTrace_3049063 : CollatzResearch.WordTrace tailWord_3049063 prefixEnd_3049063 347918858853313169042249 := by
  unfold tailWord_3049063
  simp only [CollatzResearch.WordTrace]
  refine ⟨111208463752772964347399843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74138975835181976231599895 111208463752772964347399843)
  ·
    refine ⟨166812695629159446521099765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111208463752772964347399843 166812695629159446521099765)
    ·
      refine ⟨15638690215233698111353103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166812695629159446521099765 15638690215233698111353103)
      ·
        refine ⟨23458035322850547167029655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15638690215233698111353103 23458035322850547167029655)
        ·
          refine ⟨35187052984275820750544483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23458035322850547167029655 35187052984275820750544483)
          ·
            refine ⟨52780579476413731125816725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35187052984275820750544483 52780579476413731125816725)
            ·
              refine ⟨2474089662956893646522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52780579476413731125816725 2474089662956893646522659)
              ·
                refine ⟨3711134494435340469783989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474089662956893646522659 3711134494435340469783989)
                ·
                  refine ⟨347918858853313169042249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711134494435340469783989 347918858853313169042249)
                  ·
                    rfl

theorem cell22_3049063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 5].length) (baseStart_3049063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049063 prefixEnd_3049063 := by exact prefixLift 3049063
  have htrace : WordTrace (prefixWord ++ tailWord_3049063) baseStart_3049063 baseEnd_3049063 := by
    simpa [prefixWord, tailWord_3049063, baseEnd_3049063] using wordTrace_append hprefix tailTrace_3049063
  have hstable : (prefixWord ++ tailWord_3049063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049063).length < 2 ^ (prefixWord ++ tailWord_3049063).sum := by decide
  have hdescent : baseEnd_3049063 < baseStart_3049063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049123 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 2, 3]
def baseStart_3049123 : Nat := 118140960795 + 3049123 * 2 ^ 59
def prefixEnd_3049123 : Nat := 4983230072969 + 3 ^ 40 * 3049123 * 2
def baseEnd_3049123 : Nat := 1043777115786119350626563

theorem tailTrace_3049123 : CollatzResearch.WordTrace tailWord_3049123 prefixEnd_3049123 1043777115786119350626563 := by
  unfold tailWord_3049123
  simp only [CollatzResearch.WordTrace]
  refine ⟨111210652132555594594584023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74140434755037063063056015 111210652132555594594584023)
  ·
    refine ⟨166815978198833391891876035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111210652132555594594584023 166815978198833391891876035)
    ·
      refine ⟨250223967298250087837814053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166815978198833391891876035 250223967298250087837814053)
      ·
        refine ⟨46916993868421891469590135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250223967298250087837814053 46916993868421891469590135)
        ·
          refine ⟨70375490802632837204385203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46916993868421891469590135 70375490802632837204385203)
          ·
            refine ⟨105563236203949255806577805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70375490802632837204385203 105563236203949255806577805)
            ·
              refine ⟨39586213576480970927466677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105563236203949255806577805 39586213576480970927466677)
              ·
                refine ⟨3711207522795091024450001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39586213576480970927466677 3711207522795091024450001)
                ·
                  refine ⟨2783405642096318268337501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3711207522795091024450001 2783405642096318268337501)
                  ·
                    refine ⟨1043777115786119350626563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783405642096318268337501 1043777115786119350626563)
                    ·
                      rfl

theorem cell22_3049123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2, 3].length) (baseStart_3049123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049123 prefixEnd_3049123 := by exact prefixLift 3049123
  have htrace : WordTrace (prefixWord ++ tailWord_3049123) baseStart_3049123 baseEnd_3049123 := by
    simpa [prefixWord, tailWord_3049123, baseEnd_3049123] using wordTrace_append hprefix tailTrace_3049123
  have hstable : (prefixWord ++ tailWord_3049123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049123).length < 2 ^ (prefixWord ++ tailWord_3049123).sum := by decide
  have hdescent : baseEnd_3049123 < baseStart_3049123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049138 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3049138 : Nat := 118140960795 + 3049138 * 2 ^ 59
def prefixEnd_3049138 : Nat := 4983230072969 + 3 ^ 40 * 3049138 * 2
def baseEnd_3049138 : Nat := 1043782250592664311501517

theorem tailTrace_3049138 : CollatzResearch.WordTrace tailWord_3049138 prefixEnd_3049138 1043782250592664311501517 := by
  unfold tailWord_3049138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27802799806875313039095017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74140799485000834770920045 27802799806875313039095017)
  ·
    refine ⟨20852099855156484779321263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27802799806875313039095017 20852099855156484779321263)
    ·
      refine ⟨31278149782734727168981895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20852099855156484779321263 31278149782734727168981895)
      ·
        refine ⟨46917224674102090753472843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31278149782734727168981895 46917224674102090753472843)
        ·
          refine ⟨70375837011153136130209265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46917224674102090753472843 70375837011153136130209265)
          ·
            refine ⟨52781877758364852097656949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70375837011153136130209265 52781877758364852097656949)
            ·
              refine ⟨4948301039846704884155339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52781877758364852097656949 4948301039846704884155339)
              ·
                refine ⟨7422451559770057326233009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948301039846704884155339 7422451559770057326233009)
                ·
                  refine ⟨5566838669827542994674757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7422451559770057326233009 5566838669827542994674757)
                  ·
                    refine ⟨1043782250592664311501517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5566838669827542994674757 1043782250592664311501517)
                    ·
                      rfl

theorem cell22_3049138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3049138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049138 prefixEnd_3049138 := by exact prefixLift 3049138
  have htrace : WordTrace (prefixWord ++ tailWord_3049138) baseStart_3049138 baseEnd_3049138 := by
    simpa [prefixWord, tailWord_3049138, baseEnd_3049138] using wordTrace_append hprefix tailTrace_3049138
  have hstable : (prefixWord ++ tailWord_3049138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049138).length < 2 ^ (prefixWord ++ tailWord_3049138).sum := by decide
  have hdescent : baseEnd_3049138 < baseStart_3049138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049142 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_3049142 : Nat := 118140960795 + 3049142 * 2 ^ 59
def prefixEnd_3049142 : Nat := 4983230072969 + 3 ^ 40 * 3049142 * 2
def baseEnd_3049142 : Nat := 347927873291469878133835

theorem tailTrace_3049142 : CollatzResearch.WordTrace tailWord_3049142 prefixEnd_3049142 347927873291469878133835 := by
  unfold tailWord_3049142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950709069967922552470355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74140896746324507226350453 6950709069967922552470355)
  ·
    refine ⟨10426063604951883828705533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6950709069967922552470355 10426063604951883828705533)
    ·
      refine ⟨3909773851856956435764575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10426063604951883828705533 3909773851856956435764575)
      ·
        refine ⟨5864660777785434653646863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3909773851856956435764575 5864660777785434653646863)
        ·
          refine ⟨8796991166678151980470295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864660777785434653646863 8796991166678151980470295)
          ·
            refine ⟨13195486750017227970705443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8796991166678151980470295 13195486750017227970705443)
            ·
              refine ⟨19793230125025841956058165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13195486750017227970705443 19793230125025841956058165)
              ·
                refine ⟨1855615324221172683380453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19793230125025841956058165 1855615324221172683380453)
                ·
                  refine ⟨347927873291469878133835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855615324221172683380453 347927873291469878133835)
                  ·
                    rfl

theorem cell22_3049142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_3049142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049142 prefixEnd_3049142 := by exact prefixLift 3049142
  have htrace : WordTrace (prefixWord ++ tailWord_3049142) baseStart_3049142 baseEnd_3049142 := by
    simpa [prefixWord, tailWord_3049142, baseEnd_3049142] using wordTrace_append hprefix tailTrace_3049142
  have hstable : (prefixWord ++ tailWord_3049142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049142).length < 2 ^ (prefixWord ++ tailWord_3049142).sum := by decide
  have hdescent : baseEnd_3049142 < baseStart_3049142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049174 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3049174 : Nat := 118140960795 + 3049174 * 2 ^ 59
def prefixEnd_3049174 : Nat := 4983230072969 + 3 ^ 40 * 3049174 * 2
def baseEnd_3049174 : Nat := 1043794574128372217601407

theorem tailTrace_3049174 : CollatzResearch.WordTrace tailWord_3049174 prefixEnd_3049174 1043794574128372217601407 := by
  unfold tailWord_3049174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950782015960676894043161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74141674836913886869793717 6950782015960676894043161)
  ·
    refine ⟨5213086511970507670532371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6950782015960676894043161 5213086511970507670532371)
    ·
      refine ⟨7819629767955761505798557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213086511970507670532371 7819629767955761505798557)
      ·
        refine ⟨2932361162983410564674459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7819629767955761505798557 2932361162983410564674459)
        ·
          refine ⟨4398541744475115847011689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932361162983410564674459 4398541744475115847011689)
          ·
            refine ⟨3298906308356336885258767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398541744475115847011689 3298906308356336885258767)
            ·
              refine ⟨4948359462534505327888151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3298906308356336885258767 4948359462534505327888151)
              ·
                refine ⟨7422539193801757991832227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948359462534505327888151 7422539193801757991832227)
                ·
                  refine ⟨11133808790702636987748341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7422539193801757991832227 11133808790702636987748341)
                  ·
                    refine ⟨1043794574128372217601407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11133808790702636987748341 1043794574128372217601407)
                    ·
                      rfl

theorem cell22_3049174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3049174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049174 prefixEnd_3049174 := by exact prefixLift 3049174
  have htrace : WordTrace (prefixWord ++ tailWord_3049174) baseStart_3049174 baseEnd_3049174 := by
    simpa [prefixWord, tailWord_3049174, baseEnd_3049174] using wordTrace_append hprefix tailTrace_3049174
  have hstable : (prefixWord ++ tailWord_3049174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049174).length < 2 ^ (prefixWord ++ tailWord_3049174).sum := by decide
  have hdescent : baseEnd_3049174 < baseStart_3049174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049187 : List Nat := [1, 1, 1, 7, 3, 1, 2, 6]
def baseStart_3049187 : Nat := 118140960795 + 3049187 * 2 ^ 59
def prefixEnd_3049187 : Nat := 4983230072969 + 3 ^ 40 * 3049187 * 2
def baseEnd_3049187 : Nat := 115977669366004946336263

theorem tailTrace_3049187 : CollatzResearch.WordTrace tailWord_3049187 prefixEnd_3049187 115977669366004946336263 := by
  unfold tailWord_3049187
  simp only [CollatzResearch.WordTrace]
  refine ⟨111212986404323733524913815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74141990936215822349942543 111212986404323733524913815)
  ·
    refine ⟨166819479606485600287370723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111212986404323733524913815 166819479606485600287370723)
    ·
      refine ⟨250229219409728400431056085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166819479606485600287370723 250229219409728400431056085)
      ·
        refine ⟨5864747329915509385102877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 250229219409728400431056085 5864747329915509385102877)
        ·
          refine ⟨2199280248718316019413579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5864747329915509385102877 2199280248718316019413579)
          ·
            refine ⟨3298920373077474029120369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199280248718316019413579 3298920373077474029120369)
            ·
              refine ⟨2474190279808105521840277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3298920373077474029120369 2474190279808105521840277)
              ·
                refine ⟨115977669366004946336263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2474190279808105521840277 115977669366004946336263)
                ·
                  rfl

theorem cell22_3049187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 6].length) (baseStart_3049187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049187 prefixEnd_3049187 := by exact prefixLift 3049187
  have htrace : WordTrace (prefixWord ++ tailWord_3049187) baseStart_3049187 baseEnd_3049187 := by
    simpa [prefixWord, tailWord_3049187, baseEnd_3049187] using wordTrace_append hprefix tailTrace_3049187
  have hstable : (prefixWord ++ tailWord_3049187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049187).length < 2 ^ (prefixWord ++ tailWord_3049187).sum := by decide
  have hdescent : baseEnd_3049187 < baseStart_3049187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049196 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_3049196 : Nat := 118140960795 + 3049196 * 2 ^ 59
def prefixEnd_3049196 : Nat := 4983230072969 + 3 ^ 40 * 3049196 * 2
def baseEnd_3049196 : Nat := 1043802105177971493551339

theorem tailTrace_3049196 : CollatzResearch.WordTrace tailWord_3049196 prefixEnd_3049196 1043802105177971493551339 := by
  unfold tailWord_3049196
  simp only [CollatzResearch.WordTrace]
  refine ⟨55606657330645564030995721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74142209774194085374660961 55606657330645564030995721)
  ·
    refine ⟨41704992997984173023246791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55606657330645564030995721 41704992997984173023246791)
    ·
      refine ⟨62557489496976259534870187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41704992997984173023246791 62557489496976259534870187)
      ·
        refine ⟨93836234245464389302305281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62557489496976259534870187 93836234245464389302305281)
        ·
          refine ⟨70377175684098291976728961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93836234245464389302305281 70377175684098291976728961)
          ·
            refine ⟨52782881763073718982546721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70377175684098291976728961 52782881763073718982546721)
            ·
              refine ⟨39587161322305289236910041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52782881763073718982546721 39587161322305289236910041)
              ·
                refine ⟨29690370991728966927682531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39587161322305289236910041 29690370991728966927682531)
                ·
                  refine ⟨44535556487593450391523797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29690370991728966927682531 44535556487593450391523797)
                  ·
                    refine ⟨1043802105177971493551339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44535556487593450391523797 1043802105177971493551339)
                    ·
                      rfl

theorem cell22_3049196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_3049196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049196 prefixEnd_3049196 := by exact prefixLift 3049196
  have htrace : WordTrace (prefixWord ++ tailWord_3049196) baseStart_3049196 baseEnd_3049196 := by
    simpa [prefixWord, tailWord_3049196, baseEnd_3049196] using wordTrace_append hprefix tailTrace_3049196
  have hstable : (prefixWord ++ tailWord_3049196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049196).length < 2 ^ (prefixWord ++ tailWord_3049196).sum := by decide
  have hdescent : baseEnd_3049196 < baseStart_3049196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049277 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 4]
def baseStart_3049277 : Nat := 118140960795 + 3049277 * 2 ^ 59
def prefixEnd_3049277 : Nat := 4983230072969 + 3 ^ 40 * 3049277 * 2
def baseEnd_3049277 : Nat := 347943277711104760758697

theorem tailTrace_3049277 : CollatzResearch.WordTrace tailWord_3049277 prefixEnd_3049277 347943277711104760758697 := by
  unfold tailWord_3049277
  simp only [CollatzResearch.WordTrace]
  refine ⟨111216268973997678895690085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74144179315998452597126723 111216268973997678895690085)
  ·
    refine ⟨20853050432624564792941891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111216268973997678895690085 20853050432624564792941891)
    ·
      refine ⟨31279575648936847189412837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20853050432624564792941891 31279575648936847189412837)
      ·
        refine ⟨5864920434175658848014907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31279575648936847189412837 5864920434175658848014907)
        ·
          refine ⟨8797380651263488272022361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5864920434175658848014907 8797380651263488272022361)
          ·
            refine ⟨6598035488447616204016771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8797380651263488272022361 6598035488447616204016771)
            ·
              refine ⟨9897053232671424306025157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6598035488447616204016771 9897053232671424306025157)
              ·
                refine ⟨1855697481125892057379717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9897053232671424306025157 1855697481125892057379717)
                ·
                  refine ⟨347943277711104760758697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1855697481125892057379717 347943277711104760758697)
                  ·
                    rfl

theorem cell22_3049277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_3049277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049277 prefixEnd_3049277 := by exact prefixLift 3049277
  have htrace : WordTrace (prefixWord ++ tailWord_3049277) baseStart_3049277 baseEnd_3049277 := by
    simpa [prefixWord, tailWord_3049277, baseEnd_3049277] using wordTrace_append hprefix tailTrace_3049277
  have hstable : (prefixWord ++ tailWord_3049277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049277).length < 2 ^ (prefixWord ++ tailWord_3049277).sum := by decide
  have hdescent : baseEnd_3049277 < baseStart_3049277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049288 : List Nat := [2, 1, 3, 1, 1, 4, 3, 7]
def baseStart_3049288 : Nat := 118140960795 + 3049288 * 2 ^ 59
def prefixEnd_3049288 : Nat := 4983230072969 + 3 ^ 40 * 3049288 * 2
def baseEnd_3049288 : Nat := 115981510962012657805673

theorem tailTrace_3049288 : CollatzResearch.WordTrace tailWord_3049288 prefixEnd_3049288 115981510962012657805673 := by
  unfold tailWord_3049288
  simp only [CollatzResearch.WordTrace]
  refine ⟨55608335088478913887170259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74144446784638551849560345 55608335088478913887170259)
  ·
    refine ⟨83412502632718370830755389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55608335088478913887170259 83412502632718370830755389)
    ·
      refine ⟨31279688487269389061533271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83412502632718370830755389 31279688487269389061533271)
      ·
        refine ⟨46919532730904083592299907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31279688487269389061533271 46919532730904083592299907)
        ·
          refine ⟨70379299096356125388449861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46919532730904083592299907 70379299096356125388449861)
          ·
            refine ⟨13196118580566773510334349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70379299096356125388449861 13196118580566773510334349)
            ·
              refine ⟨4948544467712540066375381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13196118580566773510334349 4948544467712540066375381)
              ·
                refine ⟨115981510962012657805673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4948544467712540066375381 115981510962012657805673)
                ·
                  rfl

theorem cell22_3049288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_3049288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049288 prefixEnd_3049288 := by exact prefixLift 3049288
  have htrace : WordTrace (prefixWord ++ tailWord_3049288) baseStart_3049288 baseEnd_3049288 := by
    simpa [prefixWord, tailWord_3049288, baseEnd_3049288] using wordTrace_append hprefix tailTrace_3049288
  have hstable : (prefixWord ++ tailWord_3049288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049288).length < 2 ^ (prefixWord ++ tailWord_3049288).sum := by decide
  have hdescent : baseEnd_3049288 < baseStart_3049288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049320 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_3049320 : Nat := 118140960795 + 3049320 * 2 ^ 59
def prefixEnd_3049320 : Nat := 4983230072969 + 3 ^ 40 * 3049320 * 2
def baseEnd_3049320 : Nat := 1043844552912076503450959

theorem tailTrace_3049320 : CollatzResearch.WordTrace tailWord_3049320 prefixEnd_3049320 1043844552912076503450959 := by
  unfold tailWord_3049320
  simp only [CollatzResearch.WordTrace]
  refine ⟨55608918656420948619752707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74145224875227931493003609 55608918656420948619752707)
  ·
    refine ⟨83413377984631422929629061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55608918656420948619752707 83413377984631422929629061)
    ·
      refine ⟨15640008372118391799305449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83413377984631422929629061 15640008372118391799305449)
      ·
        refine ⟨11730006279088793849479087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15640008372118391799305449 11730006279088793849479087)
        ·
          refine ⟨17595009418633190774218631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730006279088793849479087 17595009418633190774218631)
          ·
            refine ⟨26392514127949786161327947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17595009418633190774218631 26392514127949786161327947)
            ·
              refine ⟨39588771191924679241991921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26392514127949786161327947 39588771191924679241991921)
              ·
                refine ⟨29691578393943509431493941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39588771191924679241991921 29691578393943509431493941)
                ·
                  refine ⟨2783585474432204009202557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29691578393943509431493941 2783585474432204009202557)
                  ·
                    refine ⟨1043844552912076503450959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783585474432204009202557 1043844552912076503450959)
                    ·
                      rfl

theorem cell22_3049320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_3049320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049320 prefixEnd_3049320 := by exact prefixLift 3049320
  have htrace : WordTrace (prefixWord ++ tailWord_3049320) baseStart_3049320 baseEnd_3049320 := by
    simpa [prefixWord, tailWord_3049320, baseEnd_3049320] using wordTrace_append hprefix tailTrace_3049320
  have hstable : (prefixWord ++ tailWord_3049320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049320).length < 2 ^ (prefixWord ++ tailWord_3049320).sum := by decide
  have hdescent : baseEnd_3049320 < baseStart_3049320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049337 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 1, 3]
def baseStart_3049337 : Nat := 118140960795 + 3049337 * 2 ^ 59
def prefixEnd_3049337 : Nat := 4983230072969 + 3 ^ 40 * 3049337 * 2
def baseEnd_3049337 : Nat := 1043850372359494125775907

theorem tailTrace_3049337 : CollatzResearch.WordTrace tailWord_3049337 prefixEnd_3049337 1043850372359494125775907 := by
  unfold tailWord_3049337
  simp only [CollatzResearch.WordTrace]
  refine ⟨111218457353780309142874265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74145638235853539428582843 111218457353780309142874265)
  ·
    refine ⟨83413843015335231857155699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111218457353780309142874265 83413843015335231857155699)
    ·
      refine ⟨125120764523002847785733549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83413843015335231857155699 125120764523002847785733549)
      ·
        refine ⟨46920286696126067919650081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125120764523002847785733549 46920286696126067919650081)
        ·
          refine ⟨35190215022094550939737561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46920286696126067919650081 35190215022094550939737561)
          ·
            refine ⟨26392661266570913204803171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35190215022094550939737561 26392661266570913204803171)
            ·
              refine ⟨39588991899856369807204757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26392661266570913204803171 39588991899856369807204757)
              ·
                refine ⟨1855733995305767334712723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39588991899856369807204757 1855733995305767334712723)
                ·
                  refine ⟨2783600992958651002069085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855733995305767334712723 2783600992958651002069085)
                  ·
                    refine ⟨1043850372359494125775907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783600992958651002069085 1043850372359494125775907)
                    ·
                      rfl

theorem cell22_3049337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_3049337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049337 prefixEnd_3049337 := by exact prefixLift 3049337
  have htrace : WordTrace (prefixWord ++ tailWord_3049337) baseStart_3049337 baseEnd_3049337 := by
    simpa [prefixWord, tailWord_3049337, baseEnd_3049337] using wordTrace_append hprefix tailTrace_3049337
  have hstable : (prefixWord ++ tailWord_3049337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049337).length < 2 ^ (prefixWord ++ tailWord_3049337).sum := by decide
  have hdescent : baseEnd_3049337 < baseStart_3049337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049363 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_3049363 : Nat := 118140960795 + 3049363 * 2 ^ 59
def prefixEnd_3049363 : Nat := 4983230072969 + 3 ^ 40 * 3049363 * 2
def baseEnd_3049363 : Nat := 1043859272690838724625827

theorem tailTrace_3049363 : CollatzResearch.WordTrace tailWord_3049363 prefixEnd_3049363 1043859272690838724625827 := by
  unfold tailWord_3049363
  simp only [CollatzResearch.WordTrace]
  refine ⟨111219405651686115583320743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74146270434457410388880495 111219405651686115583320743)
  ·
    refine ⟨166829108477529173374981115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111219405651686115583320743 166829108477529173374981115)
    ·
      refine ⟨250243662716293760062471673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166829108477529173374981115 250243662716293760062471673)
      ·
        refine ⟨187682747037220320046853755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250243662716293760062471673 187682747037220320046853755)
        ·
          refine ⟨281524120555830480070280633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187682747037220320046853755 281524120555830480070280633)
          ·
            refine ⟨211143090416872860052710475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281524120555830480070280633 211143090416872860052710475)
            ·
              refine ⟨316714635625309290079065713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211143090416872860052710475 316714635625309290079065713)
              ·
                refine ⟨237535976718981967559299285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316714635625309290079065713 237535976718981967559299285)
                ·
                  refine ⟨5567249454351139864671077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 237535976718981967559299285 5567249454351139864671077)
                  ·
                    refine ⟨1043859272690838724625827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567249454351139864671077 1043859272690838724625827)
                    ·
                      rfl

theorem cell22_3049363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_3049363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049363 prefixEnd_3049363 := by exact prefixLift 3049363
  have htrace : WordTrace (prefixWord ++ tailWord_3049363) baseStart_3049363 baseEnd_3049363 := by
    simpa [prefixWord, tailWord_3049363, baseEnd_3049363] using wordTrace_append hprefix tailTrace_3049363
  have hstable : (prefixWord ++ tailWord_3049363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049363).length < 2 ^ (prefixWord ++ tailWord_3049363).sum := by decide
  have hdescent : baseEnd_3049363 < baseStart_3049363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049423 : List Nat := [1, 1, 2, 1, 1, 5, 1, 10]
def baseStart_3049423 : Nat := 118140960795 + 3049423 * 2 ^ 59
def prefixEnd_3049423 : Nat := 4983230072969 + 3 ^ 40 * 3049423 * 2
def baseEnd_3049423 : Nat := 115986645768557618680627

theorem tailTrace_3049423 : CollatzResearch.WordTrace tailWord_3049423 prefixEnd_3049423 115986645768557618680627 := by
  unfold tailWord_3049423
  simp only [CollatzResearch.WordTrace]
  refine ⟨111221594031468745830504923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74147729354312497220336615 111221594031468745830504923)
  ·
    refine ⟨166832391047203118745757385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111221594031468745830504923 166832391047203118745757385)
    ·
      refine ⟨125124293285402339059318039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166832391047203118745757385 125124293285402339059318039)
      ·
        refine ⟨187686439928103508588977059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125124293285402339059318039 187686439928103508588977059)
        ·
          refine ⟨281529659892155262883465589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187686439928103508588977059 281529659892155262883465589)
          ·
            refine ⟨26393405614889555895324899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281529659892155262883465589 26393405614889555895324899)
            ·
              refine ⟨39590108422334333842987349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26393405614889555895324899 39590108422334333842987349)
              ·
                refine ⟨115986645768557618680627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39590108422334333842987349 115986645768557618680627)
                ·
                  rfl

theorem cell22_3049423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 10].length) (baseStart_3049423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049423 prefixEnd_3049423 := by exact prefixLift 3049423
  have htrace : WordTrace (prefixWord ++ tailWord_3049423) baseStart_3049423 baseEnd_3049423 := by
    simpa [prefixWord, tailWord_3049423, baseEnd_3049423] using wordTrace_append hprefix tailTrace_3049423
  have hstable : (prefixWord ++ tailWord_3049423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049423).length < 2 ^ (prefixWord ++ tailWord_3049423).sum := by decide
  have hdescent : baseEnd_3049423 < baseStart_3049423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049457 : List Nat := [1, 2, 2, 2, 5, 2, 1, 7]
def baseStart_3049457 : Nat := 118140960795 + 3049457 * 2 ^ 59
def prefixEnd_3049457 : Nat := 4983230072969 + 3 ^ 40 * 3049457 * 2
def baseEnd_3049457 : Nat := 115987938979094868086171

theorem tailTrace_3049457 : CollatzResearch.WordTrace tailWord_3049457 prefixEnd_3049457 115987938979094868086171 := by
  unfold tailWord_3049457
  simp only [CollatzResearch.WordTrace]
  refine ⟨111222834113345569637242625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74148556075563713091495083 111222834113345569637242625)
  ·
    refine ⟨83417125585009177227931969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111222834113345569637242625 83417125585009177227931969)
    ·
      refine ⟨62562844188756882920948977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83417125585009177227931969 62562844188756882920948977)
      ·
        refine ⟨46922133141567662190711733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62562844188756882920948977 46922133141567662190711733)
        ·
          refine ⟨4398949982021968330379225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46922133141567662190711733 4398949982021968330379225)
          ·
            refine ⟨3299212486516476247784419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398949982021968330379225 3299212486516476247784419)
            ·
              refine ⟨4948818729774714371676629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299212486516476247784419 4948818729774714371676629)
              ·
                refine ⟨115987938979094868086171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4948818729774714371676629 115987938979094868086171)
                ·
                  rfl

theorem cell22_3049457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 7].length) (baseStart_3049457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049457 prefixEnd_3049457 := by exact prefixLift 3049457
  have htrace : WordTrace (prefixWord ++ tailWord_3049457) baseStart_3049457 baseEnd_3049457 := by
    simpa [prefixWord, tailWord_3049457, baseEnd_3049457] using wordTrace_append hprefix tailTrace_3049457
  have hstable : (prefixWord ++ tailWord_3049457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049457).length < 2 ^ (prefixWord ++ tailWord_3049457).sum := by decide
  have hdescent : baseEnd_3049457 < baseStart_3049457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049476 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_3049476 : Nat := 118140960795 + 3049476 * 2 ^ 59
def prefixEnd_3049476 : Nat := 4983230072969 + 3 ^ 40 * 3049476 * 2
def baseEnd_3049476 : Nat := 1043897954900144096550481

theorem tailTrace_3049476 : CollatzResearch.WordTrace tailWord_3049476 prefixEnd_3049476 1043897954900144096550481 := by
  unfold tailWord_3049476
  simp only [CollatzResearch.WordTrace]
  refine ⟨55611763550138367941092141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74149018066851157254789521 55611763550138367941092141)
  ·
    refine ⟨20854411331301887977909553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55611763550138367941092141 20854411331301887977909553)
    ·
      refine ⟨15640808498476415983432165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20854411331301887977909553 15640808498476415983432165)
      ·
        refine ⟨2932651593464327996893531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15640808498476415983432165 2932651593464327996893531)
        ·
          refine ⟨4398977390196491995340297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932651593464327996893531 4398977390196491995340297)
          ·
            refine ⟨3299233042647368996505223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4398977390196491995340297 3299233042647368996505223)
            ·
              refine ⟨4948849563971053494757835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299233042647368996505223 4948849563971053494757835)
              ·
                refine ⟨7423274345956580242136753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948849563971053494757835 7423274345956580242136753)
                ·
                  refine ⟨5567455759467435181602565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423274345956580242136753 5567455759467435181602565)
                  ·
                    refine ⟨1043897954900144096550481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567455759467435181602565 1043897954900144096550481)
                    ·
                      rfl

theorem cell22_3049476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_3049476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049476 prefixEnd_3049476 := by exact prefixLift 3049476
  have htrace : WordTrace (prefixWord ++ tailWord_3049476) baseStart_3049476 baseEnd_3049476 := by
    simpa [prefixWord, tailWord_3049476, baseEnd_3049476] using wordTrace_append hprefix tailTrace_3049476
  have hstable : (prefixWord ++ tailWord_3049476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049476).length < 2 ^ (prefixWord ++ tailWord_3049476).sum := by decide
  have hdescent : baseEnd_3049476 < baseStart_3049476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049515 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_3049515 : Nat := 118140960795 + 3049515 * 2 ^ 59
def prefixEnd_3049515 : Nat := 4983230072969 + 3 ^ 40 * 3049515 * 2
def baseEnd_3049515 : Nat := 1043911305397160994825361

theorem tailTrace_3049515 : CollatzResearch.WordTrace tailWord_3049515 prefixEnd_3049515 1043911305397160994825361 := by
  unfold tailWord_3049515
  simp only [CollatzResearch.WordTrace]
  refine ⟨111224949547135445542853999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74149966364756963695235999 111224949547135445542853999)
  ·
    refine ⟨166837424320703168314280999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111224949547135445542853999 166837424320703168314280999)
    ·
      refine ⟨250256136481054752471421499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166837424320703168314280999 250256136481054752471421499)
      ·
        refine ⟨375384204721582128707132249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250256136481054752471421499 375384204721582128707132249)
        ·
          refine ⟨281538153541186596530349187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375384204721582128707132249 281538153541186596530349187)
          ·
            refine ⟨422307230311779894795523781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281538153541186596530349187 422307230311779894795523781)
            ·
              refine ⟨79182605683458730274160709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422307230311779894795523781 79182605683458730274160709)
              ·
                refine ⟨14846738565648511926405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79182605683458730274160709 14846738565648511926405133)
                ·
                  refine ⟨5567526962118191972401925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14846738565648511926405133 5567526962118191972401925)
                  ·
                    refine ⟨1043911305397160994825361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567526962118191972401925 1043911305397160994825361)
                    ·
                      rfl

theorem cell22_3049515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_3049515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049515 prefixEnd_3049515 := by exact prefixLift 3049515
  have htrace : WordTrace (prefixWord ++ tailWord_3049515) baseStart_3049515 baseEnd_3049515 := by
    simpa [prefixWord, tailWord_3049515, baseEnd_3049515] using wordTrace_append hprefix tailTrace_3049515
  have hstable : (prefixWord ++ tailWord_3049515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049515).length < 2 ^ (prefixWord ++ tailWord_3049515).sum := by decide
  have hdescent : baseEnd_3049515 < baseStart_3049515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049545 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_3049545 : Nat := 118140960795 + 3049545 * 2 ^ 59
def prefixEnd_3049545 : Nat := 4983230072969 + 3 ^ 40 * 3049545 * 2
def baseEnd_3049545 : Nat := 1043921575010250916575269

theorem tailTrace_3049545 : CollatzResearch.WordTrace tailWord_3049545 prefixEnd_3049545 1043921575010250916575269 := by
  unfold tailWord_3049545
  simp only [CollatzResearch.WordTrace]
  refine ⟨111226043737026760666446089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74150695824684507110964059 111226043737026760666446089)
  ·
    refine ⟨83419532802770070499834567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111226043737026760666446089 83419532802770070499834567)
    ·
      refine ⟨125129299204155105749751851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83419532802770070499834567 125129299204155105749751851)
      ·
        refine ⟨187693948806232658624627777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125129299204155105749751851 187693948806232658624627777)
        ·
          refine ⟨140770461604674493968470833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187693948806232658624627777 140770461604674493968470833)
          ·
            refine ⟨105577846203505870476353125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140770461604674493968470833 105577846203505870476353125)
            ·
              refine ⟨19795846163157350714316211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105577846203505870476353125 19795846163157350714316211)
              ·
                refine ⟨29693769244736026071474317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19795846163157350714316211 29693769244736026071474317)
                ·
                  refine ⟨11135163466776009776802869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29693769244736026071474317 11135163466776009776802869)
                  ·
                    refine ⟨1043921575010250916575269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11135163466776009776802869 1043921575010250916575269)
                    ·
                      rfl

theorem cell22_3049545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_3049545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049545 prefixEnd_3049545 := by exact prefixLift 3049545
  have htrace : WordTrace (prefixWord ++ tailWord_3049545) baseStart_3049545 baseEnd_3049545 := by
    simpa [prefixWord, tailWord_3049545, baseEnd_3049545] using wordTrace_append hprefix tailTrace_3049545
  have hstable : (prefixWord ++ tailWord_3049545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049545).length < 2 ^ (prefixWord ++ tailWord_3049545).sum := by decide
  have hdescent : baseEnd_3049545 < baseStart_3049545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049549 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3049549 : Nat := 118140960795 + 3049549 * 2 ^ 59
def prefixEnd_3049549 : Nat := 4983230072969 + 3 ^ 40 * 3049549 * 2
def baseEnd_3049549 : Nat := 1043922944291996239475257

theorem tailTrace_3049549 : CollatzResearch.WordTrace tailWord_3049549 prefixEnd_3049549 1043922944291996239475257 := by
  unfold tailWord_3049549
  simp only [CollatzResearch.WordTrace]
  refine ⟨111226189629012269349591701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74150793086008179566394467 111226189629012269349591701)
  ·
    refine ⟨5213727638859950125762111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111226189629012269349591701 5213727638859950125762111)
    ·
      refine ⟨7820591458289925188643167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213727638859950125762111 7820591458289925188643167)
      ·
        refine ⟨11730887187434887782964751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820591458289925188643167 11730887187434887782964751)
        ·
          refine ⟨17596330781152331674447127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730887187434887782964751 17596330781152331674447127)
          ·
            refine ⟨26394496171728497511670691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17596330781152331674447127 26394496171728497511670691)
            ·
              refine ⟨39591744257592746267506037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26394496171728497511670691 39591744257592746267506037)
              ·
                refine ⟨3711726024149319962578691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39591744257592746267506037 3711726024149319962578691)
                ·
                  refine ⟨5567589036223979943868037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711726024149319962578691 5567589036223979943868037)
                  ·
                    refine ⟨1043922944291996239475257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567589036223979943868037 1043922944291996239475257)
                    ·
                      rfl

theorem cell22_3049549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3049549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049549 prefixEnd_3049549 := by exact prefixLift 3049549
  have htrace : WordTrace (prefixWord ++ tailWord_3049549) baseStart_3049549 baseEnd_3049549 := by
    simpa [prefixWord, tailWord_3049549, baseEnd_3049549] using wordTrace_append hprefix tailTrace_3049549
  have hstable : (prefixWord ++ tailWord_3049549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049549).length < 2 ^ (prefixWord ++ tailWord_3049549).sum := by decide
  have hdescent : baseEnd_3049549 < baseStart_3049549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049562 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_3049562 : Nat := 118140960795 + 3049562 * 2 ^ 59
def prefixEnd_3049562 : Nat := 4983230072969 + 3 ^ 40 * 3049562 * 2
def baseEnd_3049562 : Nat := 1043927394457668538900217

theorem tailTrace_3049562 : CollatzResearch.WordTrace tailWord_3049562 prefixEnd_3049562 1043927394457668538900217 := by
  unfold tailWord_3049562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27806665944491293142453735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74151109185310115046543293 27806665944491293142453735)
  ·
    refine ⟨41709998916736939713680603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27806665944491293142453735 41709998916736939713680603)
    ·
      refine ⟨62564998375105409570520905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41709998916736939713680603 62564998375105409570520905)
      ·
        refine ⟨46923748781329057177890679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62564998375105409570520905 46923748781329057177890679)
        ·
          refine ⟨70385623171993585766836019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46923748781329057177890679 70385623171993585766836019)
          ·
            refine ⟨105578434757990378650254029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70385623171993585766836019 105578434757990378650254029)
            ·
              refine ⟨39591913034246391993845261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105578434757990378650254029 39591913034246391993845261)
              ·
                refine ⟨14846967387842396997691973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39591913034246391993845261 14846967387842396997691973)
                ·
                  refine ⟨2783806385220449437067245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14846967387842396997691973 2783806385220449437067245)
                  ·
                    refine ⟨1043927394457668538900217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2783806385220449437067245 1043927394457668538900217)
                    ·
                      rfl

theorem cell22_3049562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_3049562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049562 prefixEnd_3049562 := by exact prefixLift 3049562
  have htrace : WordTrace (prefixWord ++ tailWord_3049562) baseStart_3049562 baseEnd_3049562 := by
    simpa [prefixWord, tailWord_3049562, baseEnd_3049562] using wordTrace_append hprefix tailTrace_3049562
  have hstable : (prefixWord ++ tailWord_3049562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049562).length < 2 ^ (prefixWord ++ tailWord_3049562).sum := by decide
  have hdescent : baseEnd_3049562 < baseStart_3049562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049564 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_3049564 : Nat := 118140960795 + 3049564 * 2 ^ 59
def prefixEnd_3049564 : Nat := 4983230072969 + 3 ^ 40 * 3049564 * 2
def baseEnd_3049564 : Nat := 347976026366180400116737

theorem tailTrace_3049564 : CollatzResearch.WordTrace tailWord_3049564 prefixEnd_3049564 347976026366180400116737 := by
  unfold tailWord_3049564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55613368361978963455693873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74151157815971951274258497 55613368361978963455693873)
  ·
    refine ⟨41710026271484222591770405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55613368361978963455693873 41710026271484222591770405)
    ·
      refine ⟨7820629925903291735956951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41710026271484222591770405 7820629925903291735956951)
      ·
        refine ⟨11730944888854937603935427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820629925903291735956951 11730944888854937603935427)
        ·
          refine ⟨17596417333282406405903141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730944888854937603935427 17596417333282406405903141)
          ·
            refine ⟨3299328249990451201106839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17596417333282406405903141 3299328249990451201106839)
            ·
              refine ⟨4948992374985676801660259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299328249990451201106839 4948992374985676801660259)
              ·
                refine ⟨7423488562478515202490389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948992374985676801660259 7423488562478515202490389)
                ·
                  refine ⟨347976026366180400116737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7423488562478515202490389 347976026366180400116737)
                  ·
                    rfl

theorem cell22_3049564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_3049564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049564 prefixEnd_3049564 := by exact prefixLift 3049564
  have htrace : WordTrace (prefixWord ++ tailWord_3049564) baseStart_3049564 baseEnd_3049564 := by
    simpa [prefixWord, tailWord_3049564, baseEnd_3049564] using wordTrace_append hprefix tailTrace_3049564
  have hstable : (prefixWord ++ tailWord_3049564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049564).length < 2 ^ (prefixWord ++ tailWord_3049564).sum := by decide
  have hdescent : baseEnd_3049564 < baseStart_3049564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049626 : List Nat := [3, 1, 1, 5, 3, 1, 1, 7]
def baseStart_3049626 : Nat := 118140960795 + 3049626 * 2 ^ 59
def prefixEnd_3049626 : Nat := 4983230072969 + 3 ^ 40 * 3049626 * 2
def baseEnd_3049626 : Nat := 115994366996177078366669

theorem tailTrace_3049626 : CollatzResearch.WordTrace tailWord_3049626 prefixEnd_3049626 115994366996177078366669 := by
  unfold tailWord_3049626
  simp only [CollatzResearch.WordTrace]
  refine ⟨27807249512433327875036183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74152665366488874333429821 27807249512433327875036183)
  ·
    refine ⟨41710874268649991812554275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27807249512433327875036183 41710874268649991812554275)
    ·
      refine ⟨62566311402974987718831413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41710874268649991812554275 62566311402974987718831413)
      ·
        refine ⟨5865591694028905098640445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62566311402974987718831413 5865591694028905098640445)
        ·
          refine ⟨2199596885260839411990167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5865591694028905098640445 2199596885260839411990167)
          ·
            refine ⟨3299395327891259117985251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199596885260839411990167 3299395327891259117985251)
            ·
              refine ⟨4949092991836888676977877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299395327891259117985251 4949092991836888676977877)
              ·
                refine ⟨115994366996177078366669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4949092991836888676977877 115994366996177078366669)
                ·
                  rfl

theorem cell22_3049626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_3049626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049626 prefixEnd_3049626 := by exact prefixLift 3049626
  have htrace : WordTrace (prefixWord ++ tailWord_3049626) baseStart_3049626 baseEnd_3049626 := by
    simpa [prefixWord, tailWord_3049626, baseEnd_3049626] using wordTrace_append hprefix tailTrace_3049626
  have hstable : (prefixWord ++ tailWord_3049626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049626).length < 2 ^ (prefixWord ++ tailWord_3049626).sum := by decide
  have hdescent : baseEnd_3049626 < baseStart_3049626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049637 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 5]
def baseStart_3049637 : Nat := 118140960795 + 3049637 * 2 ^ 59
def prefixEnd_3049637 : Nat := 4983230072969 + 3 ^ 40 * 3049637 * 2
def baseEnd_3049637 : Nat := 347984356163464447758329

theorem tailTrace_3049637 : CollatzResearch.WordTrace tailWord_3049637 prefixEnd_3049637 347984356163464447758329 := by
  unfold tailWord_3049637
  simp only [CollatzResearch.WordTrace]
  refine ⟨111229399252693460378795165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74152932835128973585863443 111229399252693460378795165)
  ·
    refine ⟨41711024719760047642048187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111229399252693460378795165 41711024719760047642048187)
    ·
      refine ⟨62566537079640071463072281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41711024719760047642048187 62566537079640071463072281)
      ·
        refine ⟨46924902809730053597304211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62566537079640071463072281 46924902809730053597304211)
        ·
          refine ⟨70387354214595080395956317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46924902809730053597304211 70387354214595080395956317)
          ·
            refine ⟨26395257830473155148483619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70387354214595080395956317 26395257830473155148483619)
            ·
              refine ⟨39592886745709732722725429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26395257830473155148483619 39592886745709732722725429)
              ·
                refine ⟨3711833132410287442755509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39592886745709732722725429 3711833132410287442755509)
                ·
                  refine ⟨347984356163464447758329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3711833132410287442755509 347984356163464447758329)
                  ·
                    rfl

theorem cell22_3049637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_3049637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049637 prefixEnd_3049637 := by exact prefixLift 3049637
  have htrace : WordTrace (prefixWord ++ tailWord_3049637) baseStart_3049637 baseEnd_3049637 := by
    simpa [prefixWord, tailWord_3049637, baseEnd_3049637] using wordTrace_append hprefix tailTrace_3049637
  have hstable : (prefixWord ++ tailWord_3049637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049637).length < 2 ^ (prefixWord ++ tailWord_3049637).sum := by decide
  have hdescent : baseEnd_3049637 < baseStart_3049637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049686 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3049686 : Nat := 118140960795 + 3049686 * 2 ^ 59
def prefixEnd_3049686 : Nat := 4983230072969 + 3 ^ 40 * 3049686 * 2
def baseEnd_3049686 : Nat := 1043969842191773548799837

theorem tailTrace_3049686 : CollatzResearch.WordTrace tailWord_3049686 prefixEnd_3049686 1043969842191773548799837 := by
  unfold tailWord_3049686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951949151844746359208057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74154124286343961164885941 6951949151844746359208057)
  ·
    refine ⟨5213961863883559769406043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6951949151844746359208057 5213961863883559769406043)
    ·
      refine ⟨7820942795825339654109065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213961863883559769406043 7820942795825339654109065)
      ·
        refine ⟨5865707096869004740581799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7820942795825339654109065 5865707096869004740581799)
        ·
          refine ⟨8798560645303507110872699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865707096869004740581799 8798560645303507110872699)
          ·
            refine ⟨13197840967955260666309049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8798560645303507110872699 13197840967955260666309049)
            ·
              refine ⟨9898380725966445499731787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13197840967955260666309049 9898380725966445499731787)
              ·
                refine ⟨14847571088949668249597681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9898380725966445499731787 14847571088949668249597681)
                ·
                  refine ⟨11135678316712251187198261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14847571088949668249597681 11135678316712251187198261)
                  ·
                    refine ⟨1043969842191773548799837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11135678316712251187198261 1043969842191773548799837)
                    ·
                      rfl

theorem cell22_3049686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3049686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049686 prefixEnd_3049686 := by exact prefixLift 3049686
  have htrace : WordTrace (prefixWord ++ tailWord_3049686) baseStart_3049686 baseEnd_3049686 := by
    simpa [prefixWord, tailWord_3049686, baseEnd_3049686] using wordTrace_append hprefix tailTrace_3049686
  have hstable : (prefixWord ++ tailWord_3049686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049686).length < 2 ^ (prefixWord ++ tailWord_3049686).sum := by decide
  have hdescent : baseEnd_3049686 < baseStart_3049686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049701 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_3049701 : Nat := 118140960795 + 3049701 * 2 ^ 59
def prefixEnd_3049701 : Nat := 4983230072969 + 3 ^ 40 * 3049701 * 2
def baseEnd_3049701 : Nat := 1043974976998318509674791

theorem tailTrace_3049701 : CollatzResearch.WordTrace tailWord_3049701 prefixEnd_3049701 1043974976998318509674791 := by
  unfold tailWord_3049701
  simp only [CollatzResearch.WordTrace]
  refine ⟨111231733524461599309124957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74154489016307732872749971 111231733524461599309124957)
  ·
    refine ⟨41711900071673099740921859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111231733524461599309124957 41711900071673099740921859)
    ·
      refine ⟨62567850107509649611382789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41711900071673099740921859 62567850107509649611382789)
      ·
        refine ⟨11731471895158059302134273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62567850107509649611382789 11731471895158059302134273)
        ·
          refine ⟨8798603921368544476600705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11731471895158059302134273 8798603921368544476600705)
          ·
            refine ⟨6598952941026408357450529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8798603921368544476600705 6598952941026408357450529)
            ·
              refine ⟨4949214705769806268087897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6598952941026408357450529 4949214705769806268087897)
              ·
                refine ⟨3711911029327354701065923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4949214705769806268087897 3711911029327354701065923)
                ·
                  refine ⟨5567866543991032051598885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3711911029327354701065923 5567866543991032051598885)
                  ·
                    refine ⟨1043974976998318509674791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567866543991032051598885 1043974976998318509674791)
                    ·
                      rfl

theorem cell22_3049701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_3049701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049701 prefixEnd_3049701 := by exact prefixLift 3049701
  have htrace : WordTrace (prefixWord ++ tailWord_3049701) baseStart_3049701 baseEnd_3049701 := by
    simpa [prefixWord, tailWord_3049701, baseEnd_3049701] using wordTrace_append hprefix tailTrace_3049701
  have hstable : (prefixWord ++ tailWord_3049701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049701).length < 2 ^ (prefixWord ++ tailWord_3049701).sum := by decide
  have hdescent : baseEnd_3049701 < baseStart_3049701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049712 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_3049712 : Nat := 118140960795 + 3049712 * 2 ^ 59
def prefixEnd_3049712 : Nat := 4983230072969 + 3 ^ 40 * 3049712 * 2
def baseEnd_3049712 : Nat := 1043978742523118147649757

theorem tailTrace_3049712 : CollatzResearch.WordTrace tailWord_3049712 prefixEnd_3049712 1043978742523118147649757 := by
  unfold tailWord_3049712
  simp only [CollatzResearch.WordTrace]
  refine ⟨55616067363710874093887695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74154756484947832125183593 55616067363710874093887695)
  ·
    refine ⟨83424101045566311140831543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55616067363710874093887695 83424101045566311140831543)
    ·
      refine ⟨125136151568349466711247315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83424101045566311140831543 125136151568349466711247315)
      ·
        refine ⟨187704227352524200066870973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125136151568349466711247315 187704227352524200066870973)
        ·
          refine ⟨70389085257196575025076615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187704227352524200066870973 70389085257196575025076615)
          ·
            refine ⟨105583627885794862537614923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70389085257196575025076615 105583627885794862537614923)
            ·
              refine ⟨158375441828692293806422385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105583627885794862537614923 158375441828692293806422385)
              ·
                refine ⟨118781581371519220354816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158375441828692293806422385 118781581371519220354816789)
                ·
                  refine ⟨5567886626789963454132037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118781581371519220354816789 5567886626789963454132037)
                  ·
                    refine ⟨1043978742523118147649757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567886626789963454132037 1043978742523118147649757)
                    ·
                      rfl

theorem cell22_3049712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_3049712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049712 prefixEnd_3049712 := by exact prefixLift 3049712
  have htrace : WordTrace (prefixWord ++ tailWord_3049712) baseStart_3049712 baseEnd_3049712 := by
    simpa [prefixWord, tailWord_3049712, baseEnd_3049712] using wordTrace_append hprefix tailTrace_3049712
  have hstable : (prefixWord ++ tailWord_3049712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049712).length < 2 ^ (prefixWord ++ tailWord_3049712).sum := by decide
  have hdescent : baseEnd_3049712 < baseStart_3049712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049729 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3049729 : Nat := 118140960795 + 3049729 * 2 ^ 59
def prefixEnd_3049729 : Nat := 4983230072969 + 3 ^ 40 * 3049729 * 2
def baseEnd_3049729 : Nat := 1043984561970535769974705

theorem tailTrace_3049729 : CollatzResearch.WordTrace tailWord_3049729 prefixEnd_3049729 1043984561970535769974705 := by
  unfold tailWord_3049729
  simp only [CollatzResearch.WordTrace]
  refine ⟨111232754768360160091144241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74155169845573440060762827 111232754768360160091144241)
  ·
    refine ⟨83424566076270120068358181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111232754768360160091144241 83424566076270120068358181)
    ·
      refine ⟨15642106139300647512817159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83424566076270120068358181 15642106139300647512817159)
      ·
        refine ⟨23463159208950971269225739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642106139300647512817159 23463159208950971269225739)
        ·
          refine ⟨35194738813426456903838609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23463159208950971269225739 35194738813426456903838609)
          ·
            refine ⟨26396054110069842677878957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35194738813426456903838609 26396054110069842677878957)
            ·
              refine ⟨9898520291276191004204609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26396054110069842677878957 9898520291276191004204609)
              ·
                refine ⟨7423890218457143253153457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9898520291276191004204609 7423890218457143253153457)
                ·
                  refine ⟨5567917663842857439865093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423890218457143253153457 5567917663842857439865093)
                  ·
                    refine ⟨1043984561970535769974705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567917663842857439865093 1043984561970535769974705)
                    ·
                      rfl

theorem cell22_3049729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3049729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049729 prefixEnd_3049729 := by exact prefixLift 3049729
  have htrace : WordTrace (prefixWord ++ tailWord_3049729) baseStart_3049729 baseEnd_3049729 := by
    simpa [prefixWord, tailWord_3049729, baseEnd_3049729] using wordTrace_append hprefix tailTrace_3049729
  have hstable : (prefixWord ++ tailWord_3049729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049729).length < 2 ^ (prefixWord ++ tailWord_3049729).sum := by decide
  have hdescent : baseEnd_3049729 < baseStart_3049729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049772 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_3049772 : Nat := 118140960795 + 3049772 * 2 ^ 59
def prefixEnd_3049772 : Nat := 4983230072969 + 3 ^ 40 * 3049772 * 2
def baseEnd_3049772 : Nat := 347999760583099330383191

theorem tailTrace_3049772 : CollatzResearch.WordTrace tailWord_3049772 prefixEnd_3049772 347999760583099330383191 := by
  unfold tailWord_3049772
  simp only [CollatzResearch.WordTrace]
  refine ⟨55617161553602189217479785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74156215404802918956639713 55617161553602189217479785)
  ·
    refine ⟨41712871165201641913109839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55617161553602189217479785 41712871165201641913109839)
    ·
      refine ⟨62569306747802462869664759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41712871165201641913109839 62569306747802462869664759)
      ·
        refine ⟨93853960121703694304497139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62569306747802462869664759 93853960121703694304497139)
        ·
          refine ⟨140780940182555541456745709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93853960121703694304497139 140780940182555541456745709)
          ·
            refine ⟨52792852568458328046279641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140780940182555541456745709 52792852568458328046279641)
            ·
              refine ⟨39594639426343746034709731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52792852568458328046279641 39594639426343746034709731)
              ·
                refine ⟨59391959139515619052064597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39594639426343746034709731 59391959139515619052064597)
                ·
                  refine ⟨347999760583099330383191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59391959139515619052064597 347999760583099330383191)
                  ·
                    rfl

theorem cell22_3049772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_3049772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049772 prefixEnd_3049772 := by exact prefixLift 3049772
  have htrace : WordTrace (prefixWord ++ tailWord_3049772) baseStart_3049772 baseEnd_3049772 := by
    simpa [prefixWord, tailWord_3049772, baseEnd_3049772] using wordTrace_append hprefix tailTrace_3049772
  have hstable : (prefixWord ++ tailWord_3049772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049772).length < 2 ^ (prefixWord ++ tailWord_3049772).sum := by decide
  have hdescent : baseEnd_3049772 < baseStart_3049772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049804 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_3049804 : Nat := 118140960795 + 3049804 * 2 ^ 59
def prefixEnd_3049804 : Nat := 4983230072969 + 3 ^ 40 * 3049804 * 2
def baseEnd_3049804 : Nat := 1044010236003260574349475

theorem tailTrace_3049804 : CollatzResearch.WordTrace tailWord_3049804 prefixEnd_3049804 1044010236003260574349475 := by
  unfold tailWord_3049804
  simp only [CollatzResearch.WordTrace]
  refine ⟨55617745121544223950062233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74156993495392298600082977 55617745121544223950062233)
  ·
    refine ⟨41713308841158167962546675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55617745121544223950062233 41713308841158167962546675)
    ·
      refine ⟨62569963261737251943820013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41713308841158167962546675 62569963261737251943820013)
      ·
        refine ⟨23463736223151469478932505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62569963261737251943820013 23463736223151469478932505)
        ·
          refine ⟨17597802167363602109199379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23463736223151469478932505 17597802167363602109199379)
          ·
            refine ⟨26396703251045403163799069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17597802167363602109199379 26396703251045403163799069)
            ·
              refine ⟨9898763719142026186424651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26396703251045403163799069 9898763719142026186424651)
              ·
                refine ⟨14848145578713039279636977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9898763719142026186424651 14848145578713039279636977)
                ·
                  refine ⟨11136109184034779459727733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14848145578713039279636977 11136109184034779459727733)
                  ·
                    refine ⟨1044010236003260574349475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11136109184034779459727733 1044010236003260574349475)
                    ·
                      rfl

theorem cell22_3049804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_3049804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049804 prefixEnd_3049804 := by exact prefixLift 3049804
  have htrace : WordTrace (prefixWord ++ tailWord_3049804) baseStart_3049804 baseEnd_3049804 := by
    simpa [prefixWord, tailWord_3049804, baseEnd_3049804] using wordTrace_append hprefix tailTrace_3049804
  have hstable : (prefixWord ++ tailWord_3049804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049804).length < 2 ^ (prefixWord ++ tailWord_3049804).sum := by decide
  have hdescent : baseEnd_3049804 < baseStart_3049804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049851 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 4]
def baseStart_3049851 : Nat := 118140960795 + 3049851 * 2 ^ 59
def prefixEnd_3049851 : Nat := 4983230072969 + 3 ^ 40 * 3049851 * 2
def baseEnd_3049851 : Nat := 348008775021256039474777

theorem tailTrace_3049851 : CollatzResearch.WordTrace tailWord_3049851 prefixEnd_3049851 348008775021256039474777 := by
  unfold tailWord_3049851
  simp only [CollatzResearch.WordTrace]
  refine ⟨111237204473918174927085407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74158136315945449951390271 111237204473918174927085407)
  ·
    refine ⟨166855806710877262390628111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111237204473918174927085407 166855806710877262390628111)
    ·
      refine ⟨250283710066315893585942167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166855806710877262390628111 250283710066315893585942167)
      ·
        refine ⟨375425565099473840378913251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250283710066315893585942167 375425565099473840378913251)
        ·
          refine ⟨563138347649210760568369877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375425565099473840378913251 563138347649210760568369877)
          ·
            refine ⟨13198555023028377200821169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 563138347649210760568369877 13198555023028377200821169)
            ·
              refine ⟨9898916267271282900615877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13198555023028377200821169 9898916267271282900615877)
              ·
                refine ⟨1856046800113365543865477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9898916267271282900615877 1856046800113365543865477)
                ·
                  refine ⟨348008775021256039474777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856046800113365543865477 348008775021256039474777)
                  ·
                    rfl

theorem cell22_3049851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 4].length) (baseStart_3049851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049851 prefixEnd_3049851 := by exact prefixLift 3049851
  have htrace : WordTrace (prefixWord ++ tailWord_3049851) baseStart_3049851 baseEnd_3049851 := by
    simpa [prefixWord, tailWord_3049851, baseEnd_3049851] using wordTrace_append hprefix tailTrace_3049851
  have hstable : (prefixWord ++ tailWord_3049851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049851).length < 2 ^ (prefixWord ++ tailWord_3049851).sum := by decide
  have hdescent : baseEnd_3049851 < baseStart_3049851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049864 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3049864 : Nat := 118140960795 + 3049864 * 2 ^ 59
def prefixEnd_3049864 : Nat := 4983230072969 + 3 ^ 40 * 3049864 * 2
def baseEnd_3049864 : Nat := 1044030775229440417849291

theorem tailTrace_3049864 : CollatzResearch.WordTrace tailWord_3049864 prefixEnd_3049864 1044030775229440417849291 := by
  unfold tailWord_3049864
  simp only [CollatzResearch.WordTrace]
  refine ⟨55618839311435539073654323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74158452415247385431539097 55618839311435539073654323)
  ·
    refine ⟨83428258967153308610481485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55618839311435539073654323 83428258967153308610481485)
    ·
      refine ⟨31285597112682490728930557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83428258967153308610481485 31285597112682490728930557)
      ·
        refine ⟨11732098917255934023348959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31285597112682490728930557 11732098917255934023348959)
        ·
          refine ⟨17598148375883901035023439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11732098917255934023348959 17598148375883901035023439)
          ·
            refine ⟨26397222563825851552535159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17598148375883901035023439 26397222563825851552535159)
            ·
              refine ⟨39595833845738777328802739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26397222563825851552535159 39595833845738777328802739)
              ·
                refine ⟨59393750768608165993204109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39595833845738777328802739 59393750768608165993204109)
                ·
                  refine ⟨22272656538228062247451541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59393750768608165993204109 22272656538228062247451541)
                  ·
                    refine ⟨1044030775229440417849291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22272656538228062247451541 1044030775229440417849291)
                    ·
                      rfl

theorem cell22_3049864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3049864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049864 prefixEnd_3049864 := by exact prefixLift 3049864
  have htrace : WordTrace (prefixWord ++ tailWord_3049864) baseStart_3049864 baseEnd_3049864 := by
    simpa [prefixWord, tailWord_3049864, baseEnd_3049864] using wordTrace_append hprefix tailTrace_3049864
  have hstable : (prefixWord ++ tailWord_3049864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049864).length < 2 ^ (prefixWord ++ tailWord_3049864).sum := by decide
  have hdescent : baseEnd_3049864 < baseStart_3049864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049878 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3049878 : Nat := 118140960795 + 3049878 * 2 ^ 59
def prefixEnd_3049878 : Nat := 4983230072969 + 3 ^ 40 * 3049878 * 2
def baseEnd_3049878 : Nat := 1044035567715549047999249

theorem tailTrace_3049878 : CollatzResearch.WordTrace tailWord_3049878 prefixEnd_3049878 1044035567715549047999249 := by
  unfold tailWord_3049878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952386827801272408644893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74158792829880239025545525 6952386827801272408644893)
  ·
    refine ⟨2607145060425477153241835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6952386827801272408644893 2607145060425477153241835)
    ·
      refine ⟨3910717590638215729862753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607145060425477153241835 3910717590638215729862753)
      ·
        refine ⟨2933038192978661797397065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3910717590638215729862753 2933038192978661797397065)
        ·
          refine ⟨2199778644733996348047799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2933038192978661797397065 2199778644733996348047799)
          ·
            refine ⟨3299667967100994522071699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199778644733996348047799 3299667967100994522071699)
            ·
              refine ⟨4949501950651491783107549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299667967100994522071699 4949501950651491783107549)
              ·
                refine ⟨1856063231494309418665331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949501950651491783107549 1856063231494309418665331)
                ·
                  refine ⟨2784094847241464127997997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856063231494309418665331 2784094847241464127997997)
                  ·
                    refine ⟨1044035567715549047999249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784094847241464127997997 1044035567715549047999249)
                    ·
                      rfl

theorem cell22_3049878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3049878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049878 prefixEnd_3049878 := by exact prefixLift 3049878
  have htrace : WordTrace (prefixWord ++ tailWord_3049878) baseStart_3049878 baseEnd_3049878 := by
    simpa [prefixWord, tailWord_3049878, baseEnd_3049878] using wordTrace_append hprefix tailTrace_3049878
  have hstable : (prefixWord ++ tailWord_3049878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049878).length < 2 ^ (prefixWord ++ tailWord_3049878).sum := by decide
  have hdescent : baseEnd_3049878 < baseStart_3049878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049885 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 4]
def baseStart_3049885 : Nat := 118140960795 + 3049885 * 2 ^ 59
def prefixEnd_3049885 : Nat := 4983230072969 + 3 ^ 40 * 3049885 * 2
def baseEnd_3049885 : Nat := 348012654652867787691409

theorem tailTrace_3049885 : CollatzResearch.WordTrace tailWord_3049885 prefixEnd_3049885 348012654652867787691409 := by
  unfold tailWord_3049885
  simp only [CollatzResearch.WordTrace]
  refine ⟨111238444555794998733823109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74158963037196665822548739 111238444555794998733823109)
  ·
    refine ⟨20857208354211562262591833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111238444555794998733823109 20857208354211562262591833)
    ·
      refine ⟨15642906265658671696943875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20857208354211562262591833 15642906265658671696943875)
      ·
        refine ⟨23464359398488007545415813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15642906265658671696943875 23464359398488007545415813)
        ·
          refine ⟨4399567387216501414765465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23464359398488007545415813 4399567387216501414765465)
          ·
            refine ⟨3299675540412376061074099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4399567387216501414765465 3299675540412376061074099)
            ·
              refine ⟨4949513310618564091611149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299675540412376061074099 4949513310618564091611149)
              ·
                refine ⟨1856067491481961534354181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949513310618564091611149 1856067491481961534354181)
                ·
                  refine ⟨348012654652867787691409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856067491481961534354181 348012654652867787691409)
                  ·
                    rfl

theorem cell22_3049885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_3049885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049885 prefixEnd_3049885 := by exact prefixLift 3049885
  have htrace : WordTrace (prefixWord ++ tailWord_3049885) baseStart_3049885 baseEnd_3049885 := by
    simpa [prefixWord, tailWord_3049885, baseEnd_3049885] using wordTrace_append hprefix tailTrace_3049885
  have hstable : (prefixWord ++ tailWord_3049885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049885).length < 2 ^ (prefixWord ++ tailWord_3049885).sum := by decide
  have hdescent : baseEnd_3049885 < baseStart_3049885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049896 : List Nat := [2, 1, 6, 1, 1, 1, 10]
def baseStart_3049896 : Nat := 118140960795 + 3049896 * 2 ^ 59
def prefixEnd_3049896 : Nat := 4983230072969 + 3 ^ 40 * 3049896 * 2
def baseEnd_3049896 : Nat := 38668212203089000038859

theorem tailTrace_3049896 : CollatzResearch.WordTrace tailWord_3049896 prefixEnd_3049896 38668212203089000038859 := by
  unfold tailWord_3049896
  simp only [CollatzResearch.WordTrace]
  refine ⟨55619422879377573806236771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74159230505836765074982361 55619422879377573806236771)
  ·
    refine ⟨83429134319066360709355157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55619422879377573806236771 83429134319066360709355157)
    ·
      refine ⟨3910740671206235658251023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83429134319066360709355157 3910740671206235658251023)
      ·
        refine ⟨5866111006809353487376535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3910740671206235658251023 5866111006809353487376535)
        ·
          refine ⟨8799166510214030231064803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866111006809353487376535 8799166510214030231064803)
          ·
            refine ⟨13198749765321045346597205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799166510214030231064803 13198749765321045346597205)
            ·
              refine ⟨38668212203089000038859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13198749765321045346597205 38668212203089000038859)
              ·
                rfl

theorem cell22_3049896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 10].length) (baseStart_3049896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049896 prefixEnd_3049896 := by exact prefixLift 3049896
  have htrace : WordTrace (prefixWord ++ tailWord_3049896) baseStart_3049896 baseEnd_3049896 := by
    simpa [prefixWord, tailWord_3049896, baseEnd_3049896] using wordTrace_append hprefix tailTrace_3049896
  have hstable : (prefixWord ++ tailWord_3049896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049896).length < 2 ^ (prefixWord ++ tailWord_3049896).sum := by decide
  have hdescent : baseEnd_3049896 < baseStart_3049896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049962 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3049962 : Nat := 118140960795 + 3049962 * 2 ^ 59
def prefixEnd_3049962 : Nat := 4983230072969 + 3 ^ 40 * 3049962 * 2
def baseEnd_3049962 : Nat := 1044064322632200828898991

theorem tailTrace_3049962 : CollatzResearch.WordTrace tailWord_3049962 prefixEnd_3049962 1044064322632200828898991 := by
  unfold tailWord_3049962
  simp only [CollatzResearch.WordTrace]
  refine ⟨27810313244129010221094035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74160835317677360589584093 27810313244129010221094035)
  ·
    refine ⟨41715469866193515331641053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27810313244129010221094035 41715469866193515331641053)
    ·
      refine ⟨15643301199822568249365395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41715469866193515331641053 15643301199822568249365395)
      ·
        refine ⟨23464951799733852374048093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15643301199822568249365395 23464951799733852374048093)
        ·
          refine ⟨8799356924900194640268035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23464951799733852374048093 8799356924900194640268035)
          ·
            refine ⟨13199035387350291960402053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799356924900194640268035 13199035387350291960402053)
            ·
              refine ⟨2474819135128179742575385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13199035387350291960402053 2474819135128179742575385)
              ·
                refine ⟨1856114351346134806931539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474819135128179742575385 1856114351346134806931539)
                ·
                  refine ⟨2784171527019202210397309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856114351346134806931539 2784171527019202210397309)
                  ·
                    refine ⟨1044064322632200828898991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784171527019202210397309 1044064322632200828898991)
                    ·
                      rfl

theorem cell22_3049962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3049962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049962 prefixEnd_3049962 := by exact prefixLift 3049962
  have htrace : WordTrace (prefixWord ++ tailWord_3049962) baseStart_3049962 baseEnd_3049962 := by
    simpa [prefixWord, tailWord_3049962, baseEnd_3049962] using wordTrace_append hprefix tailTrace_3049962
  have hstable : (prefixWord ++ tailWord_3049962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049962).length < 2 ^ (prefixWord ++ tailWord_3049962).sum := by decide
  have hdescent : baseEnd_3049962 < baseStart_3049962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3049988 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3049988 : Nat := 118140960795 + 3049988 * 2 ^ 59
def prefixEnd_3049988 : Nat := 4983230072969 + 3 ^ 40 * 3049988 * 2
def baseEnd_3049988 : Nat := 1044073222963545427748911

theorem tailTrace_3049988 : CollatzResearch.WordTrace tailWord_3049988 prefixEnd_3049988 1044073222963545427748911 := by
  unfold tailWord_3049988
  simp only [CollatzResearch.WordTrace]
  refine ⟨55621100637210923662411309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74161467516281231549881745 55621100637210923662411309)
  ·
    refine ⟨20857912738954096373404241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55621100637210923662411309 20857912738954096373404241)
    ·
      refine ⟨15643434554215572280053181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20857912738954096373404241 15643434554215572280053181)
      ·
        refine ⟨5866287957830839605019943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15643434554215572280053181 5866287957830839605019943)
        ·
          refine ⟨8799431936746259407529915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5866287957830839605019943 8799431936746259407529915)
          ·
            refine ⟨13199147905119389111294873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8799431936746259407529915 13199147905119389111294873)
            ·
              refine ⟨9899360928839541833471155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13199147905119389111294873 9899360928839541833471155)
              ·
                refine ⟨14849041393259312750206733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9899360928839541833471155 14849041393259312750206733)
                ·
                  refine ⟨5568390522472242281327525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14849041393259312750206733 5568390522472242281327525)
                  ·
                    refine ⟨1044073222963545427748911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5568390522472242281327525 1044073222963545427748911)
                    ·
                      rfl

theorem cell22_3049988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3049988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3049988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3049988 prefixEnd_3049988 := by exact prefixLift 3049988
  have htrace : WordTrace (prefixWord ++ tailWord_3049988) baseStart_3049988 baseEnd_3049988 := by
    simpa [prefixWord, tailWord_3049988, baseEnd_3049988] using wordTrace_append hprefix tailTrace_3049988
  have hstable : (prefixWord ++ tailWord_3049988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3049988).length < 2 ^ (prefixWord ++ tailWord_3049988).sum := by decide
  have hdescent : baseEnd_3049988 < baseStart_3049988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3049988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050003 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 4]
def baseStart_3050003 : Nat := 118140960795 + 3050003 * 2 ^ 59
def prefixEnd_3050003 : Nat := 4983230072969 + 3 ^ 40 * 3050003 * 2
def baseEnd_3050003 : Nat := 348026119256696796207955

theorem tailTrace_3050003 : CollatzResearch.WordTrace tailWord_3050003 prefixEnd_3050003 348026119256696796207955 := by
  unfold tailWord_3050003
  simp only [CollatzResearch.WordTrace]
  refine ⟨111242748369367504886618663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74161832246245003257745775 111242748369367504886618663)
  ·
    refine ⟨166864122554051257329927995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111242748369367504886618663 166864122554051257329927995)
    ·
      refine ⟨250296183831076885994891993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166864122554051257329927995 250296183831076885994891993)
      ·
        refine ⟨187722137873307664496168995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250296183831076885994891993 187722137873307664496168995)
        ·
          refine ⟨281583206809961496744253493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187722137873307664496168995 281583206809961496744253493)
          ·
            refine ⟨26398425638433890319773765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281583206809961496744253493 26398425638433890319773765)
            ·
              refine ⟨4949704807206354434957581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26398425638433890319773765 4949704807206354434957581)
              ·
                refine ⟨1856139302702382913109093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949704807206354434957581 1856139302702382913109093)
                ·
                  refine ⟨348026119256696796207955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856139302702382913109093 348026119256696796207955)
                  ·
                    rfl

theorem cell22_3050003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 4].length) (baseStart_3050003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050003 prefixEnd_3050003 := by exact prefixLift 3050003
  have htrace : WordTrace (prefixWord ++ tailWord_3050003) baseStart_3050003 baseEnd_3050003 := by
    simpa [prefixWord, tailWord_3050003, baseEnd_3050003] using wordTrace_append hprefix tailTrace_3050003
  have hstable : (prefixWord ++ tailWord_3050003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050003).length < 2 ^ (prefixWord ++ tailWord_3050003).sum := by decide
  have hdescent : baseEnd_3050003 < baseStart_3050003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050020 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3050020 : Nat := 118140960795 + 3050020 * 2 ^ 59
def prefixEnd_3050020 : Nat := 4983230072969 + 3 ^ 40 * 3050020 * 2
def baseEnd_3050020 : Nat := 348028059072502670316271

theorem tailTrace_3050020 : CollatzResearch.WordTrace tailWord_3050020 prefixEnd_3050020 348028059072502670316271 := by
  unfold tailWord_3050020
  simp only [CollatzResearch.WordTrace]
  refine ⟨55621684205152958394993757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74162245606870611193325009 55621684205152958394993757)
  ·
    refine ⟨20858131576932359398122659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55621684205152958394993757 20858131576932359398122659)
    ·
      refine ⟨31287197365398539097183989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858131576932359398122659 31287197365398539097183989)
      ·
        refine ⟨2933174753006113040360999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31287197365398539097183989 2933174753006113040360999)
        ·
          refine ⟨4399762129509169560541499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933174753006113040360999 4399762129509169560541499)
          ·
            refine ⟨6599643194263754340812249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399762129509169560541499 6599643194263754340812249)
            ·
              refine ⟨4949732395697815755609187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6599643194263754340812249 4949732395697815755609187)
              ·
                refine ⟨7424598593546723633413781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4949732395697815755609187 7424598593546723633413781)
                ·
                  refine ⟨348028059072502670316271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7424598593546723633413781 348028059072502670316271)
                  ·
                    rfl

theorem cell22_3050020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3050020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050020 prefixEnd_3050020 := by exact prefixLift 3050020
  have htrace : WordTrace (prefixWord ++ tailWord_3050020) baseStart_3050020 baseEnd_3050020 := by
    simpa [prefixWord, tailWord_3050020, baseEnd_3050020] using wordTrace_append hprefix tailTrace_3050020
  have hstable : (prefixWord ++ tailWord_3050020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050020).length < 2 ^ (prefixWord ++ tailWord_3050020).sum := by decide
  have hdescent : baseEnd_3050020 < baseStart_3050020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050035 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 2, 3]
def baseStart_3050035 : Nat := 118140960795 + 3050035 * 2 ^ 59
def prefixEnd_3050035 : Nat := 4983230072969 + 3 ^ 40 * 3050035 * 2
def baseEnd_3050035 : Nat := 1044089312024052971823767

theorem tailTrace_3050035 : CollatzResearch.WordTrace tailWord_3050035 prefixEnd_3050035 1044089312024052971823767 := by
  unfold tailWord_3050035
  simp only [CollatzResearch.WordTrace]
  refine ⟨111243915505251574351783559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74162610336834382901189039 111243915505251574351783559)
  ·
    refine ⟨166865873257877361527675339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111243915505251574351783559 166865873257877361527675339)
    ·
      refine ⟨250298809886816042291513009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166865873257877361527675339 250298809886816042291513009)
      ·
        refine ⟨187724107415112031718634757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250298809886816042291513009 187724107415112031718634757)
        ·
          refine ⟨35198270140333505947244017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187724107415112031718634757 35198270140333505947244017)
          ·
            refine ⟨26398702605250129460433013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35198270140333505947244017 26398702605250129460433013)
            ·
              refine ⟨2474878369242199636915595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26398702605250129460433013 2474878369242199636915595)
              ·
                refine ⟨3712317553863299455373393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2474878369242199636915595 3712317553863299455373393)
                ·
                  refine ⟨2784238165397474591530045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712317553863299455373393 2784238165397474591530045)
                  ·
                    refine ⟨1044089312024052971823767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784238165397474591530045 1044089312024052971823767)
                    ·
                      rfl

theorem cell22_3050035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 3].length) (baseStart_3050035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050035 prefixEnd_3050035 := by exact prefixLift 3050035
  have htrace : WordTrace (prefixWord ++ tailWord_3050035) baseStart_3050035 baseEnd_3050035 := by
    simpa [prefixWord, tailWord_3050035, baseEnd_3050035] using wordTrace_append hprefix tailTrace_3050035
  have hstable : (prefixWord ++ tailWord_3050035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050035).length < 2 ^ (prefixWord ++ tailWord_3050035).sum := by decide
  have hdescent : baseEnd_3050035 < baseStart_3050035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050054 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3050054 : Nat := 118140960795 + 3050054 * 2 ^ 59
def prefixEnd_3050054 : Nat := 4983230072969 + 3 ^ 40 * 3050054 * 2
def baseEnd_3050054 : Nat := 348031938704114418532903

theorem tailTrace_3050054 : CollatzResearch.WordTrace tailWord_3050054 prefixEnd_3050054 348031938704114418532903 := by
  unfold tailWord_3050054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476394015380710643647663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74163072328121827064483477 3476394015380710643647663)
  ·
    refine ⟨5214591023071065965471495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3476394015380710643647663 5214591023071065965471495)
    ·
      refine ⟨7821886534606598948207243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5214591023071065965471495 7821886534606598948207243)
      ·
        refine ⟨11732829801909898422310865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7821886534606598948207243 11732829801909898422310865)
        ·
          refine ⟨8799622351432423816733149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11732829801909898422310865 8799622351432423816733149)
          ·
            refine ⟨3299858381787158931274931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8799622351432423816733149 3299858381787158931274931)
            ·
              refine ⟨4949787572680738396912397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299858381787158931274931 4949787572680738396912397)
              ·
                refine ⟨1856170339755276898842149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4949787572680738396912397 1856170339755276898842149)
                ·
                  refine ⟨348031938704114418532903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856170339755276898842149 348031938704114418532903)
                  ·
                    rfl

theorem cell22_3050054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3050054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050054 prefixEnd_3050054 := by exact prefixLift 3050054
  have htrace : WordTrace (prefixWord ++ tailWord_3050054) baseStart_3050054 baseEnd_3050054 := by
    simpa [prefixWord, tailWord_3050054, baseEnd_3050054] using wordTrace_append hprefix tailTrace_3050054
  have hstable : (prefixWord ++ tailWord_3050054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050054).length < 2 ^ (prefixWord ++ tailWord_3050054).sum := by decide
  have hdescent : baseEnd_3050054 < baseStart_3050054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050080 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 1, 3]
def baseStart_3050080 : Nat := 118140960795 + 3050080 * 2 ^ 59
def prefixEnd_3050080 : Nat := 4983230072969 + 3 ^ 40 * 3050080 * 2
def baseEnd_3050080 : Nat := 1044104716443687854448629

theorem tailTrace_3050080 : CollatzResearch.WordTrace tailWord_3050080 prefixEnd_3050080 1044104716443687854448629 := by
  unfold tailWord_3050080
  simp only [CollatzResearch.WordTrace]
  refine ⟨55622778395044273518585847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74163704526725698024781129 55622778395044273518585847)
  ·
    refine ⟨83434167592566410277878771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55622778395044273518585847 83434167592566410277878771)
    ·
      refine ⟨125151251388849615416818157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83434167592566410277878771 125151251388849615416818157)
      ·
        refine ⟨46931719270818605781306809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125151251388849615416818157 46931719270818605781306809)
        ·
          refine ⟨35198789453113954335980107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46931719270818605781306809 35198789453113954335980107)
          ·
            refine ⟨52798184179670931503970161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35198789453113954335980107 52798184179670931503970161)
            ·
              refine ⟨39598638134753198627977621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52798184179670931503970161 39598638134753198627977621)
              ·
                refine ⟨1856186162566556185686451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39598638134753198627977621 1856186162566556185686451)
                ·
                  refine ⟨2784279243849834278529677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856186162566556185686451 2784279243849834278529677)
                  ·
                    refine ⟨1044104716443687854448629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784279243849834278529677 1044104716443687854448629)
                    ·
                      rfl

theorem cell22_3050080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_3050080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050080 prefixEnd_3050080 := by exact prefixLift 3050080
  have htrace : WordTrace (prefixWord ++ tailWord_3050080) baseStart_3050080 baseEnd_3050080 := by
    simpa [prefixWord, tailWord_3050080, baseEnd_3050080] using wordTrace_append hprefix tailTrace_3050080
  have hstable : (prefixWord ++ tailWord_3050080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050080).length < 2 ^ (prefixWord ++ tailWord_3050080).sum := by decide
  have hdescent : baseEnd_3050080 < baseStart_3050080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050273 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 8]
def baseStart_3050273 : Nat := 118140960795 + 3050273 * 2 ^ 59
def prefixEnd_3050273 : Nat := 4983230072969 + 3 ^ 40 * 3050273 * 2
def baseEnd_3050273 : Nat := 348056928095966561457679

theorem tailTrace_3050273 : CollatzResearch.WordTrace tailWord_3050273 prefixEnd_3050273 348056928095966561457679 := by
  unfold tailWord_3050273
  simp only [CollatzResearch.WordTrace]
  refine ⟨111252596078389340998947473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74168397385592893999298315 111252596078389340998947473)
  ·
    refine ⟨83439447058792005749210605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111252596078389340998947473 83439447058792005749210605)
    ·
      refine ⟨31289792647047002155953977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83439447058792005749210605 31289792647047002155953977)
      ·
        refine ⟨23467344485285251616965483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31289792647047002155953977 23467344485285251616965483)
        ·
          refine ⟨35201016727927877425448225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23467344485285251616965483 35201016727927877425448225)
          ·
            refine ⟨26400762545945908069086169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35201016727927877425448225 26400762545945908069086169)
            ·
              refine ⟨19800571909459431051814627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26400762545945908069086169 19800571909459431051814627)
              ·
                refine ⟨29700857864189146577721941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19800571909459431051814627 29700857864189146577721941)
                ·
                  refine ⟨348056928095966561457679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29700857864189146577721941 348056928095966561457679)
                  ·
                    rfl

theorem cell22_3050273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_3050273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050273 prefixEnd_3050273 := by exact prefixLift 3050273
  have htrace : WordTrace (prefixWord ++ tailWord_3050273) baseStart_3050273 baseEnd_3050273 := by
    simpa [prefixWord, tailWord_3050273, baseEnd_3050273] using wordTrace_append hprefix tailTrace_3050273
  have hstable : (prefixWord ++ tailWord_3050273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050273).length < 2 ^ (prefixWord ++ tailWord_3050273).sum := by decide
  have hdescent : baseEnd_3050273 < baseStart_3050273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050322 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3050322 : Nat := 118140960795 + 3050322 * 2 ^ 59
def prefixEnd_3050322 : Nat := 4983230072969 + 3 ^ 40 * 3050322 * 2
def baseEnd_3050322 : Nat := 1044187557989279889897887

theorem tailTrace_3050322 : CollatzResearch.WordTrace tailWord_3050322 prefixEnd_3050322 1044187557989279889897887 := by
  unfold tailWord_3050322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27813595813802955591870305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74169588836807881578320813 27813595813802955591870305)
  ·
    refine ⟨20860196860352216693902729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27813595813802955591870305 20860196860352216693902729)
    ·
      refine ⟨15645147645264162520427047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20860196860352216693902729 15645147645264162520427047)
      ·
        refine ⟨23467721467896243780640571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15645147645264162520427047 23467721467896243780640571)
        ·
          refine ⟨35201582201844365670960857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23467721467896243780640571 35201582201844365670960857)
          ·
            refine ⟨26401186651383274253220643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35201582201844365670960857 26401186651383274253220643)
            ·
              refine ⟨39601779977074911379830965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26401186651383274253220643 39601779977074911379830965)
              ·
                refine ⟨3712666872850772941859153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39601779977074911379830965 3712666872850772941859153)
                ·
                  refine ⟨2784500154638079706394365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712666872850772941859153 2784500154638079706394365)
                  ·
                    refine ⟨1044187557989279889897887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784500154638079706394365 1044187557989279889897887)
                    ·
                      rfl

theorem cell22_3050322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3050322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050322 prefixEnd_3050322 := by exact prefixLift 3050322
  have htrace : WordTrace (prefixWord ++ tailWord_3050322) baseStart_3050322 baseEnd_3050322 := by
    simpa [prefixWord, tailWord_3050322, baseEnd_3050322] using wordTrace_append hprefix tailTrace_3050322
  have hstable : (prefixWord ++ tailWord_3050322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050322).length < 2 ^ (prefixWord ++ tailWord_3050322).sum := by decide
  have hdescent : baseEnd_3050322 < baseStart_3050322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050335 : List Nat := [1, 1, 2, 3, 1, 3, 5, 6]
def baseStart_3050335 : Nat := 118140960795 + 3050335 * 2 ^ 59
def prefixEnd_3050335 : Nat := 4983230072969 + 3 ^ 40 * 3050335 * 2
def baseEnd_3050335 : Nat := 116021334239439132146983

theorem tailTrace_3050335 : CollatzResearch.WordTrace tailWord_3050335 prefixEnd_3050335 116021334239439132146983 := by
  unfold tailWord_3050335
  simp only [CollatzResearch.WordTrace]
  refine ⟨111254857404164725587704459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74169904936109817058469639 111254857404164725587704459)
  ·
    refine ⟨166882286106247088381556689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111254857404164725587704459 166882286106247088381556689)
    ·
      refine ⟨125161714579685316286167517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166882286106247088381556689 125161714579685316286167517)
      ·
        refine ⟨46935642967381993607312819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125161714579685316286167517 46935642967381993607312819)
        ·
          refine ⟨70403464451072990410969229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46935642967381993607312819 70403464451072990410969229)
          ·
            refine ⟨26401299169152371404113461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70403464451072990410969229 26401299169152371404113461)
            ·
              refine ⟨2475121797108034819135637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26401299169152371404113461 2475121797108034819135637)
              ·
                refine ⟨116021334239439132146983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2475121797108034819135637 116021334239439132146983)
                ·
                  rfl

theorem cell22_3050335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 6].length) (baseStart_3050335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050335 prefixEnd_3050335 := by exact prefixLift 3050335
  have htrace : WordTrace (prefixWord ++ tailWord_3050335) baseStart_3050335 baseEnd_3050335 := by
    simpa [prefixWord, tailWord_3050335, baseEnd_3050335] using wordTrace_append hprefix tailTrace_3050335
  have hstable : (prefixWord ++ tailWord_3050335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050335).length < 2 ^ (prefixWord ++ tailWord_3050335).sum := by decide
  have hdescent : baseEnd_3050335 < baseStart_3050335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050380 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_3050380 : Nat := 118140960795 + 3050380 * 2 ^ 59
def prefixEnd_3050380 : Nat := 4983230072969 + 3 ^ 40 * 3050380 * 2
def baseEnd_3050380 : Nat := 348069137524862357315903

theorem tailTrace_3050380 : CollatzResearch.WordTrace tailWord_3050380 prefixEnd_3050380 348069137524862357315903 := by
  unfold tailWord_3050380
  simp only [CollatzResearch.WordTrace]
  refine ⟨55628249344500849136546297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74170999126001132182061729 55628249344500849136546297)
  ·
    refine ⟨41721187008375636852409723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55628249344500849136546297 41721187008375636852409723)
    ·
      refine ⟨62581780512563455278614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41721187008375636852409723 62581780512563455278614585)
      ·
        refine ⟨46936335384422591458960939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62581780512563455278614585 46936335384422591458960939)
        ·
          refine ⟨70404503076633887188441409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46936335384422591458960939 70404503076633887188441409)
          ·
            refine ⟨52803377307475415391331057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70404503076633887188441409 52803377307475415391331057)
            ·
              refine ⟨39602532980606561543498293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52803377307475415391331057 39602532980606561543498293)
              ·
                refine ⟨3712737466931865144702965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39602532980606561543498293 3712737466931865144702965)
                ·
                  refine ⟨348069137524862357315903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3712737466931865144702965 348069137524862357315903)
                  ·
                    rfl

theorem cell22_3050380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_3050380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050380 prefixEnd_3050380 := by exact prefixLift 3050380
  have htrace : WordTrace (prefixWord ++ tailWord_3050380) baseStart_3050380 baseEnd_3050380 := by
    simpa [prefixWord, tailWord_3050380, baseEnd_3050380] using wordTrace_append hprefix tailTrace_3050380
  have hstable : (prefixWord ++ tailWord_3050380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050380).length < 2 ^ (prefixWord ++ tailWord_3050380).sum := by decide
  have hdescent : baseEnd_3050380 < baseStart_3050380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050386 : List Nat := [3, 2, 3, 2, 3, 1, 2, 6]
def baseStart_3050386 : Nat := 118140960795 + 3050386 * 2 ^ 59
def prefixEnd_3050386 : Nat := 4983230072969 + 3 ^ 40 * 3050386 * 2
def baseEnd_3050386 : Nat := 116023274055245006255299

theorem tailTrace_3050386 : CollatzResearch.WordTrace tailWord_3050386 prefixEnd_3050386 116023274055245006255299 := by
  unfold tailWord_3050386
  simp only [CollatzResearch.WordTrace]
  refine ⟨27814179381744990324452753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74171145017986640865207341 27814179381744990324452753)
  ·
    refine ⟨20860634536308742743339565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27814179381744990324452753 20860634536308742743339565)
    ·
      refine ⟨7822737951115778528752337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20860634536308742743339565 7822737951115778528752337)
      ·
        refine ⟨5867053463336833896564253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7822737951115778528752337 5867053463336833896564253)
        ·
          refine ⟨2200145048751312711211595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5867053463336833896564253 2200145048751312711211595)
          ·
            refine ⟨3300217573126969066817393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200145048751312711211595 3300217573126969066817393)
            ·
              refine ⟨2475163179845226800113045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3300217573126969066817393 2475163179845226800113045)
              ·
                refine ⟨116023274055245006255299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2475163179845226800113045 116023274055245006255299)
                ·
                  rfl

theorem cell22_3050386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_3050386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050386 prefixEnd_3050386 := by exact prefixLift 3050386
  have htrace : WordTrace (prefixWord ++ tailWord_3050386) baseStart_3050386 baseEnd_3050386 := by
    simpa [prefixWord, tailWord_3050386, baseEnd_3050386] using wordTrace_append hprefix tailTrace_3050386
  have hstable : (prefixWord ++ tailWord_3050386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050386).length < 2 ^ (prefixWord ++ tailWord_3050386).sum := by decide
  have hdescent : baseEnd_3050386 < baseStart_3050386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050401 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 1, 3]
def baseStart_3050401 : Nat := 118140960795 + 3050401 * 2 ^ 59
def prefixEnd_3050401 : Nat := 4983230072969 + 3 ^ 40 * 3050401 * 2
def baseEnd_3050401 : Nat := 1044214601303750017172645

theorem tailTrace_3050401 : CollatzResearch.WordTrace tailWord_3050401 prefixEnd_3050401 1044214601303750017172645 := by
  unfold tailWord_3050401
  simp only [CollatzResearch.WordTrace]
  refine ⟨111257264621925618859607057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74171509747950412573071371 111257264621925618859607057)
  ·
    refine ⟨83442948466444214144705293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111257264621925618859607057 83442948466444214144705293)
    ·
      refine ⟨31291105674916580304264485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83442948466444214144705293 31291105674916580304264485)
      ·
        refine ⟨5867082314046858807049591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31291105674916580304264485 5867082314046858807049591)
        ·
          refine ⟨8800623471070288210574387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867082314046858807049591 8800623471070288210574387)
          ·
            refine ⟨13200935206605432315861581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8800623471070288210574387 13200935206605432315861581)
            ·
              refine ⟨4950350702477037118448093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13200935206605432315861581 4950350702477037118448093)
              ·
                refine ⟨1856381513428888919418035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4950350702477037118448093 1856381513428888919418035)
                ·
                  refine ⟨2784572270143333379127053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856381513428888919418035 2784572270143333379127053)
                  ·
                    refine ⟨1044214601303750017172645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784572270143333379127053 1044214601303750017172645)
                    ·
                      rfl

theorem cell22_3050401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_3050401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050401 prefixEnd_3050401 := by exact prefixLift 3050401
  have htrace : WordTrace (prefixWord ++ tailWord_3050401) baseStart_3050401 baseEnd_3050401 := by
    simpa [prefixWord, tailWord_3050401, baseEnd_3050401] using wordTrace_append hprefix tailTrace_3050401
  have hstable : (prefixWord ++ tailWord_3050401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050401).length < 2 ^ (prefixWord ++ tailWord_3050401).sum := by decide
  have hdescent : baseEnd_3050401 < baseStart_3050401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050457 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_3050457 : Nat := 118140960795 + 3050457 * 2 ^ 59
def prefixEnd_3050457 : Nat := 4983230072969 + 3 ^ 40 * 3050457 * 2
def baseEnd_3050457 : Nat := 1044233771248184537772473

theorem tailTrace_3050457 : CollatzResearch.WordTrace tailWord_3050457 prefixEnd_3050457 1044233771248184537772473 := by
  unfold tailWord_3050457
  simp only [CollatzResearch.WordTrace]
  refine ⟨111259307109722740423645625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74172871406481826949097083 111259307109722740423645625)
  ·
    refine ⟨83444480332292055317734219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111259307109722740423645625 83444480332292055317734219)
    ·
      refine ⟨125166720498438082976601329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83444480332292055317734219 125166720498438082976601329)
      ·
        refine ⟨93875040373828562232450997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125166720498438082976601329 93875040373828562232450997)
        ·
          refine ⟨8800785035046427709292281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93875040373828562232450997 8800785035046427709292281)
          ·
            refine ⟨6600588776284820781969211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800785035046427709292281 6600588776284820781969211)
            ·
              refine ⟨9900883164427231172953817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6600588776284820781969211 9900883164427231172953817)
              ·
                refine ⟨7425662373320423379715363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9900883164427231172953817 7425662373320423379715363)
                ·
                  refine ⟨11138493559980635069573045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7425662373320423379715363 11138493559980635069573045)
                  ·
                    refine ⟨1044233771248184537772473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11138493559980635069573045 1044233771248184537772473)
                    ·
                      rfl

theorem cell22_3050457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_3050457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050457 prefixEnd_3050457 := by exact prefixLift 3050457
  have htrace : WordTrace (prefixWord ++ tailWord_3050457) baseStart_3050457 baseEnd_3050457 := by
    simpa [prefixWord, tailWord_3050457, baseEnd_3050457] using wordTrace_append hprefix tailTrace_3050457
  have hstable : (prefixWord ++ tailWord_3050457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050457).length < 2 ^ (prefixWord ++ tailWord_3050457).sum := by decide
  have hdescent : baseEnd_3050457 < baseStart_3050457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050461 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3050461 : Nat := 118140960795 + 3050461 * 2 ^ 59
def prefixEnd_3050461 : Nat := 4983230072969 + 3 ^ 40 * 3050461 * 2
def baseEnd_3050461 : Nat := 1044235140529929860672461

theorem tailTrace_3050461 : CollatzResearch.WordTrace tailWord_3050461 prefixEnd_3050461 1044235140529929860672461 := by
  unfold tailWord_3050461
  simp only [CollatzResearch.WordTrace]
  refine ⟨111259453001708249106791237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74172968667805499404527491 111259453001708249106791237)
  ·
    refine ⟨20861147437820296707523357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111259453001708249106791237 20861147437820296707523357)
    ·
      refine ⟨7822930289182611265321259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20861147437820296707523357 7822930289182611265321259)
      ·
        refine ⟨11734395433773916897981889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7822930289182611265321259 11734395433773916897981889)
        ·
          refine ⟨8800796575330437673486417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11734395433773916897981889 8800796575330437673486417)
          ·
            refine ⟨6600597431497828255114813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8800796575330437673486417 6600597431497828255114813)
            ·
              refine ⟨2475224036811685595668055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6600597431497828255114813 2475224036811685595668055)
              ·
                refine ⟨3712836055217528393502083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475224036811685595668055 3712836055217528393502083)
                ·
                  refine ⟨5569254082826292590253125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3712836055217528393502083 5569254082826292590253125)
                  ·
                    refine ⟨1044235140529929860672461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569254082826292590253125 1044235140529929860672461)
                    ·
                      rfl

theorem cell22_3050461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3050461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050461 prefixEnd_3050461 := by exact prefixLift 3050461
  have htrace : WordTrace (prefixWord ++ tailWord_3050461) baseStart_3050461 baseEnd_3050461 := by
    simpa [prefixWord, tailWord_3050461, baseEnd_3050461] using wordTrace_append hprefix tailTrace_3050461
  have hstable : (prefixWord ++ tailWord_3050461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050461).length < 2 ^ (prefixWord ++ tailWord_3050461).sum := by decide
  have hdescent : baseEnd_3050461 < baseStart_3050461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050472 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3050472 : Nat := 118140960795 + 3050472 * 2 ^ 59
def prefixEnd_3050472 : Nat := 4983230072969 + 3 ^ 40 * 3050472 * 2
def baseEnd_3050472 : Nat := 1044238906054729498647427

theorem tailTrace_3050472 : CollatzResearch.WordTrace tailWord_3050472 prefixEnd_3050472 1044238906054729498647427 := by
  unfold tailWord_3050472
  simp only [CollatzResearch.WordTrace]
  refine ⟨55629927102334198992720835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74173236136445598656961113 55629927102334198992720835)
  ·
    refine ⟨83444890653501298489081253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55629927102334198992720835 83444890653501298489081253)
    ·
      refine ⟨15645916997531493466702735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83444890653501298489081253 15645916997531493466702735)
      ·
        refine ⟨23468875496297240200054103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15645916997531493466702735 23468875496297240200054103)
        ·
          refine ⟨35203313244445860300081155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23468875496297240200054103 35203313244445860300081155)
          ·
            refine ⟨52804969866668790450121733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35203313244445860300081155 52804969866668790450121733)
            ·
              refine ⟨9900931850000398209397825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52804969866668790450121733 9900931850000398209397825)
              ·
                refine ⟨7425698887500298657048369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9900931850000398209397825 7425698887500298657048369)
                ·
                  refine ⟨5569274165625223992786277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7425698887500298657048369 5569274165625223992786277)
                  ·
                    refine ⟨1044238906054729498647427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569274165625223992786277 1044238906054729498647427)
                    ·
                      rfl

theorem cell22_3050472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3050472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050472 prefixEnd_3050472 := by exact prefixLift 3050472
  have htrace : WordTrace (prefixWord ++ tailWord_3050472) baseStart_3050472 baseEnd_3050472 := by
    simpa [prefixWord, tailWord_3050472, baseEnd_3050472] using wordTrace_append hprefix tailTrace_3050472
  have hstable : (prefixWord ++ tailWord_3050472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050472).length < 2 ^ (prefixWord ++ tailWord_3050472).sum := by decide
  have hdescent : baseEnd_3050472 < baseStart_3050472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050474 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3050474 : Nat := 118140960795 + 3050474 * 2 ^ 59
def prefixEnd_3050474 : Nat := 4983230072969 + 3 ^ 40 * 3050474 * 2
def baseEnd_3050474 : Nat := 1044239590695602160097421

theorem tailTrace_3050474 : CollatzResearch.WordTrace tailWord_3050474 prefixEnd_3050474 1044239590695602160097421 := by
  unfold tailWord_3050474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27814981787665288081753619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74173284767107434884676317 27814981787665288081753619)
  ·
    refine ⟨41722472681497932122630429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27814981787665288081753619 41722472681497932122630429)
    ·
      refine ⟨15645927255561724545986411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41722472681497932122630429 15645927255561724545986411)
      ·
        refine ⟨23468890883342586818979617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15645927255561724545986411 23468890883342586818979617)
        ·
          refine ⟨17601668162506940114234713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23468890883342586818979617 17601668162506940114234713)
          ·
            refine ⟨13201251121880205085676035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17601668162506940114234713 13201251121880205085676035)
            ·
              refine ⟨19801876682820307628514053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13201251121880205085676035 19801876682820307628514053)
              ·
                refine ⟨3712851878028807680346385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19801876682820307628514053 3712851878028807680346385)
                ·
                  refine ⟨2784638908521605760259789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712851878028807680346385 2784638908521605760259789)
                  ·
                    refine ⟨1044239590695602160097421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784638908521605760259789 1044239590695602160097421)
                    ·
                      rfl

theorem cell22_3050474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3050474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050474 prefixEnd_3050474 := by exact prefixLift 3050474
  have htrace : WordTrace (prefixWord ++ tailWord_3050474) baseStart_3050474 baseEnd_3050474 := by
    simpa [prefixWord, tailWord_3050474, baseEnd_3050474] using wordTrace_append hprefix tailTrace_3050474
  have hstable : (prefixWord ++ tailWord_3050474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050474).length < 2 ^ (prefixWord ++ tailWord_3050474).sum := by decide
  have hdescent : baseEnd_3050474 < baseStart_3050474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050515 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 7]
def baseStart_3050515 : Nat := 118140960795 + 3050515 * 2 ^ 59
def prefixEnd_3050515 : Nat := 4983230072969 + 3 ^ 40 * 3050515 * 2
def baseEnd_3050515 : Nat := 348084541944497239940765

theorem tailTrace_3050515 : CollatzResearch.WordTrace tailWord_3050515 prefixEnd_3050515 348084541944497239940765 := by
  unfold tailWord_3050515
  simp only [CollatzResearch.WordTrace]
  refine ⟨111261422543512616329256999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74174281695675077552837999 111261422543512616329256999)
  ·
    refine ⟨166892133815268924493885499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111261422543512616329256999 166892133815268924493885499)
    ·
      refine ⟨250338200722903386740828249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166892133815268924493885499 250338200722903386740828249)
      ·
        refine ⟨187753650542177540055621187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250338200722903386740828249 187753650542177540055621187)
        ·
          refine ⟨281630475813266310083431781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187753650542177540055621187 281630475813266310083431781)
          ·
            refine ⟨52805714214987433140643459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281630475813266310083431781 52805714214987433140643459)
            ·
              refine ⟨79208571322481149710965189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52805714214987433140643459 79208571322481149710965189)
              ·
                refine ⟨14851607122965215570805973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79208571322481149710965189 14851607122965215570805973)
                ·
                  refine ⟨348084541944497239940765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14851607122965215570805973 348084541944497239940765)
                  ·
                    rfl

theorem cell22_3050515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_3050515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050515 prefixEnd_3050515 := by exact prefixLift 3050515
  have htrace : WordTrace (prefixWord ++ tailWord_3050515) baseStart_3050515 baseEnd_3050515 := by
    simpa [prefixWord, tailWord_3050515, baseEnd_3050515] using wordTrace_append hprefix tailTrace_3050515
  have hstable : (prefixWord ++ tailWord_3050515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050515).length < 2 ^ (prefixWord ++ tailWord_3050515).sum := by decide
  have hdescent : baseEnd_3050515 < baseStart_3050515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050600 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_3050600 : Nat := 118140960795 + 3050600 * 2 ^ 59
def prefixEnd_3050600 : Nat := 4983230072969 + 3 ^ 40 * 3050600 * 2
def baseEnd_3050600 : Nat := 348094241023526610482345

theorem tailTrace_3050600 : CollatzResearch.WordTrace tailWord_3050600 prefixEnd_3050600 348094241023526610482345 := by
  unfold tailWord_3050600
  simp only [CollatzResearch.WordTrace]
  refine ⟨55632261374102337923050627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74176348498803117230734169 55632261374102337923050627)
  ·
    refine ⟨83448392061153506884575941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55632261374102337923050627 83448392061153506884575941)
    ·
      refine ⟨15646573511466282540857989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83448392061153506884575941 15646573511466282540857989)
      ·
        refine ⟨2933732533399927976410873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15646573511466282540857989 2933732533399927976410873)
        ·
          refine ⟨2200299400049945982308155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2933732533399927976410873 2200299400049945982308155)
          ·
            refine ⟨3300449100074918973462233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200299400049945982308155 3300449100074918973462233)
            ·
              refine ⟨2475336825056189230096675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3300449100074918973462233 2475336825056189230096675)
              ·
                refine ⟨3713005237584283845145013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475336825056189230096675 3713005237584283845145013)
                ·
                  refine ⟨348094241023526610482345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3713005237584283845145013 348094241023526610482345)
                  ·
                    rfl

theorem cell22_3050600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_3050600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050600 prefixEnd_3050600 := by exact prefixLift 3050600
  have htrace : WordTrace (prefixWord ++ tailWord_3050600) baseStart_3050600 baseEnd_3050600 := by
    simpa [prefixWord, tailWord_3050600, baseEnd_3050600] using wordTrace_append hprefix tailTrace_3050600
  have hstable : (prefixWord ++ tailWord_3050600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050600).length < 2 ^ (prefixWord ++ tailWord_3050600).sum := by decide
  have hdescent : baseEnd_3050600 < baseStart_3050600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050607 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_3050607 : Nat := 118140960795 + 3050607 * 2 ^ 59
def prefixEnd_3050607 : Nat := 4983230072969 + 3 ^ 40 * 3050607 * 2
def baseEnd_3050607 : Nat := 1044285119313634146522013

theorem tailTrace_3050607 : CollatzResearch.WordTrace tailWord_3050607 prefixEnd_3050607 1044285119313634146522013 := by
  unfold tailWord_3050607
  simp only [CollatzResearch.WordTrace]
  refine ⟨111264778059179316041606075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74176518706119544027737383 111264778059179316041606075)
  ·
    refine ⟨166897167088768974062409113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111264778059179316041606075 166897167088768974062409113)
    ·
      refine ⟨125172875316576730546806835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166897167088768974062409113 125172875316576730546806835)
      ·
        refine ⟨187759312974865095820210253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125172875316576730546806835 187759312974865095820210253)
        ·
          refine ⟨70409742365574410932578845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187759312974865095820210253 70409742365574410932578845)
          ·
            refine ⟨26403653387090404099717067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70409742365574410932578845 26403653387090404099717067)
            ·
              refine ⟨39605480080635606149575601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26403653387090404099717067 39605480080635606149575601)
              ·
                refine ⟨29704110060476704612181701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39605480080635606149575601 29704110060476704612181701)
                ·
                  refine ⟨5569520636339382114784069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29704110060476704612181701 5569520636339382114784069)
                  ·
                    refine ⟨1044285119313634146522013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569520636339382114784069 1044285119313634146522013)
                    ·
                      rfl

theorem cell22_3050607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_3050607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050607 prefixEnd_3050607 := by exact prefixLift 3050607
  have htrace : WordTrace (prefixWord ++ tailWord_3050607) baseStart_3050607 baseEnd_3050607 := by
    simpa [prefixWord, tailWord_3050607, baseEnd_3050607] using wordTrace_append hprefix tailTrace_3050607
  have hstable : (prefixWord ++ tailWord_3050607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050607).length < 2 ^ (prefixWord ++ tailWord_3050607).sum := by decide
  have hdescent : baseEnd_3050607 < baseStart_3050607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050682 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_3050682 : Nat := 118140960795 + 3050682 * 2 ^ 59
def prefixEnd_3050682 : Nat := 4983230072969 + 3 ^ 40 * 3050682 * 2
def baseEnd_3050682 : Nat := 1044310793346358950896783

theorem tailTrace_3050682 : CollatzResearch.WordTrace tailWord_3050682 prefixEnd_3050682 1044310793346358950896783 := by
  unfold tailWord_3050682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27816878383476900962646575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74178342355938402567057533 27816878383476900962646575)
  ·
    refine ⟨41725317575215351443969863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27816878383476900962646575 41725317575215351443969863)
    ·
      refine ⟨62587976362823027165954795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41725317575215351443969863 62587976362823027165954795)
      ·
        refine ⟨93881964544234540748932193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62587976362823027165954795 93881964544234540748932193)
        ·
          refine ⟨70411473408175905561699145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93881964544234540748932193 70411473408175905561699145)
          ·
            refine ⟨52808605056131929171274359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70411473408175905561699145 52808605056131929171274359)
            ·
              refine ⟨79212907584197893756911539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52808605056131929171274359 79212907584197893756911539)
              ·
                refine ⟨118819361376296840635367309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79212907584197893756911539 118819361376296840635367309)
                ·
                  refine ⟨44557260516111315238262741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118819361376296840635367309 44557260516111315238262741)
                  ·
                    refine ⟨1044310793346358950896783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44557260516111315238262741 1044310793346358950896783)
                    ·
                      rfl

theorem cell22_3050682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_3050682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050682 prefixEnd_3050682 := by exact prefixLift 3050682
  have htrace : WordTrace (prefixWord ++ tailWord_3050682) baseStart_3050682 baseEnd_3050682 := by
    simpa [prefixWord, tailWord_3050682, baseEnd_3050682] using wordTrace_append hprefix tailTrace_3050682
  have hstable : (prefixWord ++ tailWord_3050682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050682).length < 2 ^ (prefixWord ++ tailWord_3050682).sum := by decide
  have hdescent : baseEnd_3050682 < baseStart_3050682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050694 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3050694 : Nat := 118140960795 + 3050694 * 2 ^ 59
def prefixEnd_3050694 : Nat := 4983230072969 + 3 ^ 40 * 3050694 * 2
def baseEnd_3050694 : Nat := 1044314901191594919596747

theorem tailTrace_3050694 : CollatzResearch.WordTrace tailWord_3050694 prefixEnd_3050694 1044314901191594919596747 := by
  unfold tailWord_3050694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477123475308254059375723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74178634139909419933348757 3477123475308254059375723)
  ·
    refine ⟨5215685212962381089063585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3477123475308254059375723 5215685212962381089063585)
    ·
      refine ⟨3911763909721785816797689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5215685212962381089063585 3911763909721785816797689)
      ·
        refine ⟨2933822932291339362598267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3911763909721785816797689 2933822932291339362598267)
        ·
          refine ⟨4400734398437009043897401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933822932291339362598267 4400734398437009043897401)
          ·
            refine ⟨3300550798827756782923051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400734398437009043897401 3300550798827756782923051)
            ·
              refine ⟨4950826198241635174384577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300550798827756782923051 4950826198241635174384577)
              ·
                refine ⟨3713119648681226380788433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4950826198241635174384577 3713119648681226380788433)
                ·
                  refine ⟨2784839736510919785591325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713119648681226380788433 2784839736510919785591325)
                  ·
                    refine ⟨1044314901191594919596747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784839736510919785591325 1044314901191594919596747)
                    ·
                      rfl

theorem cell22_3050694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3050694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050694 prefixEnd_3050694 := by exact prefixLift 3050694
  have htrace : WordTrace (prefixWord ++ tailWord_3050694) baseStart_3050694 baseEnd_3050694 := by
    simpa [prefixWord, tailWord_3050694, baseEnd_3050694] using wordTrace_append hprefix tailTrace_3050694
  have hstable : (prefixWord ++ tailWord_3050694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050694).length < 2 ^ (prefixWord ++ tailWord_3050694).sum := by decide
  have hdescent : baseEnd_3050694 < baseStart_3050694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050731 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 1, 4]
def baseStart_3050731 : Nat := 118140960795 + 3050731 * 2 ^ 59
def prefixEnd_3050731 : Nat := 4983230072969 + 3 ^ 40 * 3050731 * 2
def baseEnd_3050731 : Nat := 1044327567047739156421633

theorem tailTrace_3050731 : CollatzResearch.WordTrace tailWord_3050731 prefixEnd_3050731 1044327567047739156421633 := by
  unfold tailWord_3050731
  simp only [CollatzResearch.WordTrace]
  refine ⟨111269300710730085219120047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74179533807153390146080031 111269300710730085219120047)
  ·
    refine ⟨166903951066095127828680071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111269300710730085219120047 166903951066095127828680071)
    ·
      refine ⟨250355926599142691743020107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166903951066095127828680071 250355926599142691743020107)
      ·
        refine ⟨375533889898714037614530161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250355926599142691743020107 375533889898714037614530161)
        ·
          refine ⟨281650417424035528210897621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375533889898714037614530161 281650417424035528210897621)
          ·
            refine ⟨6601181658375832692442913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 281650417424035528210897621 6601181658375832692442913)
            ·
              refine ⟨4950886243781874519332185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6601181658375832692442913 4950886243781874519332185)
              ·
                refine ⟨3713164682836405889499139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4950886243781874519332185 3713164682836405889499139)
                ·
                  refine ⟨5569747024254608834248709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713164682836405889499139 5569747024254608834248709)
                  ·
                    refine ⟨1044327567047739156421633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569747024254608834248709 1044327567047739156421633)
                    ·
                      rfl

theorem cell22_3050731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 4].length) (baseStart_3050731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050731 prefixEnd_3050731 := by exact prefixLift 3050731
  have htrace : WordTrace (prefixWord ++ tailWord_3050731) baseStart_3050731 baseEnd_3050731 := by
    simpa [prefixWord, tailWord_3050731, baseEnd_3050731] using wordTrace_append hprefix tailTrace_3050731
  have hstable : (prefixWord ++ tailWord_3050731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050731).length < 2 ^ (prefixWord ++ tailWord_3050731).sum := by decide
  have hdescent : baseEnd_3050731 < baseStart_3050731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050761 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_3050761 : Nat := 118140960795 + 3050761 * 2 ^ 59
def prefixEnd_3050761 : Nat := 4983230072969 + 3 ^ 40 * 3050761 * 2
def baseEnd_3050761 : Nat := 1044337836660829078171541

theorem tailTrace_3050761 : CollatzResearch.WordTrace tailWord_3050761 prefixEnd_3050761 1044337836660829078171541 := by
  unfold tailWord_3050761
  simp only [CollatzResearch.WordTrace]
  refine ⟨111270394900621400342712137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74180263267080933561808091 111270394900621400342712137)
  ·
    refine ⟨83452796175466050257034103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111270394900621400342712137 83452796175466050257034103)
    ·
      refine ⟨125179194263199075385551155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83452796175466050257034103 125179194263199075385551155)
      ·
        refine ⟨187768791394798613078326733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125179194263199075385551155 187768791394798613078326733)
        ·
          refine ⟨70413296773049479904372525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187768791394798613078326733 70413296773049479904372525)
          ·
            refine ⟨26404986289893554964139697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70413296773049479904372525 26404986289893554964139697)
            ·
              refine ⟨19803739717420166223104773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26404986289893554964139697 19803739717420166223104773)
              ·
                refine ⟨3713201197016281166832145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19803739717420166223104773 3713201197016281166832145)
                ·
                  refine ⟨2784900897762210875124109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713201197016281166832145 2784900897762210875124109)
                  ·
                    refine ⟨1044337836660829078171541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784900897762210875124109 1044337836660829078171541)
                    ·
                      rfl

theorem cell22_3050761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_3050761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050761 prefixEnd_3050761 := by exact prefixLift 3050761
  have htrace : WordTrace (prefixWord ++ tailWord_3050761) baseStart_3050761 baseEnd_3050761 := by
    simpa [prefixWord, tailWord_3050761, baseEnd_3050761] using wordTrace_append hprefix tailTrace_3050761
  have hstable : (prefixWord ++ tailWord_3050761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050761).length < 2 ^ (prefixWord ++ tailWord_3050761).sum := by decide
  have hdescent : baseEnd_3050761 < baseStart_3050761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050763 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 4]
def baseStart_3050763 : Nat := 118140960795 + 3050763 * 2 ^ 59
def prefixEnd_3050763 : Nat := 4983230072969 + 3 ^ 40 * 3050763 * 2
def baseEnd_3050763 : Nat := 348112840433900579873845

theorem tailTrace_3050763 : CollatzResearch.WordTrace tailWord_3050763 prefixEnd_3050763 348112840433900579873845 := by
  unfold tailWord_3050763
  simp only [CollatzResearch.WordTrace]
  refine ⟨111270467846614154684284943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74180311897742769789523295 111270467846614154684284943)
  ·
    refine ⟨166905701769921232026427415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111270467846614154684284943 166905701769921232026427415)
    ·
      refine ⟨250358552654881848039641123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166905701769921232026427415 250358552654881848039641123)
      ·
        refine ⟨375537828982322772059461685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250358552654881848039641123 375537828982322772059461685)
        ·
          refine ⟨35206671467092759880574533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375537828982322772059461685 35206671467092759880574533)
          ·
            refine ⟨6601250900079892477607725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35206671467092759880574533 6601250900079892477607725)
            ·
              refine ⟨2475469087529959679102897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6601250900079892477607725 2475469087529959679102897)
              ·
                refine ⟨1856601815647469759327173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2475469087529959679102897 1856601815647469759327173)
                ·
                  refine ⟨348112840433900579873845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1856601815647469759327173 348112840433900579873845)
                  ·
                    rfl

theorem cell22_3050763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 4].length) (baseStart_3050763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050763 prefixEnd_3050763 := by exact prefixLift 3050763
  have htrace : WordTrace (prefixWord ++ tailWord_3050763) baseStart_3050763 baseEnd_3050763 := by
    simpa [prefixWord, tailWord_3050763, baseEnd_3050763] using wordTrace_append hprefix tailTrace_3050763
  have hstable : (prefixWord ++ tailWord_3050763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050763).length < 2 ^ (prefixWord ++ tailWord_3050763).sum := by decide
  have hdescent : baseEnd_3050763 < baseStart_3050763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050778 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_3050778 : Nat := 118140960795 + 3050778 * 2 ^ 59
def prefixEnd_3050778 : Nat := 4983230072969 + 3 ^ 40 * 3050778 * 2
def baseEnd_3050778 : Nat := 1044343656108246700496489

theorem tailTrace_3050778 : CollatzResearch.WordTrace tailWord_3050778 prefixEnd_3050778 1044343656108246700496489 := by
  unfold tailWord_3050778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27817753735389953061520247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74180676627706541497387325 27817753735389953061520247)
  ·
    refine ⟨41726630603084929592280371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27817753735389953061520247 41726630603084929592280371)
    ·
      refine ⟨62589945904627394388420557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41726630603084929592280371 62589945904627394388420557)
      ·
        refine ⟨23471229714235272895657709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62589945904627394388420557 23471229714235272895657709)
        ·
          refine ⟨8801711142838227335871641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23471229714235272895657709 8801711142838227335871641)
          ·
            refine ⟨6601283357128670501903731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8801711142838227335871641 6601283357128670501903731)
            ·
              refine ⟨9901925035693005752855597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6601283357128670501903731 9901925035693005752855597)
              ·
                refine ⟨3713221888384877157320849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9901925035693005752855597 3713221888384877157320849)
                ·
                  refine ⟨2784916416288657867990637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3713221888384877157320849 2784916416288657867990637)
                  ·
                    refine ⟨1044343656108246700496489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2784916416288657867990637 1044343656108246700496489)
                    ·
                      rfl

theorem cell22_3050778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_3050778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050778 prefixEnd_3050778 := by exact prefixLift 3050778
  have htrace : WordTrace (prefixWord ++ tailWord_3050778) baseStart_3050778 baseEnd_3050778 := by
    simpa [prefixWord, tailWord_3050778, baseEnd_3050778] using wordTrace_append hprefix tailTrace_3050778
  have hstable : (prefixWord ++ tailWord_3050778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050778).length < 2 ^ (prefixWord ++ tailWord_3050778).sum := by decide
  have hdescent : baseEnd_3050778 < baseStart_3050778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050782 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3050782 : Nat := 118140960795 + 3050782 * 2 ^ 59
def prefixEnd_3050782 : Nat := 4983230072969 + 3 ^ 40 * 3050782 * 2
def baseEnd_3050782 : Nat := 1044345025389992023396477

theorem tailTrace_3050782 : CollatzResearch.WordTrace tailWord_3050782 prefixEnd_3050782 1044345025389992023396477 := by
  unfold tailWord_3050782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13908895104193165116153325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74180773889030213952817733 13908895104193165116153325)
  ·
    refine ⟨5215835664072436918557497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13908895104193165116153325 5215835664072436918557497)
    ·
      refine ⟨3911876748054327688918123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5215835664072436918557497 3911876748054327688918123)
      ·
        refine ⟨5867815122081491533377185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911876748054327688918123 5867815122081491533377185)
        ·
          refine ⟨4400861341561118650032889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5867815122081491533377185 4400861341561118650032889)
          ·
            refine ⟨3300646006170838987524667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4400861341561118650032889 3300646006170838987524667)
            ·
              refine ⟨4950969009256258481287001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300646006170838987524667 4950969009256258481287001)
              ·
                refine ⟨3713226756942193860965251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4950969009256258481287001 3713226756942193860965251)
                ·
                  refine ⟨5569840135413290791447877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713226756942193860965251 5569840135413290791447877)
                  ·
                    refine ⟨1044345025389992023396477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5569840135413290791447877 1044345025389992023396477)
                    ·
                      rfl

theorem cell22_3050782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3050782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050782 prefixEnd_3050782 := by exact prefixLift 3050782
  have htrace : WordTrace (prefixWord ++ tailWord_3050782) baseStart_3050782 baseEnd_3050782 := by
    simpa [prefixWord, tailWord_3050782, baseEnd_3050782] using wordTrace_append hprefix tailTrace_3050782
  have hstable : (prefixWord ++ tailWord_3050782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050782).length < 2 ^ (prefixWord ++ tailWord_3050782).sum := by decide
  have hdescent : baseEnd_3050782 < baseStart_3050782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050836 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3050836 : Nat := 118140960795 + 3050836 * 2 ^ 59
def prefixEnd_3050836 : Nat := 4983230072969 + 3 ^ 40 * 3050836 * 2
def baseEnd_3050836 : Nat := 348121170231184627515437

theorem tailTrace_3050836 : CollatzResearch.WordTrace tailWord_3050836 prefixEnd_3050836 348121170231184627515437 := by
  unfold tailWord_3050836
  simp only [CollatzResearch.WordTrace]
  refine ⟨55636565187674844075846181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74182086916899792101128241 55636565187674844075846181)
  ·
    refine ⟨10431855972689033264221159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55636565187674844075846181 10431855972689033264221159)
    ·
      refine ⟨15647783959033549896331739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10431855972689033264221159 15647783959033549896331739)
      ·
        refine ⟨23471675938550324844497609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15647783959033549896331739 23471675938550324844497609)
        ·
          refine ⟨17603756953912743633373207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23471675938550324844497609 17603756953912743633373207)
          ·
            refine ⟨26405635430869115450059811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17603756953912743633373207 26405635430869115450059811)
            ·
              refine ⟨39608453146303673175089717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26405635430869115450059811 39608453146303673175089717)
              ·
                refine ⟨3713292482465969360164661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39608453146303673175089717 3713292482465969360164661)
                ·
                  refine ⟨348121170231184627515437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3713292482465969360164661 348121170231184627515437)
                  ·
                    rfl

theorem cell22_3050836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3050836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050836 prefixEnd_3050836 := by exact prefixLift 3050836
  have htrace : WordTrace (prefixWord ++ tailWord_3050836) baseStart_3050836 baseEnd_3050836 := by
    simpa [prefixWord, tailWord_3050836, baseEnd_3050836] using wordTrace_append hprefix tailTrace_3050836
  have hstable : (prefixWord ++ tailWord_3050836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050836).length < 2 ^ (prefixWord ++ tailWord_3050836).sum := by decide
  have hdescent : baseEnd_3050836 < baseStart_3050836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050864 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_3050864 : Nat := 118140960795 + 3050864 * 2 ^ 59
def prefixEnd_3050864 : Nat := 4983230072969 + 3 ^ 40 * 3050864 * 2
def baseEnd_3050864 : Nat := 348124365221923714282075

theorem tailTrace_3050864 : CollatzResearch.WordTrace tailWord_3050864 prefixEnd_3050864 348124365221923714282075 := by
  unfold tailWord_3050864
  simp only [CollatzResearch.WordTrace]
  refine ⟨55637075809624124466855823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74182767746165499289141097 55637075809624124466855823)
  ·
    refine ⟨83455613714436186700283735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55637075809624124466855823 83455613714436186700283735)
    ·
      refine ⟨125183420571654280050425603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83455613714436186700283735 125183420571654280050425603)
      ·
        refine ⟨187775130857481420075638405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125183420571654280050425603 187775130857481420075638405)
        ·
          refine ⟨35207837035777766264182201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187775130857481420075638405 35207837035777766264182201)
          ·
            refine ⟨26405877776833324698136651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35207837035777766264182201 26405877776833324698136651)
            ·
              refine ⟨39608816665249987047204977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26405877776833324698136651 39608816665249987047204977)
              ·
                refine ⟨29706612498937490285403733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39608816665249987047204977 29706612498937490285403733)
                ·
                  refine ⟨348124365221923714282075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29706612498937490285403733 348124365221923714282075)
                  ·
                    rfl

theorem cell22_3050864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_3050864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050864 prefixEnd_3050864 := by exact prefixLift 3050864
  have htrace : WordTrace (prefixWord ++ tailWord_3050864) baseStart_3050864 baseEnd_3050864 := by
    simpa [prefixWord, tailWord_3050864, baseEnd_3050864] using wordTrace_append hprefix tailTrace_3050864
  have hstable : (prefixWord ++ tailWord_3050864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050864).length < 2 ^ (prefixWord ++ tailWord_3050864).sum := by decide
  have hdescent : baseEnd_3050864 < baseStart_3050864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050900 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3050900 : Nat := 118140960795 + 3050900 * 2 ^ 59
def prefixEnd_3050900 : Nat := 4983230072969 + 3 ^ 40 * 3050900 * 2
def baseEnd_3050900 : Nat := 1044385419201479048946115

theorem tailTrace_3050900 : CollatzResearch.WordTrace tailWord_3050900 prefixEnd_3050900 1044385419201479048946115 := by
  unfold tailWord_3050900
  simp only [CollatzResearch.WordTrace]
  refine ⟨55637732323558913541011077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74183643098078551388014769 55637732323558913541011077)
  ·
    refine ⟨10432074810667296288939577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55637732323558913541011077 10432074810667296288939577)
    ·
      refine ⟨7824056108000472216704683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10432074810667296288939577 7824056108000472216704683)
      ·
        refine ⟨11736084162000708325057025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824056108000472216704683 11736084162000708325057025)
        ·
          refine ⟨8802063121500531243792769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11736084162000708325057025 8802063121500531243792769)
          ·
            refine ⟨6601547341125398432844577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8802063121500531243792769 6601547341125398432844577)
            ·
              refine ⟨4951160505844048824633433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6601547341125398432844577 4951160505844048824633433)
              ·
                refine ⟨3713370379383036618475075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4951160505844048824633433 3713370379383036618475075)
                ·
                  refine ⟨5570055569074554927712613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3713370379383036618475075 5570055569074554927712613)
                  ·
                    refine ⟨1044385419201479048946115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570055569074554927712613 1044385419201479048946115)
                    ·
                      rfl

theorem cell22_3050900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3050900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050900 prefixEnd_3050900 := by exact prefixLift 3050900
  have htrace : WordTrace (prefixWord ++ tailWord_3050900) baseStart_3050900 baseEnd_3050900 := by
    simpa [prefixWord, tailWord_3050900, baseEnd_3050900] using wordTrace_append hprefix tailTrace_3050900
  have hstable : (prefixWord ++ tailWord_3050900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050900).length < 2 ^ (prefixWord ++ tailWord_3050900).sum := by decide
  have hdescent : baseEnd_3050900 < baseStart_3050900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050911 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_3050911 : Nat := 118140960795 + 3050911 * 2 ^ 59
def prefixEnd_3050911 : Nat := 4983230072969 + 3 ^ 40 * 3050911 * 2
def baseEnd_3050911 : Nat := 1044389184726278686921081

theorem tailTrace_3050911 : CollatzResearch.WordTrace tailWord_3050911 prefixEnd_3050911 1044389184726278686921081 := by
  unfold tailWord_3050911
  simp only [CollatzResearch.WordTrace]
  refine ⟨111275865850077975960672587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74183910566718650640448391 111275865850077975960672587)
  ·
    refine ⟨166913798775116963941008881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111275865850077975960672587 166913798775116963941008881)
    ·
      refine ⟨125185349081337722955756661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166913798775116963941008881 125185349081337722955756661)
      ·
        refine ⟨11736126476375411527102187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125185349081337722955756661 11736126476375411527102187)
        ·
          refine ⟨17604189714563117290653281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736126476375411527102187 17604189714563117290653281)
          ·
            refine ⟨13203142285922337967989961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17604189714563117290653281 13203142285922337967989961)
            ·
              refine ⟨9902356714441753475992471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13203142285922337967989961 9902356714441753475992471)
              ·
                refine ⟨14853535071662630213988707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9902356714441753475992471 14853535071662630213988707)
                ·
                  refine ⟨22280302607493945320983061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14853535071662630213988707 22280302607493945320983061)
                  ·
                    refine ⟨1044389184726278686921081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22280302607493945320983061 1044389184726278686921081)
                    ·
                      rfl

theorem cell22_3050911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_3050911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050911 prefixEnd_3050911 := by exact prefixLift 3050911
  have htrace : WordTrace (prefixWord ++ tailWord_3050911) baseStart_3050911 baseEnd_3050911 := by
    simpa [prefixWord, tailWord_3050911, baseEnd_3050911] using wordTrace_append hprefix tailTrace_3050911
  have hstable : (prefixWord ++ tailWord_3050911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050911).length < 2 ^ (prefixWord ++ tailWord_3050911).sum := by decide
  have hdescent : baseEnd_3050911 < baseStart_3050911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3050958 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_3050958 : Nat := 118140960795 + 3050958 * 2 ^ 59
def prefixEnd_3050958 : Nat := 4983230072969 + 3 ^ 40 * 3050958 * 2
def baseEnd_3050958 : Nat := 1044405273786786230995937

theorem tailTrace_3050958 : CollatzResearch.WordTrace tailWord_3050958 prefixEnd_3050958 1044405273786786230995937 := by
  unfold tailWord_3050958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909697510113462873454191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74185053387271801991755685 13909697510113462873454191)
  ·
    refine ⟨20864546265170194310181287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13909697510113462873454191 20864546265170194310181287)
    ·
      refine ⟨31296819397755291465271931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20864546265170194310181287 31296819397755291465271931)
      ·
        refine ⟨46945229096632937197907897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31296819397755291465271931 46945229096632937197907897)
        ·
          refine ⟨35208921822474702898430923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46945229096632937197907897 35208921822474702898430923)
          ·
            refine ⟨52813382733712054347646385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35208921822474702898430923 52813382733712054347646385)
            ·
              refine ⟨39610037050284040760734789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52813382733712054347646385 39610037050284040760734789)
              ·
                refine ⟨7426881946928257642637773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39610037050284040760734789 7426881946928257642637773)
                ·
                  refine ⟨2785080730098096615989165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7426881946928257642637773 2785080730098096615989165)
                  ·
                    refine ⟨1044405273786786230995937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2785080730098096615989165 1044405273786786230995937)
                    ·
                      rfl

theorem cell22_3050958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_3050958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3050958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3050958 prefixEnd_3050958 := by exact prefixLift 3050958
  have htrace : WordTrace (prefixWord ++ tailWord_3050958) baseStart_3050958 baseEnd_3050958 := by
    simpa [prefixWord, tailWord_3050958, baseEnd_3050958] using wordTrace_append hprefix tailTrace_3050958
  have hstable : (prefixWord ++ tailWord_3050958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3050958).length < 2 ^ (prefixWord ++ tailWord_3050958).sum := by decide
  have hdescent : baseEnd_3050958 < baseStart_3050958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3050958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
