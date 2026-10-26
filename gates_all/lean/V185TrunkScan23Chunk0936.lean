import V185TrunkScan23Chunk0935

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5539404 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5539404 : Nat := 118140960795 + 5539404 * 2 ^ 59
def prefixEnd_5539404 : Nat := 4983230072969 + 3 ^ 40 * 5539404 * 2
def baseEnd_5539404 : Nat := 2844376791438350290074751

theorem tailTrace_5539404 : CollatzResearch.WordTrace tailWord_5539404 prefixEnd_5539404 2844376791438350290074751 := by
  unfold tailWord_5539404
  simp only [CollatzResearch.WordTrace]
  refine ⟨101019331011846418864516633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134692441349128558486022177 101019331011846418864516633)
  ·
    refine ⟨75764498258884814148387475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101019331011846418864516633 75764498258884814148387475)
    ·
      refine ⟨113646747388327221222581213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75764498258884814148387475 113646747388327221222581213)
      ·
        refine ⟨42617530270622707958467955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113646747388327221222581213 42617530270622707958467955)
        ·
          refine ⟨63926295405934061937701933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42617530270622707958467955 63926295405934061937701933)
          ·
            refine ⟨23972360777225273226638225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63926295405934061937701933 23972360777225273226638225)
            ·
              refine ⟨17979270582918954919978669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23972360777225273226638225 17979270582918954919978669)
              ·
                refine ⟨6742226468594608094992001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17979270582918954919978669 6742226468594608094992001)
                ·
                  refine ⟨5056669851445956071244001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6742226468594608094992001 5056669851445956071244001)
                  ·
                    refine ⟨3792502388584467053433001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056669851445956071244001 3792502388584467053433001)
                    ·
                      refine ⟨2844376791438350290074751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792502388584467053433001 2844376791438350290074751)
                      ·
                        rfl

theorem cell23_5539404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5539404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539404 prefixEnd_5539404 := by exact prefixLift 5539404
  have htrace : WordTrace (prefixWord ++ tailWord_5539404) baseStart_5539404 baseEnd_5539404 := by
    simpa [prefixWord, tailWord_5539404, baseEnd_5539404] using wordTrace_append hprefix tailTrace_5539404
  have hstable : (prefixWord ++ tailWord_5539404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539404).length < 2 ^ (prefixWord ++ tailWord_5539404).sum := by decide
  have hdescent : baseEnd_5539404 < baseStart_5539404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539410 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_5539410 : Nat := 118140960795 + 5539410 * 2 ^ 59
def prefixEnd_5539410 : Nat := 4983230072969 + 3 ^ 40 * 5539410 * 2
def baseEnd_5539410 : Nat := 316042208035808585177747

theorem tailTrace_5539410 : CollatzResearch.WordTrace tailWord_5539410 prefixEnd_5539410 316042208035808585177747 := by
  unfold tailWord_5539410
  simp only [CollatzResearch.WordTrace]
  refine ⟨50509720215417775188437921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134692587241114067169167789 50509720215417775188437921)
  ·
    refine ⟨37882290161563331391328441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50509720215417775188437921 37882290161563331391328441)
    ·
      refine ⟨28411717621172498543496331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37882290161563331391328441 28411717621172498543496331)
      ·
        refine ⟨42617576431758747815244497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28411717621172498543496331 42617576431758747815244497)
        ·
          refine ⟨31963182323819060861433373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42617576431758747815244497 31963182323819060861433373)
          ·
            refine ⟨11986193371432147823037515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31963182323819060861433373 11986193371432147823037515)
            ·
              refine ⟨17979290057148221734556273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11986193371432147823037515 17979290057148221734556273)
              ·
                refine ⟨13484467542861166300917205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17979290057148221734556273 13484467542861166300917205)
                ·
                  refine ⟨316042208035808585177747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13484467542861166300917205 316042208035808585177747)
                  ·
                    rfl

theorem cell23_5539410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_5539410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539410 prefixEnd_5539410 := by exact prefixLift 5539410
  have htrace : WordTrace (prefixWord ++ tailWord_5539410) baseStart_5539410 baseEnd_5539410 := by
    simpa [prefixWord, tailWord_5539410, baseEnd_5539410] using wordTrace_append hprefix tailTrace_5539410
  have hstable : (prefixWord ++ tailWord_5539410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539410).length < 2 ^ (prefixWord ++ tailWord_5539410).sum := by decide
  have hdescent : baseEnd_5539410 < baseStart_5539410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539427 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 5]
def baseStart_5539427 : Nat := 118140960795 + 5539427 * 2 ^ 59
def prefixEnd_5539427 : Nat := 4983230072969 + 3 ^ 40 * 5539427 * 2
def baseEnd_5539427 : Nat := 316043177943711522231905

theorem tailTrace_5539427 : CollatzResearch.WordTrace tailWord_5539427 prefixEnd_5539427 316043177943711522231905 := by
  unfold tailWord_5539427
  simp only [CollatzResearch.WordTrace]
  refine ⟨202039500902609512657120535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134693000601739675104747023 202039500902609512657120535)
  ·
    refine ⟨303059251353914268985680803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202039500902609512657120535 303059251353914268985680803)
    ·
      refine ⟨454588877030871403478521205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303059251353914268985680803 454588877030871403478521205)
      ·
        refine ⟨42617707221644194076111363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 454588877030871403478521205 42617707221644194076111363)
        ·
          refine ⟨63926560832466291114167045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42617707221644194076111363 63926560832466291114167045)
          ·
            refine ⟨11986230156087429583906321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63926560832466291114167045 11986230156087429583906321)
            ·
              refine ⟨8989672617065572187929741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11986230156087429583906321 8989672617065572187929741)
              ·
                refine ⟨3371127231399589570473653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8989672617065572187929741 3371127231399589570473653)
                ·
                  refine ⟨316043177943711522231905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3371127231399589570473653 316043177943711522231905)
                  ·
                    rfl

theorem cell23_5539427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 5].length) (baseStart_5539427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539427 prefixEnd_5539427 := by exact prefixLift 5539427
  have htrace : WordTrace (prefixWord ++ tailWord_5539427) baseStart_5539427 baseEnd_5539427 := by
    simpa [prefixWord, tailWord_5539427, baseEnd_5539427] using wordTrace_append hprefix tailTrace_5539427
  have hstable : (prefixWord ++ tailWord_5539427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539427).length < 2 ^ (prefixWord ++ tailWord_5539427).sum := by decide
  have hdescent : baseEnd_5539427 < baseStart_5539427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539433 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_5539433 : Nat := 118140960795 + 5539433 * 2 ^ 59
def prefixEnd_5539433 : Nat := 4983230072969 + 3 ^ 40 * 5539433 * 2
def baseEnd_5539433 : Nat := 2844391682377330676612117

theorem tailTrace_5539433 : CollatzResearch.WordTrace tailWord_5539433 prefixEnd_5539433 2844391682377330676612117 := by
  unfold tailWord_5539433
  simp only [CollatzResearch.WordTrace]
  refine ⟨202039719740587775681838953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134693146493725183787892635 202039719740587775681838953)
  ·
    refine ⟨151529789805440831761379215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202039719740587775681838953 151529789805440831761379215)
    ·
      refine ⟨227294684708161247642068823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151529789805440831761379215 227294684708161247642068823)
      ·
        refine ⟨340942027062241871463103235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227294684708161247642068823 340942027062241871463103235)
        ·
          refine ⟨511413040593362807194654853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340942027062241871463103235 511413040593362807194654853)
          ·
            refine ⟨95889945111255526348997785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 511413040593362807194654853 95889945111255526348997785)
            ·
              refine ⟨71917458833441644761748339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95889945111255526348997785 71917458833441644761748339)
              ·
                refine ⟨107876188250162467142622509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71917458833441644761748339 107876188250162467142622509)
                ·
                  refine ⟨40453570593810925178483441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107876188250162467142622509 40453570593810925178483441)
                  ·
                    refine ⟨30340177945358193883862581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40453570593810925178483441 30340177945358193883862581)
                    ·
                      refine ⟨2844391682377330676612117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30340177945358193883862581 2844391682377330676612117)
                      ·
                        rfl

theorem cell23_5539433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_5539433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539433 prefixEnd_5539433 := by exact prefixLift 5539433
  have htrace : WordTrace (prefixWord ++ tailWord_5539433) baseStart_5539433 baseEnd_5539433 := by
    simpa [prefixWord, tailWord_5539433, baseEnd_5539433] using wordTrace_append hprefix tailTrace_5539433
  have hstable : (prefixWord ++ tailWord_5539433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539433).length < 2 ^ (prefixWord ++ tailWord_5539433).sum := by decide
  have hdescent : baseEnd_5539433 < baseStart_5539433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539438 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5539438 : Nat := 118140960795 + 5539438 * 2 ^ 59
def prefixEnd_5539438 : Nat := 4983230072969 + 3 ^ 40 * 5539438 * 2
def baseEnd_5539438 : Nat := 2844394249780603157049595

theorem tailTrace_5539438 : CollatzResearch.WordTrace tailWord_5539438 prefixEnd_5539438 2844394249780603157049595 := by
  unfold tailWord_5539438
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254987763196207691971371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134693268070379774357180645 25254987763196207691971371)
  ·
    refine ⟨37882481644794311537957057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25254987763196207691971371 37882481644794311537957057)
    ·
      refine ⟨28411861233595733653467793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37882481644794311537957057 28411861233595733653467793)
      ·
        refine ⟨21308895925196800240100845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28411861233595733653467793 21308895925196800240100845)
        ·
          refine ⟨7990835971948800090037817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21308895925196800240100845 7990835971948800090037817)
          ·
            refine ⟨5993126978961600067528363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7990835971948800090037817 5993126978961600067528363)
            ·
              refine ⟨8989690468442400101292545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993126978961600067528363 8989690468442400101292545)
              ·
                refine ⟨6742267851331800075969409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8989690468442400101292545 6742267851331800075969409)
                ·
                  refine ⟨5056700888498850056977057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6742267851331800075969409 5056700888498850056977057)
                  ·
                    refine ⟨3792525666374137542732793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056700888498850056977057 3792525666374137542732793)
                    ·
                      refine ⟨2844394249780603157049595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792525666374137542732793 2844394249780603157049595)
                      ·
                        rfl

theorem cell23_5539438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5539438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539438 prefixEnd_5539438 := by exact prefixLift 5539438
  have htrace : WordTrace (prefixWord ++ tailWord_5539438) baseStart_5539438 baseEnd_5539438 := by
    simpa [prefixWord, tailWord_5539438, baseEnd_5539438] using wordTrace_append hprefix tailTrace_5539438
  have hstable : (prefixWord ++ tailWord_5539438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539438).length < 2 ^ (prefixWord ++ tailWord_5539438).sum := by decide
  have hdescent : baseEnd_5539438 < baseStart_5539438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539473 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_5539473 : Nat := 118140960795 + 5539473 * 2 ^ 59
def prefixEnd_5539473 : Nat := 4983230072969 + 3 ^ 40 * 5539473 * 2
def baseEnd_5539473 : Nat := 2844412221603510520111933

theorem tailTrace_5539473 : CollatzResearch.WordTrace tailWord_5539473 prefixEnd_5539473 2844412221603510520111933 := by
  unfold tailWord_5539473
  simp only [CollatzResearch.WordTrace]
  refine ⟨202041178660442862513295073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134694119106961908342196715 202041178660442862513295073)
  ·
    refine ⟨151530883995332146884971305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202041178660442862513295073 151530883995332146884971305)
    ·
      refine ⟨113648162996499110163728479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151530883995332146884971305 113648162996499110163728479)
      ·
        refine ⟨170472244494748665245592719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113648162996499110163728479 170472244494748665245592719)
        ·
          refine ⟨255708366742122997868389079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170472244494748665245592719 255708366742122997868389079)
          ·
            refine ⟨383562550113184496802583619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255708366742122997868389079 383562550113184496802583619)
            ·
              refine ⟨575343825169776745203875429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383562550113184496802583619 575343825169776745203875429)
              ·
                refine ⟨107876967219333139725726643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575343825169776745203875429 107876967219333139725726643)
                ·
                  refine ⟨161815450828999709588589965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107876967219333139725726643 161815450828999709588589965)
                  ·
                    refine ⟨60680794060874891095721237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 161815450828999709588589965 60680794060874891095721237)
                    ·
                      refine ⟨2844412221603510520111933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60680794060874891095721237 2844412221603510520111933)
                      ·
                        rfl

theorem cell23_5539473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_5539473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539473 prefixEnd_5539473 := by exact prefixLift 5539473
  have htrace : WordTrace (prefixWord ++ tailWord_5539473) baseStart_5539473 baseEnd_5539473 := by
    simpa [prefixWord, tailWord_5539473, baseEnd_5539473] using wordTrace_append hprefix tailTrace_5539473
  have hstable : (prefixWord ++ tailWord_5539473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539473).length < 2 ^ (prefixWord ++ tailWord_5539473).sum := by decide
  have hdescent : baseEnd_5539473 < baseStart_5539473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539527 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_5539527 : Nat := 118140960795 + 5539527 * 2 ^ 59
def prefixEnd_5539527 : Nat := 4983230072969 + 3 ^ 40 * 5539527 * 2
def baseEnd_5539527 : Nat := 2844439949558853308836685

theorem tailTrace_5539527 : CollatzResearch.WordTrace tailWord_5539527 prefixEnd_5539527 2844439949558853308836685 := by
  unfold tailWord_5539527
  simp only [CollatzResearch.WordTrace]
  refine ⟨202043148202247229735760835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134695432134831486490507223 202043148202247229735760835)
  ·
    refine ⟨303064722303370844603641253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202043148202247229735760835 303064722303370844603641253)
    ·
      refine ⟨56824635431882033363182735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303064722303370844603641253 56824635431882033363182735)
      ·
        refine ⟨85236953147823050044774103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56824635431882033363182735 85236953147823050044774103)
        ·
          refine ⟨127855429721734575067161155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85236953147823050044774103 127855429721734575067161155)
          ·
            refine ⟨191783144582601862600741733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127855429721734575067161155 191783144582601862600741733)
            ·
              refine ⟨35959339609237849237639075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191783144582601862600741733 35959339609237849237639075)
              ·
                refine ⟨53939009413856773856458613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35959339609237849237639075 53939009413856773856458613)
                ·
                  refine ⟨5056782132549072549042995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53939009413856773856458613 5056782132549072549042995)
                  ·
                    refine ⟨7585173198823608823564493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5056782132549072549042995 7585173198823608823564493)
                    ·
                      refine ⟨2844439949558853308836685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585173198823608823564493 2844439949558853308836685)
                      ·
                        rfl

theorem cell23_5539527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_5539527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539527 prefixEnd_5539527 := by exact prefixLift 5539527
  have htrace : WordTrace (prefixWord ++ tailWord_5539527) baseStart_5539527 baseEnd_5539527 := by
    simpa [prefixWord, tailWord_5539527, baseEnd_5539527] using wordTrace_append hprefix tailTrace_5539527
  have hstable : (prefixWord ++ tailWord_5539527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539527).length < 2 ^ (prefixWord ++ tailWord_5539527).sum := by decide
  have hdescent : baseEnd_5539527 < baseStart_5539527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539555 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 1, 4]
def baseStart_5539555 : Nat := 118140960795 + 5539555 * 2 ^ 59
def prefixEnd_5539555 : Nat := 4983230072969 + 3 ^ 40 * 5539555 * 2
def baseEnd_5539555 : Nat := 948151442339059733095519

theorem tailTrace_5539555 : CollatzResearch.WordTrace tailWord_5539555 prefixEnd_5539555 948151442339059733095519 := by
  unfold tailWord_5539555
  simp only [CollatzResearch.WordTrace]
  refine ⟨202044169446145790517780119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134696112964097193678520079 202044169446145790517780119)
  ·
    refine ⟨303066254169218685776670179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202044169446145790517780119 303066254169218685776670179)
    ·
      refine ⟨454599381253828028665005269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303066254169218685776670179 454599381253828028665005269)
      ·
        refine ⟨10654672998136594421836061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 454599381253828028665005269 10654672998136594421836061)
        ·
          refine ⟨3995502374301222908188523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10654672998136594421836061 3995502374301222908188523)
          ·
            refine ⟨5993253561451834362282785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995502374301222908188523 5993253561451834362282785)
            ·
              refine ⟨4494940171088875771712089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5993253561451834362282785 4494940171088875771712089)
              ·
                refine ⟨3371205128316656828784067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494940171088875771712089 3371205128316656828784067)
                ·
                  refine ⟨5056807692474985243176101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371205128316656828784067 5056807692474985243176101)
                  ·
                    refine ⟨948151442339059733095519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056807692474985243176101 948151442339059733095519)
                    ·
                      rfl

theorem cell23_5539555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 1, 4].length) (baseStart_5539555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539555 prefixEnd_5539555 := by exact prefixLift 5539555
  have htrace : WordTrace (prefixWord ++ tailWord_5539555) baseStart_5539555 baseEnd_5539555 := by
    simpa [prefixWord, tailWord_5539555, baseEnd_5539555] using wordTrace_append hprefix tailTrace_5539555
  have hstable : (prefixWord ++ tailWord_5539555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539555).length < 2 ^ (prefixWord ++ tailWord_5539555).sum := by decide
  have hdescent : baseEnd_5539555 < baseStart_5539555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539584 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2]
def baseStart_5539584 : Nat := 118140960795 + 5539584 * 2 ^ 59
def prefixEnd_5539584 : Nat := 4983230072969 + 3 ^ 40 * 5539584 * 2
def baseEnd_5539584 : Nat := 2844469217956159585823923

theorem tailTrace_5539584 : CollatzResearch.WordTrace tailWord_5539584 prefixEnd_5539584 2844469217956159585823923 := by
  unfold tailWord_5539584
  simp only [CollatzResearch.WordTrace]
  refine ⟨101022613581520364235292903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134696818108693818980390537 101022613581520364235292903)
  ·
    refine ⟨151533920372280546352939355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101022613581520364235292903 151533920372280546352939355)
    ·
      refine ⟨227300880558420819529409033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151533920372280546352939355 227300880558420819529409033)
      ·
        refine ⟨170475660418815614647056775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227300880558420819529409033 170475660418815614647056775)
        ·
          refine ⟨255713490628223421970585163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170475660418815614647056775 255713490628223421970585163)
          ·
            refine ⟨383570235942335132955877745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255713490628223421970585163 383570235942335132955877745)
            ·
              refine ⟨287677676956751349716908309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383570235942335132955877745 287677676956751349716908309)
              ·
                refine ⟨13484891107347719517980077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 287677676956751349716908309 13484891107347719517980077)
                ·
                  refine ⟨5056834165255394819242529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13484891107347719517980077 5056834165255394819242529)
                  ·
                    refine ⟨3792625623941546114431897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056834165255394819242529 3792625623941546114431897)
                    ·
                      refine ⟨2844469217956159585823923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792625623941546114431897 2844469217956159585823923)
                      ·
                        rfl

theorem cell23_5539584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_5539584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539584 prefixEnd_5539584 := by exact prefixLift 5539584
  have htrace : WordTrace (prefixWord ++ tailWord_5539584) baseStart_5539584 baseEnd_5539584 := by
    simpa [prefixWord, tailWord_5539584, baseEnd_5539584] using wordTrace_append hprefix tailTrace_5539584
  have hstable : (prefixWord ++ tailWord_5539584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539584).length < 2 ^ (prefixWord ++ tailWord_5539584).sum := by decide
  have hdescent : baseEnd_5539584 < baseStart_5539584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539587 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3]
def baseStart_5539587 : Nat := 118140960795 + 5539587 * 2 ^ 59
def prefixEnd_5539587 : Nat := 4983230072969 + 3 ^ 40 * 5539587 * 2
def baseEnd_5539587 : Nat := 2844470758398123074086409

theorem tailTrace_5539587 : CollatzResearch.WordTrace tailWord_5539587 prefixEnd_5539587 2844470758398123074086409 := by
  unfold tailWord_5539587
  simp only [CollatzResearch.WordTrace]
  refine ⟨202045336582029859982945015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134696891054686573321963343 202045336582029859982945015)
  ·
    refine ⟨303068004873044789974417523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202045336582029859982945015 303068004873044789974417523)
    ·
      refine ⟨454602007309567184961626285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303068004873044789974417523 454602007309567184961626285)
      ·
        refine ⟨170475752741087694360609857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454602007309567184961626285 170475752741087694360609857)
        ·
          refine ⟨127856814555815770770457393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170475752741087694360609857 127856814555815770770457393)
          ·
            refine ⟨95892610916861828077843045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127856814555815770770457393 95892610916861828077843045)
            ·
              refine ⟨17979864546911592764595571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95892610916861828077843045 17979864546911592764595571)
              ·
                refine ⟨26969796820367389146893357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17979864546911592764595571 26969796820367389146893357)
                ·
                  refine ⟨10113673807637770930085009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26969796820367389146893357 10113673807637770930085009)
                  ·
                    refine ⟨7585255355728328197563757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10113673807637770930085009 7585255355728328197563757)
                    ·
                      refine ⟨2844470758398123074086409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585255355728328197563757 2844470758398123074086409)
                      ·
                        rfl

theorem cell23_5539587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_5539587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539587 prefixEnd_5539587 := by exact prefixLift 5539587
  have htrace : WordTrace (prefixWord ++ tailWord_5539587) baseStart_5539587 baseEnd_5539587 := by
    simpa [prefixWord, tailWord_5539587, baseEnd_5539587] using wordTrace_append hprefix tailTrace_5539587
  have hstable : (prefixWord ++ tailWord_5539587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539587).length < 2 ^ (prefixWord ++ tailWord_5539587).sum := by decide
  have hdescent : baseEnd_5539587 < baseStart_5539587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539618 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_5539618 : Nat := 118140960795 + 5539618 * 2 ^ 59
def prefixEnd_5539618 : Nat := 4983230072969 + 3 ^ 40 * 5539618 * 2
def baseEnd_5539618 : Nat := 2844486676298412452798767

theorem tailTrace_5539618 : CollatzResearch.WordTrace tailWord_5539618 prefixEnd_5539618 2844486676298412452798767 := by
  unfold tailWord_5539618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50511616811229388069330877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134697644829945034851549005 50511616811229388069330877)
  ·
    refine ⟨18941856304211020525999079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50511616811229388069330877 18941856304211020525999079)
    ·
      refine ⟨28412784456316530788998619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18941856304211020525999079 28412784456316530788998619)
      ·
        refine ⟨42619176684474796183497929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28412784456316530788998619 42619176684474796183497929)
        ·
          refine ⟨31964382513356097137623447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42619176684474796183497929 31964382513356097137623447)
          ·
            refine ⟨47946573770034145706435171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31964382513356097137623447 47946573770034145706435171)
            ·
              refine ⟨71919860655051218559652757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47946573770034145706435171 71919860655051218559652757)
              ·
                refine ⟨3371243468205525869983723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71919860655051218559652757 3371243468205525869983723)
                ·
                  refine ⟨5056865202308288804975585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371243468205525869983723 5056865202308288804975585)
                  ·
                    refine ⟨3792648901731216603731689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5056865202308288804975585 3792648901731216603731689)
                    ·
                      refine ⟨2844486676298412452798767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792648901731216603731689 2844486676298412452798767)
                      ·
                        rfl

theorem cell23_5539618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_5539618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539618 prefixEnd_5539618 := by exact prefixLift 5539618
  have htrace : WordTrace (prefixWord ++ tailWord_5539618) baseStart_5539618 baseEnd_5539618 := by
    simpa [prefixWord, tailWord_5539618, baseEnd_5539618] using wordTrace_append hprefix tailTrace_5539618
  have hstable : (prefixWord ++ tailWord_5539618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539618).length < 2 ^ (prefixWord ++ tailWord_5539618).sum := by decide
  have hdescent : baseEnd_5539618 < baseStart_5539618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539634 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_5539634 : Nat := 118140960795 + 5539634 * 2 ^ 59
def prefixEnd_5539634 : Nat := 4983230072969 + 3 ^ 40 * 5539634 * 2
def baseEnd_5539634 : Nat := 2844494891988884390198693

theorem tailTrace_5539634 : CollatzResearch.WordTrace tailWord_5539634 prefixEnd_5539634 2844494891988884390198693 := by
  unfold tailWord_5539634
  simp only [CollatzResearch.WordTrace]
  refine ⟨50511762703214896752476489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134698033875239724673270637 50511762703214896752476489)
  ·
    refine ⟨37883822027411172564357367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50511762703214896752476489 37883822027411172564357367)
    ·
      refine ⟨56825733041116758846536051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37883822027411172564357367 56825733041116758846536051)
      ·
        refine ⟨85238599561675138269804077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56825733041116758846536051 85238599561675138269804077)
        ·
          refine ⟨31964474835628176851176529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85238599561675138269804077 31964474835628176851176529)
          ·
            refine ⟨23973356126721132638382397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31964474835628176851176529 23973356126721132638382397)
            ·
              refine ⟨8990008547520424739393399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23973356126721132638382397 8990008547520424739393399)
              ·
                refine ⟨13485012821280637109090099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8990008547520424739393399 13485012821280637109090099)
                ·
                  refine ⟨20227519231920955663635149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13485012821280637109090099 20227519231920955663635149)
                  ·
                    refine ⟨7585319711970358373863181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20227519231920955663635149 7585319711970358373863181)
                    ·
                      refine ⟨2844494891988884390198693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585319711970358373863181 2844494891988884390198693)
                      ·
                        rfl

theorem cell23_5539634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_5539634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539634 prefixEnd_5539634 := by exact prefixLift 5539634
  have htrace : WordTrace (prefixWord ++ tailWord_5539634) baseStart_5539634 baseEnd_5539634 := by
    simpa [prefixWord, tailWord_5539634, baseEnd_5539634] using wordTrace_append hprefix tailTrace_5539634
  have hstable : (prefixWord ++ tailWord_5539634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539634).length < 2 ^ (prefixWord ++ tailWord_5539634).sum := by decide
  have hdescent : baseEnd_5539634 < baseStart_5539634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539638 : List Nat := [5, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5539638 : Nat := 118140960795 + 5539638 * 2 ^ 59
def prefixEnd_5539638 : Nat := 4983230072969 + 3 ^ 40 * 5539638 * 2
def baseEnd_5539638 : Nat := 2844496945911502374548675

theorem tailTrace_5539638 : CollatzResearch.WordTrace tailWord_5539638 prefixEnd_5539638 2844496945911502374548675 := by
  unfold tailWord_5539638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12627949794052818480815723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134698131136563397128701045 12627949794052818480815723)
  ·
    refine ⟨18941924691079227721223585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12627949794052818480815723 18941924691079227721223585)
    ·
      refine ⟨14206443518309420790917689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18941924691079227721223585 14206443518309420790917689)
      ·
        refine ⟨10654832638732065593188267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14206443518309420790917689 10654832638732065593188267)
        ·
          refine ⟨15982248958098098389782401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10654832638732065593188267 15982248958098098389782401)
          ·
            refine ⟨11986686718573573792336801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15982248958098098389782401 11986686718573573792336801)
            ·
              refine ⟨8990015038930180344252601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11986686718573573792336801 8990015038930180344252601)
              ·
                refine ⟨6742511279197635258189451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8990015038930180344252601 6742511279197635258189451)
                ·
                  refine ⟨10113766918796452887284177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742511279197635258189451 10113766918796452887284177)
                  ·
                    refine ⟨7585325189097339665463133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10113766918796452887284177 7585325189097339665463133)
                    ·
                      refine ⟨2844496945911502374548675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585325189097339665463133 2844496945911502374548675)
                      ·
                        rfl

theorem cell23_5539638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5539638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539638 prefixEnd_5539638 := by exact prefixLift 5539638
  have htrace : WordTrace (prefixWord ++ tailWord_5539638) baseStart_5539638 baseEnd_5539638 := by
    simpa [prefixWord, tailWord_5539638, baseEnd_5539638] using wordTrace_append hprefix tailTrace_5539638
  have hstable : (prefixWord ++ tailWord_5539638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539638).length < 2 ^ (prefixWord ++ tailWord_5539638).sum := by decide
  have hdescent : baseEnd_5539638 < baseStart_5539638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539641 : List Nat := [1, 2, 1, 7, 1, 2, 2, 7]
def baseStart_5539641 : Nat := 118140960795 + 5539641 * 2 ^ 59
def prefixEnd_5539641 : Nat := 4983230072969 + 3 ^ 40 * 5539641 * 2
def baseEnd_5539641 : Nat := 105351795790869106030043

theorem tailTrace_5539641 : CollatzResearch.WordTrace tailWord_5539641 prefixEnd_5539641 105351795790869106030043 := by
  unfold tailWord_5539641
  simp only [CollatzResearch.WordTrace]
  refine ⟨202047306123834227205410777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134698204082556151470273851 202047306123834227205410777)
  ·
    refine ⟨151535479592875670404058083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202047306123834227205410777 151535479592875670404058083)
    ·
      refine ⟨227303219389313505606087125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151535479592875670404058083 227303219389313505606087125)
      ·
        refine ⟨5327419204437035287642667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 227303219389313505606087125 5327419204437035287642667)
        ·
          refine ⟨7991128806655552931464001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327419204437035287642667 7991128806655552931464001)
          ·
            refine ⟨5993346604991664698598001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7991128806655552931464001 5993346604991664698598001)
            ·
              refine ⟨4495009953743748523948501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5993346604991664698598001 4495009953743748523948501)
              ·
                refine ⟨105351795790869106030043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4495009953743748523948501 105351795790869106030043)
                ·
                  rfl

theorem cell23_5539641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 7].length) (baseStart_5539641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539641 prefixEnd_5539641 := by exact prefixLift 5539641
  have htrace : WordTrace (prefixWord ++ tailWord_5539641) baseStart_5539641 baseEnd_5539641 := by
    simpa [prefixWord, tailWord_5539641, baseEnd_5539641] using wordTrace_append hprefix tailTrace_5539641
  have hstable : (prefixWord ++ tailWord_5539641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539641).length < 2 ^ (prefixWord ++ tailWord_5539641).sum := by decide
  have hdescent : baseEnd_5539641 < baseStart_5539641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539644 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_5539644 : Nat := 118140960795 + 5539644 * 2 ^ 59
def prefixEnd_5539644 : Nat := 4983230072969 + 3 ^ 40 * 5539644 * 2
def baseEnd_5539644 : Nat := 2844500026795429351073647

theorem tailTrace_5539644 : CollatzResearch.WordTrace tailWord_5539644 prefixEnd_5539644 2844500026795429351073647 := by
  unfold tailWord_5539644
  simp only [CollatzResearch.WordTrace]
  refine ⟨101023707771411679358884993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134698277028548905811846657 101023707771411679358884993)
  ·
    refine ⟨75767780828558759519163745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101023707771411679358884993 75767780828558759519163745)
    ·
      refine ⟨56825835621419069639372809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75767780828558759519163745 56825835621419069639372809)
      ·
        refine ⟨42619376716064302229529607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56825835621419069639372809 42619376716064302229529607)
        ·
          refine ⟨63929065074096453344294411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42619376716064302229529607 63929065074096453344294411)
          ·
            refine ⟨95893597611144680016441617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63929065074096453344294411 95893597611144680016441617)
            ·
              refine ⟨71920198208358510012331213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95893597611144680016441617 71920198208358510012331213)
              ·
                refine ⟨26970074328134441254624205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71920198208358510012331213 26970074328134441254624205)
                ·
                  refine ⟨10113777873050415470484077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26970074328134441254624205 10113777873050415470484077)
                  ·
                    refine ⟨3792666702393905801431529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10113777873050415470484077 3792666702393905801431529)
                    ·
                      refine ⟨2844500026795429351073647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792666702393905801431529 2844500026795429351073647)
                      ·
                        rfl

theorem cell23_5539644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_5539644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539644 prefixEnd_5539644 := by exact prefixLift 5539644
  have htrace : WordTrace (prefixWord ++ tailWord_5539644) baseStart_5539644 baseEnd_5539644 := by
    simpa [prefixWord, tailWord_5539644, baseEnd_5539644] using wordTrace_append hprefix tailTrace_5539644
  have hstable : (prefixWord ++ tailWord_5539644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539644).length < 2 ^ (prefixWord ++ tailWord_5539644).sum := by decide
  have hdescent : baseEnd_5539644 < baseStart_5539644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539687 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5539687 : Nat := 118140960795 + 5539687 * 2 ^ 59
def prefixEnd_5539687 : Nat := 4983230072969 + 3 ^ 40 * 5539687 * 2
def baseEnd_5539687 : Nat := 2844522106463572682835949

theorem tailTrace_5539687 : CollatzResearch.WordTrace tailWord_5539687 prefixEnd_5539687 2844522106463572682835949 := by
  unfold tailWord_5539687
  simp only [CollatzResearch.WordTrace]
  refine ⟨202048983881667577061585315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134699322587778384707723543 202048983881667577061585315)
  ·
    refine ⟨303073475822501365592377973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202048983881667577061585315 303073475822501365592377973)
    ·
      refine ⟨28413138358359503024285435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303073475822501365592377973 28413138358359503024285435)
      ·
        refine ⟨42619707537539254536428153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28413138358359503024285435 42619707537539254536428153)
        ·
          refine ⟨31964780653154440902321115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42619707537539254536428153 31964780653154440902321115)
          ·
            refine ⟨47947170979731661353481673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31964780653154440902321115 47947170979731661353481673)
            ·
              refine ⟨35960378234798746015111255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47947170979731661353481673 35960378234798746015111255)
              ·
                refine ⟨53940567352198119022666883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35960378234798746015111255 53940567352198119022666883)
                ·
                  refine ⟨80910851028297178534000325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53940567352198119022666883 80910851028297178534000325)
                  ·
                    refine ⟨15170784567805720975125061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80910851028297178534000325 15170784567805720975125061)
                    ·
                      refine ⟨2844522106463572682835949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15170784567805720975125061 2844522106463572682835949)
                      ·
                        rfl

theorem cell23_5539687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5539687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539687 prefixEnd_5539687 := by exact prefixLift 5539687
  have htrace : WordTrace (prefixWord ++ tailWord_5539687) baseStart_5539687 baseEnd_5539687 := by
    simpa [prefixWord, tailWord_5539687, baseEnd_5539687] using wordTrace_append hprefix tailTrace_5539687
  have hstable : (prefixWord ++ tailWord_5539687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539687).length < 2 ^ (prefixWord ++ tailWord_5539687).sum := by decide
  have hdescent : baseEnd_5539687 < baseStart_5539687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539694 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5539694 : Nat := 118140960795 + 5539694 * 2 ^ 59
def prefixEnd_5539694 : Nat := 4983230072969 + 3 ^ 40 * 5539694 * 2
def baseEnd_5539694 : Nat := 2844525700828154155448417

theorem tailTrace_5539694 : CollatzResearch.WordTrace tailWord_5539694 prefixEnd_5539694 2844525700828154155448417 := by
  unfold tailWord_5539694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25256154899080277157136267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134699492795094811504726757 25256154899080277157136267)
  ·
    refine ⟨37884232348620415735704401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25256154899080277157136267 37884232348620415735704401)
    ·
      refine ⟨28413174261465311801778301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37884232348620415735704401 28413174261465311801778301)
      ·
        refine ⟨10654940348049491925666863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28413174261465311801778301 10654940348049491925666863)
        ·
          refine ⟨15982410522074237888500295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10654940348049491925666863 15982410522074237888500295)
          ·
            refine ⟨23973615783111356832750443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15982410522074237888500295 23973615783111356832750443)
            ·
              refine ⟨35960423674667035249125665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23973615783111356832750443 35960423674667035249125665)
              ·
                refine ⟨26970317756000276436844249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35960423674667035249125665 26970317756000276436844249)
                ·
                  refine ⟨20227738317000207327633187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26970317756000276436844249 20227738317000207327633187)
                  ·
                    refine ⟨30341607475500310991449781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20227738317000207327633187 30341607475500310991449781)
                    ·
                      refine ⟨2844525700828154155448417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30341607475500310991449781 2844525700828154155448417)
                      ·
                        rfl

theorem cell23_5539694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5539694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539694 prefixEnd_5539694 := by exact prefixLift 5539694
  have htrace : WordTrace (prefixWord ++ tailWord_5539694) baseStart_5539694 baseEnd_5539694 := by
    simpa [prefixWord, tailWord_5539694, baseEnd_5539694] using wordTrace_append hprefix tailTrace_5539694
  have hstable : (prefixWord ++ tailWord_5539694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539694).length < 2 ^ (prefixWord ++ tailWord_5539694).sum := by decide
  have hdescent : baseEnd_5539694 < baseStart_5539694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539707 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3]
def baseStart_5539707 : Nat := 118140960795 + 5539707 * 2 ^ 59
def prefixEnd_5539707 : Nat := 4983230072969 + 3 ^ 40 * 5539707 * 2
def baseEnd_5539707 : Nat := 2844532376076662604585857

theorem tailTrace_5539707 : CollatzResearch.WordTrace tailWord_5539707 prefixEnd_5539707 2844532376076662604585857 := by
  unfold tailWord_5539707
  simp only [CollatzResearch.WordTrace]
  refine ⟨202049713341595120477313375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134699808894396746984875583 202049713341595120477313375)
  ·
    refine ⟨303074570012392680715970063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202049713341595120477313375 303074570012392680715970063)
    ·
      refine ⟨454611855018589021073955095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303074570012392680715970063 454611855018589021073955095)
      ·
        refine ⟨681917782527883531610932643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454611855018589021073955095 681917782527883531610932643)
        ·
          refine ⟨1022876673791825297416398965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681917782527883531610932643 1022876673791825297416398965)
          ·
            refine ⟨95894688167983621632787403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1022876673791825297416398965 95894688167983621632787403)
            ·
              refine ⟨143842032251975432449181105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95894688167983621632787403 143842032251975432449181105)
              ·
                refine ⟨107881524188981574336885829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143842032251975432449181105 107881524188981574336885829)
                ·
                  refine ⟨20227785785434045188166093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107881524188981574336885829 20227785785434045188166093)
                  ·
                    refine ⟨7585419669537766945562285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20227785785434045188166093 7585419669537766945562285)
                    ·
                      refine ⟨2844532376076662604585857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585419669537766945562285 2844532376076662604585857)
                      ·
                        rfl

theorem cell23_5539707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 3].length) (baseStart_5539707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539707 prefixEnd_5539707 := by exact prefixLift 5539707
  have htrace : WordTrace (prefixWord ++ tailWord_5539707) baseStart_5539707 baseEnd_5539707 := by
    simpa [prefixWord, tailWord_5539707, baseEnd_5539707] using wordTrace_append hprefix tailTrace_5539707
  have hstable : (prefixWord ++ tailWord_5539707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539707).length < 2 ^ (prefixWord ++ tailWord_5539707).sum := by decide
  have hdescent : baseEnd_5539707 < baseStart_5539707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539737 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_5539737 : Nat := 118140960795 + 5539737 * 2 ^ 59
def prefixEnd_5539737 : Nat := 4983230072969 + 3 ^ 40 * 5539737 * 2
def baseEnd_5539737 : Nat := 2844547780496297487210719

theorem tailTrace_5539737 : CollatzResearch.WordTrace tailWord_5539737 prefixEnd_5539737 2844547780496297487210719 := by
  unfold tailWord_5539737
  simp only [CollatzResearch.WordTrace]
  refine ⟨202050807531486435600905465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134700538354324290400603643 202050807531486435600905465)
  ·
    refine ⟨151538105648614826700679099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202050807531486435600905465 151538105648614826700679099)
    ·
      refine ⟨227307158472922240051018649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151538105648614826700679099 227307158472922240051018649)
      ·
        refine ⟨170480368854691680038263987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227307158472922240051018649 170480368854691680038263987)
        ·
          refine ⟨255720553282037520057395981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170480368854691680038263987 255720553282037520057395981)
          ·
            refine ⟨95895207480764070021523493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255720553282037520057395981 95895207480764070021523493)
            ·
              refine ⟨17980351402643263129035655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95895207480764070021523493 17980351402643263129035655)
              ·
                refine ⟨26970527103964894693553483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17980351402643263129035655 26970527103964894693553483)
                ·
                  refine ⟨40455790655947342040330225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26970527103964894693553483 40455790655947342040330225)
                  ·
                    refine ⟨30341842991960506530247669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40455790655947342040330225 30341842991960506530247669)
                    ·
                      refine ⟨2844547780496297487210719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30341842991960506530247669 2844547780496297487210719)
                      ·
                        rfl

theorem cell23_5539737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_5539737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539737 prefixEnd_5539737 := by exact prefixLift 5539737
  have htrace : WordTrace (prefixWord ++ tailWord_5539737) baseStart_5539737 baseEnd_5539737 := by
    simpa [prefixWord, tailWord_5539737, baseEnd_5539737] using wordTrace_append hprefix tailTrace_5539737
  have hstable : (prefixWord ++ tailWord_5539737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539737).length < 2 ^ (prefixWord ++ tailWord_5539737).sum := by decide
  have hdescent : baseEnd_5539737 < baseStart_5539737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539747 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_5539747 : Nat := 118140960795 + 5539747 * 2 ^ 59
def prefixEnd_5539747 : Nat := 4983230072969 + 3 ^ 40 * 5539747 * 2
def baseEnd_5539747 : Nat := 2844552915302842448085673

theorem tailTrace_5539747 : CollatzResearch.WordTrace tailWord_5539747 prefixEnd_5539747 2844552915302842448085673 := by
  unfold tailWord_5539747
  simp only [CollatzResearch.WordTrace]
  refine ⟨202051172261450207308769495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134700781507633471539179663 202051172261450207308769495)
  ·
    refine ⟨303076758392175310963154243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202051172261450207308769495 303076758392175310963154243)
    ·
      refine ⟨454615137588262966444731365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303076758392175310963154243 454615137588262966444731365)
      ·
        refine ⟨85240338297799306208387131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 454615137588262966444731365 85240338297799306208387131)
        ·
          refine ⟨127860507446698959312580697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85240338297799306208387131 127860507446698959312580697)
          ·
            refine ⟨95895380585024219484435523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127860507446698959312580697 95895380585024219484435523)
            ·
              refine ⟨143843070877536329226653285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95895380585024219484435523 143843070877536329226653285)
              ·
                refine ⟨26970575789538061729997491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143843070877536329226653285 26970575789538061729997491)
                ·
                  refine ⟨40455863684307092594996237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26970575789538061729997491 40455863684307092594996237)
                  ·
                    refine ⟨15170948881615159723123589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40455863684307092594996237 15170948881615159723123589)
                    ·
                      refine ⟨2844552915302842448085673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15170948881615159723123589 2844552915302842448085673)
                      ·
                        rfl

theorem cell23_5539747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_5539747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539747 prefixEnd_5539747 := by exact prefixLift 5539747
  have htrace : WordTrace (prefixWord ++ tailWord_5539747) baseStart_5539747 baseEnd_5539747 := by
    simpa [prefixWord, tailWord_5539747, baseEnd_5539747] using wordTrace_append hprefix tailTrace_5539747
  have hstable : (prefixWord ++ tailWord_5539747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539747).length < 2 ^ (prefixWord ++ tailWord_5539747).sum := by decide
  have hdescent : baseEnd_5539747 < baseStart_5539747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539761 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 2, 5]
def baseStart_5539761 : Nat := 118140960795 + 5539761 * 2 ^ 59
def prefixEnd_5539761 : Nat := 4983230072969 + 3 ^ 40 * 5539761 * 2
def baseEnd_5539761 : Nat := 948186701344001797770203

theorem tailTrace_5539761 : CollatzResearch.WordTrace tailWord_5539761 prefixEnd_5539761 948186701344001797770203 := by
  unfold tailWord_5539761
  simp only [CollatzResearch.WordTrace]
  refine ⟨202051682883399487699779137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134701121922266325133186091 202051682883399487699779137)
  ·
    refine ⟨151538762162549615774834353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202051682883399487699779137 151538762162549615774834353)
    ·
      refine ⟨113654071621912211831125765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151538762162549615774834353 113654071621912211831125765)
      ·
        refine ⟨21310138429108539718336081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113654071621912211831125765 21310138429108539718336081)
        ·
          refine ⟨15982603821831404788752061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21310138429108539718336081 15982603821831404788752061)
          ·
            refine ⟨5993476433186776795782023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15982603821831404788752061 5993476433186776795782023)
            ·
              refine ⟨8990214649780165193673035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993476433186776795782023 8990214649780165193673035)
              ·
                refine ⟨13485321974670247790509553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8990214649780165193673035 13485321974670247790509553)
                ·
                  refine ⟨10113991481002685842882165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13485321974670247790509553 10113991481002685842882165)
                  ·
                    refine ⟨948186701344001797770203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10113991481002685842882165 948186701344001797770203)
                    ·
                      rfl

theorem cell23_5539761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_5539761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539761 prefixEnd_5539761 := by exact prefixLift 5539761
  have htrace : WordTrace (prefixWord ++ tailWord_5539761) baseStart_5539761 baseEnd_5539761 := by
    simpa [prefixWord, tailWord_5539761, baseEnd_5539761] using wordTrace_append hprefix tailTrace_5539761
  have hstable : (prefixWord ++ tailWord_5539761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539761).length < 2 ^ (prefixWord ++ tailWord_5539761).sum := by decide
  have hdescent : baseEnd_5539761 < baseStart_5539761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539787 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 8]
def baseStart_5539787 : Nat := 118140960795 + 5539787 * 2 ^ 59
def prefixEnd_5539787 : Nat := 4983230072969 + 3 ^ 40 * 5539787 * 2
def baseEnd_5539787 : Nat := 316063717169891365731721

theorem tailTrace_5539787 : CollatzResearch.WordTrace tailWord_5539787 prefixEnd_5539787 316063717169891365731721 := by
  unfold tailWord_5539787
  simp only [CollatzResearch.WordTrace]
  refine ⟨202052631181305294140225615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134701754120870196093483743 202052631181305294140225615)
  ·
    refine ⟨303078946771957941210338423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202052631181305294140225615 303078946771957941210338423)
    ·
      refine ⟨454618420157936911815507635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303078946771957941210338423 454618420157936911815507635)
      ·
        refine ⟨681927630236905367723261453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454618420157936911815507635 681927630236905367723261453)
        ·
          refine ⟨255722861338839512896223045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681927630236905367723261453 255722861338839512896223045)
          ·
            refine ⟨47948036501032408668041821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255722861338839512896223045 47948036501032408668041821)
            ·
              refine ⟨17980513687887153250515683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47948036501032408668041821 17980513687887153250515683)
              ·
                refine ⟨26970770531830729875773525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17980513687887153250515683 26970770531830729875773525)
                ·
                  refine ⟨316063717169891365731721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26970770531830729875773525 316063717169891365731721)
                  ·
                    rfl

theorem cell23_5539787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 8].length) (baseStart_5539787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539787 prefixEnd_5539787 := by exact prefixLift 5539787
  have htrace : WordTrace (prefixWord ++ tailWord_5539787) baseStart_5539787 baseEnd_5539787 := by
    simpa [prefixWord, tailWord_5539787, baseEnd_5539787] using wordTrace_append hprefix tailTrace_5539787
  have hstable : (prefixWord ++ tailWord_5539787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539787).length < 2 ^ (prefixWord ++ tailWord_5539787).sum := by decide
  have hdescent : baseEnd_5539787 < baseStart_5539787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539791 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 1, 4]
def baseStart_5539791 : Nat := 118140960795 + 5539791 * 2 ^ 59
def prefixEnd_5539791 : Nat := 4983230072969 + 3 ^ 40 * 5539791 * 2
def baseEnd_5539791 : Nat := 948191836150546758645157

theorem tailTrace_5539791 : CollatzResearch.WordTrace tailWord_5539791 prefixEnd_5539791 948191836150546758645157 := by
  unfold tailWord_5539791
  simp only [CollatzResearch.WordTrace]
  refine ⟨202052777073290802823371227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134701851382193868548914151 202052777073290802823371227)
  ·
    refine ⟨303079165609936204235056841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202052777073290802823371227 303079165609936204235056841)
    ·
      refine ⟨227309374207452153176292631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303079165609936204235056841 227309374207452153176292631)
      ·
        refine ⟨340964061311178229764438947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227309374207452153176292631 340964061311178229764438947)
        ·
          refine ⟨511446091966767344646658421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340964061311178229764438947 511446091966767344646658421)
          ·
            refine ⟨47948071121884438560624227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 511446091966767344646658421 47948071121884438560624227)
            ·
              refine ⟨71922106682826657840936341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47948071121884438560624227 71922106682826657840936341)
              ·
                refine ⟨3371348750757499586293891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71922106682826657840936341 3371348750757499586293891)
                ·
                  refine ⟨5057023126136249379440837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371348750757499586293891 5057023126136249379440837)
                  ·
                    refine ⟨948191836150546758645157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057023126136249379440837 948191836150546758645157)
                    ·
                      rfl

theorem cell23_5539791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 1, 4].length) (baseStart_5539791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539791 prefixEnd_5539791 := by exact prefixLift 5539791
  have htrace : WordTrace (prefixWord ++ tailWord_5539791) baseStart_5539791 baseEnd_5539791 := by
    simpa [prefixWord, tailWord_5539791, baseEnd_5539791] using wordTrace_append hprefix tailTrace_5539791
  have hstable : (prefixWord ++ tailWord_5539791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539791).length < 2 ^ (prefixWord ++ tailWord_5539791).sum := by decide
  have hdescent : baseEnd_5539791 < baseStart_5539791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539825 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 1, 4]
def baseStart_5539825 : Nat := 118140960795 + 5539825 * 2 ^ 59
def prefixEnd_5539825 : Nat := 4983230072969 + 3 ^ 40 * 5539825 * 2
def baseEnd_5539825 : Nat := 948197655597964380970105

theorem tailTrace_5539825 : CollatzResearch.WordTrace tailWord_5539825 prefixEnd_5539825 948197655597964380970105 := by
  unfold tailWord_5539825
  simp only [CollatzResearch.WordTrace]
  refine ⟨202054017155167626630108929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134702678103445084420072619 202054017155167626630108929)
  ·
    refine ⟨151540512866375719972581697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202054017155167626630108929 151540512866375719972581697)
    ·
      refine ⟨113655384649781789979436273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151540512866375719972581697 113655384649781789979436273)
      ·
        refine ⟨85241538487336342484577205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113655384649781789979436273 85241538487336342484577205)
        ·
          refine ⟨7991394233187782107929113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85241538487336342484577205 7991394233187782107929113)
          ·
            refine ⟨5993545674890836580946835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7991394233187782107929113 5993545674890836580946835)
            ·
              refine ⟨8990318512336254871420253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993545674890836580946835 8990318512336254871420253)
              ·
                refine ⟨3371369442126095576782595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8990318512336254871420253 3371369442126095576782595)
                ·
                  refine ⟨5057054163189143365173893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371369442126095576782595 5057054163189143365173893)
                  ·
                    refine ⟨948197655597964380970105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057054163189143365173893 948197655597964380970105)
                    ·
                      rfl

theorem cell23_5539825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_5539825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539825 prefixEnd_5539825 := by exact prefixLift 5539825
  have htrace : WordTrace (prefixWord ++ tailWord_5539825) baseStart_5539825 baseEnd_5539825 := by
    simpa [prefixWord, tailWord_5539825, baseEnd_5539825] using wordTrace_append hprefix tailTrace_5539825
  have hstable : (prefixWord ++ tailWord_5539825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539825).length < 2 ^ (prefixWord ++ tailWord_5539825).sum := by decide
  have hdescent : baseEnd_5539825 < baseStart_5539825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539864 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_5539864 : Nat := 118140960795 + 5539864 * 2 ^ 59
def prefixEnd_5539864 : Nat := 4983230072969 + 3 ^ 40 * 5539864 * 2
def baseEnd_5539864 : Nat := 948204330846472830107545

theorem tailTrace_5539864 : CollatzResearch.WordTrace tailWord_5539864 prefixEnd_5539864 948204330846472830107545 := by
  unfold tailWord_5539864
  simp only [CollatzResearch.WordTrace]
  refine ⟨101027719801013168145389323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134703626401350890860519097 101027719801013168145389323)
  ·
    refine ⟨151541579701519752218083985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101027719801013168145389323 151541579701519752218083985)
    ·
      refine ⟨113656184776139814163562989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151541579701519752218083985 113656184776139814163562989)
      ·
        refine ⟨42621069291052430311336121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113656184776139814163562989 42621069291052430311336121)
        ·
          refine ⟨31965801968289322733502091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42621069291052430311336121 31965801968289322733502091)
          ·
            refine ⟨47948702952433984100253137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31965801968289322733502091 47948702952433984100253137)
            ·
              refine ⟨35961527214325488075189853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47948702952433984100253137 35961527214325488075189853)
              ·
                refine ⟨13485572705372058028196195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35961527214325488075189853 13485572705372058028196195)
                ·
                  refine ⟨20228359058058087042294293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13485572705372058028196195 20228359058058087042294293)
                  ·
                    refine ⟨948204330846472830107545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20228359058058087042294293 948204330846472830107545)
                    ·
                      rfl

theorem cell23_5539864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_5539864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539864 prefixEnd_5539864 := by exact prefixLift 5539864
  have htrace : WordTrace (prefixWord ++ tailWord_5539864) baseStart_5539864 baseEnd_5539864 := by
    simpa [prefixWord, tailWord_5539864, baseEnd_5539864] using wordTrace_append hprefix tailTrace_5539864
  have hstable : (prefixWord ++ tailWord_5539864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539864).length < 2 ^ (prefixWord ++ tailWord_5539864).sum := by decide
  have hdescent : baseEnd_5539864 < baseStart_5539864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539868 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_5539868 : Nat := 118140960795 + 5539868 * 2 ^ 59
def prefixEnd_5539868 : Nat := 4983230072969 + 3 ^ 40 * 5539868 * 2
def baseEnd_5539868 : Nat := 948205015487345491557539

theorem tailTrace_5539868 : CollatzResearch.WordTrace tailWord_5539868 prefixEnd_5539868 948205015487345491557539 := by
  unfold tailWord_5539868
  simp only [CollatzResearch.WordTrace]
  refine ⟨101027792747005922486962129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134703723662674563315949505 101027792747005922486962129)
  ·
    refine ⟨75770844560254441865221597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101027792747005922486962129 75770844560254441865221597)
    ·
      refine ⟨28414066710095415699458099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75770844560254441865221597 28414066710095415699458099)
      ·
        refine ⟨42621100065143123549187149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28414066710095415699458099 42621100065143123549187149)
        ·
          refine ⟨15982912524428671330945181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42621100065143123549187149 15982912524428671330945181)
          ·
            refine ⟨5993592196660751749104443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15982912524428671330945181 5993592196660751749104443)
            ·
              refine ⟨8990388294991127623656665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993592196660751749104443 8990388294991127623656665)
              ·
                refine ⟨6742791221243345717742499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8990388294991127623656665 6742791221243345717742499)
                ·
                  refine ⟨10114186831865018576613749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742791221243345717742499 10114186831865018576613749)
                  ·
                    refine ⟨948205015487345491557539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10114186831865018576613749 948205015487345491557539)
                    ·
                      rfl

theorem cell23_5539868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_5539868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539868 prefixEnd_5539868 := by exact prefixLift 5539868
  have htrace : WordTrace (prefixWord ++ tailWord_5539868) baseStart_5539868 baseEnd_5539868 := by
    simpa [prefixWord, tailWord_5539868, baseEnd_5539868] using wordTrace_append hprefix tailTrace_5539868
  have hstable : (prefixWord ++ tailWord_5539868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539868).length < 2 ^ (prefixWord ++ tailWord_5539868).sum := by decide
  have hdescent : baseEnd_5539868 < baseStart_5539868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539888 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4]
def baseStart_5539888 : Nat := 118140960795 + 5539888 * 2 ^ 59
def prefixEnd_5539888 : Nat := 4983230072969 + 3 ^ 40 * 5539888 * 2
def baseEnd_5539888 : Nat := 2844625316075126396422525

theorem tailTrace_5539888 : CollatzResearch.WordTrace tailWord_5539888 prefixEnd_5539888 2844625316075126396422525 := by
  unfold tailWord_5539888
  simp only [CollatzResearch.WordTrace]
  refine ⟨101028157476969694194826159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134704209969292925593101545 101028157476969694194826159)
  ·
    refine ⟨151542236215454541292239239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101028157476969694194826159 151542236215454541292239239)
    ·
      refine ⟨227313354323181811938358859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151542236215454541292239239 227313354323181811938358859)
      ·
        refine ⟨340970031484772717907538289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227313354323181811938358859 340970031484772717907538289)
        ·
          refine ⟨255727523613579538430653717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340970031484772717907538289 255727523613579538430653717)
          ·
            refine ⟨11987227669386540863936893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255727523613579538430653717 11987227669386540863936893)
            ·
              refine ⟨4495210376019952823976335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11987227669386540863936893 4495210376019952823976335)
              ·
                refine ⟨6742815564029929235964503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495210376019952823976335 6742815564029929235964503)
                ·
                  refine ⟨10114223346044893853946755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742815564029929235964503 10114223346044893853946755)
                  ·
                    refine ⟨15171335019067340780920133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10114223346044893853946755 15171335019067340780920133)
                    ·
                      refine ⟨2844625316075126396422525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15171335019067340780920133 2844625316075126396422525)
                      ·
                        rfl

theorem cell23_5539888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4].length) (baseStart_5539888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539888 prefixEnd_5539888 := by exact prefixLift 5539888
  have htrace : WordTrace (prefixWord ++ tailWord_5539888) baseStart_5539888 baseEnd_5539888 := by
    simpa [prefixWord, tailWord_5539888, baseEnd_5539888] using wordTrace_append hprefix tailTrace_5539888
  have hstable : (prefixWord ++ tailWord_5539888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539888).length < 2 ^ (prefixWord ++ tailWord_5539888).sum := by decide
  have hdescent : baseEnd_5539888 < baseStart_5539888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539891 : List Nat := [1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 3]
def baseStart_5539891 : Nat := 118140960795 + 5539891 * 2 ^ 59
def prefixEnd_5539891 : Nat := 4983230072969 + 3 ^ 40 * 5539891 * 2
def baseEnd_5539891 : Nat := 2844626856517089884685011

theorem tailTrace_5539891 : CollatzResearch.WordTrace tailWord_5539891 prefixEnd_5539891 2844626856517089884685011 := by
  unfold tailWord_5539891
  simp only [CollatzResearch.WordTrace]
  refine ⟨202056424372928519902011527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134704282915285679934674351 202056424372928519902011527)
  ·
    refine ⟨303084636559392779853017291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202056424372928519902011527 303084636559392779853017291)
    ·
      refine ⟨454626954839089169779525937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303084636559392779853017291 454626954839089169779525937)
      ·
        refine ⟨340970216129316877334644453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454626954839089169779525937 340970216129316877334644453)
        ·
          refine ⟨63931915524246914500245835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340970216129316877334644453 63931915524246914500245835)
          ·
            refine ⟨95897873286370371750368753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63931915524246914500245835 95897873286370371750368753)
            ·
              refine ⟨71923404964777778812776565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95897873286370371750368753 71923404964777778812776565)
              ·
                refine ⟨6742819215447916763697803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71923404964777778812776565 6742819215447916763697803)
                ·
                  refine ⟨10114228823171875145546705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742819215447916763697803 10114228823171875145546705)
                  ·
                    refine ⟨7585671617378906359160029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10114228823171875145546705 7585671617378906359160029)
                    ·
                      refine ⟨2844626856517089884685011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585671617378906359160029 2844626856517089884685011)
                      ·
                        rfl

theorem cell23_5539891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 3].length) (baseStart_5539891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539891 prefixEnd_5539891 := by exact prefixLift 5539891
  have htrace : WordTrace (prefixWord ++ tailWord_5539891) baseStart_5539891 baseEnd_5539891 := by
    simpa [prefixWord, tailWord_5539891, baseEnd_5539891] using wordTrace_append hprefix tailTrace_5539891
  have hstable : (prefixWord ++ tailWord_5539891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539891).length < 2 ^ (prefixWord ++ tailWord_5539891).sum := by decide
  have hdescent : baseEnd_5539891 < baseStart_5539891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539921 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_5539921 : Nat := 118140960795 + 5539921 * 2 ^ 59
def prefixEnd_5539921 : Nat := 4983230072969 + 3 ^ 40 * 5539921 * 2
def baseEnd_5539921 : Nat := 2844642260936724767309873

theorem tailTrace_5539921 : CollatzResearch.WordTrace tailWord_5539921 prefixEnd_5539921 2844642260936724767309873 := by
  unfold tailWord_5539921
  simp only [CollatzResearch.WordTrace]
  refine ⟨202057518562819835025603617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134705012375213223350402411 202057518562819835025603617)
  ·
    refine ⟨151543138922114876269202713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202057518562819835025603617 151543138922114876269202713)
    ·
      refine ⟨113657354191586157201902035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151543138922114876269202713 113657354191586157201902035)
      ·
        refine ⟨170486031287379235802853053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113657354191586157201902035 170486031287379235802853053)
        ·
          refine ⟨63932261732767213426069895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170486031287379235802853053 63932261732767213426069895)
          ·
            refine ⟨95898392599150820139104843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63932261732767213426069895 95898392599150820139104843)
            ·
              refine ⟨143847588898726230208657265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95898392599150820139104843 143847588898726230208657265)
              ·
                refine ⟨107885691674044672656492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143847588898726230208657265 107885691674044672656492949)
                ·
                  refine ⟨5057141797220844030773107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107885691674044672656492949 5057141797220844030773107)
                  ·
                    refine ⟨7585712695831266046159661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5057141797220844030773107 7585712695831266046159661)
                    ·
                      refine ⟨2844642260936724767309873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585712695831266046159661 2844642260936724767309873)
                      ·
                        rfl

theorem cell23_5539921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_5539921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539921 prefixEnd_5539921 := by exact prefixLift 5539921
  have htrace : WordTrace (prefixWord ++ tailWord_5539921) baseStart_5539921 baseEnd_5539921 := by
    simpa [prefixWord, tailWord_5539921, baseEnd_5539921] using wordTrace_append hprefix tailTrace_5539921
  have hstable : (prefixWord ++ tailWord_5539921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539921).length < 2 ^ (prefixWord ++ tailWord_5539921).sum := by decide
  have hdescent : baseEnd_5539921 < baseStart_5539921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539924 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_5539924 : Nat := 118140960795 + 5539924 * 2 ^ 59
def prefixEnd_5539924 : Nat := 4983230072969 + 3 ^ 40 * 5539924 * 2
def baseEnd_5539924 : Nat := 948214600459562751857453

theorem tailTrace_5539924 : CollatzResearch.WordTrace tailWord_5539924 prefixEnd_5539924 948214600459562751857453 := by
  unfold tailWord_5539924
  simp only [CollatzResearch.WordTrace]
  refine ⟨101028813990904483268981413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134705085321205977691975217 101028813990904483268981413)
  ·
    refine ⟨18942902623294590612934015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101028813990904483268981413 18942902623294590612934015)
    ·
      refine ⟨28414353934941885919401023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18942902623294590612934015 28414353934941885919401023)
      ·
        refine ⟨42621530902412828879101535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28414353934941885919401023 42621530902412828879101535)
        ·
          refine ⟨63932296353619243318652303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42621530902412828879101535 63932296353619243318652303)
          ·
            refine ⟨95898444530428864977978455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63932296353619243318652303 95898444530428864977978455)
            ·
              refine ⟨143847666795643297466967683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95898444530428864977978455 143847666795643297466967683)
              ·
                refine ⟨215771500193464946200451525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143847666795643297466967683 215771500193464946200451525)
                ·
                  refine ⟨40457156286274677412584661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215771500193464946200451525 40457156286274677412584661)
                  ·
                    refine ⟨948214600459562751857453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40457156286274677412584661 948214600459562751857453)
                    ·
                      rfl

theorem cell23_5539924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_5539924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539924 prefixEnd_5539924 := by exact prefixLift 5539924
  have htrace : WordTrace (prefixWord ++ tailWord_5539924) baseStart_5539924 baseEnd_5539924 := by
    simpa [prefixWord, tailWord_5539924, baseEnd_5539924] using wordTrace_append hprefix tailTrace_5539924
  have hstable : (prefixWord ++ tailWord_5539924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539924).length < 2 ^ (prefixWord ++ tailWord_5539924).sum := by decide
  have hdescent : baseEnd_5539924 < baseStart_5539924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539982 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5539982 : Nat := 118140960795 + 5539982 * 2 ^ 59
def prefixEnd_5539982 : Nat := 4983230072969 + 3 ^ 40 * 5539982 * 2
def baseEnd_5539982 : Nat := 2844673583256649028647093

theorem tailTrace_5539982 : CollatzResearch.WordTrace tailWord_5539982 prefixEnd_5539982 2844673583256649028647093 := by
  unfold tailWord_5539982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25257467926949855305446775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134706495610399228295716133 25257467926949855305446775)
  ·
    refine ⟨37886201890424782958170163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25257467926949855305446775 37886201890424782958170163)
    ·
      refine ⟨56829302835637174437255245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37886201890424782958170163 56829302835637174437255245)
      ·
        refine ⟨21310988563363940413970717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56829302835637174437255245 21310988563363940413970717)
        ·
          refine ⟨7991620711261477655239019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21310988563363940413970717 7991620711261477655239019)
          ·
            refine ⟨11987431066892216482858529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991620711261477655239019 11987431066892216482858529)
            ·
              refine ⟨8990573300169162362143897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11987431066892216482858529 8990573300169162362143897)
              ·
                refine ⟨6742929975126871771607923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8990573300169162362143897 6742929975126871771607923)
                ·
                  refine ⟨10114394962690307657411885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6742929975126871771607923 10114394962690307657411885)
                  ·
                    refine ⟨3792898111008865371529457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10114394962690307657411885 3792898111008865371529457)
                    ·
                      refine ⟨2844673583256649028647093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792898111008865371529457 2844673583256649028647093)
                      ·
                        rfl

theorem cell23_5539982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5539982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539982 prefixEnd_5539982 := by exact prefixLift 5539982
  have htrace : WordTrace (prefixWord ++ tailWord_5539982) baseStart_5539982 baseEnd_5539982 := by
    simpa [prefixWord, tailWord_5539982, baseEnd_5539982] using wordTrace_append hprefix tailTrace_5539982
  have hstable : (prefixWord ++ tailWord_5539982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539982).length < 2 ^ (prefixWord ++ tailWord_5539982).sum := by decide
  have hdescent : baseEnd_5539982 < baseStart_5539982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5539984 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 7]
def baseStart_5539984 : Nat := 118140960795 + 5539984 * 2 ^ 59
def prefixEnd_5539984 : Nat := 4983230072969 + 3 ^ 40 * 5539984 * 2
def baseEnd_5539984 : Nat := 316074956690884224535787

theorem tailTrace_5539984 : CollatzResearch.WordTrace tailWord_5539984 prefixEnd_5539984 316074956690884224535787 := by
  unfold tailWord_5539984
  simp only [CollatzResearch.WordTrace]
  refine ⟨101029908180795798392573503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134706544241061064523431337 101029908180795798392573503)
  ·
    refine ⟨151544862271193697588860255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101029908180795798392573503 151544862271193697588860255)
    ·
      refine ⟨227317293406790546383290383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151544862271193697588860255 227317293406790546383290383)
      ·
        refine ⟨340975940110185819574935575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227317293406790546383290383 340975940110185819574935575)
        ·
          refine ⟨511463910165278729362403363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340975940110185819574935575 511463910165278729362403363)
          ·
            refine ⟨767195865247918094043605045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511463910165278729362403363 767195865247918094043605045)
            ·
              refine ⟨71924612366992321316587973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 767195865247918094043605045 71924612366992321316587973)
              ·
                refine ⟨13485864818811060246860245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71924612366992321316587973 13485864818811060246860245)
                ·
                  refine ⟨316074956690884224535787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13485864818811060246860245 316074956690884224535787)
                  ·
                    rfl

theorem cell23_5539984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_5539984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5539984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5539984 prefixEnd_5539984 := by exact prefixLift 5539984
  have htrace : WordTrace (prefixWord ++ tailWord_5539984) baseStart_5539984 baseEnd_5539984 := by
    simpa [prefixWord, tailWord_5539984, baseEnd_5539984] using wordTrace_append hprefix tailTrace_5539984
  have hstable : (prefixWord ++ tailWord_5539984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5539984).length < 2 ^ (prefixWord ++ tailWord_5539984).sum := by decide
  have hdescent : baseEnd_5539984 < baseStart_5539984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5539984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540068 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_5540068 : Nat := 118140960795 + 5540068 * 2 ^ 59
def prefixEnd_5540068 : Nat := 4983230072969 + 3 ^ 40 * 5540068 * 2
def baseEnd_5540068 : Nat := 2844717742592935692171697

theorem tailTrace_5540068 : CollatzResearch.WordTrace tailWord_5540068 prefixEnd_5540068 2844717742592935692171697 := by
  unfold tailWord_5540068
  simp only [CollatzResearch.WordTrace]
  refine ⟨101031440046643639565602429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134708586728858186087469905 101031440046643639565602429)
  ·
    refine ⟨37886790017491364837100911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101031440046643639565602429 37886790017491364837100911)
    ·
      refine ⟨56830185026237047255651367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37886790017491364837100911 56830185026237047255651367)
      ·
        refine ⟨85245277539355570883477051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56830185026237047255651367 85245277539355570883477051)
        ·
          refine ⟨127867916309033356325215577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85245277539355570883477051 127867916309033356325215577)
          ·
            refine ⟨95900937231775017243911683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127867916309033356325215577 95900937231775017243911683)
            ·
              refine ⟨143851405847662525865867525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95900937231775017243911683 143851405847662525865867525)
              ·
                refine ⟨26972138596436723599850161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143851405847662525865867525 26972138596436723599850161)
                ·
                  refine ⟨20229103947327542699887621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26972138596436723599850161 20229103947327542699887621)
                  ·
                    refine ⟨3792956990123914256228929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20229103947327542699887621 3792956990123914256228929)
                    ·
                      refine ⟨2844717742592935692171697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3792956990123914256228929 2844717742592935692171697)
                      ·
                        rfl

theorem cell23_5540068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_5540068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540068 prefixEnd_5540068 := by exact prefixLift 5540068
  have htrace : WordTrace (prefixWord ++ tailWord_5540068) baseStart_5540068 baseEnd_5540068 := by
    simpa [prefixWord, tailWord_5540068, baseEnd_5540068] using wordTrace_append hprefix tailTrace_5540068
  have hstable : (prefixWord ++ tailWord_5540068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540068).length < 2 ^ (prefixWord ++ tailWord_5540068).sum := by decide
  have hdescent : baseEnd_5540068 < baseStart_5540068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540078 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_5540078 : Nat := 118140960795 + 5540078 * 2 ^ 59
def prefixEnd_5540078 : Nat := 4983230072969 + 3 ^ 40 * 5540078 * 2
def baseEnd_5540078 : Nat := 948240959133160217682217

theorem tailTrace_5540078 : CollatzResearch.WordTrace tailWord_5540078 prefixEnd_5540078 948240959133160217682217 := by
  unfold tailWord_5540078
  simp only [CollatzResearch.WordTrace]
  refine ⟨25257905602906381354883611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134708829882167367226045925 25257905602906381354883611)
  ·
    refine ⟨37886858404359572032325417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25257905602906381354883611 37886858404359572032325417)
    ·
      refine ⟨28415143803269679024244063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37886858404359572032325417 28415143803269679024244063)
      ·
        refine ⟨42622715704904518536366095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28415143803269679024244063 42622715704904518536366095)
        ·
          refine ⟨63934073557356777804549143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42622715704904518536366095 63934073557356777804549143)
          ·
            refine ⟨95901110336035166706823715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63934073557356777804549143 95901110336035166706823715)
            ·
              refine ⟨143851665504052750060235573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95901110336035166706823715 143851665504052750060235573)
              ·
                refine ⟨13486093641004945318147085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143851665504052750060235573 13486093641004945318147085)
                ·
                  refine ⟨5057285115376854494305157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13486093641004945318147085 5057285115376854494305157)
                  ·
                    refine ⟨948240959133160217682217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057285115376854494305157 948240959133160217682217)
                    ·
                      rfl

theorem cell23_5540078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_5540078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540078 prefixEnd_5540078 := by exact prefixLift 5540078
  have htrace : WordTrace (prefixWord ++ tailWord_5540078) baseStart_5540078 baseEnd_5540078 := by
    simpa [prefixWord, tailWord_5540078, baseEnd_5540078] using wordTrace_append hprefix tailTrace_5540078
  have hstable : (prefixWord ++ tailWord_5540078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540078).length < 2 ^ (prefixWord ++ tailWord_5540078).sum := by decide
  have hdescent : baseEnd_5540078 < baseStart_5540078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540101 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_5540101 : Nat := 118140960795 + 5540101 * 2 ^ 59
def prefixEnd_5540101 : Nat := 4983230072969 + 3 ^ 40 * 5540101 * 2
def baseEnd_5540101 : Nat := 2844734687454534063059045

theorem tailTrace_5540101 : CollatzResearch.WordTrace tailWord_5540101 prefixEnd_5540101 2844734687454534063059045 := by
  unfold tailWord_5540101
  simp only [CollatzResearch.WordTrace]
  refine ⟨202064083702167725767156157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134709389134778483844770771 202064083702167725767156157)
  ·
    refine ⟨75774031388312897162683559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202064083702167725767156157 75774031388312897162683559)
    ·
      refine ⟨113661047082469345744025339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75774031388312897162683559 113661047082469345744025339)
      ·
        refine ⟨170491570623704018616038009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113661047082469345744025339 170491570623704018616038009)
        ·
          refine ⟨127868677967778013962028507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170491570623704018616038009 127868677967778013962028507)
          ·
            refine ⟨191803016951667020943042761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127868677967778013962028507 191803016951667020943042761)
            ·
              refine ⟨143852262713750265707282071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191803016951667020943042761 143852262713750265707282071)
              ·
                refine ⟨215778394070625398560923107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143852262713750265707282071 215778394070625398560923107)
                ·
                  refine ⟨323667591105938097841384661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215778394070625398560923107 323667591105938097841384661)
                  ·
                    refine ⟨7585959166545424168157453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 323667591105938097841384661 7585959166545424168157453)
                    ·
                      refine ⟨2844734687454534063059045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585959166545424168157453 2844734687454534063059045)
                      ·
                        rfl

theorem cell23_5540101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_5540101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540101 prefixEnd_5540101 := by exact prefixLift 5540101
  have htrace : WordTrace (prefixWord ++ tailWord_5540101) baseStart_5540101 baseEnd_5540101 := by
    simpa [prefixWord, tailWord_5540101, baseEnd_5540101] using wordTrace_append hprefix tailTrace_5540101
  have hstable : (prefixWord ++ tailWord_5540101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540101).length < 2 ^ (prefixWord ++ tailWord_5540101).sum := by decide
  have hdescent : baseEnd_5540101 < baseStart_5540101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540105 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_5540105 : Nat := 118140960795 + 5540105 * 2 ^ 59
def prefixEnd_5540105 : Nat := 4983230072969 + 3 ^ 40 * 5540105 * 2
def baseEnd_5540105 : Nat := 2844736741377152047409027

theorem tailTrace_5540105 : CollatzResearch.WordTrace tailWord_5540105 prefixEnd_5540105 2844736741377152047409027 := by
  unfold tailWord_5540105
  simp only [CollatzResearch.WordTrace]
  refine ⟨202064229594153234450301769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134709486396102156300201179 202064229594153234450301769)
  ·
    refine ⟨151548172195614925837726327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202064229594153234450301769 151548172195614925837726327)
    ·
      refine ⟨227322258293422388756589491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151548172195614925837726327 227322258293422388756589491)
      ·
        refine ⟨340983387440133583134884237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227322258293422388756589491 340983387440133583134884237)
        ·
          refine ⟨127868770290050093675581589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340983387440133583134884237 127868770290050093675581589)
          ·
            refine ⟨5993848607346098141042887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127868770290050093675581589 5993848607346098141042887)
            ·
              refine ⟨8990772911019147211564331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993848607346098141042887 8990772911019147211564331)
              ·
                refine ⟨13486159366528720817346497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8990772911019147211564331 13486159366528720817346497)
                ·
                  refine ⟨10114619524896540613009873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13486159366528720817346497 10114619524896540613009873)
                  ·
                    refine ⟨7585964643672405459757405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10114619524896540613009873 7585964643672405459757405)
                    ·
                      refine ⟨2844736741377152047409027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7585964643672405459757405 2844736741377152047409027)
                      ·
                        rfl

theorem cell23_5540105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_5540105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540105 prefixEnd_5540105 := by exact prefixLift 5540105
  have htrace : WordTrace (prefixWord ++ tailWord_5540105) baseStart_5540105 baseEnd_5540105 := by
    simpa [prefixWord, tailWord_5540105, baseEnd_5540105] using wordTrace_append hprefix tailTrace_5540105
  have hstable : (prefixWord ++ tailWord_5540105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540105).length < 2 ^ (prefixWord ++ tailWord_5540105).sum := by decide
  have hdescent : baseEnd_5540105 < baseStart_5540105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540168 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_5540168 : Nat := 118140960795 + 5540168 * 2 ^ 59
def prefixEnd_5540168 : Nat := 4983230072969 + 3 ^ 40 * 5540168 * 2
def baseEnd_5540168 : Nat := 948256363552795100307079

theorem tailTrace_5540168 : CollatzResearch.WordTrace tailWord_5540168 prefixEnd_5540168 948256363552795100307079 := by
  unfold tailWord_5540168
  simp only [CollatzResearch.WordTrace]
  refine ⟨101033263696462498104922579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134711018261949997473230105 101033263696462498104922579)
  ·
    refine ⟨151549895544693747157383869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101033263696462498104922579 151549895544693747157383869)
    ·
      refine ⟨56831210829260155184018951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151549895544693747157383869 56831210829260155184018951)
      ·
        refine ⟨85246816243890232776028427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56831210829260155184018951 85246816243890232776028427)
        ·
          refine ⟨127870224365835349164042641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85246816243890232776028427 127870224365835349164042641)
          ·
            refine ⟨95902668274376511873031981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127870224365835349164042641 95902668274376511873031981)
            ·
              refine ⟨35963500602891191952386993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95902668274376511873031981 35963500602891191952386993)
              ·
                refine ⟨26972625452168393964290245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35963500602891191952386993 26972625452168393964290245)
                ·
                  refine ⟨5057367272281573868304421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26972625452168393964290245 5057367272281573868304421)
                  ·
                    refine ⟨948256363552795100307079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057367272281573868304421 948256363552795100307079)
                    ·
                      rfl

theorem cell23_5540168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_5540168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540168 prefixEnd_5540168 := by exact prefixLift 5540168
  have htrace : WordTrace (prefixWord ++ tailWord_5540168) baseStart_5540168 baseEnd_5540168 := by
    simpa [prefixWord, tailWord_5540168, baseEnd_5540168] using wordTrace_append hprefix tailTrace_5540168
  have hstable : (prefixWord ++ tailWord_5540168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540168).length < 2 ^ (prefixWord ++ tailWord_5540168).sum := by decide
  have hdescent : baseEnd_5540168 < baseStart_5540168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540178 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5540178 : Nat := 118140960795 + 5540178 * 2 ^ 59
def prefixEnd_5540178 : Nat := 4983230072969 + 3 ^ 40 * 5540178 * 2
def baseEnd_5540178 : Nat := 2844774225464930261796191

theorem tailTrace_5540178 : CollatzResearch.WordTrace tailWord_5540178 prefixEnd_5540178 2844774225464930261796191 := by
  unfold tailWord_5540178
  simp only [CollatzResearch.WordTrace]
  refine ⟨50516723030722191979427297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134711261415259178611806125 50516723030722191979427297)
  ·
    refine ⟨37887542273041643984570473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50516723030722191979427297 37887542273041643984570473)
    ·
      refine ⟨28415656704781232988427855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37887542273041643984570473 28415656704781232988427855)
      ·
        refine ⟨42623485057171849482641783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28415656704781232988427855 42623485057171849482641783)
        ·
          refine ⟨63935227585757774223962675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42623485057171849482641783 63935227585757774223962675)
          ·
            refine ⟨95902841378636661335944013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63935227585757774223962675 95902841378636661335944013)
            ·
              refine ⟨35963565516988748000979005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95902841378636661335944013 35963565516988748000979005)
              ·
                refine ⟨13486337068870780500367127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35963565516988748000979005 13486337068870780500367127)
                ·
                  refine ⟨20229505603306170750550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13486337068870780500367127 20229505603306170750550691)
                  ·
                    refine ⟨30344258404959256125826037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20229505603306170750550691 30344258404959256125826037)
                    ·
                      refine ⟨2844774225464930261796191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30344258404959256125826037 2844774225464930261796191)
                      ·
                        rfl

theorem cell23_5540178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5540178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540178 prefixEnd_5540178 := by exact prefixLift 5540178
  have htrace : WordTrace (prefixWord ++ tailWord_5540178) baseStart_5540178 baseEnd_5540178 := by
    simpa [prefixWord, tailWord_5540178, baseEnd_5540178] using wordTrace_append hprefix tailTrace_5540178
  have hstable : (prefixWord ++ tailWord_5540178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540178).length < 2 ^ (prefixWord ++ tailWord_5540178).sum := by decide
  have hdescent : baseEnd_5540178 < baseStart_5540178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540201 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_5540201 : Nat := 118140960795 + 5540201 * 2 ^ 59
def prefixEnd_5540201 : Nat := 4983230072969 + 3 ^ 40 * 5540201 * 2
def baseEnd_5540201 : Nat := 2844786035519983671808585

theorem tailTrace_5540201 : CollatzResearch.WordTrace tailWord_5540201 prefixEnd_5540201 2844786035519983671808585 := by
  unfold tailWord_5540201
  simp only [CollatzResearch.WordTrace]
  refine ⟨202067731001805442845796457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134711820667870295230530971 202067731001805442845796457)
  ·
    refine ⟨151550798251354082134347343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202067731001805442845796457 151550798251354082134347343)
    ·
      refine ⟨227326197377031123201521015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151550798251354082134347343 227326197377031123201521015)
      ·
        refine ⟨340989296065546684802281523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227326197377031123201521015 340989296065546684802281523)
        ·
          refine ⟨511483944098320027203422285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340989296065546684802281523 511483944098320027203422285)
          ·
            refine ⟨191806479036870010201283357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511483944098320027203422285 191806479036870010201283357)
            ·
              refine ⟨71927429638826253825481259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191806479036870010201283357 71927429638826253825481259)
              ·
                refine ⟨107891144458239380738221889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71927429638826253825481259 107891144458239380738221889)
                ·
                  refine ⟨80918358343679535553666417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107891144458239380738221889 80918358343679535553666417)
                  ·
                    refine ⟨60688768757759651665249813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80918358343679535553666417 60688768757759651665249813)
                    ·
                      refine ⟨2844786035519983671808585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60688768757759651665249813 2844786035519983671808585)
                      ·
                        rfl

theorem cell23_5540201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_5540201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540201 prefixEnd_5540201 := by exact prefixLift 5540201
  have htrace : WordTrace (prefixWord ++ tailWord_5540201) baseStart_5540201 baseEnd_5540201 := by
    simpa [prefixWord, tailWord_5540201, baseEnd_5540201] using wordTrace_append hprefix tailTrace_5540201
  have hstable : (prefixWord ++ tailWord_5540201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540201).length < 2 ^ (prefixWord ++ tailWord_5540201).sum := by decide
  have hdescent : baseEnd_5540201 < baseStart_5540201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540202 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_5540202 : Nat := 118140960795 + 5540202 * 2 ^ 59
def prefixEnd_5540202 : Nat := 4983230072969 + 3 ^ 40 * 5540202 * 2
def baseEnd_5540202 : Nat := 948262183000212722632027

theorem tailTrace_5540202 : CollatzResearch.WordTrace tailWord_5540202 prefixEnd_5540202 948262183000212722632027 := by
  unfold tailWord_5540202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50516941868700455004145715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134711844983201213344388573 50516941868700455004145715)
  ·
    refine ⟨75775412803050682506218573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50516941868700455004145715 75775412803050682506218573)
    ·
      refine ⟨28415779801144005939831965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75775412803050682506218573 28415779801144005939831965)
      ·
        refine ⟨10655917425429002227436987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28415779801144005939831965 10655917425429002227436987)
        ·
          refine ⟨15983876138143503341155481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10655917425429002227436987 15983876138143503341155481)
          ·
            refine ⟨11987907103607627505866611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15983876138143503341155481 11987907103607627505866611)
            ·
              refine ⟨17981860655411441258799917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11987907103607627505866611 17981860655411441258799917)
              ·
                refine ⟨6743197745779290472049969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17981860655411441258799917 6743197745779290472049969)
                ·
                  refine ⟨5057398309334467854037477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6743197745779290472049969 5057398309334467854037477)
                  ·
                    refine ⟨948262183000212722632027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057398309334467854037477 948262183000212722632027)
                    ·
                      rfl

theorem cell23_5540202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_5540202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540202 prefixEnd_5540202 := by exact prefixLift 5540202
  have htrace : WordTrace (prefixWord ++ tailWord_5540202) baseStart_5540202 baseEnd_5540202 := by
    simpa [prefixWord, tailWord_5540202, baseEnd_5540202] using wordTrace_append hprefix tailTrace_5540202
  have hstable : (prefixWord ++ tailWord_5540202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540202).length < 2 ^ (prefixWord ++ tailWord_5540202).sum := by decide
  have hdescent : baseEnd_5540202 < baseStart_5540202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540211 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 7]
def baseStart_5540211 : Nat := 118140960795 + 5540211 * 2 ^ 59
def prefixEnd_5540211 : Nat := 4983230072969 + 3 ^ 40 * 5540211 * 2
def baseEnd_5540211 : Nat := 948263723442176210894513

theorem tailTrace_5540211 : CollatzResearch.WordTrace tailWord_5540211 prefixEnd_5540211 948263723442176210894513 := by
  unfold tailWord_5540211
  simp only [CollatzResearch.WordTrace]
  refine ⟨202068095731769214553660487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134712063821179476369106991 202068095731769214553660487)
  ·
    refine ⟨303102143597653821830490731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202068095731769214553660487 303102143597653821830490731)
    ·
      refine ⟨454653215396480732745736097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303102143597653821830490731 454653215396480732745736097)
      ·
        refine ⟨340989911547360549559302073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454653215396480732745736097 340989911547360549559302073)
        ·
          refine ⟨255742433660520412169476555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340989911547360549559302073 255742433660520412169476555)
          ·
            refine ⟨383613650490780618254214833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255742433660520412169476555 383613650490780618254214833)
            ·
              refine ⟨287710237868085463690661125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383613650490780618254214833 287710237868085463690661125)
              ·
                refine ⟨53945669600266024441998961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287710237868085463690661125 53945669600266024441998961)
                ·
                  refine ⟨40459252200199518331499221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53945669600266024441998961 40459252200199518331499221)
                  ·
                    refine ⟨948263723442176210894513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40459252200199518331499221 948263723442176210894513)
                    ·
                      rfl

theorem cell23_5540211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_5540211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540211 prefixEnd_5540211 := by exact prefixLift 5540211
  have htrace : WordTrace (prefixWord ++ tailWord_5540211) baseStart_5540211 baseEnd_5540211 := by
    simpa [prefixWord, tailWord_5540211, baseEnd_5540211] using wordTrace_append hprefix tailTrace_5540211
  have hstable : (prefixWord ++ tailWord_5540211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540211).length < 2 ^ (prefixWord ++ tailWord_5540211).sum := by decide
  have hdescent : baseEnd_5540211 < baseStart_5540211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540225 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_5540225 : Nat := 118140960795 + 5540225 * 2 ^ 59
def prefixEnd_5540225 : Nat := 4983230072969 + 3 ^ 40 * 5540225 * 2
def baseEnd_5540225 : Nat := 2844798359055691577908475

theorem tailTrace_5540225 : CollatzResearch.WordTrace tailWord_5540225 prefixEnd_5540225 2844798359055691577908475 := by
  unfold tailWord_5540225
  simp only [CollatzResearch.WordTrace]
  refine ⟨202068606353718494944670129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134712404235812329963113419 202068606353718494944670129)
  ·
    refine ⟨151551454765288871208502597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202068606353718494944670129 151551454765288871208502597)
    ·
      refine ⟨28415897768491663351594237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151551454765288871208502597 28415897768491663351594237)
      ·
        refine ⟨10655961663184373756847839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28415897768491663351594237 10655961663184373756847839)
        ·
          refine ⟨15983942494776560635271759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10655961663184373756847839 15983942494776560635271759)
          ·
            refine ⟨23975913742164840952907639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15983942494776560635271759 23975913742164840952907639)
            ·
              refine ⟨35963870613247261429361459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23975913742164840952907639 35963870613247261429361459)
              ·
                refine ⟨53945805919870892144042189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35963870613247261429361459 53945805919870892144042189)
                ·
                  refine ⟨20229677219951584554015821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53945805919870892144042189 20229677219951584554015821)
                  ·
                    refine ⟨7586128957481844207755933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20229677219951584554015821 7586128957481844207755933)
                    ·
                      refine ⟨2844798359055691577908475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7586128957481844207755933 2844798359055691577908475)
                      ·
                        rfl

theorem cell23_5540225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_5540225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540225 prefixEnd_5540225 := by exact prefixLift 5540225
  have htrace : WordTrace (prefixWord ++ tailWord_5540225) baseStart_5540225 baseEnd_5540225 := by
    simpa [prefixWord, tailWord_5540225, baseEnd_5540225] using wordTrace_append hprefix tailTrace_5540225
  have hstable : (prefixWord ++ tailWord_5540225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540225).length < 2 ^ (prefixWord ++ tailWord_5540225).sum := by decide
  have hdescent : baseEnd_5540225 < baseStart_5540225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540226 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5540226 : Nat := 118140960795 + 5540226 * 2 ^ 59
def prefixEnd_5540226 : Nat := 4983230072969 + 3 ^ 40 * 5540226 * 2
def baseEnd_5540226 : Nat := 2844798872536346073995971

theorem tailTrace_5540226 : CollatzResearch.WordTrace tailWord_5540226 prefixEnd_5540226 2844798872536346073995971 := by
  unfold tailWord_5540226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50517160706678718028864133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134712428551143248076971021 50517160706678718028864133)
  ·
    refine ⟨9471967632502259630412025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50517160706678718028864133 9471967632502259630412025)
    ·
      refine ⟨7103975724376694722809019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9471967632502259630412025 7103975724376694722809019)
      ·
        refine ⟨10655963586565042084213529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7103975724376694722809019 10655963586565042084213529)
        ·
          refine ⟨7991972689923781563160147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10655963586565042084213529 7991972689923781563160147)
          ·
            refine ⟨11987959034885672344740221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991972689923781563160147 11987959034885672344740221)
            ·
              refine ⟨4495484638082127129277583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11987959034885672344740221 4495484638082127129277583)
              ·
                refine ⟨6743226957123190693916375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495484638082127129277583 6743226957123190693916375)
                ·
                  refine ⟨10114840435684786040874563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6743226957123190693916375 10114840435684786040874563)
                  ·
                    refine ⟨15172260653527179061311845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10114840435684786040874563 15172260653527179061311845)
                    ·
                      refine ⟨2844798872536346073995971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15172260653527179061311845 2844798872536346073995971)
                      ·
                        rfl

theorem cell23_5540226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5540226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540226 prefixEnd_5540226 := by exact prefixLift 5540226
  have htrace : WordTrace (prefixWord ++ tailWord_5540226) baseStart_5540226 baseEnd_5540226 := by
    simpa [prefixWord, tailWord_5540226, baseEnd_5540226] using wordTrace_append hprefix tailTrace_5540226
  have hstable : (prefixWord ++ tailWord_5540226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540226).length < 2 ^ (prefixWord ++ tailWord_5540226).sum := by decide
  have hdescent : baseEnd_5540226 < baseStart_5540226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540268 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_5540268 : Nat := 118140960795 + 5540268 * 2 ^ 59
def prefixEnd_5540268 : Nat := 4983230072969 + 3 ^ 40 * 5540268 * 2
def baseEnd_5540268 : Nat := 2844820438723834909670777

theorem tailTrace_5540268 : CollatzResearch.WordTrace tailWord_5540268 prefixEnd_5540268 2844820438723834909670777 := by
  unfold tailWord_5540268
  simp only [CollatzResearch.WordTrace]
  refine ⟨101035087346281356644242729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134713449795041808858990305 101035087346281356644242729)
  ·
    refine ⟨75776315509711017483182047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101035087346281356644242729 75776315509711017483182047)
    ·
      refine ⟨113664473264566526224773071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75776315509711017483182047 113664473264566526224773071)
      ·
        refine ⟨170496709896849789337159607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113664473264566526224773071 170496709896849789337159607)
        ·
          refine ⟨255745064845274684005739411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170496709896849789337159607 255745064845274684005739411)
          ·
            refine ⟨383617597267912026008609117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255745064845274684005739411 383617597267912026008609117)
            ·
              refine ⟨143856598975467009753228419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383617597267912026008609117 143856598975467009753228419)
              ·
                refine ⟨215784898463200514629842629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143856598975467009753228419 215784898463200514629842629)
                ·
                  refine ⟨40459668461850096493095493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215784898463200514629842629 40459668461850096493095493)
                  ·
                    refine ⟨7586187836596893092455405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40459668461850096493095493 7586187836596893092455405)
                    ·
                      refine ⟨2844820438723834909670777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7586187836596893092455405 2844820438723834909670777)
                      ·
                        rfl

theorem cell23_5540268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_5540268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540268 prefixEnd_5540268 := by exact prefixLift 5540268
  have htrace : WordTrace (prefixWord ++ tailWord_5540268) baseStart_5540268 baseEnd_5540268 := by
    simpa [prefixWord, tailWord_5540268, baseEnd_5540268] using wordTrace_append hprefix tailTrace_5540268
  have hstable : (prefixWord ++ tailWord_5540268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540268).length < 2 ^ (prefixWord ++ tailWord_5540268).sum := by decide
  have hdescent : baseEnd_5540268 < baseStart_5540268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540355 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4]
def baseStart_5540355 : Nat := 118140960795 + 5540355 * 2 ^ 59
def prefixEnd_5540355 : Nat := 4983230072969 + 3 ^ 40 * 5540355 * 2
def baseEnd_5540355 : Nat := 2844865111540776069282877

theorem tailTrace_5540355 : CollatzResearch.WordTrace tailWord_5540355 prefixEnd_5540355 2844865111540776069282877 := by
  unfold tailWord_5540355
  simp only [CollatzResearch.WordTrace]
  refine ⟨202073347843247527146902519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134715565228831684764601679 202073347843247527146902519)
  ·
    refine ⟨303110021764871290720353779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202073347843247527146902519 303110021764871290720353779)
    ·
      refine ⟨454665032647306936080530669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303110021764871290720353779 454665032647306936080530669)
      ·
        refine ⟨170499387242740101030199001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454665032647306936080530669 170499387242740101030199001)
        ·
          refine ⟨127874540432055075772649251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170499387242740101030199001 127874540432055075772649251)
          ·
            refine ⟨191811810648082613658973877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127874540432055075772649251 191811810648082613658973877)
            ·
              refine ⟨17982357248257745030528801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191811810648082613658973877 17982357248257745030528801)
              ·
                refine ⟨13486767936193308772896601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17982357248257745030528801 13486767936193308772896601)
                ·
                  refine ⟨10115075952144981579672451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13486767936193308772896601 10115075952144981579672451)
                  ·
                    refine ⟨15172613928217472369508677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10115075952144981579672451 15172613928217472369508677)
                    ·
                      refine ⟨2844865111540776069282877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15172613928217472369508677 2844865111540776069282877)
                      ·
                        rfl

theorem cell23_5540355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_5540355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540355 prefixEnd_5540355 := by exact prefixLift 5540355
  have htrace : WordTrace (prefixWord ++ tailWord_5540355) baseStart_5540355 baseEnd_5540355 := by
    simpa [prefixWord, tailWord_5540355, baseEnd_5540355] using wordTrace_append hprefix tailTrace_5540355
  have hstable : (prefixWord ++ tailWord_5540355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540355).length < 2 ^ (prefixWord ++ tailWord_5540355).sum := by decide
  have hdescent : baseEnd_5540355 < baseStart_5540355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540368 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_5540368 : Nat := 118140960795 + 5540368 * 2 ^ 59
def prefixEnd_5540368 : Nat := 4983230072969 + 3 ^ 40 * 5540368 * 2
def baseEnd_5540368 : Nat := 2844871786789284518420317

theorem tailTrace_5540368 : CollatzResearch.WordTrace tailWord_5540368 prefixEnd_5540368 2844871786789284518420317 := by
  unfold tailWord_5540368
  simp only [CollatzResearch.WordTrace]
  refine ⟨101036910996100215183562879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134715881328133620244750505 101036910996100215183562879)
  ·
    refine ⟨151555366494150322775344319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101036910996100215183562879 151555366494150322775344319)
    ·
      refine ⟨227333049741225484163016479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151555366494150322775344319 227333049741225484163016479)
      ·
        refine ⟨340999574611838226244524719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227333049741225484163016479 340999574611838226244524719)
        ·
          refine ⟨511499361917757339366787079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340999574611838226244524719 511499361917757339366787079)
          ·
            refine ⟨767249042876636009050180619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511499361917757339366787079 767249042876636009050180619)
            ·
              refine ⟨1150873564314954013575270929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767249042876636009050180619 1150873564314954013575270929)
              ·
                refine ⟨863155173236215510181453197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150873564314954013575270929 863155173236215510181453197)
                ·
                  refine ⟨323683189963580816318044949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863155173236215510181453197 323683189963580816318044949)
                  ·
                    refine ⟨15172649529542850764908357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 323683189963580816318044949 15172649529542850764908357)
                    ·
                      refine ⟨2844871786789284518420317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15172649529542850764908357 2844871786789284518420317)
                      ·
                        rfl

theorem cell23_5540368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_5540368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540368 prefixEnd_5540368 := by exact prefixLift 5540368
  have htrace : WordTrace (prefixWord ++ tailWord_5540368) baseStart_5540368 baseEnd_5540368 := by
    simpa [prefixWord, tailWord_5540368, baseEnd_5540368] using wordTrace_append hprefix tailTrace_5540368
  have hstable : (prefixWord ++ tailWord_5540368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540368).length < 2 ^ (prefixWord ++ tailWord_5540368).sum := by decide
  have hdescent : baseEnd_5540368 < baseStart_5540368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540412 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 6]
def baseStart_5540412 : Nat := 118140960795 + 5540412 * 2 ^ 59
def prefixEnd_5540412 : Nat := 4983230072969 + 3 ^ 40 * 5540412 * 2
def baseEnd_5540412 : Nat := 316099375548675816252235

theorem tailTrace_5540412 : CollatzResearch.WordTrace tailWord_5540412 prefixEnd_5540412 316099375548675816252235 := by
  unfold tailWord_5540412
  simp only [CollatzResearch.WordTrace]
  refine ⟨101037713402020512940863745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134716951202694017254484993 101037713402020512940863745)
  ·
    refine ⟨75778285051515384705647809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101037713402020512940863745 75778285051515384705647809)
    ·
      refine ⟨56833713788636538529235857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75778285051515384705647809 56833713788636538529235857)
      ·
        refine ⟨42625285341477403896926893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56833713788636538529235857 42625285341477403896926893)
        ·
          refine ⟨15984482003054026461347585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42625285341477403896926893 15984482003054026461347585)
          ·
            refine ⟨11988361502290519846010689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15984482003054026461347585 11988361502290519846010689)
            ·
              refine ⟨8991271126717889884508017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11988361502290519846010689 8991271126717889884508017)
              ·
                refine ⟨6743453345038417413381013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8991271126717889884508017 6743453345038417413381013)
                ·
                  refine ⟨316099375548675816252235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6743453345038417413381013 316099375548675816252235)
                  ·
                    rfl

theorem cell23_5540412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_5540412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540412 prefixEnd_5540412 := by exact prefixLift 5540412
  have htrace : WordTrace (prefixWord ++ tailWord_5540412) baseStart_5540412 baseEnd_5540412 := by
    simpa [prefixWord, tailWord_5540412, baseEnd_5540412] using wordTrace_append hprefix tailTrace_5540412
  have hstable : (prefixWord ++ tailWord_5540412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540412).length < 2 ^ (prefixWord ++ tailWord_5540412).sum := by decide
  have hdescent : baseEnd_5540412 < baseStart_5540412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540449 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_5540449 : Nat := 118140960795 + 5540449 * 2 ^ 59
def prefixEnd_5540449 : Nat := 4983230072969 + 3 ^ 40 * 5540449 * 2
def baseEnd_5540449 : Nat := 2844913378722298701507445

theorem tailTrace_5540449 : CollatzResearch.WordTrace tailWord_5540449 prefixEnd_5540449 2844913378722298701507445 := by
  unfold tailWord_5540449
  simp only [CollatzResearch.WordTrace]
  refine ⟨202076776304906981200824401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134717850869937987467216267 202076776304906981200824401)
  ·
    refine ⟨151557582228680235900618301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202076776304906981200824401 151557582228680235900618301)
    ·
      refine ⟨56834093335755088462731863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151557582228680235900618301 56834093335755088462731863)
      ·
        refine ⟨85251140003632632694097795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56834093335755088462731863 85251140003632632694097795)
        ·
          refine ⟨127876710005448949041146693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85251140003632632694097795 127876710005448949041146693)
          ·
            refine ⟨23976883126021677945215005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127876710005448949041146693 23976883126021677945215005)
            ·
              refine ⟨8991331172258129229455627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23976883126021677945215005 8991331172258129229455627)
              ·
                refine ⟨13486996758387193844183441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8991331172258129229455627 13486996758387193844183441)
                ·
                  refine ⟨10115247568790395383137581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13486996758387193844183441 10115247568790395383137581)
                  ·
                    refine ⟨3793217838296398268676593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10115247568790395383137581 3793217838296398268676593)
                    ·
                      refine ⟨2844913378722298701507445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793217838296398268676593 2844913378722298701507445)
                      ·
                        rfl

theorem cell23_5540449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_5540449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540449 prefixEnd_5540449 := by exact prefixLift 5540449
  have htrace : WordTrace (prefixWord ++ tailWord_5540449) baseStart_5540449 baseEnd_5540449 := by
    simpa [prefixWord, tailWord_5540449, baseEnd_5540449] using wordTrace_append hprefix tailTrace_5540449
  have hstable : (prefixWord ++ tailWord_5540449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540449).length < 2 ^ (prefixWord ++ tailWord_5540449).sum := by decide
  have hdescent : baseEnd_5540449 < baseStart_5540449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540519 : List Nat := [1, 1, 6, 3, 1, 2, 9]
def baseStart_5540519 : Nat := 118140960795 + 5540519 * 2 ^ 59
def prefixEnd_5540519 : Nat := 4983230072969 + 3 ^ 40 * 5540519 * 2
def baseEnd_5540519 : Nat := 35122831140347079353483

theorem tailTrace_5540519 : CollatzResearch.WordTrace tailWord_5540519 prefixEnd_5540519 35122831140347079353483 := by
  unfold tailWord_5540519
  simp only [CollatzResearch.WordTrace]
  refine ⟨202079329414653383155872611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134719552943102255437248407 202079329414653383155872611)
  ·
    refine ⟨303118994121980074733808917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202079329414653383155872611 303118994121980074733808917)
    ·
      refine ⟨14208702849467816003147293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 303118994121980074733808917 14208702849467816003147293)
      ·
        refine ⟨5328263568550431001180235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14208702849467816003147293 5328263568550431001180235)
        ·
          refine ⟨7992395352825646501770353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328263568550431001180235 7992395352825646501770353)
          ·
            refine ⟨5994296514619234876327765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7992395352825646501770353 5994296514619234876327765)
            ·
              refine ⟨35122831140347079353483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5994296514619234876327765 35122831140347079353483)
              ·
                rfl

theorem cell23_5540519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 9].length) (baseStart_5540519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540519 prefixEnd_5540519 := by exact prefixLift 5540519
  have htrace : WordTrace (prefixWord ++ tailWord_5540519) baseStart_5540519 baseEnd_5540519 := by
    simpa [prefixWord, tailWord_5540519, baseEnd_5540519] using wordTrace_append hprefix tailTrace_5540519
  have hstable : (prefixWord ++ tailWord_5540519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540519).length < 2 ^ (prefixWord ++ tailWord_5540519).sum := by decide
  have hdescent : baseEnd_5540519 < baseStart_5540519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540556 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5540556 : Nat := 118140960795 + 5540556 * 2 ^ 59
def prefixEnd_5540556 : Nat := 4983230072969 + 3 ^ 40 * 5540556 * 2
def baseEnd_5540556 : Nat := 2844968321152329782869453

theorem tailTrace_5540556 : CollatzResearch.WordTrace tailWord_5540556 prefixEnd_5540556 2844968321152329782869453 := by
  unfold tailWord_5540556
  simp only [CollatzResearch.WordTrace]
  refine ⟨101040339457759669237484761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134720452610346225649979681 101040339457759669237484761)
  ·
    refine ⟨75780254593319751928113571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101040339457759669237484761 75780254593319751928113571)
    ·
      refine ⟨113670381889979627892170357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75780254593319751928113571 113670381889979627892170357)
      ·
        refine ⟨10656598302185590114890971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113670381889979627892170357 10656598302185590114890971)
        ·
          refine ⟨15984897453278385172336457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10656598302185590114890971 15984897453278385172336457)
          ·
            refine ⟨11988673089958788879252343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15984897453278385172336457 11988673089958788879252343)
            ·
              refine ⟨17983009634938183318878515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11988673089958788879252343 17983009634938183318878515)
              ·
                refine ⟨26974514452407274978317773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17983009634938183318878515 26974514452407274978317773)
                ·
                  refine ⟨10115442919652728116869165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26974514452407274978317773 10115442919652728116869165)
                  ·
                    refine ⟨3793291094869773043825937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10115442919652728116869165 3793291094869773043825937)
                    ·
                      refine ⟨2844968321152329782869453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793291094869773043825937 2844968321152329782869453)
                      ·
                        rfl

theorem cell23_5540556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5540556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540556 prefixEnd_5540556 := by exact prefixLift 5540556
  have htrace : WordTrace (prefixWord ++ tailWord_5540556) baseStart_5540556 baseEnd_5540556 := by
    simpa [prefixWord, tailWord_5540556, baseEnd_5540556] using wordTrace_append hprefix tailTrace_5540556
  have hstable : (prefixWord ++ tailWord_5540556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540556).length < 2 ^ (prefixWord ++ tailWord_5540556).sum := by decide
  have hdescent : baseEnd_5540556 < baseStart_5540556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540569 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 1, 4, 2]
def baseStart_5540569 : Nat := 118140960795 + 5540569 * 2 ^ 59
def prefixEnd_5540569 : Nat := 4983230072969 + 3 ^ 40 * 5540569 * 2
def baseEnd_5540569 : Nat := 2844974996400838232006893

theorem tailTrace_5540569 : CollatzResearch.WordTrace tailWord_5540569 prefixEnd_5540569 2844974996400838232006893 := by
  unfold tailWord_5540569
  simp only [CollatzResearch.WordTrace]
  refine ⟨202081153064472241695192761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134720768709648161130128507 202081153064472241695192761)
  ·
    refine ⟨151560864798354181271394571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202081153064472241695192761 151560864798354181271394571)
    ·
      refine ⟨227341297197531271907091857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151560864798354181271394571 227341297197531271907091857)
      ·
        refine ⟨170505972898148453930318893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227341297197531271907091857 170505972898148453930318893)
        ·
          refine ⟨63939739836805670223869585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170505972898148453930318893 63939739836805670223869585)
          ·
            refine ⟨47954804877604252667902189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63939739836805670223869585 47954804877604252667902189)
            ·
              refine ⟨17983051829101594750463321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47954804877604252667902189 17983051829101594750463321)
              ·
                refine ⟨13487288871826196062847491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17983051829101594750463321 13487288871826196062847491)
                ·
                  refine ⟨20230933307739294094271237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13487288871826196062847491 20230933307739294094271237)
                  ·
                    refine ⟨3793299995201117642675857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20230933307739294094271237 3793299995201117642675857)
                    ·
                      refine ⟨2844974996400838232006893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793299995201117642675857 2844974996400838232006893)
                      ·
                        rfl

theorem cell23_5540569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_5540569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540569 prefixEnd_5540569 := by exact prefixLift 5540569
  have htrace : WordTrace (prefixWord ++ tailWord_5540569) baseStart_5540569 baseEnd_5540569 := by
    simpa [prefixWord, tailWord_5540569, baseEnd_5540569] using wordTrace_append hprefix tailTrace_5540569
  have hstable : (prefixWord ++ tailWord_5540569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540569).length < 2 ^ (prefixWord ++ tailWord_5540569).sum := by decide
  have hdescent : baseEnd_5540569 < baseStart_5540569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540585 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_5540585 : Nat := 118140960795 + 5540585 * 2 ^ 59
def prefixEnd_5540585 : Nat := 4983230072969 + 3 ^ 40 * 5540585 * 2
def baseEnd_5540585 : Nat := 2844983212091310169406819

theorem tailTrace_5540585 : CollatzResearch.WordTrace tailWord_5540585 prefixEnd_5540585 2844983212091310169406819 := by
  unfold tailWord_5540585
  simp only [CollatzResearch.WordTrace]
  refine ⟨202081736632414276427775209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134721157754942850951850139 202081736632414276427775209)
  ·
    refine ⟨151561302474310707320831407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202081736632414276427775209 151561302474310707320831407)
    ·
      refine ⟨227341953711466060981247111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151561302474310707320831407 227341953711466060981247111)
      ·
        refine ⟨341012930567199091471870667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227341953711466060981247111 341012930567199091471870667)
        ·
          refine ⟨511519395850798637207806001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341012930567199091471870667 511519395850798637207806001)
          ·
            refine ⟨383639546888098977905854501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511519395850798637207806001 383639546888098977905854501)
            ·
              refine ⟨71932415041518558357347719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 383639546888098977905854501 71932415041518558357347719)
              ·
                refine ⟨107898622562277837536021579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71932415041518558357347719 107898622562277837536021579)
                ·
                  refine ⟨161847933843416756304032369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107898622562277837536021579 161847933843416756304032369)
                  ·
                    refine ⟨121385950382562567228024277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161847933843416756304032369 121385950382562567228024277)
                    ·
                      refine ⟨2844983212091310169406819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121385950382562567228024277 2844983212091310169406819)
                      ·
                        rfl

theorem cell23_5540585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_5540585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540585 prefixEnd_5540585 := by exact prefixLift 5540585
  have htrace : WordTrace (prefixWord ++ tailWord_5540585) baseStart_5540585 baseEnd_5540585 := by
    simpa [prefixWord, tailWord_5540585, baseEnd_5540585] using wordTrace_append hprefix tailTrace_5540585
  have hstable : (prefixWord ++ tailWord_5540585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540585).length < 2 ^ (prefixWord ++ tailWord_5540585).sum := by decide
  have hdescent : baseEnd_5540585 < baseStart_5540585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540595 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_5540595 : Nat := 118140960795 + 5540595 * 2 ^ 59
def prefixEnd_5540595 : Nat := 4983230072969 + 3 ^ 40 * 5540595 * 2
def baseEnd_5540595 : Nat := 2844988346897855130281773

theorem tailTrace_5540595 : CollatzResearch.WordTrace tailWord_5540595 prefixEnd_5540595 2844988346897855130281773 := by
  unfold tailWord_5540595
  simp only [CollatzResearch.WordTrace]
  refine ⟨202082101362378048135639239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134721400908252032090426159 202082101362378048135639239)
  ·
    refine ⟨303123152043567072203458859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202082101362378048135639239 303123152043567072203458859)
    ·
      refine ⟨454684728065350608305188289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303123152043567072203458859 454684728065350608305188289)
      ·
        refine ⟨341013546049012956228891217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454684728065350608305188289 341013546049012956228891217)
        ·
          refine ⟨255760159536759717171668413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341013546049012956228891217 255760159536759717171668413)
          ·
            refine ⟨95910059826284893939375655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255760159536759717171668413 95910059826284893939375655)
            ·
              refine ⟨143865089739427340909063483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95910059826284893939375655 143865089739427340909063483)
              ·
                refine ⟨215797634609141011363595225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143865089739427340909063483 215797634609141011363595225)
                ·
                  refine ⟨161848225956855758522696419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215797634609141011363595225 161848225956855758522696419)
                  ·
                    refine ⟨242772338935283637784044629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161848225956855758522696419 242772338935283637784044629)
                    ·
                      refine ⟨2844988346897855130281773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 242772338935283637784044629 2844988346897855130281773)
                      ·
                        rfl

theorem cell23_5540595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_5540595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540595 prefixEnd_5540595 := by exact prefixLift 5540595
  have htrace : WordTrace (prefixWord ++ tailWord_5540595) baseStart_5540595 baseEnd_5540595 := by
    simpa [prefixWord, tailWord_5540595, baseEnd_5540595] using wordTrace_append hprefix tailTrace_5540595
  have hstable : (prefixWord ++ tailWord_5540595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540595).length < 2 ^ (prefixWord ++ tailWord_5540595).sum := by decide
  have hdescent : baseEnd_5540595 < baseStart_5540595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540602 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_5540602 : Nat := 118140960795 + 5540602 * 2 ^ 59
def prefixEnd_5540602 : Nat := 4983230072969 + 3 ^ 40 * 5540602 * 2
def baseEnd_5540602 : Nat := 2844991941262436602894241

theorem tailTrace_5540602 : CollatzResearch.WordTrace tailWord_5540602 prefixEnd_5540602 2844991941262436602894241 := by
  unfold tailWord_5540602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50520589168338172082786015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134721571115568458887429373 50520589168338172082786015)
  ·
    refine ⟨75780883752507258124179023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50520589168338172082786015 75780883752507258124179023)
    ·
      refine ⟨113671325628760887186268535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75780883752507258124179023 113671325628760887186268535)
      ·
        refine ⟨170506988443141330779402803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113671325628760887186268535 170506988443141330779402803)
        ·
          refine ⟨255760482664711996169104205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170506988443141330779402803 255760482664711996169104205)
          ·
            refine ⟨95910180999266998563414077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255760482664711996169104205 95910180999266998563414077)
            ·
              refine ⟨35966317874725124461280279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95910180999266998563414077 35966317874725124461280279)
              ·
                refine ⟨53949476812087686691920419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35966317874725124461280279 53949476812087686691920419)
                ·
                  refine ⟨80924215218131530037880629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53949476812087686691920419 80924215218131530037880629)
                  ·
                    refine ⟨7586645176699830941051309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80924215218131530037880629 7586645176699830941051309)
                    ·
                      refine ⟨2844991941262436602894241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7586645176699830941051309 2844991941262436602894241)
                      ·
                        rfl

theorem cell23_5540602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_5540602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540602 prefixEnd_5540602 := by exact prefixLift 5540602
  have htrace : WordTrace (prefixWord ++ tailWord_5540602) baseStart_5540602 baseEnd_5540602 := by
    simpa [prefixWord, tailWord_5540602, baseEnd_5540602] using wordTrace_append hprefix tailTrace_5540602
  have hstable : (prefixWord ++ tailWord_5540602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540602).length < 2 ^ (prefixWord ++ tailWord_5540602).sum := by decide
  have hdescent : baseEnd_5540602 < baseStart_5540602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540637 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5540637 : Nat := 118140960795 + 5540637 * 2 ^ 59
def prefixEnd_5540637 : Nat := 4983230072969 + 3 ^ 40 * 5540637 * 2
def baseEnd_5540637 : Nat := 2845009913085343965956581

theorem tailTrace_5540637 : CollatzResearch.WordTrace tailWord_5540637 prefixEnd_5540637 2845009913085343965956581 := by
  unfold tailWord_5540637
  simp only [CollatzResearch.WordTrace]
  refine ⟨202083633228225889308668165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134722422152150592872445443 202083633228225889308668165)
  ·
    refine ⟨37890681230292354245375281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202083633228225889308668165 37890681230292354245375281)
    ·
      refine ⟨28418010922719265684031461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37890681230292354245375281 28418010922719265684031461)
      ·
        refine ⟨5328377048009862315755899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28418010922719265684031461 5328377048009862315755899)
        ·
          refine ⟨7992565572014793473633849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328377048009862315755899 7992565572014793473633849)
          ·
            refine ⟨5994424179011095105225387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7992565572014793473633849 5994424179011095105225387)
            ·
              refine ⟨8991636268516642657838081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994424179011095105225387 8991636268516642657838081)
              ·
                refine ⟨6743727201387481993378561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8991636268516642657838081 6743727201387481993378561)
                ·
                  refine ⟨5057795401040611495033921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6743727201387481993378561 5057795401040611495033921)
                  ·
                    refine ⟨3793346550780458621275441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5057795401040611495033921 3793346550780458621275441)
                    ·
                      refine ⟨2845009913085343965956581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793346550780458621275441 2845009913085343965956581)
                      ·
                        rfl

theorem cell23_5540637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5540637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540637 prefixEnd_5540637 := by exact prefixLift 5540637
  have htrace : WordTrace (prefixWord ++ tailWord_5540637) baseStart_5540637 baseEnd_5540637 := by
    simpa [prefixWord, tailWord_5540637, baseEnd_5540637] using wordTrace_append hprefix tailTrace_5540637
  have hstable : (prefixWord ++ tailWord_5540637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540637).length < 2 ^ (prefixWord ++ tailWord_5540637).sum := by decide
  have hdescent : baseEnd_5540637 < baseStart_5540637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540679 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_5540679 : Nat := 118140960795 + 5540679 * 2 ^ 59
def prefixEnd_5540679 : Nat := 4983230072969 + 3 ^ 40 * 5540679 * 2
def baseEnd_5540679 : Nat := 2845031479272832801631387

theorem tailTrace_5540679 : CollatzResearch.WordTrace tailWord_5540679 prefixEnd_5540679 2845031479272832801631387 := by
  unfold tailWord_5540679
  simp only [CollatzResearch.WordTrace]
  refine ⟨202085165094073730481697091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134723443396049153654464727 202085165094073730481697091)
  ·
    refine ⟨303127747641110595722545637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202085165094073730481697091 303127747641110595722545637)
    ·
      refine ⟨56836452682708236697977307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303127747641110595722545637 56836452682708236697977307)
      ·
        refine ⟨85254679024062355046965961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56836452682708236697977307 85254679024062355046965961)
        ·
          refine ⟨63941009268046766285224471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85254679024062355046965961 63941009268046766285224471)
          ·
            refine ⟨95911513902070149427836707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63941009268046766285224471 95911513902070149427836707)
            ·
              refine ⟨143867270853105224141755061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95911513902070149427836707 143867270853105224141755061)
              ·
                refine ⟨13487556642478614763289537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143867270853105224141755061 13487556642478614763289537)
                ·
                  refine ⟨10115667481858961072467153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13487556642478614763289537 10115667481858961072467153)
                  ·
                    refine ⟨7586750611394220804350365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10115667481858961072467153 7586750611394220804350365)
                    ·
                      refine ⟨2845031479272832801631387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7586750611394220804350365 2845031479272832801631387)
                      ·
                        rfl

theorem cell23_5540679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_5540679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540679 prefixEnd_5540679 := by exact prefixLift 5540679
  have htrace : WordTrace (prefixWord ++ tailWord_5540679) baseStart_5540679 baseEnd_5540679 := by
    simpa [prefixWord, tailWord_5540679, baseEnd_5540679] using wordTrace_append hprefix tailTrace_5540679
  have hstable : (prefixWord ++ tailWord_5540679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540679).length < 2 ^ (prefixWord ++ tailWord_5540679).sum := by decide
  have hdescent : baseEnd_5540679 < baseStart_5540679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540703 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 1, 4]
def baseStart_5540703 : Nat := 118140960795 + 5540703 * 2 ^ 59
def prefixEnd_5540703 : Nat := 4983230072969 + 3 ^ 40 * 5540703 * 2
def baseEnd_5540703 : Nat := 948347934269513569243759

theorem tailTrace_5540703 : CollatzResearch.WordTrace tailWord_5540703 prefixEnd_5540703 948347934269513569243759 := by
  unfold tailWord_5540703
  simp only [CollatzResearch.WordTrace]
  refine ⟨202086040445986782580570763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134724026963991188387047175 202086040445986782580570763)
  ·
    refine ⟨303129060668980173870856145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202086040445986782580570763 303129060668980173870856145)
    ·
      refine ⟨227346795501735130403142109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303129060668980173870856145 227346795501735130403142109)
      ·
        refine ⟨85255048313150673901178291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227346795501735130403142109 85255048313150673901178291)
        ·
          refine ⟨127882572469726010851767437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85255048313150673901178291 127882572469726010851767437)
          ·
            refine ⟨47955964676147254069412789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127882572469726010851767437 47955964676147254069412789)
            ·
              refine ⟨4495871688388805069007449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47955964676147254069412789 4495871688388805069007449)
              ·
                refine ⟨3371903766291603801755587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495871688388805069007449 3371903766291603801755587)
                ·
                  refine ⟨5057855649437405702633381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371903766291603801755587 5057855649437405702633381)
                  ·
                    refine ⟨948347934269513569243759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057855649437405702633381 948347934269513569243759)
                    ·
                      rfl

theorem cell23_5540703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 1, 4].length) (baseStart_5540703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540703 prefixEnd_5540703 := by exact prefixLift 5540703
  have htrace : WordTrace (prefixWord ++ tailWord_5540703) baseStart_5540703 baseEnd_5540703 := by
    simpa [prefixWord, tailWord_5540703, baseEnd_5540703] using wordTrace_append hprefix tailTrace_5540703
  have hstable : (prefixWord ++ tailWord_5540703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540703).length < 2 ^ (prefixWord ++ tailWord_5540703).sum := by decide
  have hdescent : baseEnd_5540703 < baseStart_5540703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540719 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 5, 2]
def baseStart_5540719 : Nat := 118140960795 + 5540719 * 2 ^ 59
def prefixEnd_5540719 : Nat := 4983230072969 + 3 ^ 40 * 5540719 * 2
def baseEnd_5540719 : Nat := 2845052018499012645131203

theorem tailTrace_5540719 : CollatzResearch.WordTrace tailWord_5540719 prefixEnd_5540719 2845052018499012645131203 := by
  unfold tailWord_5540719
  simp only [CollatzResearch.WordTrace]
  refine ⟨202086624013928817313153211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134724416009285878208768807 202086624013928817313153211)
  ·
    refine ⟨303129936020893225969729817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202086624013928817313153211 303129936020893225969729817)
    ·
      refine ⟨227347452015669919477297363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303129936020893225969729817 227347452015669919477297363)
      ·
        refine ⟨341021178023504879215946045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227347452015669919477297363 341021178023504879215946045)
        ·
          refine ⟨127882941758814329705979767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341021178023504879215946045 127882941758814329705979767)
          ·
            refine ⟨191824412638221494558969651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127882941758814329705979767 191824412638221494558969651)
            ·
              refine ⟨287736618957332241838454477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191824412638221494558969651 287736618957332241838454477)
              ·
                refine ⟨107901232108999590689420429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287736618957332241838454477 107901232108999590689420429)
                ·
                  refine ⟨40462962040874846508532661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107901232108999590689420429 40462962040874846508532661)
                  ·
                    refine ⟨3793402691332016860174937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40462962040874846508532661 3793402691332016860174937)
                    ·
                      refine ⟨2845052018499012645131203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793402691332016860174937 2845052018499012645131203)
                      ·
                        rfl

theorem cell23_5540719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5, 2].length) (baseStart_5540719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540719 prefixEnd_5540719 := by exact prefixLift 5540719
  have htrace : WordTrace (prefixWord ++ tailWord_5540719) baseStart_5540719 baseEnd_5540719 := by
    simpa [prefixWord, tailWord_5540719, baseEnd_5540719] using wordTrace_append hprefix tailTrace_5540719
  have hstable : (prefixWord ++ tailWord_5540719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540719).length < 2 ^ (prefixWord ++ tailWord_5540719).sum := by decide
  have hdescent : baseEnd_5540719 < baseStart_5540719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540729 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_5540729 : Nat := 118140960795 + 5540729 * 2 ^ 59
def prefixEnd_5540729 : Nat := 4983230072969 + 3 ^ 40 * 5540729 * 2
def baseEnd_5540729 : Nat := 948352384435185868668719

theorem tailTrace_5540729 : CollatzResearch.WordTrace tailWord_5540729 prefixEnd_5540729 948352384435185868668719 := by
  unfold tailWord_5540729
  simp only [CollatzResearch.WordTrace]
  refine ⟨202086988743892589021017241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134724659162595059347344827 202086988743892589021017241)
  ·
    refine ⟨151565241557919441765762931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202086988743892589021017241 151565241557919441765762931)
    ·
      refine ⟨227347862336879162648644397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151565241557919441765762931 227347862336879162648644397)
      ·
        refine ⟨85255448376329685993241649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227347862336879162648644397 85255448376329685993241649)
        ·
          refine ⟨63941586282247264494931237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85255448376329685993241649 63941586282247264494931237)
          ·
            refine ⟨11989047427921362092799607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63941586282247264494931237 11989047427921362092799607)
            ·
              refine ⟨17983571141882043139199411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11989047427921362092799607 17983571141882043139199411)
              ·
                refine ⟨26975356712823064708799117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17983571141882043139199411 26975356712823064708799117)
                ·
                  refine ⟨10115758767308649265799669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26975356712823064708799117 10115758767308649265799669)
                  ·
                    refine ⟨948352384435185868668719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10115758767308649265799669 948352384435185868668719)
                    ·
                      rfl

theorem cell23_5540729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_5540729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540729 prefixEnd_5540729 := by exact prefixLift 5540729
  have htrace : WordTrace (prefixWord ++ tailWord_5540729) baseStart_5540729 baseEnd_5540729 := by
    simpa [prefixWord, tailWord_5540729, baseEnd_5540729] using wordTrace_append hprefix tailTrace_5540729
  have hstable : (prefixWord ++ tailWord_5540729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540729).length < 2 ^ (prefixWord ++ tailWord_5540729).sum := by decide
  have hdescent : baseEnd_5540729 < baseStart_5540729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540754 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_5540754 : Nat := 118140960795 + 5540754 * 2 ^ 59
def prefixEnd_5540754 : Nat := 4983230072969 + 3 ^ 40 * 5540754 * 2
def baseEnd_5540754 : Nat := 948356663440640002731181

theorem tailTrace_5540754 : CollatzResearch.WordTrace tailWord_5540754 prefixEnd_5540754 948356663440640002731181 := by
  unfold tailWord_5540754
  simp only [CollatzResearch.WordTrace]
  refine ⟨50521975142200504572669329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134725267045868012193784877 50521975142200504572669329)
  ·
    refine ⟨37891481356650378429501997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50521975142200504572669329 37891481356650378429501997)
    ·
      refine ⟨14209305508743891911063249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37891481356650378429501997 14209305508743891911063249)
      ·
        refine ⟨10656979131557918933297437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14209305508743891911063249 10656979131557918933297437)
        ·
          refine ⟨3996367174334219599986539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10656979131557918933297437 3996367174334219599986539)
          ·
            refine ⟨5994550761501329399979809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996367174334219599986539 5994550761501329399979809)
            ·
              refine ⟨4495913071125997049984857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5994550761501329399979809 4495913071125997049984857)
              ·
                refine ⟨3371934803344497787488643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495913071125997049984857 3371934803344497787488643)
                ·
                  refine ⟨5057902205016746681232965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371934803344497787488643 5057902205016746681232965)
                  ·
                    refine ⟨948356663440640002731181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5057902205016746681232965 948356663440640002731181)
                    ·
                      rfl

theorem cell23_5540754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_5540754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540754 prefixEnd_5540754 := by exact prefixLift 5540754
  have htrace : WordTrace (prefixWord ++ tailWord_5540754) baseStart_5540754 baseEnd_5540754 := by
    simpa [prefixWord, tailWord_5540754, baseEnd_5540754] using wordTrace_append hprefix tailTrace_5540754
  have hstable : (prefixWord ++ tailWord_5540754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540754).length < 2 ^ (prefixWord ++ tailWord_5540754).sum := by decide
  have hdescent : baseEnd_5540754 < baseStart_5540754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540799 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_5540799 : Nat := 118140960795 + 5540799 * 2 ^ 59
def prefixEnd_5540799 : Nat := 4983230072969 + 3 ^ 40 * 5540799 * 2
def baseEnd_5540799 : Nat := 2845093096951372332130835

theorem tailTrace_5540799 : CollatzResearch.WordTrace tailWord_5540799 prefixEnd_5540799 2845093096951372332130835 := by
  unfold tailWord_5540799
  simp only [CollatzResearch.WordTrace]
  refine ⟨202089541853638990976065451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134726361235759327317376967 202089541853638990976065451)
  ·
    refine ⟨303134312780458486464098177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202089541853638990976065451 303134312780458486464098177)
    ·
      refine ⟨227350734585343864848073633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303134312780458486464098177 227350734585343864848073633)
      ·
        refine ⟨170513050939007898636055225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227350734585343864848073633 170513050939007898636055225)
        ·
          refine ⟨127884788204255923977041419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170513050939007898636055225 127884788204255923977041419)
          ·
            refine ⟨191827182306383885965562129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127884788204255923977041419 191827182306383885965562129)
            ·
              refine ⟨143870386729787914474171597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191827182306383885965562129 143870386729787914474171597)
              ·
                refine ⟨53951395023670467927814349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143870386729787914474171597 53951395023670467927814349)
                ·
                  refine ⟨20231773133876425472930381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53951395023670467927814349 20231773133876425472930381)
                  ·
                    refine ⟨7586914925203659552348893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20231773133876425472930381 7586914925203659552348893)
                    ·
                      refine ⟨2845093096951372332130835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7586914925203659552348893 2845093096951372332130835)
                      ·
                        rfl

theorem cell23_5540799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_5540799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540799 prefixEnd_5540799 := by exact prefixLift 5540799
  have htrace : WordTrace (prefixWord ++ tailWord_5540799) baseStart_5540799 baseEnd_5540799 := by
    simpa [prefixWord, tailWord_5540799, baseEnd_5540799] using wordTrace_append hprefix tailTrace_5540799
  have hstable : (prefixWord ++ tailWord_5540799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540799).length < 2 ^ (prefixWord ++ tailWord_5540799).sum := by decide
  have hdescent : baseEnd_5540799 < baseStart_5540799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540800 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 1, 2, 2]
def baseStart_5540800 : Nat := 118140960795 + 5540800 * 2 ^ 59
def prefixEnd_5540800 : Nat := 4983230072969 + 3 ^ 40 * 5540800 * 2
def baseEnd_5540800 : Nat := 2845093610432026828218331

theorem tailTrace_5540800 : CollatzResearch.WordTrace tailWord_5540800 prefixEnd_5540800 2845093610432026828218331 := by
  unfold tailWord_5540800
  simp only [CollatzResearch.WordTrace]
  refine ⟨101044789163317684073425927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134726385551090245431234569 101044789163317684073425927)
  ·
    refine ⟨151567183744976526110138891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101044789163317684073425927 151567183744976526110138891)
    ·
      refine ⟨227350775617464789165208337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151567183744976526110138891 227350775617464789165208337)
      ·
        refine ⟨170513081713098591873906253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227350775617464789165208337 170513081713098591873906253)
        ·
          refine ⟨63942405642411971952714845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170513081713098591873906253 63942405642411971952714845)
          ·
            refine ⟨23978402115904489482268067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63942405642411971952714845 23978402115904489482268067)
            ·
              refine ⟨35967603173856734223402101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23978402115904489482268067 35967603173856734223402101)
              ·
                refine ⟨3371962797549068833443947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35967603173856734223402101 3371962797549068833443947)
                ·
                  refine ⟨5057944196323603250165921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371962797549068833443947 5057944196323603250165921)
                  ·
                    refine ⟨3793458147242702437624441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5057944196323603250165921 3793458147242702437624441)
                    ·
                      refine ⟨2845093610432026828218331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793458147242702437624441 2845093610432026828218331)
                      ·
                        rfl

theorem cell23_5540800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_5540800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540800 prefixEnd_5540800 := by exact prefixLift 5540800
  have htrace : WordTrace (prefixWord ++ tailWord_5540800) baseStart_5540800 baseEnd_5540800 := by
    simpa [prefixWord, tailWord_5540800, baseEnd_5540800] using wordTrace_append hprefix tailTrace_5540800
  have hstable : (prefixWord ++ tailWord_5540800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540800).length < 2 ^ (prefixWord ++ tailWord_5540800).sum := by decide
  have hdescent : baseEnd_5540800 < baseStart_5540800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540856 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_5540856 : Nat := 118140960795 + 5540856 * 2 ^ 59
def prefixEnd_5540856 : Nat := 4983230072969 + 3 ^ 40 * 5540856 * 2
def baseEnd_5540856 : Nat := 2845122365348678609118073

theorem tailTrace_5540856 : CollatzResearch.WordTrace tailWord_5540856 prefixEnd_5540856 2845122365348678609118073 := by
  unfold tailWord_5540856
  simp only [CollatzResearch.WordTrace]
  refine ⟨101045810407216244855445211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134727747209621659807260281 101045810407216244855445211)
  ·
    refine ⟨151568715610824367283167817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101045810407216244855445211 151568715610824367283167817)
    ·
      refine ⟨113676536708118275462375863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151568715610824367283167817 113676536708118275462375863)
      ·
        refine ⟨170514805062177413193563795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113676536708118275462375863 170514805062177413193563795)
        ·
          refine ⟨255772207593266119790345693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170514805062177413193563795 255772207593266119790345693)
          ·
            refine ⟨95914577847474794921379635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255772207593266119790345693 95914577847474794921379635)
            ·
              refine ⟨143871866771212192382069453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95914577847474794921379635 143871866771212192382069453)
              ·
                refine ⟨53951950039204572143276045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143871866771212192382069453 53951950039204572143276045)
                ·
                  refine ⟨20231981264701714553728517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53951950039204572143276045 20231981264701714553728517)
                  ·
                    refine ⟨3793496487131571478824097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20231981264701714553728517 3793496487131571478824097)
                    ·
                      refine ⟨2845122365348678609118073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793496487131571478824097 2845122365348678609118073)
                      ·
                        rfl

theorem cell23_5540856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_5540856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540856 prefixEnd_5540856 := by exact prefixLift 5540856
  have htrace : WordTrace (prefixWord ++ tailWord_5540856) baseStart_5540856 baseEnd_5540856 := by
    simpa [prefixWord, tailWord_5540856, baseEnd_5540856] using wordTrace_append hprefix tailTrace_5540856
  have hstable : (prefixWord ++ tailWord_5540856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540856).length < 2 ^ (prefixWord ++ tailWord_5540856).sum := by decide
  have hdescent : baseEnd_5540856 < baseStart_5540856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540859 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3]
def baseStart_5540859 : Nat := 118140960795 + 5540859 * 2 ^ 59
def prefixEnd_5540859 : Nat := 4983230072969 + 3 ^ 40 * 5540859 * 2
def baseEnd_5540859 : Nat := 2845123905790642097380559

theorem tailTrace_5540859 : CollatzResearch.WordTrace tailWord_5540859 prefixEnd_5540859 2845123905790642097380559 := by
  unfold tailWord_5540859
  simp only [CollatzResearch.WordTrace]
  refine ⟨202091730233421621223249631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134727820155614414148833087 202091730233421621223249631)
  ·
    refine ⟨303137595350132431834874447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202091730233421621223249631 303137595350132431834874447)
    ·
      refine ⟨454706393025198647752311671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303137595350132431834874447 454706393025198647752311671)
      ·
        refine ⟨682059589537797971628467507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454706393025198647752311671 682059589537797971628467507)
        ·
          refine ⟨1023089384306696957442701261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682059589537797971628467507 1023089384306696957442701261)
          ·
            refine ⟨383658519115011359041012973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1023089384306696957442701261 383658519115011359041012973)
            ·
              refine ⟨143871944668129259640379865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383658519115011359041012973 143871944668129259640379865)
              ·
                refine ⟨107903958501096944730284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143871944668129259640379865 107903958501096944730284899)
                ·
                  refine ⟨161855937751645417095427349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107903958501096944730284899 161855937751645417095427349)
                  ·
                    refine ⟨7586997082108378926348157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161855937751645417095427349 7586997082108378926348157)
                    ·
                      refine ⟨2845123905790642097380559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7586997082108378926348157 2845123905790642097380559)
                      ·
                        rfl

theorem cell23_5540859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 3].length) (baseStart_5540859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540859 prefixEnd_5540859 := by exact prefixLift 5540859
  have htrace : WordTrace (prefixWord ++ tailWord_5540859) baseStart_5540859 baseEnd_5540859 := by
    simpa [prefixWord, tailWord_5540859, baseEnd_5540859] using wordTrace_append hprefix tailTrace_5540859
  have hstable : (prefixWord ++ tailWord_5540859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540859).length < 2 ^ (prefixWord ++ tailWord_5540859).sum := by decide
  have hdescent : baseEnd_5540859 < baseStart_5540859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540890 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_5540890 : Nat := 118140960795 + 5540890 * 2 ^ 59
def prefixEnd_5540890 : Nat := 4983230072969 + 3 ^ 40 * 5540890 * 2
def baseEnd_5540890 : Nat := 2845139823690931476092917

theorem tailTrace_5540890 : CollatzResearch.WordTrace tailWord_5540890 prefixEnd_5540890 2845139823690931476092917 := by
  unfold tailWord_5540890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50523215224077328379407031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134728573930872875678418749 50523215224077328379407031)
  ·
    refine ⟨75784822836115992569110547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50523215224077328379407031 75784822836115992569110547)
    ·
      refine ⟨113677234254173988853665821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75784822836115992569110547 113677234254173988853665821)
      ·
        refine ⟨42628962845315245820124683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113677234254173988853665821 42628962845315245820124683)
        ·
          refine ⟨63943444267972868730187025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42628962845315245820124683 63943444267972868730187025)
          ·
            refine ⟨47957583200979651547640269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63943444267972868730187025 47957583200979651547640269)
            ·
              refine ⟨17984093700367369330365101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47957583200979651547640269 17984093700367369330365101)
              ·
                refine ⟨6744035137637763498886913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17984093700367369330365101 6744035137637763498886913)
                ·
                  refine ⟨5058026353228322624165185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6744035137637763498886913 5058026353228322624165185)
                  ·
                    refine ⟨3793519764921241968123889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5058026353228322624165185 3793519764921241968123889)
                    ·
                      refine ⟨2845139823690931476092917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793519764921241968123889 2845139823690931476092917)
                      ·
                        rfl

theorem cell23_5540890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_5540890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540890 prefixEnd_5540890 := by exact prefixLift 5540890
  have htrace : WordTrace (prefixWord ++ tailWord_5540890) baseStart_5540890 baseEnd_5540890 := by
    simpa [prefixWord, tailWord_5540890, baseEnd_5540890] using wordTrace_append hprefix tailTrace_5540890
  have hstable : (prefixWord ++ tailWord_5540890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540890).length < 2 ^ (prefixWord ++ tailWord_5540890).sum := by decide
  have hdescent : baseEnd_5540890 < baseStart_5540890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5540979 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_5540979 : Nat := 118140960795 + 5540979 * 2 ^ 59
def prefixEnd_5540979 : Nat := 4983230072969 + 3 ^ 40 * 5540979 * 2
def baseEnd_5540979 : Nat := 2845185523469181627880007

theorem tailTrace_5540979 : CollatzResearch.WordTrace tailWord_5540979 prefixEnd_5540979 2845185523469181627880007 := by
  unfold tailWord_5540979
  simp only [CollatzResearch.WordTrace]
  refine ⟨202096106992986881717617991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134730737995324587811745327 202096106992986881717617991)
  ·
    refine ⟨303144160489480322576426987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202096106992986881717617991 303144160489480322576426987)
    ·
      refine ⟨454716240734220483864640481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303144160489480322576426987 454716240734220483864640481)
      ·
        refine ⟨341037180550665362898480361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454716240734220483864640481 341037180550665362898480361)
        ·
          refine ⟨255777885412999022173860271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341037180550665362898480361 255777885412999022173860271)
          ·
            refine ⟨383666828119498533260790407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255777885412999022173860271 383666828119498533260790407)
            ·
              refine ⟨575500242179247799891185611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383666828119498533260790407 575500242179247799891185611)
              ·
                refine ⟨863250363268871699836778417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575500242179247799891185611 863250363268871699836778417)
                ·
                  refine ⟨647437772451653774877583813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863250363268871699836778417 647437772451653774877583813)
                  ·
                    refine ⟨121394582334685082789546965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647437772451653774877583813 121394582334685082789546965)
                    ·
                      refine ⟨2845185523469181627880007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121394582334685082789546965 2845185523469181627880007)
                      ·
                        rfl

theorem cell23_5540979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_5540979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5540979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5540979 prefixEnd_5540979 := by exact prefixLift 5540979
  have htrace : WordTrace (prefixWord ++ tailWord_5540979) baseStart_5540979 baseEnd_5540979 := by
    simpa [prefixWord, tailWord_5540979, baseEnd_5540979] using wordTrace_append hprefix tailTrace_5540979
  have hstable : (prefixWord ++ tailWord_5540979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5540979).length < 2 ^ (prefixWord ++ tailWord_5540979).sum := by decide
  have hdescent : baseEnd_5540979 < baseStart_5540979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5540979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541013 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_5541013 : Nat := 118140960795 + 5541013 * 2 ^ 59
def prefixEnd_5541013 : Nat := 4983230072969 + 3 ^ 40 * 5541013 * 2
def baseEnd_5541013 : Nat := 2845202981811434494854851

theorem tailTrace_5541013 : CollatzResearch.WordTrace tailWord_5541013 prefixEnd_5541013 2845202981811434494854851 := by
  unfold tailWord_5541013
  simp only [CollatzResearch.WordTrace]
  refine ⟨202097347074863705524355693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134731564716575803682903795 202097347074863705524355693)
  ·
    refine ⟨75786505153073889571633385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202097347074863705524355693 75786505153073889571633385)
    ·
      refine ⟨56839878864805417178725039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75786505153073889571633385 56839878864805417178725039)
      ·
        refine ⟨85259818297208125768087559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56839878864805417178725039 85259818297208125768087559)
        ·
          refine ⟨127889727445812188652131339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85259818297208125768087559 127889727445812188652131339)
          ·
            refine ⟨191834591168718282978197009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127889727445812188652131339 191834591168718282978197009)
            ·
              refine ⟨143875943376538712233647757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191834591168718282978197009 143875943376538712233647757)
              ·
                refine ⟨53953478766202017087617909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143875943376538712233647757 53953478766202017087617909)
                ·
                  refine ⟨5058138634331439101964179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53953478766202017087617909 5058138634331439101964179)
                  ·
                    refine ⟨7587207951497158652946269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058138634331439101964179 7587207951497158652946269)
                    ·
                      refine ⟨2845202981811434494854851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7587207951497158652946269 2845202981811434494854851)
                      ·
                        rfl

theorem cell23_5541013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_5541013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541013 prefixEnd_5541013 := by exact prefixLift 5541013
  have htrace : WordTrace (prefixWord ++ tailWord_5541013) baseStart_5541013 baseEnd_5541013 := by
    simpa [prefixWord, tailWord_5541013, baseEnd_5541013] using wordTrace_append hprefix tailTrace_5541013
  have hstable : (prefixWord ++ tailWord_5541013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541013).length < 2 ^ (prefixWord ++ tailWord_5541013).sum := by decide
  have hdescent : baseEnd_5541013 < baseStart_5541013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541070 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_5541070 : Nat := 118140960795 + 5541070 * 2 ^ 59
def prefixEnd_5541070 : Nat := 4983230072969 + 3 ^ 40 * 5541070 * 2
def baseEnd_5541070 : Nat := 2845232250208740771842089

theorem tailTrace_5541070 : CollatzResearch.WordTrace tailWord_5541070 prefixEnd_5541070 2845232250208740771842089 := by
  unfold tailWord_5541070
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262428254457150532397583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134732950690438136172787109 25262428254457150532397583)
  ·
    refine ⟨37893642381685725798596375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25262428254457150532397583 37893642381685725798596375)
    ·
      refine ⟨56840463572528588697894563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37893642381685725798596375 56840463572528588697894563)
      ·
        refine ⟨85260695358792883046841845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56840463572528588697894563 85260695358792883046841845)
        ·
          refine ⟨7993190189886832785641423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85260695358792883046841845 7993190189886832785641423)
          ·
            refine ⟨11989785284830249178462135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993190189886832785641423 11989785284830249178462135)
            ·
              refine ⟨17984677927245373767693203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11989785284830249178462135 17984677927245373767693203)
              ·
                refine ⟨26977016890868060651539805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17984677927245373767693203 26977016890868060651539805)
                ·
                  refine ⟨10116381334075522744327427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26977016890868060651539805 10116381334075522744327427)
                  ·
                    refine ⟨15174572001113284116491141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10116381334075522744327427 15174572001113284116491141)
                    ·
                      refine ⟨2845232250208740771842089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15174572001113284116491141 2845232250208740771842089)
                      ·
                        rfl

theorem cell23_5541070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_5541070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541070 prefixEnd_5541070 := by exact prefixLift 5541070
  have htrace : WordTrace (prefixWord ++ tailWord_5541070) baseStart_5541070 baseEnd_5541070 := by
    simpa [prefixWord, tailWord_5541070, baseEnd_5541070] using wordTrace_append hprefix tailTrace_5541070
  have hstable : (prefixWord ++ tailWord_5541070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541070).length < 2 ^ (prefixWord ++ tailWord_5541070).sum := by decide
  have hdescent : baseEnd_5541070 < baseStart_5541070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541093 : List Nat := [1, 3, 1, 4, 4, 10]
def baseStart_5541093 : Nat := 118140960795 + 5541093 * 2 ^ 59
def prefixEnd_5541093 : Nat := 4983230072969 + 3 ^ 40 * 5541093 * 2
def baseEnd_5541093 : Nat := 11708823293266642723681

theorem tailTrace_5541093 : CollatzResearch.WordTrace tailWord_5541093 prefixEnd_5541093 11708823293266642723681 := by
  unfold tailWord_5541093
  simp only [CollatzResearch.WordTrace]
  refine ⟨202100264914573879187267933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134733509943049252791511955 202100264914573879187267933)
  ·
    refine ⟨75787599342965204695225475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202100264914573879187267933 75787599342965204695225475)
    ·
      refine ⟨113681399014447807042838213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75787599342965204695225475 113681399014447807042838213)
      ·
        refine ⟨21315262315208963820532165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113681399014447807042838213 21315262315208963820532165)
        ·
          refine ⟨3996611684101680716349781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21315262315208963820532165 3996611684101680716349781)
          ·
            refine ⟨11708823293266642723681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3996611684101680716349781 11708823293266642723681)
            ·
              rfl

theorem cell23_5541093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 10].length) (baseStart_5541093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541093 prefixEnd_5541093 := by exact prefixLift 5541093
  have htrace : WordTrace (prefixWord ++ tailWord_5541093) baseStart_5541093 baseEnd_5541093 := by
    simpa [prefixWord, tailWord_5541093, baseEnd_5541093] using wordTrace_append hprefix tailTrace_5541093
  have hstable : (prefixWord ++ tailWord_5541093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541093).length < 2 ^ (prefixWord ++ tailWord_5541093).sum := by decide
  have hdescent : baseEnd_5541093 < baseStart_5541093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541138 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5541138 : Nat := 118140960795 + 5541138 * 2 ^ 59
def prefixEnd_5541138 : Nat := 4983230072969 + 3 ^ 40 * 5541138 * 2
def baseEnd_5541138 : Nat := 2845267166893246505791777

theorem tailTrace_5541138 : CollatzResearch.WordTrace tailWord_5541138 prefixEnd_5541138 2845267166893246505791777 := by
  unfold tailWord_5541138
  simp only [CollatzResearch.WordTrace]
  refine ⟨50525476549852712968164017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134734604132940567915104045 50525476549852712968164017)
  ·
    refine ⟨37894107412389534726123013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50525476549852712968164017 37894107412389534726123013)
    ·
      refine ⟨7105145139823037761148065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37894107412389534726123013 7105145139823037761148065)
      ·
        refine ⟨5328858854867278320861049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105145139823037761148065 5328858854867278320861049)
        ·
          refine ⟨3996644141150458740645787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5328858854867278320861049 3996644141150458740645787)
          ·
            refine ⟨5994966211725688110968681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3996644141150458740645787 5994966211725688110968681)
            ·
              refine ⟨4496224658794266083226511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5994966211725688110968681 4496224658794266083226511)
              ·
                refine ⟨6744336988191399124839767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496224658794266083226511 6744336988191399124839767)
                ·
                  refine ⟨10116505482287098687259651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744336988191399124839767 10116505482287098687259651)
                  ·
                    refine ⟨15174758223430648030889477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10116505482287098687259651 15174758223430648030889477)
                    ·
                      refine ⟨2845267166893246505791777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15174758223430648030889477 2845267166893246505791777)
                      ·
                        rfl

theorem cell23_5541138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5541138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541138 prefixEnd_5541138 := by exact prefixLift 5541138
  have htrace : WordTrace (prefixWord ++ tailWord_5541138) baseStart_5541138 baseEnd_5541138 := by
    simpa [prefixWord, tailWord_5541138, baseEnd_5541138] using wordTrace_append hprefix tailTrace_5541138
  have hstable : (prefixWord ++ tailWord_5541138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541138).length < 2 ^ (prefixWord ++ tailWord_5541138).sum := by decide
  have hdescent : baseEnd_5541138 < baseStart_5541138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541181 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5541181 : Nat := 118140960795 + 5541181 * 2 ^ 59
def prefixEnd_5541181 : Nat := 4983230072969 + 3 ^ 40 * 5541181 * 2
def baseEnd_5541181 : Nat := 2845289246561389837554079

theorem tailTrace_5541181 : CollatzResearch.WordTrace tailWord_5541181 prefixEnd_5541181 2845289246561389837554079 := by
  unfold tailWord_5541181
  simp only [CollatzResearch.WordTrace]
  refine ⟨202103474538255070216471397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134735649692170046810980931 202103474538255070216471397)
  ·
    refine ⟨37894401475922825665588387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202103474538255070216471397 37894401475922825665588387)
    ·
      refine ⟨56841602213884238498382581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37894401475922825665588387 56841602213884238498382581)
      ·
        refine ⟨5328900207551647359223367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56841602213884238498382581 5328900207551647359223367)
        ·
          refine ⟨7993350311327471038835051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328900207551647359223367 7993350311327471038835051)
          ·
            refine ⟨11990025466991206558252577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993350311327471038835051 11990025466991206558252577)
            ·
              refine ⟨8992519100243404918689433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11990025466991206558252577 8992519100243404918689433)
              ·
                refine ⟨6744389325182553689017075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992519100243404918689433 6744389325182553689017075)
                ·
                  refine ⟨10116583987773830533525613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744389325182553689017075 10116583987773830533525613)
                  ·
                    refine ⟨3793718995415186450072105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10116583987773830533525613 3793718995415186450072105)
                    ·
                      refine ⟨2845289246561389837554079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793718995415186450072105 2845289246561389837554079)
                      ·
                        rfl

theorem cell23_5541181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5541181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541181 prefixEnd_5541181 := by exact prefixLift 5541181
  have htrace : WordTrace (prefixWord ++ tailWord_5541181) baseStart_5541181 baseEnd_5541181 := by
    simpa [prefixWord, tailWord_5541181, baseEnd_5541181] using wordTrace_append hprefix tailTrace_5541181
  have hstable : (prefixWord ++ tailWord_5541181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541181).length < 2 ^ (prefixWord ++ tailWord_5541181).sum := by decide
  have hdescent : baseEnd_5541181 < baseStart_5541181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541183 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 7]
def baseStart_5541183 : Nat := 118140960795 + 5541183 * 2 ^ 59
def prefixEnd_5541183 : Nat := 4983230072969 + 3 ^ 40 * 5541183 * 2
def baseEnd_5541183 : Nat := 316143363724744314414341

theorem tailTrace_5541183 : CollatzResearch.WordTrace tailWord_5541183 prefixEnd_5541183 316143363724744314414341 := by
  unfold tailWord_5541183
  simp only [CollatzResearch.WordTrace]
  refine ⟨202103547484247824558044203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134735698322831883038696135 202103547484247824558044203)
  ·
    refine ⟨303155321226371736837066305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202103547484247824558044203 303155321226371736837066305)
    ·
      refine ⟨227366490919778802627799729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303155321226371736837066305 227366490919778802627799729)
      ·
        refine ⟨170524868189834101970849797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227366490919778802627799729 170524868189834101970849797)
        ·
          refine ⟨31973412785593894119534337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170524868189834101970849797 31973412785593894119534337)
          ·
            refine ⟨23980059589195420589650753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31973412785593894119534337 23980059589195420589650753)
            ·
              refine ⟨17985044691896565442238065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23980059589195420589650753 17985044691896565442238065)
              ·
                refine ⟨13488783518922424081678549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17985044691896565442238065 13488783518922424081678549)
                ·
                  refine ⟨316143363724744314414341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13488783518922424081678549 316143363724744314414341)
                  ·
                    rfl

theorem cell23_5541183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 7].length) (baseStart_5541183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541183 prefixEnd_5541183 := by exact prefixLift 5541183
  have htrace : WordTrace (prefixWord ++ tailWord_5541183) baseStart_5541183 baseEnd_5541183 := by
    simpa [prefixWord, tailWord_5541183, baseEnd_5541183] using wordTrace_append hprefix tailTrace_5541183
  have hstable : (prefixWord ++ tailWord_5541183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541183).length < 2 ^ (prefixWord ++ tailWord_5541183).sum := by decide
  have hdescent : baseEnd_5541183 < baseStart_5541183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541193 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_5541193 : Nat := 118140960795 + 5541193 * 2 ^ 59
def prefixEnd_5541193 : Nat := 4983230072969 + 3 ^ 40 * 5541193 * 2
def baseEnd_5541193 : Nat := 2845295408329243790604023

theorem tailTrace_5541193 : CollatzResearch.WordTrace tailWord_5541193 prefixEnd_5541193 2845295408329243790604023 := by
  unfold tailWord_5541193
  simp only [CollatzResearch.WordTrace]
  refine ⟨202103912214211596265908233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134735941476141064177272155 202103912214211596265908233)
  ·
    refine ⟨151577934160658697199431175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202103912214211596265908233 151577934160658697199431175)
    ·
      refine ⟨227366901240988045799146763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151577934160658697199431175 227366901240988045799146763)
      ·
        refine ⟨341050351861482068698720145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227366901240988045799146763 341050351861482068698720145)
        ·
          refine ⟨255787763896111551524040109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341050351861482068698720145 255787763896111551524040109)
          ·
            refine ⟨95920411461041831821515041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255787763896111551524040109 95920411461041831821515041)
            ·
              refine ⟨71940308595781373866136281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95920411461041831821515041 71940308595781373866136281)
              ·
                refine ⟨53955231446836030399602211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71940308595781373866136281 53955231446836030399602211)
                ·
                  refine ⟨80932847170254045599403317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53955231446836030399602211 80932847170254045599403317)
                  ·
                    refine ⟨7587454422211316774944061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80932847170254045599403317 7587454422211316774944061)
                    ·
                      refine ⟨2845295408329243790604023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7587454422211316774944061 2845295408329243790604023)
                      ·
                        rfl

theorem cell23_5541193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_5541193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541193 prefixEnd_5541193 := by exact prefixLift 5541193
  have htrace : WordTrace (prefixWord ++ tailWord_5541193) baseStart_5541193 baseEnd_5541193 := by
    simpa [prefixWord, tailWord_5541193, baseEnd_5541193] using wordTrace_append hprefix tailTrace_5541193
  have hstable : (prefixWord ++ tailWord_5541193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541193).length < 2 ^ (prefixWord ++ tailWord_5541193).sum := by decide
  have hdescent : baseEnd_5541193 < baseStart_5541193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541233 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_5541233 : Nat := 118140960795 + 5541233 * 2 ^ 59
def prefixEnd_5541233 : Nat := 4983230072969 + 3 ^ 40 * 5541233 * 2
def baseEnd_5541233 : Nat := 2845315947555423634103839

theorem tailTrace_5541233 : CollatzResearch.WordTrace tailWord_5541233 prefixEnd_5541233 2845315947555423634103839 := by
  unfold tailWord_5541233
  simp only [CollatzResearch.WordTrace]
  refine ⟨202105371134066683097364353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134736914089377788731576235 202105371134066683097364353)
  ·
    refine ⟨151579028350550012323023265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202105371134066683097364353 151579028350550012323023265)
    ·
      refine ⟨113684271262912509242267449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151579028350550012323023265 113684271262912509242267449)
      ·
        refine ⟨85263203447184381931700587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113684271262912509242267449 85263203447184381931700587)
        ·
          refine ⟨127894805170776572897550881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85263203447184381931700587 127894805170776572897550881)
          ·
            refine ⟨95921103878082429673163161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127894805170776572897550881 95921103878082429673163161)
            ·
              refine ⟨71940827908561822254872371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95921103878082429673163161 71940827908561822254872371)
              ·
                refine ⟨107911241862842733382308557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71940827908561822254872371 107911241862842733382308557)
                ·
                  refine ⟨40466715698566025018365709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107911241862842733382308557 40466715698566025018365709)
                  ·
                    refine ⟨15175018386962259381887141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40466715698566025018365709 15175018386962259381887141)
                    ·
                      refine ⟨2845315947555423634103839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15175018386962259381887141 2845315947555423634103839)
                      ·
                        rfl

theorem cell23_5541233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_5541233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541233 prefixEnd_5541233 := by exact prefixLift 5541233
  have htrace : WordTrace (prefixWord ++ tailWord_5541233) baseStart_5541233 baseEnd_5541233 := by
    simpa [prefixWord, tailWord_5541233, baseEnd_5541233] using wordTrace_append hprefix tailTrace_5541233
  have hstable : (prefixWord ++ tailWord_5541233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541233).length < 2 ^ (prefixWord ++ tailWord_5541233).sum := by decide
  have hdescent : baseEnd_5541233 < baseStart_5541233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541327 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 2, 3, 2]
def baseStart_5541327 : Nat := 118140960795 + 5541327 * 2 ^ 59
def prefixEnd_5541327 : Nat := 4983230072969 + 3 ^ 40 * 5541327 * 2
def baseEnd_5541327 : Nat := 2845364214736946266328407

theorem tailTrace_5541327 : CollatzResearch.WordTrace tailWord_5541327 prefixEnd_5541327 2845364214736946266328407 := by
  unfold tailWord_5541327
  simp only [CollatzResearch.WordTrace]
  refine ⟨202108799595726137151286235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134739199730484091434190823 202108799595726137151286235)
  ·
    refine ⟨303163199393589205726929353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202108799595726137151286235 303163199393589205726929353)
    ·
      refine ⟨227372399545191904295197015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303163199393589205726929353 227372399545191904295197015)
      ·
        refine ⟨341058599317787856442795523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227372399545191904295197015 341058599317787856442795523)
        ·
          refine ⟨511587898976681784664193285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341058599317787856442795523 511587898976681784664193285)
          ·
            refine ⟨95922731058127834624536241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 511587898976681784664193285 95922731058127834624536241)
            ·
              refine ⟨71942048293595875968402181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95922731058127834624536241 71942048293595875968402181)
              ·
                refine ⟨13489134055049226744075409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71942048293595875968402181 13489134055049226744075409)
                ·
                  refine ⟨10116850541286920058056557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13489134055049226744075409 10116850541286920058056557)
                  ·
                    refine ⟨3793818952982595021771209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10116850541286920058056557 3793818952982595021771209)
                    ·
                      refine ⟨2845364214736946266328407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793818952982595021771209 2845364214736946266328407)
                      ·
                        rfl

theorem cell23_5541327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3, 2].length) (baseStart_5541327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541327 prefixEnd_5541327 := by exact prefixLift 5541327
  have htrace : WordTrace (prefixWord ++ tailWord_5541327) baseStart_5541327 baseEnd_5541327 := by
    simpa [prefixWord, tailWord_5541327, baseEnd_5541327] using wordTrace_append hprefix tailTrace_5541327
  have hstable : (prefixWord ++ tailWord_5541327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541327).length < 2 ^ (prefixWord ++ tailWord_5541327).sum := by decide
  have hdescent : baseEnd_5541327 < baseStart_5541327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541354 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_5541354 : Nat := 118140960795 + 5541354 * 2 ^ 59
def prefixEnd_5541354 : Nat := 4983230072969 + 3 ^ 40 * 5541354 * 2
def baseEnd_5541354 : Nat := 948459359571539220230261

theorem tailTrace_5541354 : CollatzResearch.WordTrace tailWord_5541354 prefixEnd_5541354 948459359571539220230261 := by
  unfold tailWord_5541354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50527446091657080190629779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134739856244418880508346077 50527446091657080190629779)
  ·
    refine ⟨75791169137485620285944669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50527446091657080190629779 75791169137485620285944669)
    ·
      refine ⟨28421688426557107607229251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75791169137485620285944669 28421688426557107607229251)
      ·
        refine ⟨42632532639835661410843877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28421688426557107607229251 42632532639835661410843877)
        ·
          refine ⟨7993599869969186514533227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42632532639835661410843877 7993599869969186514533227)
          ·
            refine ⟨11990399804953779771799841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993599869969186514533227 11990399804953779771799841)
            ·
              refine ⟨8992799853715334828849881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11990399804953779771799841 8992799853715334828849881)
              ·
                refine ⟨6744599890286501121637411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992799853715334828849881 6744599890286501121637411)
                ·
                  refine ⟨10116899835429751682456117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744599890286501121637411 10116899835429751682456117)
                  ·
                    refine ⟨948459359571539220230261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10116899835429751682456117 948459359571539220230261)
                    ·
                      rfl

theorem cell23_5541354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_5541354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541354 prefixEnd_5541354 := by exact prefixLift 5541354
  have htrace : WordTrace (prefixWord ++ tailWord_5541354) baseStart_5541354 baseEnd_5541354 := by
    simpa [prefixWord, tailWord_5541354, baseEnd_5541354] using wordTrace_append hprefix tailTrace_5541354
  have hstable : (prefixWord ++ tailWord_5541354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541354).length < 2 ^ (prefixWord ++ tailWord_5541354).sum := by decide
  have hdescent : baseEnd_5541354 < baseStart_5541354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541370 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_5541370 : Nat := 118140960795 + 5541370 * 2 ^ 59
def prefixEnd_5541370 : Nat := 4983230072969 + 3 ^ 40 * 5541370 * 2
def baseEnd_5541370 : Nat := 2845386294405089598090709

theorem tailTrace_5541370 : CollatzResearch.WordTrace tailWord_5541370 prefixEnd_5541370 2845386294405089598090709 := by
  unfold tailWord_5541370
  simp only [CollatzResearch.WordTrace]
  refine ⟨50527591983642588873775391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134740245289713570330067709 50527591983642588873775391)
  ·
    refine ⟨75791387975463883310663087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50527591983642588873775391 75791387975463883310663087)
    ·
      refine ⟨113687081963195824965994631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75791387975463883310663087 113687081963195824965994631)
      ·
        refine ⟨170530622944793737448991947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113687081963195824965994631 170530622944793737448991947)
        ·
          refine ⟨255795934417190606173487921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170530622944793737448991947 255795934417190606173487921)
          ·
            refine ⟨191846950812892954630115941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255795934417190606173487921 191846950812892954630115941)
            ·
              refine ⟨35971303277417428993146739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191846950812892954630115941 35971303277417428993146739)
              ·
                refine ⟨53956954916126143489720109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35971303277417428993146739 53956954916126143489720109)
                ·
                  refine ⟨20233858093547303808645041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53956954916126143489720109 20233858093547303808645041)
                  ·
                    refine ⟨15175393570160477856483781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20233858093547303808645041 15175393570160477856483781)
                    ·
                      refine ⟨2845386294405089598090709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15175393570160477856483781 2845386294405089598090709)
                      ·
                        rfl

theorem cell23_5541370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_5541370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541370 prefixEnd_5541370 := by exact prefixLift 5541370
  have htrace : WordTrace (prefixWord ++ tailWord_5541370) baseStart_5541370 baseEnd_5541370 := by
    simpa [prefixWord, tailWord_5541370, baseEnd_5541370] using wordTrace_append hprefix tailTrace_5541370
  have hstable : (prefixWord ++ tailWord_5541370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541370).length < 2 ^ (prefixWord ++ tailWord_5541370).sum := by decide
  have hdescent : baseEnd_5541370 < baseStart_5541370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541411 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 3]
def baseStart_5541411 : Nat := 118140960795 + 5541411 * 2 ^ 59
def prefixEnd_5541411 : Nat := 4983230072969 + 3 ^ 40 * 5541411 * 2
def baseEnd_5541411 : Nat := 2845407347111923937678021

theorem tailTrace_5541411 : CollatzResearch.WordTrace tailWord_5541411 prefixEnd_5541411 2845407347111923937678021 := by
  unfold tailWord_5541411
  simp only [CollatzResearch.WordTrace]
  refine ⟨202111863327421819497344087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134741242218281212998229391 202111863327421819497344087)
  ·
    refine ⟨303167794991132729246016131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202111863327421819497344087 303167794991132729246016131)
    ·
      refine ⟨454751692486699093869024197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303167794991132729246016131 454751692486699093869024197)
      ·
        refine ⟨85265942341256080100442037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 454751692486699093869024197 85265942341256080100442037)
        ·
          refine ⟨7993682094492757509416441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85265942341256080100442037 7993682094492757509416441)
          ·
            refine ⟨5995261570869568132062331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7993682094492757509416441 5995261570869568132062331)
            ·
              refine ⟨8992892356304352198093497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995261570869568132062331 8992892356304352198093497)
              ·
                refine ⟨6744669267228264148570123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992892356304352198093497 6744669267228264148570123)
                ·
                  refine ⟨10117003900842396222855185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744669267228264148570123 10117003900842396222855185)
                  ·
                    refine ⟨7587752925631797167141389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10117003900842396222855185 7587752925631797167141389)
                    ·
                      refine ⟨2845407347111923937678021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7587752925631797167141389 2845407347111923937678021)
                      ·
                        rfl

theorem cell23_5541411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_5541411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541411 prefixEnd_5541411 := by exact prefixLift 5541411
  have htrace : WordTrace (prefixWord ++ tailWord_5541411) baseStart_5541411 baseEnd_5541411 := by
    simpa [prefixWord, tailWord_5541411, baseEnd_5541411] using wordTrace_append hprefix tailTrace_5541411
  have hstable : (prefixWord ++ tailWord_5541411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541411).length < 2 ^ (prefixWord ++ tailWord_5541411).sum := by decide
  have hdescent : baseEnd_5541411 < baseStart_5541411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541440 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_5541440 : Nat := 118140960795 + 5541440 * 2 ^ 59
def prefixEnd_5541440 : Nat := 4983230072969 + 3 ^ 40 * 5541440 * 2
def baseEnd_5541440 : Nat := 948474079350301441405129

theorem tailTrace_5541440 : CollatzResearch.WordTrace tailWord_5541440 prefixEnd_5541440 948474079350301441405129 := by
  unfold tailWord_5541440
  simp only [CollatzResearch.WordTrace]
  refine ⟨101056460522158378725074887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134741947362877838300099849 101056460522158378725074887)
  ·
    refine ⟨151584690783237568087612331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101056460522158378725074887 151584690783237568087612331)
    ·
      refine ⟨227377036174856352131418497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151584690783237568087612331 227377036174856352131418497)
      ·
        refine ⟨170532777131142264098563873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227377036174856352131418497 170532777131142264098563873)
        ·
          refine ⟨127899582848356698073922905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170532777131142264098563873 127899582848356698073922905)
          ·
            refine ⟨95924687136267523555442179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127899582848356698073922905 95924687136267523555442179)
            ·
              refine ⟨143887030704401285333163269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95924687136267523555442179 143887030704401285333163269)
              ·
                refine ⟨26978818257075240999968113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143887030704401285333163269 26978818257075240999968113)
                ·
                  refine ⟨20234113692806430749976085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26978818257075240999968113 20234113692806430749976085)
                  ·
                    refine ⟨948474079350301441405129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20234113692806430749976085 948474079350301441405129)
                    ·
                      rfl

theorem cell23_5541440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_5541440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541440 prefixEnd_5541440 := by exact prefixLift 5541440
  have htrace : WordTrace (prefixWord ++ tailWord_5541440) baseStart_5541440 baseEnd_5541440 := by
    simpa [prefixWord, tailWord_5541440, baseEnd_5541440] using wordTrace_append hprefix tailTrace_5541440
  have hstable : (prefixWord ++ tailWord_5541440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541440).length < 2 ^ (prefixWord ++ tailWord_5541440).sum := by decide
  have hdescent : baseEnd_5541440 < baseStart_5541440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541441 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5541441 : Nat := 118140960795 + 5541441 * 2 ^ 59
def prefixEnd_5541441 : Nat := 4983230072969 + 3 ^ 40 * 5541441 * 2
def baseEnd_5541441 : Nat := 2845422751531558820302883

theorem tailTrace_5541441 : CollatzResearch.WordTrace tailWord_5541441 prefixEnd_5541441 2845422751531558820302883 := by
  unfold tailWord_5541441
  simp only [CollatzResearch.WordTrace]
  refine ⟨202112957517313134620936177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134741971678208756413957451 202112957517313134620936177)
  ·
    refine ⟨151584718137984850965702133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202112957517313134620936177 151584718137984850965702133)
    ·
      refine ⟨14211067325436079778034575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151584718137984850965702133 14211067325436079778034575)
      ·
        refine ⟨21316600988154119667051863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14211067325436079778034575 21316600988154119667051863)
        ·
          refine ⟨31974901482231179500577795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21316600988154119667051863 31974901482231179500577795)
          ·
            refine ⟨47962352223346769250866693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31974901482231179500577795 47962352223346769250866693)
            ·
              refine ⟨8992941041877519234537505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47962352223346769250866693 8992941041877519234537505)
              ·
                refine ⟨6744705781408139425903129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992941041877519234537505 6744705781408139425903129)
                ·
                  refine ⟨5058529336056104569427347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6744705781408139425903129 5058529336056104569427347)
                  ·
                    refine ⟨7587794004084156854141021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058529336056104569427347 7587794004084156854141021)
                    ·
                      refine ⟨2845422751531558820302883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7587794004084156854141021 2845422751531558820302883)
                      ·
                        rfl

theorem cell23_5541441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5541441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541441 prefixEnd_5541441 := by exact prefixLift 5541441
  have htrace : WordTrace (prefixWord ++ tailWord_5541441) baseStart_5541441 baseEnd_5541441 := by
    simpa [prefixWord, tailWord_5541441, baseEnd_5541441] using wordTrace_append hprefix tailTrace_5541441
  have hstable : (prefixWord ++ tailWord_5541441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541441).length < 2 ^ (prefixWord ++ tailWord_5541441).sum := by decide
  have hdescent : baseEnd_5541441 < baseStart_5541441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541464 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_5541464 : Nat := 118140960795 + 5541464 * 2 ^ 59
def prefixEnd_5541464 : Nat := 4983230072969 + 3 ^ 40 * 5541464 * 2
def baseEnd_5541464 : Nat := 2845434561586612230315277

theorem tailTrace_5541464 : CollatzResearch.WordTrace tailWord_5541464 prefixEnd_5541464 2845434561586612230315277 := by
  unfold tailWord_5541464
  simp only [CollatzResearch.WordTrace]
  refine ⟨101056898198114904774511723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134742530930819873032682297 101056898198114904774511723)
  ·
    refine ⟨151585347297172357161767585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101056898198114904774511723 151585347297172357161767585)
    ·
      refine ⟨113689010472879267871325689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151585347297172357161767585 113689010472879267871325689)
      ·
        refine ⟨85266757854659450903494267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113689010472879267871325689 85266757854659450903494267)
        ·
          refine ⟨127900136781989176355241401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85266757854659450903494267 127900136781989176355241401)
          ·
            refine ⟨95925102586491882266431051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127900136781989176355241401 95925102586491882266431051)
            ·
              refine ⟨143887653879737823399646577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95925102586491882266431051 143887653879737823399646577)
              ·
                refine ⟨107915740409803367549734933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143887653879737823399646577 107915740409803367549734933)
                ·
                  refine ⟨5058550331709532853893825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107915740409803367549734933 5058550331709532853893825)
                  ·
                    refine ⟨3793912748782149640420369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5058550331709532853893825 3793912748782149640420369)
                    ·
                      refine ⟨2845434561586612230315277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793912748782149640420369 2845434561586612230315277)
                      ·
                        rfl

theorem cell23_5541464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_5541464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541464 prefixEnd_5541464 := by exact prefixLift 5541464
  have htrace : WordTrace (prefixWord ++ tailWord_5541464) baseStart_5541464 baseEnd_5541464 := by
    simpa [prefixWord, tailWord_5541464, baseEnd_5541464] using wordTrace_append hprefix tailTrace_5541464
  have hstable : (prefixWord ++ tailWord_5541464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541464).length < 2 ^ (prefixWord ++ tailWord_5541464).sum := by decide
  have hdescent : baseEnd_5541464 < baseStart_5541464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541485 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5541485 : Nat := 118140960795 + 5541485 * 2 ^ 59
def prefixEnd_5541485 : Nat := 4983230072969 + 3 ^ 40 * 5541485 * 2
def baseEnd_5541485 : Nat := 2845445344680356648152681

theorem tailTrace_5541485 : CollatzResearch.WordTrace tailWord_5541485 prefixEnd_5541485 2845445344680356648152681 := by
  unfold tailWord_5541485
  simp only [CollatzResearch.WordTrace]
  refine ⟨202114562329153730135537909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134743041552769153423691939 202114562329153730135537909)
  ·
    refine ⟨18948240218358162200206679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202114562329153730135537909 18948240218358162200206679)
    ·
      refine ⟨28422360327537243300310019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18948240218358162200206679 28422360327537243300310019)
      ·
        refine ⟨42633540491305864950465029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28422360327537243300310019 42633540491305864950465029)
        ·
          refine ⟨7993788842119849678212193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42633540491305864950465029 7993788842119849678212193)
          ·
            refine ⟨5995341631589887258659145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7993788842119849678212193 5995341631589887258659145)
            ·
              refine ⟨4496506223692415443994359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5995341631589887258659145 4496506223692415443994359)
              ·
                refine ⟨6744759335538623165991539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496506223692415443994359 6744759335538623165991539)
                ·
                  refine ⟨10117139003307934748987309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744759335538623165991539 10117139003307934748987309)
                  ·
                    refine ⟨3793927126240475530870241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10117139003307934748987309 3793927126240475530870241)
                    ·
                      refine ⟨2845445344680356648152681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793927126240475530870241 2845445344680356648152681)
                      ·
                        rfl

theorem cell23_5541485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5541485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541485 prefixEnd_5541485 := by exact prefixLift 5541485
  have htrace : WordTrace (prefixWord ++ tailWord_5541485) baseStart_5541485 baseEnd_5541485 := by
    simpa [prefixWord, tailWord_5541485, baseEnd_5541485] using wordTrace_append hprefix tailTrace_5541485
  have hstable : (prefixWord ++ tailWord_5541485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541485).length < 2 ^ (prefixWord ++ tailWord_5541485).sum := by decide
  have hdescent : baseEnd_5541485 < baseStart_5541485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541494 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5541494 : Nat := 118140960795 + 5541494 * 2 ^ 59
def prefixEnd_5541494 : Nat := 4983230072969 + 3 ^ 40 * 5541494 * 2
def baseEnd_5541494 : Nat := 2845449966006247112940139

theorem tailTrace_5541494 : CollatzResearch.WordTrace tailWord_5541494 prefixEnd_5541494 2845449966006247112940139 := by
  unfold tailWord_5541494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632180661632570292038471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134743260390747416448410357 12632180661632570292038471)
  ·
    refine ⟨18948270992448855438057707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12632180661632570292038471 18948270992448855438057707)
    ·
      refine ⟨28422406488673283157086561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18948270992448855438057707 28422406488673283157086561)
      ·
        refine ⟨21316804866504962367814921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28422406488673283157086561 21316804866504962367814921)
        ·
          refine ⟨15987603649878721775861191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21316804866504962367814921 15987603649878721775861191)
          ·
            refine ⟨23981405474818082663791787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15987603649878721775861191 23981405474818082663791787)
            ·
              refine ⟨35972108212227123995687681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23981405474818082663791787 35972108212227123995687681)
              ·
                refine ⟨26979081159170342996765761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35972108212227123995687681 26979081159170342996765761)
                ·
                  refine ⟨20234310869377757247574321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26979081159170342996765761 20234310869377757247574321)
                  ·
                    refine ⟨15175733152033317935680741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20234310869377757247574321 15175733152033317935680741)
                    ·
                      refine ⟨2845449966006247112940139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15175733152033317935680741 2845449966006247112940139)
                      ·
                        rfl

theorem cell23_5541494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5541494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541494 prefixEnd_5541494 := by exact prefixLift 5541494
  have htrace : WordTrace (prefixWord ++ tailWord_5541494) baseStart_5541494 baseEnd_5541494 := by
    simpa [prefixWord, tailWord_5541494, baseEnd_5541494] using wordTrace_append hprefix tailTrace_5541494
  have hstable : (prefixWord ++ tailWord_5541494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541494).length < 2 ^ (prefixWord ++ tailWord_5541494).sum := by decide
  have hdescent : baseEnd_5541494 < baseStart_5541494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541497 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_5541497 : Nat := 118140960795 + 5541497 * 2 ^ 59
def prefixEnd_5541497 : Nat := 4983230072969 + 3 ^ 40 * 5541497 * 2
def baseEnd_5541497 : Nat := 2845451506448210601202625

theorem tailTrace_5541497 : CollatzResearch.WordTrace tailWord_5541497 prefixEnd_5541497 2845451506448210601202625 := by
  unfold tailWord_5541497
  simp only [CollatzResearch.WordTrace]
  refine ⟨202115000005110256184974745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134743333336740170789983163 202115000005110256184974745)
  ·
    refine ⟨151586250003832692138731059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202115000005110256184974745 151586250003832692138731059)
    ·
      refine ⟨227379375005749038208096589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151586250003832692138731059 227379375005749038208096589)
      ·
        refine ⟨85267265627155889328036221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227379375005749038208096589 85267265627155889328036221)
        ·
          refine ⟨31975224610183458498013583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85267265627155889328036221 31975224610183458498013583)
          ·
            refine ⟨47962836915275187747020375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31975224610183458498013583 47962836915275187747020375)
            ·
              refine ⟨71944255372912781620530563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47962836915275187747020375 71944255372912781620530563)
              ·
                refine ⟨107916383059369172430795845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71944255372912781620530563 107916383059369172430795845)
                ·
                  refine ⟨20234321823631719830774221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107916383059369172430795845 20234321823631719830774221)
                  ·
                    refine ⟨7587870683861894936540333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20234321823631719830774221 7587870683861894936540333)
                    ·
                      refine ⟨2845451506448210601202625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7587870683861894936540333 2845451506448210601202625)
                      ·
                        rfl

theorem cell23_5541497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_5541497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541497 prefixEnd_5541497 := by exact prefixLift 5541497
  have htrace : WordTrace (prefixWord ++ tailWord_5541497) baseStart_5541497 baseEnd_5541497 := by
    simpa [prefixWord, tailWord_5541497, baseEnd_5541497] using wordTrace_append hprefix tailTrace_5541497
  have hstable : (prefixWord ++ tailWord_5541497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541497).length < 2 ^ (prefixWord ++ tailWord_5541497).sum := by decide
  have hdescent : baseEnd_5541497 < baseStart_5541497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541514 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_5541514 : Nat := 118140960795 + 5541514 * 2 ^ 59
def prefixEnd_5541514 : Nat := 4983230072969 + 3 ^ 40 * 5541514 * 2
def baseEnd_5541514 : Nat := 2845460235619337034690047

theorem tailTrace_5541514 : CollatzResearch.WordTrace tailWord_5541514 prefixEnd_5541514 2845460235619337034690047 := by
  unfold tailWord_5541514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50528905011512167022085899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134743746697365778725562397 50528905011512167022085899)
  ·
    refine ⟨75793357517268250533128849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50528905011512167022085899 75793357517268250533128849)
    ·
      refine ⟨56845018137951187899846637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75793357517268250533128849 56845018137951187899846637)
      ·
        refine ⟨21316881801731695462442489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56845018137951187899846637 21316881801731695462442489)
        ·
          refine ⟨15987661351298771596831867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21316881801731695462442489 15987661351298771596831867)
          ·
            refine ⟨23981492026948157395247801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15987661351298771596831867 23981492026948157395247801)
            ·
              refine ⟨17986119020211118046435851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23981492026948157395247801 17986119020211118046435851)
              ·
                refine ⟨26979178530316677069653777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17986119020211118046435851 26979178530316677069653777)
                ·
                  refine ⟨20234383897737507802240333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26979178530316677069653777 20234383897737507802240333)
                  ·
                    refine ⟨7587893961651565425840125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20234383897737507802240333 7587893961651565425840125)
                    ·
                      refine ⟨2845460235619337034690047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7587893961651565425840125 2845460235619337034690047)
                      ·
                        rfl

theorem cell23_5541514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_5541514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541514 prefixEnd_5541514 := by exact prefixLift 5541514
  have htrace : WordTrace (prefixWord ++ tailWord_5541514) baseStart_5541514 baseEnd_5541514 := by
    simpa [prefixWord, tailWord_5541514, baseEnd_5541514] using wordTrace_append hprefix tailTrace_5541514
  have hstable : (prefixWord ++ tailWord_5541514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541514).length < 2 ^ (prefixWord ++ tailWord_5541514).sum := by decide
  have hdescent : baseEnd_5541514 < baseStart_5541514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541534 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5541534 : Nat := 118140960795 + 5541534 * 2 ^ 59
def prefixEnd_5541534 : Nat := 4983230072969 + 3 ^ 40 * 5541534 * 2
def baseEnd_5541534 : Nat := 948490168410808985479985

theorem tailTrace_5541534 : CollatzResearch.WordTrace tailWord_5541534 prefixEnd_5541534 948490168410808985479985 := by
  unfold tailWord_5541534
  simp only [CollatzResearch.WordTrace]
  refine ⟨25264543688247026438008957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134744233003984141002714437 25264543688247026438008957)
  ·
    refine ⟨9474203883092634914253359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25264543688247026438008957 9474203883092634914253359)
    ·
      refine ⟨14211305824638952371380039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9474203883092634914253359 14211305824638952371380039)
      ·
        refine ⟨21316958736958428557070059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14211305824638952371380039 21316958736958428557070059)
        ·
          refine ⟨31975438105437642835605089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21316958736958428557070059 31975438105437642835605089)
          ·
            refine ⟨23981578579078232126703817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31975438105437642835605089 23981578579078232126703817)
            ·
              refine ⟨17986183934308674095027863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23981578579078232126703817 17986183934308674095027863)
              ·
                refine ⟨26979275901463011142541795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17986183934308674095027863 26979275901463011142541795)
                ·
                  refine ⟨40468913852194516713812693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26979275901463011142541795 40468913852194516713812693)
                  ·
                    refine ⟨948490168410808985479985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40468913852194516713812693 948490168410808985479985)
                    ·
                      rfl

theorem cell23_5541534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5541534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541534 prefixEnd_5541534 := by exact prefixLift 5541534
  have htrace : WordTrace (prefixWord ++ tailWord_5541534) baseStart_5541534 baseEnd_5541534 := by
    simpa [prefixWord, tailWord_5541534, baseEnd_5541534] using wordTrace_append hprefix tailTrace_5541534
  have hstable : (prefixWord ++ tailWord_5541534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541534).length < 2 ^ (prefixWord ++ tailWord_5541534).sum := by decide
  have hdescent : baseEnd_5541534 < baseStart_5541534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541554 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_5541554 : Nat := 118140960795 + 5541554 * 2 ^ 59
def prefixEnd_5541554 : Nat := 4983230072969 + 3 ^ 40 * 5541554 * 2
def baseEnd_5541554 : Nat := 2845480774845516878189863

theorem tailTrace_5541554 : CollatzResearch.WordTrace tailWord_5541554 prefixEnd_5541554 2845480774845516878189863 := by
  unfold tailWord_5541554
  simp only [CollatzResearch.WordTrace]
  refine ⟨50529269741475938729949929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134744719310602503279866477 50529269741475938729949929)
  ·
    refine ⟨37896952306106954047462447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50529269741475938729949929 37896952306106954047462447)
    ·
      refine ⟨56845428459160431071193671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37896952306106954047462447 56845428459160431071193671)
      ·
        refine ⟨85268142688740646606790507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56845428459160431071193671 85268142688740646606790507)
        ·
          refine ⟨127902214033110969910185761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85268142688740646606790507 127902214033110969910185761)
          ·
            refine ⟨95926660524833227432639321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127902214033110969910185761 95926660524833227432639321)
            ·
              refine ⟨71944995393624920574479491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95926660524833227432639321 71944995393624920574479491)
              ·
                refine ⟨107917493090437380861719237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71944995393624920574479491 107917493090437380861719237)
                ·
                  refine ⟨20234529954457008911572357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107917493090437380861719237 20234529954457008911572357)
                  ·
                    refine ⟨3793974366460689170919817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20234529954457008911572357 3793974366460689170919817)
                    ·
                      refine ⟨2845480774845516878189863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3793974366460689170919817 2845480774845516878189863)
                      ·
                        rfl

theorem cell23_5541554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_5541554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541554 prefixEnd_5541554 := by exact prefixLift 5541554
  have htrace : WordTrace (prefixWord ++ tailWord_5541554) baseStart_5541554 baseEnd_5541554 := by
    simpa [prefixWord, tailWord_5541554, baseEnd_5541554] using wordTrace_append hprefix tailTrace_5541554
  have hstable : (prefixWord ++ tailWord_5541554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541554).length < 2 ^ (prefixWord ++ tailWord_5541554).sum := by decide
  have hdescent : baseEnd_5541554 < baseStart_5541554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541634 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5541634 : Nat := 118140960795 + 5541634 * 2 ^ 59
def prefixEnd_5541634 : Nat := 4983230072969 + 3 ^ 40 * 5541634 * 2
def baseEnd_5541634 : Nat := 2845521853297876565189495

theorem tailTrace_5541634 : CollatzResearch.WordTrace tailWord_5541634 prefixEnd_5541634 2845521853297876565189495 := by
  unfold tailWord_5541634
  simp only [CollatzResearch.WordTrace]
  refine ⟨50529999201403482145677989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134746664537075952388474637 50529999201403482145677989)
  ·
    refine ⟨9474374850263152902314623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50529999201403482145677989 9474374850263152902314623)
    ·
      refine ⟨14211562275394729353471935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9474374850263152902314623 14211562275394729353471935)
      ·
        refine ⟨21317343413092094030207903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14211562275394729353471935 21317343413092094030207903)
        ·
          refine ⟨31976015119638141045311855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21317343413092094030207903 31976015119638141045311855)
          ·
            refine ⟨47964022679457211567967783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31976015119638141045311855 47964022679457211567967783)
            ·
              refine ⟨71946034019185817351951675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47964022679457211567967783 71946034019185817351951675)
              ·
                refine ⟨107919051028778726027927513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71946034019185817351951675 107919051028778726027927513)
                ·
                  refine ⟨80939288271584044520945635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107919051028778726027927513 80939288271584044520945635)
                  ·
                    refine ⟨121408932407376066781418453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80939288271584044520945635 121408932407376066781418453)
                    ·
                      refine ⟨2845521853297876565189495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121408932407376066781418453 2845521853297876565189495)
                      ·
                        rfl

theorem cell23_5541634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5541634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541634 prefixEnd_5541634 := by exact prefixLift 5541634
  have htrace : WordTrace (prefixWord ++ tailWord_5541634) baseStart_5541634 baseEnd_5541634 := by
    simpa [prefixWord, tailWord_5541634, baseEnd_5541634] using wordTrace_append hprefix tailTrace_5541634
  have hstable : (prefixWord ++ tailWord_5541634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541634).length < 2 ^ (prefixWord ++ tailWord_5541634).sum := by decide
  have hdescent : baseEnd_5541634 < baseStart_5541634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541644 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5541644 : Nat := 118140960795 + 5541644 * 2 ^ 59
def prefixEnd_5541644 : Nat := 4983230072969 + 3 ^ 40 * 5541644 * 2
def baseEnd_5541644 : Nat := 2845526988104421526064449

theorem tailTrace_5541644 : CollatzResearch.WordTrace tailWord_5541644 prefixEnd_5541644 2845526988104421526064449 := by
  unfold tailWord_5541644
  simp only [CollatzResearch.WordTrace]
  refine ⟨101060180767788850145287993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134746907690385133527050657 101060180767788850145287993)
  ·
    refine ⟨75795135575841637608965995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101060180767788850145287993 75795135575841637608965995)
    ·
      refine ⟨113692703363762456413448993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75795135575841637608965995 113692703363762456413448993)
      ·
        refine ⟨85269527522821842310086745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113692703363762456413448993 85269527522821842310086745)
        ·
          refine ⟨63952145642116381732565059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85269527522821842310086745 63952145642116381732565059)
          ·
            refine ⟨95928218463174572598847589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63952145642116381732565059 95928218463174572598847589)
            ·
              refine ⟨17986540961845232362283923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95928218463174572598847589 17986540961845232362283923)
              ·
                refine ⟨26979811442767848543425885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17986540961845232362283923 26979811442767848543425885)
                ·
                  refine ⟨10117429291037943203784707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26979811442767848543425885 10117429291037943203784707)
                  ·
                    refine ⟨15176143936556914805677061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10117429291037943203784707 15176143936556914805677061)
                    ·
                      refine ⟨2845526988104421526064449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15176143936556914805677061 2845526988104421526064449)
                      ·
                        rfl

theorem cell23_5541644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5541644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541644 prefixEnd_5541644 := by exact prefixLift 5541644
  have htrace : WordTrace (prefixWord ++ tailWord_5541644) baseStart_5541644 baseEnd_5541644 := by
    simpa [prefixWord, tailWord_5541644, baseEnd_5541644] using wordTrace_append hprefix tailTrace_5541644
  have hstable : (prefixWord ++ tailWord_5541644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541644).length < 2 ^ (prefixWord ++ tailWord_5541644).sum := by decide
  have hdescent : baseEnd_5541644 < baseStart_5541644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_5541647 : Nat := 118140960795 + 5541647 * 2 ^ 59
def prefixEnd_5541647 : Nat := 4983230072969 + 3 ^ 40 * 5541647 * 2
def baseEnd_5541647 : Nat := 2845528528546385014326935

theorem tailTrace_5541647 : CollatzResearch.WordTrace tailWord_5541647 prefixEnd_5541647 2845528528546385014326935 := by
  unfold tailWord_5541647
  simp only [CollatzResearch.WordTrace]
  refine ⟨202120470954566831802935195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134746980636377887868623463 202120470954566831802935195)
  ·
    refine ⟨303180706431850247704402793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202120470954566831802935195 303180706431850247704402793)
    ·
      refine ⟨227385529823887685778302095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303180706431850247704402793 227385529823887685778302095)
      ·
        refine ⟨341078294735831528667453143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227385529823887685778302095 341078294735831528667453143)
        ·
          refine ⟨511617442103747293001179715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341078294735831528667453143 511617442103747293001179715)
          ·
            refine ⟨767426163155620939501769573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511617442103747293001179715 767426163155620939501769573)
            ·
              refine ⟨143892405591678926156581795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 767426163155620939501769573 143892405591678926156581795)
              ·
                refine ⟨215838608387518389234872693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143892405591678926156581795 215838608387518389234872693)
                ·
                  refine ⟨20234869536329848990769315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215838608387518389234872693 20234869536329848990769315)
                  ·
                    refine ⟨30352304304494773486153973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20234869536329848990769315 30352304304494773486153973)
                    ·
                      refine ⟨2845528528546385014326935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30352304304494773486153973 2845528528546385014326935)
                      ·
                        rfl

theorem cell23_5541647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_5541647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541647 prefixEnd_5541647 := by exact prefixLift 5541647
  have htrace : WordTrace (prefixWord ++ tailWord_5541647) baseStart_5541647 baseEnd_5541647 := by
    simpa [prefixWord, tailWord_5541647, baseEnd_5541647] using wordTrace_append hprefix tailTrace_5541647
  have hstable : (prefixWord ++ tailWord_5541647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541647).length < 2 ^ (prefixWord ++ tailWord_5541647).sum := by decide
  have hdescent : baseEnd_5541647 < baseStart_5541647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541655 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 1, 1, 3]
def baseStart_5541655 : Nat := 118140960795 + 5541655 * 2 ^ 59
def prefixEnd_5541655 : Nat := 4983230072969 + 3 ^ 40 * 5541655 * 2
def baseEnd_5541655 : Nat := 2845532636391620983026899

theorem tailTrace_5541655 : CollatzResearch.WordTrace tailWord_5541655 prefixEnd_5541655 2845532636391620983026899 := by
  unfold tailWord_5541655
  simp only [CollatzResearch.WordTrace]
  refine ⟨202120762738537849169226419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134747175159025232779484279 202120762738537849169226419)
  ·
    refine ⟨303181144107806773753839629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202120762738537849169226419 303181144107806773753839629)
    ·
      refine ⟨113692929040427540157689861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303181144107806773753839629 113692929040427540157689861)
      ·
        refine ⟨21317424195080163779566849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113692929040427540157689861 21317424195080163779566849)
        ·
          refine ⟨15988068146310122834675137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21317424195080163779566849 15988068146310122834675137)
          ·
            refine ⟨11991051109732592126006353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15988068146310122834675137 11991051109732592126006353)
            ·
              refine ⟨8993288332299444094504765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11991051109732592126006353 8993288332299444094504765)
              ·
                refine ⟨3372483124612291535439287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8993288332299444094504765 3372483124612291535439287)
                ·
                  refine ⟨5058724686918437303158931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372483124612291535439287 5058724686918437303158931)
                  ·
                    refine ⟨7588087030377655954738397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5058724686918437303158931 7588087030377655954738397)
                    ·
                      refine ⟨2845532636391620983026899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7588087030377655954738397 2845532636391620983026899)
                      ·
                        rfl

theorem cell23_5541655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_5541655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541655 prefixEnd_5541655 := by exact prefixLift 5541655
  have htrace : WordTrace (prefixWord ++ tailWord_5541655) baseStart_5541655 baseEnd_5541655 := by
    simpa [prefixWord, tailWord_5541655, baseEnd_5541655] using wordTrace_append hprefix tailTrace_5541655
  have hstable : (prefixWord ++ tailWord_5541655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541655).length < 2 ^ (prefixWord ++ tailWord_5541655).sum := by decide
  have hdescent : baseEnd_5541655 < baseStart_5541655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541657 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_5541657 : Nat := 118140960795 + 5541657 * 2 ^ 59
def prefixEnd_5541657 : Nat := 4983230072969 + 3 ^ 40 * 5541657 * 2
def baseEnd_5541657 : Nat := 2845533663352929975201889

theorem tailTrace_5541657 : CollatzResearch.WordTrace tailWord_5541657 prefixEnd_5541657 2845533663352929975201889 := by
  unfold tailWord_5541657
  simp only [CollatzResearch.WordTrace]
  refine ⟨202120835684530603510799225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134747223789687069007199483 202120835684530603510799225)
  ·
    refine ⟨151590626763397952633099419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202120835684530603510799225 151590626763397952633099419)
    ·
      refine ⟨227385940145096928949649129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151590626763397952633099419 227385940145096928949649129)
      ·
        refine ⟨170539455108822696712236847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227385940145096928949649129 170539455108822696712236847)
        ·
          refine ⟨255809182663234045068355271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170539455108822696712236847 255809182663234045068355271)
          ·
            refine ⟨383713773994851067602532907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255809182663234045068355271 383713773994851067602532907)
            ·
              refine ⟨575570660992276601403799361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383713773994851067602532907 575570660992276601403799361)
              ·
                refine ⟨431677995744207451052849521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575570660992276601403799361 431677995744207451052849521)
                ·
                  refine ⟨323758496808155588289637141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431677995744207451052849521 323758496808155588289637141)
                  ·
                    refine ⟨15176179537882293201076741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 323758496808155588289637141 15176179537882293201076741)
                    ·
                      refine ⟨2845533663352929975201889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15176179537882293201076741 2845533663352929975201889)
                      ·
                        rfl

theorem cell23_5541657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_5541657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541657 prefixEnd_5541657 := by exact prefixLift 5541657
  have htrace : WordTrace (prefixWord ++ tailWord_5541657) baseStart_5541657 baseEnd_5541657 := by
    simpa [prefixWord, tailWord_5541657, baseEnd_5541657] using wordTrace_append hprefix tailTrace_5541657
  have hstable : (prefixWord ++ tailWord_5541657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541657).length < 2 ^ (prefixWord ++ tailWord_5541657).sum := by decide
  have hdescent : baseEnd_5541657 < baseStart_5541657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541658 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_5541658 : Nat := 118140960795 + 5541658 * 2 ^ 59
def prefixEnd_5541658 : Nat := 4983230072969 + 3 ^ 40 * 5541658 * 2
def baseEnd_5541658 : Nat := 948511392277861490429795

theorem tailTrace_5541658 : CollatzResearch.WordTrace tailWord_5541658 prefixEnd_5541658 948511392277861490429795 := by
  unfold tailWord_5541658
  simp only [CollatzResearch.WordTrace]
  refine ⟨50530218039381745170396407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134747248105017987121057085 50530218039381745170396407)
  ·
    refine ⟨75795327059072617755594611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50530218039381745170396407 75795327059072617755594611)
    ·
      refine ⟨113692990588608926633391917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75795327059072617755594611 113692990588608926633391917)
      ·
        refine ⟨42634871470728347487521969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113692990588608926633391917 42634871470728347487521969)
        ·
          refine ⟨31976153603046260615641477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42634871470728347487521969 31976153603046260615641477)
          ·
            refine ⟨5995528800571173865432777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31976153603046260615641477 5995528800571173865432777)
            ·
              refine ⟨4496646600428380399074583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5995528800571173865432777 4496646600428380399074583)
              ·
                refine ⟨6744969900642570598611875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496646600428380399074583 6744969900642570598611875)
                ·
                  refine ⟨10117454850963855897917813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744969900642570598611875 10117454850963855897917813)
                  ·
                    refine ⟨948511392277861490429795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10117454850963855897917813 948511392277861490429795)
                    ·
                      rfl

theorem cell23_5541658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_5541658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541658 prefixEnd_5541658 := by exact prefixLift 5541658
  have htrace : WordTrace (prefixWord ++ tailWord_5541658) baseStart_5541658 baseEnd_5541658 := by
    simpa [prefixWord, tailWord_5541658, baseEnd_5541658] using wordTrace_append hprefix tailTrace_5541658
  have hstable : (prefixWord ++ tailWord_5541658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541658).length < 2 ^ (prefixWord ++ tailWord_5541658).sum := by decide
  have hdescent : baseEnd_5541658 < baseStart_5541658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541662 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_5541662 : Nat := 118140960795 + 5541662 * 2 ^ 59
def prefixEnd_5541662 : Nat := 4983230072969 + 3 ^ 40 * 5541662 * 2
def baseEnd_5541662 : Nat := 316170692306244717293263

theorem tailTrace_5541662 : CollatzResearch.WordTrace tailWord_5541662 prefixEnd_5541662 316170692306244717293263 := by
  unfold tailWord_5541662
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265127256189061170591405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134747345366341659576487493 25265127256189061170591405)
  ·
    refine ⟨9474422721070897938971777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25265127256189061170591405 9474422721070897938971777)
    ·
      refine ⟨7105817040803173454228833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9474422721070897938971777 7105817040803173454228833)
      ·
        refine ⟨5329362780602380090671625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105817040803173454228833 5329362780602380090671625)
        ·
          refine ⟨3997022085451785068003719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5329362780602380090671625 3997022085451785068003719)
          ·
            refine ⟨5995533128177677602005579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997022085451785068003719 5995533128177677602005579)
            ·
              refine ⟨8993299692266516403008369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995533128177677602005579 8993299692266516403008369)
              ·
                refine ⟨6744974769199887302256277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8993299692266516403008369 6744974769199887302256277)
                ·
                  refine ⟨316170692306244717293263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6744974769199887302256277 316170692306244717293263)
                  ·
                    rfl

theorem cell23_5541662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_5541662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541662 prefixEnd_5541662 := by exact prefixLift 5541662
  have htrace : WordTrace (prefixWord ++ tailWord_5541662) baseStart_5541662 baseEnd_5541662 := by
    simpa [prefixWord, tailWord_5541662, baseEnd_5541662] using wordTrace_append hprefix tailTrace_5541662
  have hstable : (prefixWord ++ tailWord_5541662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541662).length < 2 ^ (prefixWord ++ tailWord_5541662).sum := by decide
  have hdescent : baseEnd_5541662 < baseStart_5541662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541664 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5541664 : Nat := 118140960795 + 5541664 * 2 ^ 59
def prefixEnd_5541664 : Nat := 4983230072969 + 3 ^ 40 * 5541664 * 2
def baseEnd_5541664 : Nat := 2845537257717511447814357

theorem tailTrace_5541664 : CollatzResearch.WordTrace tailWord_5541664 prefixEnd_5541664 2845537257717511447814357 := by
  unfold tailWord_5541664
  simp only [CollatzResearch.WordTrace]
  refine ⟨101060545497752621853152023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134747393997003495804202697 101060545497752621853152023)
  ·
    refine ⟨151590818246628932779728035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101060545497752621853152023 151590818246628932779728035)
    ·
      refine ⟨227386227369943399169592053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151590818246628932779728035 227386227369943399169592053)
      ·
        refine ⟨21317458815932193672149255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227386227369943399169592053 21317458815932193672149255)
        ·
          refine ⟨31976188223898290508223883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21317458815932193672149255 31976188223898290508223883)
          ·
            refine ⟨47964282335847435762335825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31976188223898290508223883 47964282335847435762335825)
            ·
              refine ⟨35973211751885576821751869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47964282335847435762335825 35973211751885576821751869)
              ·
                refine ⟨13489954406957091308156951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35973211751885576821751869 13489954406957091308156951)
                ·
                  refine ⟨20234931610435636962235427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13489954406957091308156951 20234931610435636962235427)
                  ·
                    refine ⟨30352397415653455443353141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20234931610435636962235427 30352397415653455443353141)
                    ·
                      refine ⟨2845537257717511447814357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30352397415653455443353141 2845537257717511447814357)
                      ·
                        rfl

theorem cell23_5541664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5541664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541664 prefixEnd_5541664 := by exact prefixLift 5541664
  have htrace : WordTrace (prefixWord ++ tailWord_5541664) baseStart_5541664 baseEnd_5541664 := by
    simpa [prefixWord, tailWord_5541664, baseEnd_5541664] using wordTrace_append hprefix tailTrace_5541664
  have hstable : (prefixWord ++ tailWord_5541664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541664).length < 2 ^ (prefixWord ++ tailWord_5541664).sum := by decide
  have hdescent : baseEnd_5541664 < baseStart_5541664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_5541687 : Nat := 118140960795 + 5541687 * 2 ^ 59
def prefixEnd_5541687 : Nat := 4983230072969 + 3 ^ 40 * 5541687 * 2
def baseEnd_5541687 : Nat := 2845549067772564857826751

theorem tailTrace_5541687 : CollatzResearch.WordTrace tailWord_5541687 prefixEnd_5541687 2845549067772564857826751 := by
  unfold tailWord_5541687
  simp only [CollatzResearch.WordTrace]
  refine ⟨202121929874421918634391315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134747953249614612422927543 202121929874421918634391315)
  ·
    refine ⟨303182894811632877951586973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202121929874421918634391315 303182894811632877951586973)
    ·
      refine ⟨113693585554362329231845115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303182894811632877951586973 113693585554362329231845115)
      ·
        refine ⟨170540378331543493847767673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113693585554362329231845115 170540378331543493847767673)
        ·
          refine ⟨127905283748657620385825755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170540378331543493847767673 127905283748657620385825755)
          ·
            refine ⟨191857925622986430578738633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127905283748657620385825755 191857925622986430578738633)
            ·
              refine ⟨143893444217239822934053975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191857925622986430578738633 143893444217239822934053975)
              ·
                refine ⟨215840166325859734401080963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143893444217239822934053975 215840166325859734401080963)
                ·
                  refine ⟨323760249488789601601621445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215840166325859734401080963 323760249488789601601621445)
                  ·
                    refine ⟨60705046779148050300304021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 323760249488789601601621445 60705046779148050300304021)
                    ·
                      refine ⟨2845549067772564857826751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60705046779148050300304021 2845549067772564857826751)
                      ·
                        rfl

theorem cell23_5541687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_5541687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541687 prefixEnd_5541687 := by exact prefixLift 5541687
  have htrace : WordTrace (prefixWord ++ tailWord_5541687) baseStart_5541687 baseEnd_5541687 := by
    simpa [prefixWord, tailWord_5541687, baseEnd_5541687] using wordTrace_append hprefix tailTrace_5541687
  have hstable : (prefixWord ++ tailWord_5541687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541687).length < 2 ^ (prefixWord ++ tailWord_5541687).sum := by decide
  have hdescent : baseEnd_5541687 < baseStart_5541687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541688 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 2, 4]
def baseStart_5541688 : Nat := 118140960795 + 5541688 * 2 ^ 59
def prefixEnd_5541688 : Nat := 4983230072969 + 3 ^ 40 * 5541688 * 2
def baseEnd_5541688 : Nat := 948516527084406451304749

theorem tailTrace_5541688 : CollatzResearch.WordTrace tailWord_5541688 prefixEnd_5541688 948516527084406451304749 := by
  unfold tailWord_5541688
  simp only [CollatzResearch.WordTrace]
  refine ⟨101060983173709147902588859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134747977564945530536785145 101060983173709147902588859)
  ·
    refine ⟨151591474760563721853883289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101060983173709147902588859 151591474760563721853883289)
    ·
      refine ⟨113693606070422791390412467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151591474760563721853883289 113693606070422791390412467)
      ·
        refine ⟨170540409105634187085618701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113693606070422791390412467 170540409105634187085618701)
        ·
          refine ⟨63952653414612820157107013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170540409105634187085618701 63952653414612820157107013)
          ·
            refine ⟨11991122515239903779457565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63952653414612820157107013 11991122515239903779457565)
            ·
              refine ⟨4496670943214963917296587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11991122515239903779457565 4496670943214963917296587)
              ·
                refine ⟨6745006414822445875944881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496670943214963917296587 6745006414822445875944881)
                ·
                  refine ⟨5058754811116834406958661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6745006414822445875944881 5058754811116834406958661)
                  ·
                    refine ⟨948516527084406451304749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5058754811116834406958661 948516527084406451304749)
                    ·
                      rfl

theorem cell23_5541688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_5541688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541688 prefixEnd_5541688 := by exact prefixLift 5541688
  have htrace : WordTrace (prefixWord ++ tailWord_5541688) baseStart_5541688 baseEnd_5541688 := by
    simpa [prefixWord, tailWord_5541688, baseEnd_5541688] using wordTrace_append hprefix tailTrace_5541688
  have hstable : (prefixWord ++ tailWord_5541688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541688).length < 2 ^ (prefixWord ++ tailWord_5541688).sum := by decide
  have hdescent : baseEnd_5541688 < baseStart_5541688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541754 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_5541754 : Nat := 118140960795 + 5541754 * 2 ^ 59
def prefixEnd_5541754 : Nat := 4983230072969 + 3 ^ 40 * 5541754 * 2
def baseEnd_5541754 : Nat := 2845583470976416095688943

theorem tailTrace_5541754 : CollatzResearch.WordTrace tailWord_5541754 prefixEnd_5541754 2845583470976416095688943 := by
  unfold tailWord_5541754
  simp only [CollatzResearch.WordTrace]
  refine ⟨50531093391294797269270079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134749582376786126051386877 50531093391294797269270079)
  ·
    refine ⟨75796640086942195903905119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50531093391294797269270079 75796640086942195903905119)
    ·
      refine ⟨113694960130413293855857679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75796640086942195903905119 113694960130413293855857679)
      ·
        refine ⟨170542440195619940783786519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113694960130413293855857679 170542440195619940783786519)
        ·
          refine ⟨255813660293429911175679779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170542440195619940783786519 255813660293429911175679779)
          ·
            refine ⟨383720490440144866763519669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255813660293429911175679779 383720490440144866763519669)
            ·
              refine ⟨35973795978763581259079969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383720490440144866763519669 35973795978763581259079969)
              ·
                refine ⟨26980346984072685944309977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35973795978763581259079969 26980346984072685944309977)
                ·
                  refine ⟨20235260238054514458232483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26980346984072685944309977 20235260238054514458232483)
                  ·
                    refine ⟨30352890357081771687348725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20235260238054514458232483 30352890357081771687348725)
                    ·
                      refine ⟨2845583470976416095688943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30352890357081771687348725 2845583470976416095688943)
                      ·
                        rfl

theorem cell23_5541754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_5541754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541754 prefixEnd_5541754 := by exact prefixLift 5541754
  have htrace : WordTrace (prefixWord ++ tailWord_5541754) baseStart_5541754 baseEnd_5541754 := by
    simpa [prefixWord, tailWord_5541754, baseEnd_5541754] using wordTrace_append hprefix tailTrace_5541754
  have hstable : (prefixWord ++ tailWord_5541754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541754).length < 2 ^ (prefixWord ++ tailWord_5541754).sum := by decide
  have hdescent : baseEnd_5541754 < baseStart_5541754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541811 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 5, 2]
def baseStart_5541811 : Nat := 118140960795 + 5541811 * 2 ^ 59
def prefixEnd_5541811 : Nat := 4983230072969 + 3 ^ 40 * 5541811 * 2
def baseEnd_5541811 : Nat := 2845612739373722372676181

theorem tailTrace_5541811 : CollatzResearch.WordTrace tailWord_5541811 prefixEnd_5541811 2845612739373722372676181 := by
  unfold tailWord_5541811
  simp only [CollatzResearch.WordTrace]
  refine ⟨202126452525972687811905287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134750968350648458541270191 202126452525972687811905287)
  ·
    refine ⟨303189678788959031717857931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202126452525972687811905287 303189678788959031717857931)
    ·
      refine ⟨454784518183438547576786897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303189678788959031717857931 454784518183438547576786897)
      ·
        refine ⟨341088388637578910682590173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454784518183438547576786897 341088388637578910682590173)
        ·
          refine ⟨127908145739092091505971315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341088388637578910682590173 127908145739092091505971315)
          ·
            refine ⟨191862218608638137258956973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127908145739092091505971315 191862218608638137258956973)
            ·
              refine ⟨71948331978239301472108865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191862218608638137258956973 71948331978239301472108865)
              ·
                refine ⟨53961248983679476104081649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71948331978239301472108865 53961248983679476104081649)
                ·
                  refine ⟨40470936737759607078061237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53961248983679476104081649 40470936737759607078061237)
                  ·
                    refine ⟨3794150319164963163568241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40470936737759607078061237 3794150319164963163568241)
                    ·
                      refine ⟨2845612739373722372676181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794150319164963163568241 2845612739373722372676181)
                      ·
                        rfl

theorem cell23_5541811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5, 2].length) (baseStart_5541811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541811 prefixEnd_5541811 := by exact prefixLift 5541811
  have htrace : WordTrace (prefixWord ++ tailWord_5541811) baseStart_5541811 baseEnd_5541811 := by
    simpa [prefixWord, tailWord_5541811, baseEnd_5541811] using wordTrace_append hprefix tailTrace_5541811
  have hstable : (prefixWord ++ tailWord_5541811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541811).length < 2 ^ (prefixWord ++ tailWord_5541811).sum := by decide
  have hdescent : baseEnd_5541811 < baseStart_5541811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541821 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_5541821 : Nat := 118140960795 + 5541821 * 2 ^ 59
def prefixEnd_5541821 : Nat := 4983230072969 + 3 ^ 40 * 5541821 * 2
def baseEnd_5541821 : Nat := 948539291393422444517045

theorem tailTrace_5541821 : CollatzResearch.WordTrace tailWord_5541821 prefixEnd_5541821 948539291393422444517045 := by
  unfold tailWord_5541821
  simp only [CollatzResearch.WordTrace]
  refine ⟨202126817255936459519769317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134751211503957639679846211 202126817255936459519769317)
  ·
    refine ⟨37898778235488086159956747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202126817255936459519769317 37898778235488086159956747)
    ·
      refine ⟨56848167353232129239935121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37898778235488086159956747 56848167353232129239935121)
      ·
        refine ⟨42636125514924096929951341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56848167353232129239935121 42636125514924096929951341)
        ·
          refine ⟨15988547068096536348731753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42636125514924096929951341 15988547068096536348731753)
          ·
            refine ⟨11991410301072402261548815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15988547068096536348731753 11991410301072402261548815)
            ·
              refine ⟨17987115451608603392323223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11991410301072402261548815 17987115451608603392323223)
              ·
                refine ⟨26980673177412905088484835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17987115451608603392323223 26980673177412905088484835)
                ·
                  refine ⟨40471009766119357632727253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26980673177412905088484835 40471009766119357632727253)
                  ·
                    refine ⟨948539291393422444517045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40471009766119357632727253 948539291393422444517045)
                    ·
                      rfl

theorem cell23_5541821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_5541821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541821 prefixEnd_5541821 := by exact prefixLift 5541821
  have htrace : WordTrace (prefixWord ++ tailWord_5541821) baseStart_5541821 baseEnd_5541821 := by
    simpa [prefixWord, tailWord_5541821, baseEnd_5541821] using wordTrace_append hprefix tailTrace_5541821
  have hstable : (prefixWord ++ tailWord_5541821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541821).length < 2 ^ (prefixWord ++ tailWord_5541821).sum := by decide
  have hdescent : baseEnd_5541821 < baseStart_5541821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541885 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_5541885 : Nat := 118140960795 + 5541885 * 2 ^ 59
def prefixEnd_5541885 : Nat := 4983230072969 + 3 ^ 40 * 5541885 * 2
def baseEnd_5541885 : Nat := 948550245647385027716947

theorem tailTrace_5541885 : CollatzResearch.WordTrace tailWord_5541885 prefixEnd_5541885 948550245647385027716947 := by
  unfold tailWord_5541885
  simp only [CollatzResearch.WordTrace]
  refine ⟨202129151527704598450099109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134752767685136398966732739 202129151527704598450099109)
  ·
    refine ⟨37899215911444612209393583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202129151527704598450099109 37899215911444612209393583)
    ·
      refine ⟨56848823867166918314090375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37899215911444612209393583 56848823867166918314090375)
      ·
        refine ⟨85273235800750377471135563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56848823867166918314090375 85273235800750377471135563)
        ·
          refine ⟨127909853701125566206703345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85273235800750377471135563 127909853701125566206703345)
          ·
            refine ⟨95932390275844174655027509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127909853701125566206703345 95932390275844174655027509)
            ·
              refine ⟨8993661588360391373908829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95932390275844174655027509 8993661588360391373908829)
              ·
                refine ⟨3372623095635146765215811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8993661588360391373908829 3372623095635146765215811)
                ·
                  refine ⟨5058934643452720147823717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372623095635146765215811 5058934643452720147823717)
                  ·
                    refine ⟨948550245647385027716947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5058934643452720147823717 948550245647385027716947)
                    ·
                      rfl

theorem cell23_5541885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_5541885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541885 prefixEnd_5541885 := by exact prefixLift 5541885
  have htrace : WordTrace (prefixWord ++ tailWord_5541885) baseStart_5541885 baseEnd_5541885 := by
    simpa [prefixWord, tailWord_5541885, baseEnd_5541885] using wordTrace_append hprefix tailTrace_5541885
  have hstable : (prefixWord ++ tailWord_5541885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541885).length < 2 ^ (prefixWord ++ tailWord_5541885).sum := by decide
  have hdescent : baseEnd_5541885 < baseStart_5541885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541902 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_5541902 : Nat := 118140960795 + 5541902 * 2 ^ 59
def prefixEnd_5541902 : Nat := 4983230072969 + 3 ^ 40 * 5541902 * 2
def baseEnd_5541902 : Nat := 948553155371093838879421

theorem tailTrace_5541902 : CollatzResearch.WordTrace tailWord_5541902 prefixEnd_5541902 948553155371093838879421 := by
  unfold tailWord_5541902
  simp only [CollatzResearch.WordTrace]
  refine ⟨25266221446080376294183495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134753181045762006902311973 25266221446080376294183495)
  ·
    refine ⟨37899332169120564441275243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25266221446080376294183495 37899332169120564441275243)
    ·
      refine ⟨56848998253680846661912865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37899332169120564441275243 56848998253680846661912865)
      ·
        refine ⟨42636748690260634996434649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56848998253680846661912865 42636748690260634996434649)
        ·
          refine ⟨31977561517695476247325987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42636748690260634996434649 31977561517695476247325987)
          ·
            refine ⟨47966342276543214370988981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31977561517695476247325987 47966342276543214370988981)
            ·
              refine ⟨4496844588425926347280217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47966342276543214370988981 4496844588425926347280217)
              ·
                refine ⟨3372633441319444760460163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4496844588425926347280217 3372633441319444760460163)
                ·
                  refine ⟨5058950161979167140690245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372633441319444760460163 5058950161979167140690245)
                  ·
                    refine ⟨948553155371093838879421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5058950161979167140690245 948553155371093838879421)
                    ·
                      rfl

theorem cell23_5541902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_5541902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541902 prefixEnd_5541902 := by exact prefixLift 5541902
  have htrace : WordTrace (prefixWord ++ tailWord_5541902) baseStart_5541902 baseEnd_5541902 := by
    simpa [prefixWord, tailWord_5541902, baseEnd_5541902] using wordTrace_append hprefix tailTrace_5541902
  have hstable : (prefixWord ++ tailWord_5541902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541902).length < 2 ^ (prefixWord ++ tailWord_5541902).sum := by decide
  have hdescent : baseEnd_5541902 < baseStart_5541902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541941 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5541941 : Nat := 118140960795 + 5541941 * 2 ^ 59
def prefixEnd_5541941 : Nat := 4983230072969 + 3 ^ 40 * 5541941 * 2
def baseEnd_5541941 : Nat := 948559830619602288016861

theorem tailTrace_5541941 : CollatzResearch.WordTrace tailWord_5541941 prefixEnd_5541941 948559830619602288016861 := by
  unfold tailWord_5541941
  simp only [CollatzResearch.WordTrace]
  refine ⟨202131194015501720014137677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134754129343667813342758451 202131194015501720014137677)
  ·
    refine ⟨75799197755813145005301629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202131194015501720014137677 75799197755813145005301629)
    ·
      refine ⟨28424699158429929376988111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75799197755813145005301629 28424699158429929376988111)
      ·
        refine ⟨42637048737644894065482167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28424699158429929376988111 42637048737644894065482167)
        ·
          refine ⟨63955573106467341098223251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42637048737644894065482167 63955573106467341098223251)
          ·
            refine ⟨95933359659701011647334877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63955573106467341098223251 95933359659701011647334877)
            ·
              refine ⟨35975009872387879367750579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95933359659701011647334877 35975009872387879367750579)
              ·
                refine ⟨53962514808581819051625869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35975009872387879367750579 53962514808581819051625869)
                ·
                  refine ⟨20235943053218182144359701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53962514808581819051625869 20235943053218182144359701)
                  ·
                    refine ⟨948559830619602288016861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20235943053218182144359701 948559830619602288016861)
                    ·
                      rfl

theorem cell23_5541941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5541941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541941 prefixEnd_5541941 := by exact prefixLift 5541941
  have htrace : WordTrace (prefixWord ++ tailWord_5541941) baseStart_5541941 baseEnd_5541941 := by
    simpa [prefixWord, tailWord_5541941, baseEnd_5541941] using wordTrace_append hprefix tailTrace_5541941
  have hstable : (prefixWord ++ tailWord_5541941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541941).length < 2 ^ (prefixWord ++ tailWord_5541941).sum := by decide
  have hdescent : baseEnd_5541941 < baseStart_5541941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541961 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_5541961 : Nat := 118140960795 + 5541961 * 2 ^ 59
def prefixEnd_5541961 : Nat := 4983230072969 + 3 ^ 40 * 5541961 * 2
def baseEnd_5541961 : Nat := 2845689761471896785800491

theorem tailTrace_5541961 : CollatzResearch.WordTrace tailWord_5541961 prefixEnd_5541961 2845689761471896785800491 := by
  unfold tailWord_5541961
  simp only [CollatzResearch.WordTrace]
  refine ⟨202131923475429263429865737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134754615650286175619910491 202131923475429263429865737)
  ·
    refine ⟨151598942606571947572399303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202131923475429263429865737 151598942606571947572399303)
    ·
      refine ⟨227398413909857921358598955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151598942606571947572399303 227398413909857921358598955)
      ·
        refine ⟨341097620864786882037898433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227398413909857921358598955 341097620864786882037898433)
        ·
          refine ⟨255823215648590161528423825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341097620864786882037898433 255823215648590161528423825)
          ·
            refine ⟨191867411736442621146317869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255823215648590161528423825 191867411736442621146317869)
            ·
              refine ⟨71950279401165982929869201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191867411736442621146317869 71950279401165982929869201)
              ·
                refine ⟨53962709550874487197401901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71950279401165982929869201 53962709550874487197401901)
                ·
                  refine ⟨20236016081577932699025713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53962709550874487197401901 20236016081577932699025713)
                  ·
                    refine ⟨15177012061183449524269285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20236016081577932699025713 15177012061183449524269285)
                    ·
                      refine ⟨2845689761471896785800491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15177012061183449524269285 2845689761471896785800491)
                      ·
                        rfl

theorem cell23_5541961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_5541961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541961 prefixEnd_5541961 := by exact prefixLift 5541961
  have htrace : WordTrace (prefixWord ++ tailWord_5541961) baseStart_5541961 baseEnd_5541961 := by
    simpa [prefixWord, tailWord_5541961, baseEnd_5541961] using wordTrace_append hprefix tailTrace_5541961
  have hstable : (prefixWord ++ tailWord_5541961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541961).length < 2 ^ (prefixWord ++ tailWord_5541961).sum := by decide
  have hdescent : baseEnd_5541961 < baseStart_5541961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541978 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_5541978 : Nat := 118140960795 + 5541978 * 2 ^ 59
def prefixEnd_5541978 : Nat := 4983230072969 + 3 ^ 40 * 5541978 * 2
def baseEnd_5541978 : Nat := 2845698490643023219287913

theorem tailTrace_5541978 : CollatzResearch.WordTrace tailWord_5541978 prefixEnd_5541978 2845698490643023219287913 := by
  unfold tailWord_5541978
  simp only [CollatzResearch.WordTrace]
  refine ⟨50533135879091918833308647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134755029010911783555489725 50533135879091918833308647)
  ·
    refine ⟨75799703818637878249962971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50533135879091918833308647 75799703818637878249962971)
    ·
      refine ⟨113699555727956817374944457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75799703818637878249962971 113699555727956817374944457)
      ·
        refine ⟨85274666795967613031208343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113699555727956817374944457 85274666795967613031208343)
        ·
          refine ⟨127912000193951419546812515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85274666795967613031208343 127912000193951419546812515)
          ·
            refine ⟨191868000290927129320218773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127912000193951419546812515 191868000290927129320218773)
            ·
              refine ⟨8993812513637209186885255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191868000290927129320218773 8993812513637209186885255)
              ·
                refine ⟨13490718770455813780327883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8993812513637209186885255 13490718770455813780327883)
                ·
                  refine ⟨20236078155683720670491825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13490718770455813780327883 20236078155683720670491825)
                  ·
                    refine ⟨15177058616762790502868869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20236078155683720670491825 15177058616762790502868869)
                    ·
                      refine ⟨2845698490643023219287913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15177058616762790502868869 2845698490643023219287913)
                      ·
                        rfl

theorem cell23_5541978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_5541978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541978 prefixEnd_5541978 := by exact prefixLift 5541978
  have htrace : WordTrace (prefixWord ++ tailWord_5541978) baseStart_5541978 baseEnd_5541978 := by
    simpa [prefixWord, tailWord_5541978, baseEnd_5541978] using wordTrace_append hprefix tailTrace_5541978
  have hstable : (prefixWord ++ tailWord_5541978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541978).length < 2 ^ (prefixWord ++ tailWord_5541978).sum := by decide
  have hdescent : baseEnd_5541978 < baseStart_5541978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541986 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5541986 : Nat := 118140960795 + 5541986 * 2 ^ 59
def prefixEnd_5541986 : Nat := 4983230072969 + 3 ^ 40 * 5541986 * 2
def baseEnd_5541986 : Nat := 2845702598488259187987877

theorem tailTrace_5541986 : CollatzResearch.WordTrace tailWord_5541986 prefixEnd_5541986 2845702598488259187987877 := by
  unfold tailWord_5541986
  simp only [CollatzResearch.WordTrace]
  refine ⟨50533208825084673174881453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134755223533559128466350541 50533208825084673174881453)
  ·
    refine ⟨18949953309406752440580545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50533208825084673174881453 18949953309406752440580545)
    ·
      refine ⟨14212464982055064330435409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18949953309406752440580545 14212464982055064330435409)
      ·
        refine ⟨10659348736541298247826557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14212464982055064330435409 10659348736541298247826557)
        ·
          refine ⟨3997255776202986842934959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10659348736541298247826557 3997255776202986842934959)
          ·
            refine ⟨5995883664304480264402439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997255776202986842934959 5995883664304480264402439)
            ·
              refine ⟨8993825496456720396603659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995883664304480264402439 8993825496456720396603659)
              ·
                refine ⟨13490738244685080594905489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8993825496456720396603659 13490738244685080594905489)
                ·
                  refine ⟨10118053683513810446179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13490738244685080594905489 10118053683513810446179117)
                  ·
                    refine ⟨3794270131317678917317169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10118053683513810446179117 3794270131317678917317169)
                    ·
                      refine ⟨2845702598488259187987877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794270131317678917317169 2845702598488259187987877)
                      ·
                        rfl

theorem cell23_5541986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5541986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541986 prefixEnd_5541986 := by exact prefixLift 5541986
  have htrace : WordTrace (prefixWord ++ tailWord_5541986) baseStart_5541986 baseEnd_5541986 := by
    simpa [prefixWord, tailWord_5541986, baseEnd_5541986] using wordTrace_append hprefix tailTrace_5541986
  have hstable : (prefixWord ++ tailWord_5541986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541986).length < 2 ^ (prefixWord ++ tailWord_5541986).sum := by decide
  have hdescent : baseEnd_5541986 < baseStart_5541986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5541999 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 1, 2, 2]
def baseStart_5541999 : Nat := 118140960795 + 5541999 * 2 ^ 59
def prefixEnd_5541999 : Nat := 4983230072969 + 3 ^ 40 * 5541999 * 2
def baseEnd_5541999 : Nat := 2845709273736767637125317

theorem tailTrace_5541999 : CollatzResearch.WordTrace tailWord_5541999 prefixEnd_5541999 2845709273736767637125317 := by
  unfold tailWord_5541999
  simp only [CollatzResearch.WordTrace]
  refine ⟨202133309449291595919749051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134755539632861063946499367 202133309449291595919749051)
  ·
    refine ⟨303199964173937393879623577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202133309449291595919749051 303199964173937393879623577)
    ·
      refine ⟨227399973130453045409717683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303199964173937393879623577 227399973130453045409717683)
      ·
        refine ⟨341099959695679568114576525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227399973130453045409717683 341099959695679568114576525)
        ·
          refine ⟨127912484885879838042966197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341099959695679568114576525 127912484885879838042966197)
          ·
            refine ⟨11991795458051234816528081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127912484885879838042966197 11991795458051234816528081)
            ·
              refine ⟨8993846593538426112396061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11991795458051234816528081 8993846593538426112396061)
              ·
                refine ⟨3372692472576909792148523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8993846593538426112396061 3372692472576909792148523)
                ·
                  refine ⟨5059038708865364688222785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372692472576909792148523 5059038708865364688222785)
                  ·
                    refine ⟨3794279031649023516167089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059038708865364688222785 3794279031649023516167089)
                    ·
                      refine ⟨2845709273736767637125317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794279031649023516167089 2845709273736767637125317)
                      ·
                        rfl

theorem cell23_5541999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 2, 2].length) (baseStart_5541999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5541999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5541999 prefixEnd_5541999 := by exact prefixLift 5541999
  have htrace : WordTrace (prefixWord ++ tailWord_5541999) baseStart_5541999 baseEnd_5541999 := by
    simpa [prefixWord, tailWord_5541999, baseEnd_5541999] using wordTrace_append hprefix tailTrace_5541999
  have hstable : (prefixWord ++ tailWord_5541999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5541999).length < 2 ^ (prefixWord ++ tailWord_5541999).sum := by decide
  have hdescent : baseEnd_5541999 < baseStart_5541999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5541999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542002 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_5542002 : Nat := 118140960795 + 5542002 * 2 ^ 59
def prefixEnd_5542002 : Nat := 4983230072969 + 3 ^ 40 * 5542002 * 2
def baseEnd_5542002 : Nat := 2845710814178731125387803

theorem tailTrace_5542002 : CollatzResearch.WordTrace tailWord_5542002 prefixEnd_5542002 2845710814178731125387803 := by
  unfold tailWord_5542002
  simp only [CollatzResearch.WordTrace]
  refine ⟨50533354717070181858027065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134755612578853818288072173 50533354717070181858027065)
  ·
    refine ⟨37900016037802636393520299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50533354717070181858027065 37900016037802636393520299)
    ·
      refine ⟨56850024056703954590280449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37900016037802636393520299 56850024056703954590280449)
      ·
        refine ⟨42637518042527965942710337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56850024056703954590280449 42637518042527965942710337)
        ·
          refine ⟨31978138531895974457032753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42637518042527965942710337 31978138531895974457032753)
          ·
            refine ⟨23983603898921980842774565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31978138531895974457032753 23983603898921980842774565)
            ·
              refine ⟨4496925731047871408020231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23983603898921980842774565 4496925731047871408020231)
              ·
                refine ⟨6745388596571807112030347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496925731047871408020231 6745388596571807112030347)
                ·
                  refine ⟨10118082894857710668045521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745388596571807112030347 10118082894857710668045521)
                  ·
                    refine ⟨7588562171143283001034141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10118082894857710668045521 7588562171143283001034141)
                    ·
                      refine ⟨2845710814178731125387803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7588562171143283001034141 2845710814178731125387803)
                      ·
                        rfl

theorem cell23_5542002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_5542002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542002 prefixEnd_5542002 := by exact prefixLift 5542002
  have htrace : WordTrace (prefixWord ++ tailWord_5542002) baseStart_5542002 baseEnd_5542002 := by
    simpa [prefixWord, tailWord_5542002, baseEnd_5542002] using wordTrace_append hprefix tailTrace_5542002
  have hstable : (prefixWord ++ tailWord_5542002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542002).length < 2 ^ (prefixWord ++ tailWord_5542002).sum := by decide
  have hdescent : baseEnd_5542002 < baseStart_5542002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542032 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3]
def baseStart_5542032 : Nat := 118140960795 + 5542032 * 2 ^ 59
def prefixEnd_5542032 : Nat := 4983230072969 + 3 ^ 40 * 5542032 * 2
def baseEnd_5542032 : Nat := 2845726218598366008012665

theorem tailTrace_5542032 : CollatzResearch.WordTrace tailWord_5542032 prefixEnd_5542032 2845726218598366008012665 := by
  unfold tailWord_5542032
  simp only [CollatzResearch.WordTrace]
  refine ⟨101067256529086021277850175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134756342038781361703800233 101067256529086021277850175)
  ·
    refine ⟨151600884793629031916775263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101067256529086021277850175 151600884793629031916775263)
    ·
      refine ⟨227401327190443547875162895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151600884793629031916775263 227401327190443547875162895)
      ·
        refine ⟨341101990785665321812744343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227401327190443547875162895 341101990785665321812744343)
        ·
          refine ⟨511652986178497982719116515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341101990785665321812744343 511652986178497982719116515)
          ·
            refine ⟨767479479267746974078674773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511652986178497982719116515 767479479267746974078674773)
            ·
              refine ⟨4496950073834454926242235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 767479479267746974078674773 4496950073834454926242235)
              ·
                refine ⟨6745425110751682389363353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4496950073834454926242235 6745425110751682389363353)
                ·
                  refine ⟨5059068833063761792022515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6745425110751682389363353 5059068833063761792022515)
                  ·
                    refine ⟨7588603249595642688033773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5059068833063761792022515 7588603249595642688033773)
                    ·
                      refine ⟨2845726218598366008012665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7588603249595642688033773 2845726218598366008012665)
                      ·
                        rfl

theorem cell23_5542032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3].length) (baseStart_5542032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542032 prefixEnd_5542032 := by exact prefixLift 5542032
  have htrace : WordTrace (prefixWord ++ tailWord_5542032) baseStart_5542032 baseEnd_5542032 := by
    simpa [prefixWord, tailWord_5542032, baseEnd_5542032] using wordTrace_append hprefix tailTrace_5542032
  have hstable : (prefixWord ++ tailWord_5542032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542032).length < 2 ^ (prefixWord ++ tailWord_5542032).sum := by decide
  have hdescent : baseEnd_5542032 < baseStart_5542032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542041 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_5542041 : Nat := 118140960795 + 5542041 * 2 ^ 59
def prefixEnd_5542041 : Nat := 4983230072969 + 3 ^ 40 * 5542041 * 2
def baseEnd_5542041 : Nat := 2845730839924256472800123

theorem tailTrace_5542041 : CollatzResearch.WordTrace tailWord_5542041 prefixEnd_5542041 2845730839924256472800123 := by
  unfold tailWord_5542041
  simp only [CollatzResearch.WordTrace]
  refine ⟨202134841315139437092777977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134756560876759624728518651 202134841315139437092777977)
  ·
    refine ⟨151601130986354577819583483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202134841315139437092777977 151601130986354577819583483)
    ·
      refine ⟨227401696479531866729375225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151601130986354577819583483 227401696479531866729375225)
      ·
        refine ⟨170551272359648900047031419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227401696479531866729375225 170551272359648900047031419)
        ·
          refine ⟨255826908539473350070547129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170551272359648900047031419 255826908539473350070547129)
          ·
            refine ⟨191870181404605012552910347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255826908539473350070547129 191870181404605012552910347)
            ·
              refine ⟨287805272106907518829365521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191870181404605012552910347 287805272106907518829365521)
              ·
                refine ⟨215853954080180639122024141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287805272106907518829365521 215853954080180639122024141)
                ·
                  refine ⟨80945232780067739670759053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215853954080180639122024141 80945232780067739670759053)
                  ·
                    refine ⟨30354462292525402376534645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80945232780067739670759053 30354462292525402376534645)
                    ·
                      refine ⟨2845730839924256472800123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30354462292525402376534645 2845730839924256472800123)
                      ·
                        rfl

theorem cell23_5542041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_5542041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542041 prefixEnd_5542041 := by exact prefixLift 5542041
  have htrace : WordTrace (prefixWord ++ tailWord_5542041) baseStart_5542041 baseEnd_5542041 := by
    simpa [prefixWord, tailWord_5542041, baseEnd_5542041] using wordTrace_append hprefix tailTrace_5542041
  have hstable : (prefixWord ++ tailWord_5542041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542041).length < 2 ^ (prefixWord ++ tailWord_5542041).sum := by decide
  have hdescent : baseEnd_5542041 < baseStart_5542041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542072 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_5542072 : Nat := 118140960795 + 5542072 * 2 ^ 59
def prefixEnd_5542072 : Nat := 4983230072969 + 3 ^ 40 * 5542072 * 2
def baseEnd_5542072 : Nat := 2845746757824545851512481

theorem tailTrace_5542072 : CollatzResearch.WordTrace tailWord_5542072 prefixEnd_5542072 2845746757824545851512481 := by
  unfold tailWord_5542072
  simp only [CollatzResearch.WordTrace]
  refine ⟨101067985989013564693578235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134757314652018086258104313 101067985989013564693578235)
  ·
    refine ⟨151601978983520347040367353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101067985989013564693578235 151601978983520347040367353)
    ·
      refine ⟨113701484237640260280275515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151601978983520347040367353 113701484237640260280275515)
      ·
        refine ⟨170552226356460390420413273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113701484237640260280275515 170552226356460390420413273)
        ·
          refine ⟨127914169767345292815309955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170552226356460390420413273 127914169767345292815309955)
          ·
            refine ⟨191871254651017939222964933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127914169767345292815309955 191871254651017939222964933)
            ·
              refine ⟨35975860247065863604305925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191871254651017939222964933 35975860247065863604305925)
              ·
                refine ⟨6745473796324849425807361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35975860247065863604305925 6745473796324849425807361)
                ·
                  refine ⟨5059105347243637069355521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6745473796324849425807361 5059105347243637069355521)
                  ·
                    refine ⟨3794329010432727802016641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059105347243637069355521 3794329010432727802016641)
                    ·
                      refine ⟨2845746757824545851512481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794329010432727802016641 2845746757824545851512481)
                      ·
                        rfl

theorem cell23_5542072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_5542072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542072 prefixEnd_5542072 := by exact prefixLift 5542072
  have htrace : WordTrace (prefixWord ++ tailWord_5542072) baseStart_5542072 baseEnd_5542072 := by
    simpa [prefixWord, tailWord_5542072, baseEnd_5542072] using wordTrace_append hprefix tailTrace_5542072
  have hstable : (prefixWord ++ tailWord_5542072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542072).length < 2 ^ (prefixWord ++ tailWord_5542072).sum := by decide
  have hdescent : baseEnd_5542072 < baseStart_5542072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542088 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_5542088 : Nat := 118140960795 + 5542088 * 2 ^ 59
def prefixEnd_5542088 : Nat := 4983230072969 + 3 ^ 40 * 5542088 * 2
def baseEnd_5542088 : Nat := 2845754973515017788912407

theorem tailTrace_5542088 : CollatzResearch.WordTrace tailWord_5542088 prefixEnd_5542088 2845754973515017788912407 := by
  unfold tailWord_5542088
  simp only [CollatzResearch.WordTrace]
  refine ⟨101068277772984582059869459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134757703697312776079825945 101068277772984582059869459)
  ·
    refine ⟨151602416659476873089804189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101068277772984582059869459 151602416659476873089804189)
    ·
      refine ⟨56850906247303827408676571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151602416659476873089804189 56850906247303827408676571)
      ·
        refine ⟨85276359370955741113014857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56850906247303827408676571 85276359370955741113014857)
        ·
          refine ⟨63957269528216805834761143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85276359370955741113014857 63957269528216805834761143)
          ·
            refine ⟨95935904292325208752141715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63957269528216805834761143 95935904292325208752141715)
            ·
              refine ⟨143903856438487813128212573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95935904292325208752141715 143903856438487813128212573)
              ·
                refine ⟨53963946164432929923079715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143903856438487813128212573 53963946164432929923079715)
                ·
                  refine ⟨80945919246649394884619573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53963946164432929923079715 80945919246649394884619573)
                  ·
                    refine ⟨7588679929373380770433085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80945919246649394884619573 7588679929373380770433085)
                    ·
                      refine ⟨2845754973515017788912407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7588679929373380770433085 2845754973515017788912407)
                      ·
                        rfl

theorem cell23_5542088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_5542088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542088 prefixEnd_5542088 := by exact prefixLift 5542088
  have htrace : WordTrace (prefixWord ++ tailWord_5542088) baseStart_5542088 baseEnd_5542088 := by
    simpa [prefixWord, tailWord_5542088, baseEnd_5542088] using wordTrace_append hprefix tailTrace_5542088
  have hstable : (prefixWord ++ tailWord_5542088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542088).length < 2 ^ (prefixWord ++ tailWord_5542088).sum := by decide
  have hdescent : baseEnd_5542088 < baseStart_5542088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542155 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 3, 4]
def baseStart_5542155 : Nat := 118140960795 + 5542155 * 2 ^ 59
def prefixEnd_5542155 : Nat := 4983230072969 + 3 ^ 40 * 5542155 * 2
def baseEnd_5542155 : Nat := 948596458906289675591533

theorem tailTrace_5542155 : CollatzResearch.WordTrace tailWord_5542155 prefixEnd_5542155 948596458906289675591533 := by
  unfold tailWord_5542155
  simp only [CollatzResearch.WordTrace]
  refine ⟨202138999236726434562427919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134759332824484289708285279 202138999236726434562427919)
  ·
    refine ⟨303208498855089651843641879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202138999236726434562427919 303208498855089651843641879)
    ·
      refine ⟨454812748282634477765462819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303208498855089651843641879 454812748282634477765462819)
      ·
        refine ⟨682219122423951716648194229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454812748282634477765462819 682219122423951716648194229)
        ·
          refine ⟨63958042727245473435768209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 682219122423951716648194229 63958042727245473435768209)
          ·
            refine ⟨47968532045434105076826157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63958042727245473435768209 47968532045434105076826157)
            ·
              refine ⟨17988199517037789403809809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47968532045434105076826157 17988199517037789403809809)
              ·
                refine ⟨13491149637778342052857357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17988199517037789403809809 13491149637778342052857357)
                ·
                  refine ⟨5059181114166878269821509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13491149637778342052857357 5059181114166878269821509)
                  ·
                    refine ⟨948596458906289675591533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059181114166878269821509 948596458906289675591533)
                    ·
                      rfl

theorem cell23_5542155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 4].length) (baseStart_5542155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542155 prefixEnd_5542155 := by exact prefixLift 5542155
  have htrace : WordTrace (prefixWord ++ tailWord_5542155) baseStart_5542155 baseEnd_5542155 := by
    simpa [prefixWord, tailWord_5542155, baseEnd_5542155] using wordTrace_append hprefix tailTrace_5542155
  have hstable : (prefixWord ++ tailWord_5542155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542155).length < 2 ^ (prefixWord ++ tailWord_5542155).sum := by decide
  have hdescent : baseEnd_5542155 < baseStart_5542155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542168 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 8]
def baseStart_5542168 : Nat := 118140960795 + 5542168 * 2 ^ 59
def prefixEnd_5542168 : Nat := 4983230072969 + 3 ^ 40 * 5542168 * 2
def baseEnd_5542168 : Nat := 316199561329708608434671

theorem tailTrace_5542168 : CollatzResearch.WordTrace tailWord_5542168 prefixEnd_5542168 316199561329708608434671 := by
  unfold tailWord_5542168
  simp only [CollatzResearch.WordTrace]
  refine ⟨101069736692839668891325579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134759648923786225188434105 101069736692839668891325579)
  ·
    refine ⟨151604605039259503336988369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101069736692839668891325579 151604605039259503336988369)
    ·
      refine ⟨113703453779444627502741277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151604605039259503336988369 113703453779444627502741277)
      ·
        refine ⟨42638795167291735313527979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113703453779444627502741277 42638795167291735313527979)
        ·
          refine ⟨63958192750937602970291969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42638795167291735313527979 63958192750937602970291969)
          ·
            refine ⟨47968644563203202227718977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63958192750937602970291969 47968644563203202227718977)
            ·
              refine ⟨35976483422402401670789233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47968644563203202227718977 35976483422402401670789233)
              ·
                refine ⟨26982362566801801253091925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35976483422402401670789233 26982362566801801253091925)
                ·
                  refine ⟨316199561329708608434671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26982362566801801253091925 316199561329708608434671)
                  ·
                    rfl

theorem cell23_5542168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_5542168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542168 prefixEnd_5542168 := by exact prefixLift 5542168
  have htrace : WordTrace (prefixWord ++ tailWord_5542168) baseStart_5542168 baseEnd_5542168 := by
    simpa [prefixWord, tailWord_5542168, baseEnd_5542168] using wordTrace_append hprefix tailTrace_5542168
  have hstable : (prefixWord ++ tailWord_5542168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542168).length < 2 ^ (prefixWord ++ tailWord_5542168).sum := by decide
  have hdescent : baseEnd_5542168 < baseStart_5542168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542188 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_5542188 : Nat := 118140960795 + 5542188 * 2 ^ 59
def prefixEnd_5542188 : Nat := 4983230072969 + 3 ^ 40 * 5542188 * 2
def baseEnd_5542188 : Nat := 2845806321580467397661947

theorem tailTrace_5542188 : CollatzResearch.WordTrace tailWord_5542188 prefixEnd_5542188 2845806321580467397661947 := by
  unfold tailWord_5542188
  simp only [CollatzResearch.WordTrace]
  refine ⟨101070101422803440599189609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134760135230404587465586145 101070101422803440599189609)
  ·
    refine ⟨75802576067102580449392207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101070101422803440599189609 75802576067102580449392207)
    ·
      refine ⟨113703864100653870674088311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75802576067102580449392207 113703864100653870674088311)
      ·
        refine ⟨170555796150980806011132467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113703864100653870674088311 170555796150980806011132467)
        ·
          refine ⟨255833694226471209016698701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170555796150980806011132467 255833694226471209016698701)
          ·
            refine ⟨95937635334926703381262013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255833694226471209016698701 95937635334926703381262013)
            ·
              refine ⟨35976613250597513767973255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95937635334926703381262013 35976613250597513767973255)
              ·
                refine ⟨53964919875896270651959883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35976613250597513767973255 53964919875896270651959883)
                ·
                  refine ⟨80947379813844405977939825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53964919875896270651959883 80947379813844405977939825)
                  ·
                    refine ⟨60710534860383304483454869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80947379813844405977939825 60710534860383304483454869)
                    ·
                      refine ⟨2845806321580467397661947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60710534860383304483454869 2845806321580467397661947)
                      ·
                        rfl

theorem cell23_5542188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_5542188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542188 prefixEnd_5542188 := by exact prefixLift 5542188
  have htrace : WordTrace (prefixWord ++ tailWord_5542188) baseStart_5542188 baseEnd_5542188 := by
    simpa [prefixWord, tailWord_5542188, baseEnd_5542188] using wordTrace_append hprefix tailTrace_5542188
  have hstable : (prefixWord ++ tailWord_5542188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542188).length < 2 ^ (prefixWord ++ tailWord_5542188).sum := by decide
  have hdescent : baseEnd_5542188 < baseStart_5542188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542202 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_5542202 : Nat := 118140960795 + 5542202 * 2 ^ 59
def prefixEnd_5542202 : Nat := 4983230072969 + 3 ^ 40 * 5542202 * 2
def baseEnd_5542202 : Nat := 316201501145514482542987

theorem tailTrace_5542202 : CollatzResearch.WordTrace tailWord_5542202 prefixEnd_5542202 316201501145514482542987 := by
  unfold tailWord_5542202
  simp only [CollatzResearch.WordTrace]
  refine ⟨50535178366889040397347215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134760475645037441059592573 50535178366889040397347215)
  ·
    refine ⟨75802767550333560596020823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50535178366889040397347215 75802767550333560596020823)
    ·
      refine ⟨113704151325500340894031235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75802767550333560596020823 113704151325500340894031235)
      ·
        refine ⟨170556226988250511341046853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113704151325500340894031235 170556226988250511341046853)
        ·
          refine ⟨31979292560296970876446285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170556226988250511341046853 31979292560296970876446285)
          ·
            refine ⟨11992234710111364078667357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31979292560296970876446285 11992234710111364078667357)
            ·
              refine ⟨4497088016291761529500259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11992234710111364078667357 4497088016291761529500259)
              ·
                refine ⟨6745632024437642294250389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497088016291761529500259 6745632024437642294250389)
                ·
                  refine ⟨316201501145514482542987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6745632024437642294250389 316201501145514482542987)
                  ·
                    rfl

theorem cell23_5542202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_5542202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542202 prefixEnd_5542202 := by exact prefixLift 5542202
  have htrace : WordTrace (prefixWord ++ tailWord_5542202) baseStart_5542202 baseEnd_5542202 := by
    simpa [prefixWord, tailWord_5542202, baseEnd_5542202] using wordTrace_append hprefix tailTrace_5542202
  have hstable : (prefixWord ++ tailWord_5542202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542202).length < 2 ^ (prefixWord ++ tailWord_5542202).sum := by decide
  have hdescent : baseEnd_5542202 < baseStart_5542202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542265 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5542265 : Nat := 118140960795 + 5542265 * 2 ^ 59
def prefixEnd_5542265 : Nat := 4983230072969 + 3 ^ 40 * 5542265 * 2
def baseEnd_5542265 : Nat := 2845845859590863596399093

theorem tailTrace_5542265 : CollatzResearch.WordTrace tailWord_5542265 prefixEnd_5542265 2845845859590863596399093 := by
  unfold tailWord_5542265
  simp only [CollatzResearch.WordTrace]
  refine ⟨202143011266327923348932249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134762007510885282232621499 202143011266327923348932249)
  ·
    refine ⟨151607258449745942511699187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202143011266327923348932249 151607258449745942511699187)
    ·
      refine ⟨227410887674618913767548781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151607258449745942511699187 227410887674618913767548781)
      ·
        refine ⟨85279082877982092662830793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227410887674618913767548781 85279082877982092662830793)
        ·
          refine ⟨63959312158486569497123095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85279082877982092662830793 63959312158486569497123095)
          ·
            refine ⟨95938968237729854245684643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63959312158486569497123095 95938968237729854245684643)
            ·
              refine ⟨143908452356594781368526965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95938968237729854245684643 143908452356594781368526965)
              ·
                refine ⟨13491417408430760753299403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143908452356594781368526965 13491417408430760753299403)
                ·
                  refine ⟨20237126112646141129949105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13491417408430760753299403 20237126112646141129949105)
                  ·
                    refine ⟨15177844584484605847461829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20237126112646141129949105 15177844584484605847461829)
                    ·
                      refine ⟨2845845859590863596399093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15177844584484605847461829 2845845859590863596399093)
                      ·
                        rfl

theorem cell23_5542265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5542265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542265 prefixEnd_5542265 := by exact prefixLift 5542265
  have htrace : WordTrace (prefixWord ++ tailWord_5542265) baseStart_5542265 baseEnd_5542265 := by
    simpa [prefixWord, tailWord_5542265, baseEnd_5542265] using wordTrace_append hprefix tailTrace_5542265
  have hstable : (prefixWord ++ tailWord_5542265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542265).length < 2 ^ (prefixWord ++ tailWord_5542265).sum := by decide
  have hdescent : baseEnd_5542265 < baseStart_5542265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542269 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_5542269 : Nat := 118140960795 + 5542269 * 2 ^ 59
def prefixEnd_5542269 : Nat := 4983230072969 + 3 ^ 40 * 5542269 * 2
def baseEnd_5542269 : Nat := 2845847913513481580749075

theorem tailTrace_5542269 : CollatzResearch.WordTrace tailWord_5542269 prefixEnd_5542269 2845847913513481580749075 := by
  unfold tailWord_5542269
  simp only [CollatzResearch.WordTrace]
  refine ⟨202143157158313432032077861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134762104772208954688051907 202143157158313432032077861)
  ·
    refine ⟨37901841967183768506014599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202143157158313432032077861 37901841967183768506014599)
    ·
      refine ⟨56852762950775652759021899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37901841967183768506014599 56852762950775652759021899)
      ·
        refine ⟨85279144426163479138532849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56852762950775652759021899 85279144426163479138532849)
        ·
          refine ⟨63959358319622609353899637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85279144426163479138532849 63959358319622609353899637)
          ·
            refine ⟨5996189842464619626928091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63959358319622609353899637 5996189842464619626928091)
            ·
              refine ⟨8994284763696929440392137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996189842464619626928091 8994284763696929440392137)
              ·
                refine ⟨6745713572772697080294103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8994284763696929440392137 6745713572772697080294103)
                ·
                  refine ⟨10118570359159045620441155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745713572772697080294103 10118570359159045620441155)
                  ·
                    refine ⟨15177855538738568430661733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10118570359159045620441155 15177855538738568430661733)
                    ·
                      refine ⟨2845847913513481580749075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15177855538738568430661733 2845847913513481580749075)
                      ·
                        rfl

theorem cell23_5542269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_5542269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542269 prefixEnd_5542269 := by exact prefixLift 5542269
  have htrace : WordTrace (prefixWord ++ tailWord_5542269) baseStart_5542269 baseEnd_5542269 := by
    simpa [prefixWord, tailWord_5542269, baseEnd_5542269] using wordTrace_append hprefix tailTrace_5542269
  have hstable : (prefixWord ++ tailWord_5542269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542269).length < 2 ^ (prefixWord ++ tailWord_5542269).sum := by decide
  have hdescent : baseEnd_5542269 < baseStart_5542269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542286 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5542286 : Nat := 118140960795 + 5542286 * 2 ^ 59
def prefixEnd_5542286 : Nat := 4983230072969 + 3 ^ 40 * 5542286 * 2
def baseEnd_5542286 : Nat := 2845856642684608014236497

theorem tailTrace_5542286 : CollatzResearch.WordTrace tailWord_5542286 prefixEnd_5542286 2845856642684608014236497 := by
  unfold tailWord_5542286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25267972149906480491930839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134762518132834562623631141 25267972149906480491930839)
  ·
    refine ⟨37901958224859720737896259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25267972149906480491930839 37901958224859720737896259)
    ·
      refine ⟨56852937337289581106844389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37901958224859720737896259 56852937337289581106844389)
      ·
        refine ⟨10659925750741796457533323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56852937337289581106844389 10659925750741796457533323)
        ·
          refine ⟨15989888626112694686299985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659925750741796457533323 15989888626112694686299985)
          ·
            refine ⟨11992416469584521014724989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15989888626112694686299985 11992416469584521014724989)
            ·
              refine ⟨4497156176094195380521871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11992416469584521014724989 4497156176094195380521871)
              ·
                refine ⟨6745734264141293070782807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497156176094195380521871 6745734264141293070782807)
                ·
                  refine ⟨10118601396211939606174211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745734264141293070782807 10118601396211939606174211)
                  ·
                    refine ⟨15177902094317909409261317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10118601396211939606174211 15177902094317909409261317)
                    ·
                      refine ⟨2845856642684608014236497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15177902094317909409261317 2845856642684608014236497)
                      ·
                        rfl

theorem cell23_5542286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5542286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542286 prefixEnd_5542286 := by exact prefixLift 5542286
  have htrace : WordTrace (prefixWord ++ tailWord_5542286) baseStart_5542286 baseEnd_5542286 := by
    simpa [prefixWord, tailWord_5542286, baseEnd_5542286] using wordTrace_append hprefix tailTrace_5542286
  have hstable : (prefixWord ++ tailWord_5542286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542286).length < 2 ^ (prefixWord ++ tailWord_5542286).sum := by decide
  have hdescent : baseEnd_5542286 < baseStart_5542286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542292 : List Nat := [2, 4, 2, 1, 4, 10]
def baseStart_5542292 : Nat := 118140960795 + 5542292 * 2 ^ 59
def prefixEnd_5542292 : Nat := 4983230072969 + 3 ^ 40 * 5542292 * 2
def baseEnd_5542292 : Nat := 11711356887113312719183

theorem tailTrace_5542292 : CollatzResearch.WordTrace tailWord_5542292 prefixEnd_5542292 11711356887113312719183 := by
  unfold tailWord_5542292
  simp only [CollatzResearch.WordTrace]
  refine ⟨101071998018615053480082565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134762664024820071306776753 101071998018615053480082565)
  ·
    refine ⟨18950999628490322527515481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101071998018615053480082565 18950999628490322527515481)
    ·
      refine ⟨14213249721367741895636611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18950999628490322527515481 14213249721367741895636611)
      ·
        refine ⟨21319874582051612843454917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14213249721367741895636611 21319874582051612843454917)
        ·
          refine ⟨3997476484134677408147797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21319874582051612843454917 3997476484134677408147797)
          ·
            refine ⟨11711356887113312719183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3997476484134677408147797 11711356887113312719183)
            ·
              rfl

theorem cell23_5542292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 10].length) (baseStart_5542292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542292 prefixEnd_5542292 := by exact prefixLift 5542292
  have htrace : WordTrace (prefixWord ++ tailWord_5542292) baseStart_5542292 baseEnd_5542292 := by
    simpa [prefixWord, tailWord_5542292, baseEnd_5542292] using wordTrace_append hprefix tailTrace_5542292
  have hstable : (prefixWord ++ tailWord_5542292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542292).length < 2 ^ (prefixWord ++ tailWord_5542292).sum := by decide
  have hdescent : baseEnd_5542292 < baseStart_5542292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542329 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5542329 : Nat := 118140960795 + 5542329 * 2 ^ 59
def prefixEnd_5542329 : Nat := 4983230072969 + 3 ^ 40 * 5542329 * 2
def baseEnd_5542329 : Nat := 2845878722352751345998799

theorem tailTrace_5542329 : CollatzResearch.WordTrace tailWord_5542329 prefixEnd_5542329 2845878722352751345998799 := by
  unfold tailWord_5542329
  simp only [CollatzResearch.WordTrace]
  refine ⟨202145345538096062279262041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134763563692064041519508027 202145345538096062279262041)
  ·
    refine ⟨151609009153572046709446531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202145345538096062279262041 151609009153572046709446531)
    ·
      refine ⟨227413513730358070064169797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151609009153572046709446531 227413513730358070064169797)
      ·
        refine ⟨42640033824442138137031837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227413513730358070064169797 42640033824442138137031837)
        ·
          refine ⟨15990012684165801801386939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42640033824442138137031837 15990012684165801801386939)
          ·
            refine ⟨23985019026248702702080409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15990012684165801801386939 23985019026248702702080409)
            ·
              refine ⟨17988764269686527026560307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23985019026248702702080409 17988764269686527026560307)
              ·
                refine ⟨26983146404529790539840461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17988764269686527026560307 26983146404529790539840461)
                ·
                  refine ⟨10118679901698671452440173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26983146404529790539840461 10118679901698671452440173)
                  ·
                    refine ⟨3794504963137001794665065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10118679901698671452440173 3794504963137001794665065)
                    ·
                      refine ⟨2845878722352751345998799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794504963137001794665065 2845878722352751345998799)
                      ·
                        rfl

theorem cell23_5542329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5542329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542329 prefixEnd_5542329 := by exact prefixLift 5542329
  have htrace : WordTrace (prefixWord ++ tailWord_5542329) baseStart_5542329 baseEnd_5542329 := by
    simpa [prefixWord, tailWord_5542329, baseEnd_5542329] using wordTrace_append hprefix tailTrace_5542329
  have hstable : (prefixWord ++ tailWord_5542329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542329).length < 2 ^ (prefixWord ++ tailWord_5542329).sum := by decide
  have hdescent : baseEnd_5542329 < baseStart_5542329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542337 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5542337 : Nat := 118140960795 + 5542337 * 2 ^ 59
def prefixEnd_5542337 : Nat := 4983230072969 + 3 ^ 40 * 5542337 * 2
def baseEnd_5542337 : Nat := 2845882830197987314698763

theorem tailTrace_5542337 : CollatzResearch.WordTrace tailWord_5542337 prefixEnd_5542337 2845882830197987314698763 := by
  unfold tailWord_5542337
  simp only [CollatzResearch.WordTrace]
  refine ⟨202145637322067079645553265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134763758214711386430368843 202145637322067079645553265)
  ·
    refine ⟨151609227991550309734164949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202145637322067079645553265 151609227991550309734164949)
    ·
      refine ⟨3553341281051960384394491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 151609227991550309734164949 3553341281051960384394491)
      ·
        refine ⟨5330011921577940576591737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553341281051960384394491 5330011921577940576591737)
        ·
          refine ⟨3997508941183455432443803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5330011921577940576591737 3997508941183455432443803)
          ·
            refine ⟨5996263411775183148665705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997508941183455432443803 5996263411775183148665705)
            ·
              refine ⟨4497197558831387361499279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5996263411775183148665705 4497197558831387361499279)
              ·
                refine ⟨6745796338247081042248919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497197558831387361499279 6745796338247081042248919)
                ·
                  refine ⟨10118694507370621563373379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745796338247081042248919 10118694507370621563373379)
                  ·
                    refine ⟨15178041761055932345060069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10118694507370621563373379 15178041761055932345060069)
                    ·
                      refine ⟨2845882830197987314698763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15178041761055932345060069 2845882830197987314698763)
                      ·
                        rfl

theorem cell23_5542337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5542337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542337 prefixEnd_5542337 := by exact prefixLift 5542337
  have htrace : WordTrace (prefixWord ++ tailWord_5542337) baseStart_5542337 baseEnd_5542337 := by
    simpa [prefixWord, tailWord_5542337, baseEnd_5542337] using wordTrace_append hprefix tailTrace_5542337
  have hstable : (prefixWord ++ tailWord_5542337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542337).length < 2 ^ (prefixWord ++ tailWord_5542337).sum := by decide
  have hdescent : baseEnd_5542337 < baseStart_5542337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542340 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5542340 : Nat := 118140960795 + 5542340 * 2 ^ 59
def prefixEnd_5542340 : Nat := 4983230072969 + 3 ^ 40 * 5542340 * 2
def baseEnd_5542340 : Nat := 2845884370639950802961249

theorem tailTrace_5542340 : CollatzResearch.WordTrace tailWord_5542340 prefixEnd_5542340 2845884370639950802961249 := by
  unfold tailWord_5542340
  simp only [CollatzResearch.WordTrace]
  refine ⟨101072873370528105578956237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134763831160704140771941649 101072873370528105578956237)
  ·
    refine ⟨37902327513948039592108589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101072873370528105578956237 37902327513948039592108589)
    ·
      refine ⟨14213372817730514847040721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37902327513948039592108589 14213372817730514847040721)
      ·
        refine ⟨10660029613297886135280541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14213372817730514847040721 10660029613297886135280541)
        ·
          refine ⟨3997511104986707300730203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10660029613297886135280541 3997511104986707300730203)
          ·
            refine ⟨5996266657480060951095305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997511104986707300730203 5996266657480060951095305)
            ·
              refine ⟨4497199993110045713321479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5996266657480060951095305 4497199993110045713321479)
              ·
                refine ⟨6745799989665068569982219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497199993110045713321479 6745799989665068569982219)
                ·
                  refine ⟨10118699984497602854973329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745799989665068569982219 10118699984497602854973329)
                  ·
                    refine ⟨7589024988373202141229997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10118699984497602854973329 7589024988373202141229997)
                    ·
                      refine ⟨2845884370639950802961249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589024988373202141229997 2845884370639950802961249)
                      ·
                        rfl

theorem cell23_5542340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5542340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542340 prefixEnd_5542340 := by exact prefixLift 5542340
  have htrace : WordTrace (prefixWord ++ tailWord_5542340) baseStart_5542340 baseEnd_5542340 := by
    simpa [prefixWord, tailWord_5542340, baseEnd_5542340] using wordTrace_append hprefix tailTrace_5542340
  have hstable : (prefixWord ++ tailWord_5542340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542340).length < 2 ^ (prefixWord ++ tailWord_5542340).sum := by decide
  have hdescent : baseEnd_5542340 < baseStart_5542340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542345 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_5542345 : Nat := 118140960795 + 5542345 * 2 ^ 59
def prefixEnd_5542345 : Nat := 4983230072969 + 3 ^ 40 * 5542345 * 2
def baseEnd_5542345 : Nat := 2845886938043223283398725

theorem tailTrace_5542345 : CollatzResearch.WordTrace tailWord_5542345 prefixEnd_5542345 2845886938043223283398725 := by
  unfold tailWord_5542345
  simp only [CollatzResearch.WordTrace]
  refine ⟨202145929106038097011844489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134763952737358731341229659 202145929106038097011844489)
  ·
    refine ⟨151609446829528572758883367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202145929106038097011844489 151609446829528572758883367)
    ·
      refine ⟨227414170244292859138325051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151609446829528572758883367 227414170244292859138325051)
      ·
        refine ⟨341121255366439288707487577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227414170244292859138325051 341121255366439288707487577)
        ·
          refine ⟨255840941524829466530615683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341121255366439288707487577 255840941524829466530615683)
          ·
            refine ⟨383761412287244199795923525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255840941524829466530615683 383761412287244199795923525)
            ·
              refine ⟨71955264803858287461735661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 383761412287244199795923525 71955264803858287461735661)
              ·
                refine ⟨26983224301446857798150873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71955264803858287461735661 26983224301446857798150873)
                ·
                  refine ⟨20237418226085143348613155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26983224301446857798150873 20237418226085143348613155)
                  ·
                    refine ⟨30356127339127715022919733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20237418226085143348613155 30356127339127715022919733)
                    ·
                      refine ⟨2845886938043223283398725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30356127339127715022919733 2845886938043223283398725)
                      ·
                        rfl

theorem cell23_5542345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_5542345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542345 prefixEnd_5542345 := by exact prefixLift 5542345
  have htrace : WordTrace (prefixWord ++ tailWord_5542345) baseStart_5542345 baseEnd_5542345 := by
    simpa [prefixWord, tailWord_5542345, baseEnd_5542345] using wordTrace_append hprefix tailTrace_5542345
  have hstable : (prefixWord ++ tailWord_5542345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542345).length < 2 ^ (prefixWord ++ tailWord_5542345).sum := by decide
  have hdescent : baseEnd_5542345 < baseStart_5542345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542370 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5542370 : Nat := 118140960795 + 5542370 * 2 ^ 59
def prefixEnd_5542370 : Nat := 4983230072969 + 3 ^ 40 * 5542370 * 2
def baseEnd_5542370 : Nat := 2845899775059585685586111

theorem tailTrace_5542370 : CollatzResearch.WordTrace tailWord_5542370 prefixEnd_5542370 2845899775059585685586111 := by
  unfold tailWord_5542370
  simp only [CollatzResearch.WordTrace]
  refine ⟨50536710232736881570376141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134764560620631684187669709 50536710232736881570376141)
  ·
    refine ⟨18951266337276330588891053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50536710232736881570376141 18951266337276330588891053)
    ·
      refine ⟨7106724876478623970834145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18951266337276330588891053 7106724876478623970834145)
      ·
        refine ⟨5330043657358967978125609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7106724876478623970834145 5330043657358967978125609)
        ·
          refine ⟨3997532743019225983594207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5330043657358967978125609 3997532743019225983594207)
          ·
            refine ⟨5996299114528838975391311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997532743019225983594207 5996299114528838975391311)
            ·
              refine ⟨8994448671793258463086967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996299114528838975391311 8994448671793258463086967)
              ·
                refine ⟨13491673007689887694630451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994448671793258463086967 13491673007689887694630451)
                ·
                  refine ⟨20237509511534831541945677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13491673007689887694630451 20237509511534831541945677)
                  ·
                    refine ⟨7589066066825561828229629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20237509511534831541945677 7589066066825561828229629)
                    ·
                      refine ⟨2845899775059585685586111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589066066825561828229629 2845899775059585685586111)
                      ·
                        rfl

theorem cell23_5542370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5542370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542370 prefixEnd_5542370 := by exact prefixLift 5542370
  have htrace : WordTrace (prefixWord ++ tailWord_5542370) baseStart_5542370 baseEnd_5542370 := by
    simpa [prefixWord, tailWord_5542370, baseEnd_5542370] using wordTrace_append hprefix tailTrace_5542370
  have hstable : (prefixWord ++ tailWord_5542370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542370).length < 2 ^ (prefixWord ++ tailWord_5542370).sum := by decide
  have hdescent : baseEnd_5542370 < baseStart_5542370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542376 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5542376 : Nat := 118140960795 + 5542376 * 2 ^ 59
def prefixEnd_5542376 : Nat := 4983230072969 + 3 ^ 40 * 5542376 * 2
def baseEnd_5542376 : Nat := 2845902855943512662111083

theorem tailTrace_5542376 : CollatzResearch.WordTrace tailWord_5542376 prefixEnd_5542376 2845902855943512662111083 := by
  unfold tailWord_5542376
  simp only [CollatzResearch.WordTrace]
  refine ⟨101073529884462894653111491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134764706512617192870815321 101073529884462894653111491)
  ·
    refine ⟨151610294826694341979667237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101073529884462894653111491 151610294826694341979667237)
    ·
      refine ⟨28426930280005189121187607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151610294826694341979667237 28426930280005189121187607)
      ·
        refine ⟨42640395420007783681781411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28426930280005189121187607 42640395420007783681781411)
        ·
          refine ⟨63960593130011675522672117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42640395420007783681781411 63960593130011675522672117)
          ·
            refine ⟨5996305605938594580250511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63960593130011675522672117 5996305605938594580250511)
            ·
              refine ⟨8994458408907891870375767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996305605938594580250511 8994458408907891870375767)
              ·
                refine ⟨13491687613361837805563651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994458408907891870375767 13491687613361837805563651)
                ·
                  refine ⟨20237531420042756708345477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13491687613361837805563651 20237531420042756708345477)
                  ·
                    refine ⟨3794537141258016882814777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20237531420042756708345477 3794537141258016882814777)
                    ·
                      refine ⟨2845902855943512662111083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794537141258016882814777 2845902855943512662111083)
                      ·
                        rfl

theorem cell23_5542376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5542376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542376 prefixEnd_5542376 := by exact prefixLift 5542376
  have htrace : WordTrace (prefixWord ++ tailWord_5542376) baseStart_5542376 baseEnd_5542376 := by
    simpa [prefixWord, tailWord_5542376, baseEnd_5542376] using wordTrace_append hprefix tailTrace_5542376
  have hstable : (prefixWord ++ tailWord_5542376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542376).length < 2 ^ (prefixWord ++ tailWord_5542376).sum := by decide
  have hdescent : baseEnd_5542376 < baseStart_5542376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542382 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_5542382 : Nat := 118140960795 + 5542382 * 2 ^ 59
def prefixEnd_5542382 : Nat := 4983230072969 + 3 ^ 40 * 5542382 * 2
def baseEnd_5542382 : Nat := 316211770758604404292895

theorem tailTrace_5542382 : CollatzResearch.WordTrace tailWord_5542382 prefixEnd_5542382 316211770758604404292895 := by
  unfold tailWord_5542382
  simp only [CollatzResearch.WordTrace]
  refine ⟨25268409825863006541367675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134764852404602701553960933 25268409825863006541367675)
  ·
    refine ⟨37902614738794509812051513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25268409825863006541367675 37902614738794509812051513)
    ·
      refine ⟨28426961054095882359038635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37902614738794509812051513 28426961054095882359038635)
      ·
        refine ⟨42640441581143823538557953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28426961054095882359038635 42640441581143823538557953)
        ·
          refine ⟨31980331185857867653918465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42640441581143823538557953 31980331185857867653918465)
          ·
            refine ⟨23985248389393400740438849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31980331185857867653918465 23985248389393400740438849)
            ·
              refine ⟨17988936292045050555329137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23985248389393400740438849 17988936292045050555329137)
              ·
                refine ⟨13491702219033787916496853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17988936292045050555329137 13491702219033787916496853)
                ·
                  refine ⟨316211770758604404292895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13491702219033787916496853 316211770758604404292895)
                  ·
                    rfl

theorem cell23_5542382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_5542382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542382 prefixEnd_5542382 := by exact prefixLift 5542382
  have htrace : WordTrace (prefixWord ++ tailWord_5542382) baseStart_5542382 baseEnd_5542382 := by
    simpa [prefixWord, tailWord_5542382, baseEnd_5542382] using wordTrace_append hprefix tailTrace_5542382
  have hstable : (prefixWord ++ tailWord_5542382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542382).length < 2 ^ (prefixWord ++ tailWord_5542382).sum := by decide
  have hdescent : baseEnd_5542382 < baseStart_5542382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542412 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_5542412 : Nat := 118140960795 + 5542412 * 2 ^ 59
def prefixEnd_5542412 : Nat := 4983230072969 + 3 ^ 40 * 5542412 * 2
def baseEnd_5542412 : Nat := 948640447082358173753639

theorem tailTrace_5542412 : CollatzResearch.WordTrace tailWord_5542412 prefixEnd_5542412 948640447082358173753639 := by
  unfold tailWord_5542412
  simp only [CollatzResearch.WordTrace]
  refine ⟨101074186398397683727266745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134765581864530244969688993 101074186398397683727266745)
  ·
    refine ⟨75805639798798262795450059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101074186398397683727266745 75805639798798262795450059)
    ·
      refine ⟨113708459698197394193175089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75805639798798262795450059 113708459698197394193175089)
      ·
        refine ⟨85281344773648045644881317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113708459698197394193175089 85281344773648045644881317)
        ·
          refine ⟨15990252145059008558415247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85281344773648045644881317 15990252145059008558415247)
          ·
            refine ⟨23985378217588512837622871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15990252145059008558415247 23985378217588512837622871)
            ·
              refine ⟨35978067326382769256434307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23985378217588512837622871 35978067326382769256434307)
              ·
                refine ⟨53967100989574153884651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35978067326382769256434307 53967100989574153884651461)
                ·
                  refine ⟨10118831435545153853372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53967100989574153884651461 10118831435545153853372149)
                  ·
                    refine ⟨948640447082358173753639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10118831435545153853372149 948640447082358173753639)
                    ·
                      rfl

theorem cell23_5542412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_5542412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542412 prefixEnd_5542412 := by exact prefixLift 5542412
  have htrace : WordTrace (prefixWord ++ tailWord_5542412) baseStart_5542412 baseEnd_5542412 := by
    simpa [prefixWord, tailWord_5542412, baseEnd_5542412] using wordTrace_append hprefix tailTrace_5542412
  have hstable : (prefixWord ++ tailWord_5542412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542412).length < 2 ^ (prefixWord ++ tailWord_5542412).sum := by decide
  have hdescent : baseEnd_5542412 < baseStart_5542412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542446 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5542446 : Nat := 118140960795 + 5542446 * 2 ^ 59
def prefixEnd_5542446 : Nat := 4983230072969 + 3 ^ 40 * 5542446 * 2
def baseEnd_5542446 : Nat := 948646266529775796078587

theorem tailTrace_5542446 : CollatzResearch.WordTrace tailWord_5542446 prefixEnd_5542446 948646266529775796078587 := by
  unfold tailWord_5542446
  simp only [CollatzResearch.WordTrace]
  refine ⟨25268701609834023907658899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134766408585781460840847461 25268701609834023907658899)
  ·
    refine ⟨37903052414751035861488349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25268701609834023907658899 37903052414751035861488349)
    ·
      refine ⟨14213644655531638448058131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37903052414751035861488349 14213644655531638448058131)
      ·
        refine ⟨21320466983297457672087197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14213644655531638448058131 21320466983297457672087197)
        ·
          refine ⟨7995175118736546627032699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21320466983297457672087197 7995175118736546627032699)
          ·
            refine ⟨11992762678104819940549049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995175118736546627032699 11992762678104819940549049)
            ·
              refine ⟨8994572008578614955411787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11992762678104819940549049 8994572008578614955411787)
              ·
                refine ⟨13491858012867922433117681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8994572008578614955411787 13491858012867922433117681)
                ·
                  refine ⟨10118893509650941824838261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13491858012867922433117681 10118893509650941824838261)
                  ·
                    refine ⟨948646266529775796078587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10118893509650941824838261 948646266529775796078587)
                    ·
                      rfl

theorem cell23_5542446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5542446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542446 prefixEnd_5542446 := by exact prefixLift 5542446
  have htrace : WordTrace (prefixWord ++ tailWord_5542446) baseStart_5542446 baseEnd_5542446 := by
    simpa [prefixWord, tailWord_5542446, baseEnd_5542446] using wordTrace_append hprefix tailTrace_5542446
  have hstable : (prefixWord ++ tailWord_5542446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542446).length < 2 ^ (prefixWord ++ tailWord_5542446).sum := by decide
  have hdescent : baseEnd_5542446 < baseStart_5542446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542469 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_5542469 : Nat := 118140960795 + 5542469 * 2 ^ 59
def prefixEnd_5542469 : Nat := 4983230072969 + 3 ^ 40 * 5542469 * 2
def baseEnd_5542469 : Nat := 2845950609644380798248155

theorem tailTrace_5542469 : CollatzResearch.WordTrace tailWord_5542469 prefixEnd_5542469 2845950609644380798248155 := by
  unfold tailWord_5542469
  simp only [CollatzResearch.WordTrace]
  refine ⟨202150451757588866189358461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134766967838392577459572307 202150451757588866189358461)
  ·
    refine ⟨75806419409095824821009423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202150451757588866189358461 75806419409095824821009423)
    ·
      refine ⟨113709629113643737231514135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75806419409095824821009423 113709629113643737231514135)
      ·
        refine ⟨170564443670465605847271203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113709629113643737231514135 170564443670465605847271203)
        ·
          refine ⟨255846665505698408770906805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170564443670465605847271203 255846665505698408770906805)
          ·
            refine ⟨23985624891159225822272513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255846665505698408770906805 23985624891159225822272513)
            ·
              refine ⟨17989218668369419366704385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23985624891159225822272513 17989218668369419366704385)
              ·
                refine ⟨13491914001277064525028289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17989218668369419366704385 13491914001277064525028289)
                ·
                  refine ⟨10118935500957798393771217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13491914001277064525028289 10118935500957798393771217)
                  ·
                    refine ⟨7589201625718348795328413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10118935500957798393771217 7589201625718348795328413)
                    ·
                      refine ⟨2845950609644380798248155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589201625718348795328413 2845950609644380798248155)
                      ·
                        rfl

theorem cell23_5542469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_5542469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542469 prefixEnd_5542469 := by exact prefixLift 5542469
  have htrace : WordTrace (prefixWord ++ tailWord_5542469) baseStart_5542469 baseEnd_5542469 := by
    simpa [prefixWord, tailWord_5542469, baseEnd_5542469] using wordTrace_append hprefix tailTrace_5542469
  have hstable : (prefixWord ++ tailWord_5542469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542469).length < 2 ^ (prefixWord ++ tailWord_5542469).sum := by decide
  have hdescent : baseEnd_5542469 < baseStart_5542469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542476 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_5542476 : Nat := 118140960795 + 5542476 * 2 ^ 59
def prefixEnd_5542476 : Nat := 4983230072969 + 3 ^ 40 * 5542476 * 2
def baseEnd_5542476 : Nat := 948651401336320756953541

theorem tailTrace_5542476 : CollatzResearch.WordTrace tailWord_5542476 prefixEnd_5542476 948651401336320756953541 := by
  unfold tailWord_5542476
  simp only [CollatzResearch.WordTrace]
  refine ⟨101075353534281753192431641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134767138045709004256575521 101075353534281753192431641)
  ·
    refine ⟨75806515150711314894323731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101075353534281753192431641 75806515150711314894323731)
    ·
      refine ⟨113709772726066972341485597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75806515150711314894323731 113709772726066972341485597)
      ·
        refine ⟨42641164772275114628057099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113709772726066972341485597 42641164772275114628057099)
        ·
          refine ⟨63961747158412671942085649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42641164772275114628057099 63961747158412671942085649)
          ·
            refine ⟨47971310368809503956564237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63961747158412671942085649 47971310368809503956564237)
            ·
              refine ⟨17989241388303563983711589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47971310368809503956564237 17989241388303563983711589)
              ·
                refine ⟨3372982760306918246945923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17989241388303563983711589 3372982760306918246945923)
                ·
                  refine ⟨5059474140460377370418885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372982760306918246945923 5059474140460377370418885)
                  ·
                    refine ⟨948651401336320756953541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059474140460377370418885 948651401336320756953541)
                    ·
                      rfl

theorem cell23_5542476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_5542476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542476 prefixEnd_5542476 := by exact prefixLift 5542476
  have htrace : WordTrace (prefixWord ++ tailWord_5542476) baseStart_5542476 baseEnd_5542476 := by
    simpa [prefixWord, tailWord_5542476, baseEnd_5542476] using wordTrace_append hprefix tailTrace_5542476
  have hstable : (prefixWord ++ tailWord_5542476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542476).length < 2 ^ (prefixWord ++ tailWord_5542476).sum := by decide
  have hdescent : baseEnd_5542476 < baseStart_5542476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542533 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 1, 1, 3]
def baseStart_5542533 : Nat := 118140960795 + 5542533 * 2 ^ 59
def prefixEnd_5542533 : Nat := 4983230072969 + 3 ^ 40 * 5542533 * 2
def baseEnd_5542533 : Nat := 2845983472406268547847861

theorem tailTrace_5542533 : CollatzResearch.WordTrace tailWord_5542533 prefixEnd_5542533 2845983472406268547847861 := by
  unfold tailWord_5542533
  simp only [CollatzResearch.WordTrace]
  refine ⟨202152786029357005119688253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134768524019571336746458835 202152786029357005119688253)
  ·
    refine ⟨75807294761008876919883095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202152786029357005119688253 75807294761008876919883095)
    ·
      refine ⟨113710942141513315379824643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75807294761008876919883095 113710942141513315379824643)
      ·
        refine ⟨170566413212269973069736965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113710942141513315379824643 170566413212269973069736965)
        ·
          refine ⟨31981202477300619950575681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170566413212269973069736965 31981202477300619950575681)
          ·
            refine ⟨23985901857975464962931761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31981202477300619950575681 23985901857975464962931761)
            ·
              refine ⟨17989426393481598722198821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23985901857975464962931761 17989426393481598722198821)
              ·
                refine ⟨3373017448777799760412279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17989426393481598722198821 3373017448777799760412279)
                ·
                  refine ⟨5059526173166699640618419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373017448777799760412279 5059526173166699640618419)
                  ·
                    refine ⟨7589289259750049460927629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5059526173166699640618419 7589289259750049460927629)
                    ·
                      refine ⟨2845983472406268547847861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589289259750049460927629 2845983472406268547847861)
                      ·
                        rfl

theorem cell23_5542533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_5542533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542533 prefixEnd_5542533 := by exact prefixLift 5542533
  have htrace : WordTrace (prefixWord ++ tailWord_5542533) baseStart_5542533 baseEnd_5542533 := by
    simpa [prefixWord, tailWord_5542533, baseEnd_5542533] using wordTrace_append hprefix tailTrace_5542533
  have hstable : (prefixWord ++ tailWord_5542533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542533).length < 2 ^ (prefixWord ++ tailWord_5542533).sum := by decide
  have hdescent : baseEnd_5542533 < baseStart_5542533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542556 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5542556 : Nat := 118140960795 + 5542556 * 2 ^ 59
def prefixEnd_5542556 : Nat := 4983230072969 + 3 ^ 40 * 5542556 * 2
def baseEnd_5542556 : Nat := 2845995282461321957860255

theorem tailTrace_5542556 : CollatzResearch.WordTrace tailWord_5542556 prefixEnd_5542556 2845995282461321957860255 := by
  unfold tailWord_5542556
  simp only [CollatzResearch.WordTrace]
  refine ⟨101076812454136840023887761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134769083272182453365183681 101076812454136840023887761)
  ·
    refine ⟨75807609340602630017915821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101076812454136840023887761 75807609340602630017915821)
    ·
      refine ⟨28427853502725986256718433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75807609340602630017915821 28427853502725986256718433)
      ·
        refine ⟨21320890127044489692538825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28427853502725986256718433 21320890127044489692538825)
        ·
          refine ⟨15990667595283367269404119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21320890127044489692538825 15990667595283367269404119)
          ·
            refine ⟨23986001392925050904106179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15990667595283367269404119 23986001392925050904106179)
            ·
              refine ⟨35979002089387576356159269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23986001392925050904106179 35979002089387576356159269)
              ·
                refine ⟨6746062891760170566779863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35979002089387576356159269 6746062891760170566779863)
                ·
                  refine ⟨10119094337640255850169795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6746062891760170566779863 10119094337640255850169795)
                  ·
                    refine ⟨15178641506460383775254693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10119094337640255850169795 15178641506460383775254693)
                    ·
                      refine ⟨2845995282461321957860255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15178641506460383775254693 2845995282461321957860255)
                      ·
                        rfl

theorem cell23_5542556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5542556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542556 prefixEnd_5542556 := by exact prefixLift 5542556
  have htrace : WordTrace (prefixWord ++ tailWord_5542556) baseStart_5542556 baseEnd_5542556 := by
    simpa [prefixWord, tailWord_5542556, baseEnd_5542556] using wordTrace_append hprefix tailTrace_5542556
  have hstable : (prefixWord ++ tailWord_5542556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542556).length < 2 ^ (prefixWord ++ tailWord_5542556).sum := by decide
  have hdescent : baseEnd_5542556 < baseStart_5542556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542610 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5542610 : Nat := 118140960795 + 5542610 * 2 ^ 59
def prefixEnd_5542610 : Nat := 4983230072969 + 3 ^ 40 * 5542610 * 2
def baseEnd_5542610 : Nat := 2846023010416664746585007

theorem tailTrace_5542610 : CollatzResearch.WordTrace tailWord_5542610 prefixEnd_5542610 2846023010416664746585007 := by
  unfold tailWord_5542610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50538898612519511817560321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134770396300052031513494189 50538898612519511817560321)
  ·
    refine ⟨37904173959389633863170241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50538898612519511817560321 37904173959389633863170241)
    ·
      refine ⟨28428130469542225397377681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37904173959389633863170241 28428130469542225397377681)
      ·
        refine ⟨21321097852156669048033261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28428130469542225397377681 21321097852156669048033261)
        ·
          refine ⟨7995411694558750893012473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21321097852156669048033261 7995411694558750893012473)
          ·
            refine ⟨5996558770919063169759355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7995411694558750893012473 5996558770919063169759355)
            ·
              refine ⟨8994838156378594754639033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996558770919063169759355 8994838156378594754639033)
              ·
                refine ⟨6746128617283946065979275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8994838156378594754639033 6746128617283946065979275)
                ·
                  refine ⟨10119192925925919098968913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6746128617283946065979275 10119192925925919098968913)
                  ·
                    refine ⟨7589394694444439324226685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10119192925925919098968913 7589394694444439324226685)
                    ·
                      refine ⟨2846023010416664746585007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589394694444439324226685 2846023010416664746585007)
                      ·
                        rfl

theorem cell23_5542610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5542610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542610 prefixEnd_5542610 := by exact prefixLift 5542610
  have htrace : WordTrace (prefixWord ++ tailWord_5542610) baseStart_5542610 baseEnd_5542610 := by
    simpa [prefixWord, tailWord_5542610, baseEnd_5542610] using wordTrace_append hprefix tailTrace_5542610
  have hstable : (prefixWord ++ tailWord_5542610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542610).length < 2 ^ (prefixWord ++ tailWord_5542610).sum := by decide
  have hdescent : baseEnd_5542610 < baseStart_5542610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542663 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5542663 : Nat := 118140960795 + 5542663 * 2 ^ 59
def prefixEnd_5542663 : Nat := 4983230072969 + 3 ^ 40 * 5542663 * 2
def baseEnd_5542663 : Nat := 2846050224891353039222263

theorem tailTrace_5542663 : CollatzResearch.WordTrace tailWord_5542663 prefixEnd_5542663 2846050224891353039222263 := by
  unfold tailWord_5542663
  simp only [CollatzResearch.WordTrace]
  refine ⟨202157527518886037321920643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134771685012590691547947095 202157527518886037321920643)
  ·
    refine ⟨303236291278329055982880965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202157527518886037321920643 303236291278329055982880965)
    ·
      refine ⟨56856804614686697996790181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303236291278329055982880965 56856804614686697996790181)
      ·
        refine ⟨10660650865253755874398159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56856804614686697996790181 10660650865253755874398159)
        ·
          refine ⟨15990976297880633811597239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10660650865253755874398159 15990976297880633811597239)
          ·
            refine ⟨23986464446820950717395859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15990976297880633811597239 23986464446820950717395859)
            ·
              refine ⟨35979696670231426076093789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23986464446820950717395859 35979696670231426076093789)
              ·
                refine ⟨13492386251336784778535171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35979696670231426076093789 13492386251336784778535171)
                ·
                  refine ⟨20238579377005177167802757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13492386251336784778535171 20238579377005177167802757)
                  ·
                    refine ⟨3794733633188470718963017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20238579377005177167802757 3794733633188470718963017)
                    ·
                      refine ⟨2846050224891353039222263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794733633188470718963017 2846050224891353039222263)
                      ·
                        rfl

theorem cell23_5542663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5542663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542663 prefixEnd_5542663 := by exact prefixLift 5542663
  have htrace : WordTrace (prefixWord ++ tailWord_5542663) baseStart_5542663 baseEnd_5542663 := by
    simpa [prefixWord, tailWord_5542663, baseEnd_5542663] using wordTrace_append hprefix tailTrace_5542663
  have hstable : (prefixWord ++ tailWord_5542663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542663).length < 2 ^ (prefixWord ++ tailWord_5542663).sum := by decide
  have hdescent : baseEnd_5542663 < baseStart_5542663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542696 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5542696 : Nat := 118140960795 + 5542696 * 2 ^ 59
def prefixEnd_5542696 : Nat := 4983230072969 + 3 ^ 40 * 5542696 * 2
def baseEnd_5542696 : Nat := 2846067169752951410109611

theorem tailTrace_5542696 : CollatzResearch.WordTrace tailWord_5542696 prefixEnd_5542696 2846067169752951410109611 := by
  unfold tailWord_5542696
  simp only [CollatzResearch.WordTrace]
  refine ⟨101079365563883241978935971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134772487418510989305247961 101079365563883241978935971)
  ·
    refine ⟨151619048345824862968403957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101079365563883241978935971 151619048345824862968403957)
    ·
      refine ⟨14214285782421080903287871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151619048345824862968403957 14214285782421080903287871)
      ·
        refine ⟨21321428673631621354931807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14214285782421080903287871 21321428673631621354931807)
        ·
          refine ⟨31982143010447432032397711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21321428673631621354931807 31982143010447432032397711)
          ·
            refine ⟨47973214515671148048596567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31982143010447432032397711 47973214515671148048596567)
            ·
              refine ⟨71959821773506722072894851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47973214515671148048596567 71959821773506722072894851)
              ·
                refine ⟨107939732660260083109342277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71959821773506722072894851 107939732660260083109342277)
                ·
                  refine ⟨20238699873798765583001677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107939732660260083109342277 20238699873798765583001677)
                  ·
                    refine ⟨7589512452674537093625629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20238699873798765583001677 7589512452674537093625629)
                    ·
                      refine ⟨2846067169752951410109611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589512452674537093625629 2846067169752951410109611)
                      ·
                        rfl

theorem cell23_5542696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5542696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542696 prefixEnd_5542696 := by exact prefixLift 5542696
  have htrace : WordTrace (prefixWord ++ tailWord_5542696) baseStart_5542696 baseEnd_5542696 := by
    simpa [prefixWord, tailWord_5542696, baseEnd_5542696] using wordTrace_append hprefix tailTrace_5542696
  have hstable : (prefixWord ++ tailWord_5542696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542696).length < 2 ^ (prefixWord ++ tailWord_5542696).sum := by decide
  have hdescent : baseEnd_5542696 < baseStart_5542696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542736 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2]
def baseStart_5542736 : Nat := 118140960795 + 5542736 * 2 ^ 59
def prefixEnd_5542736 : Nat := 4983230072969 + 3 ^ 40 * 5542736 * 2
def baseEnd_5542736 : Nat := 2846087708979131253609427

theorem tailTrace_5542736 : CollatzResearch.WordTrace tailWord_5542736 prefixEnd_5542736 2846087708979131253609427 := by
  unfold tailWord_5542736
  simp only [CollatzResearch.WordTrace]
  refine ⟨101080095023810785394664031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134773460031747713859552041 101080095023810785394664031)
  ·
    refine ⟨151620142535716178091996047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101080095023810785394664031 151620142535716178091996047)
    ·
      refine ⟨227430213803574267137994071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151620142535716178091996047 227430213803574267137994071)
      ·
        refine ⟨341145320705361400706991107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227430213803574267137994071 341145320705361400706991107)
        ·
          refine ⟨511717981058042101060486661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341145320705361400706991107 511717981058042101060486661)
          ·
            refine ⟨95947121448382893948841249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 511717981058042101060486661 95947121448382893948841249)
            ·
              refine ⟨71960341086287170461630937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95947121448382893948841249 71960341086287170461630937)
              ·
                refine ⟨53970255814715377846223203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71960341086287170461630937 53970255814715377846223203)
                ·
                  refine ⟨80955383722073066769334805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53970255814715377846223203 80955383722073066769334805)
                  ·
                    refine ⟨3794783611972175004812569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80955383722073066769334805 3794783611972175004812569)
                    ·
                      refine ⟨2846087708979131253609427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794783611972175004812569 2846087708979131253609427)
                      ·
                        rfl

theorem cell23_5542736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 6, 2].length) (baseStart_5542736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542736 prefixEnd_5542736 := by exact prefixLift 5542736
  have htrace : WordTrace (prefixWord ++ tailWord_5542736) baseStart_5542736 baseEnd_5542736 := by
    simpa [prefixWord, tailWord_5542736, baseEnd_5542736] using wordTrace_append hprefix tailTrace_5542736
  have hstable : (prefixWord ++ tailWord_5542736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542736).length < 2 ^ (prefixWord ++ tailWord_5542736).sum := by decide
  have hdescent : baseEnd_5542736 < baseStart_5542736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542763 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 1, 4]
def baseStart_5542763 : Nat := 118140960795 + 5542763 * 2 ^ 59
def prefixEnd_5542763 : Nat := 4983230072969 + 3 ^ 40 * 5542763 * 2
def baseEnd_5542763 : Nat := 948700524318934215990601

theorem tailTrace_5542763 : CollatzResearch.WordTrace tailWord_5542763 prefixEnd_5542763 948700524318934215990601 := by
  unfold tailWord_5542763
  simp only [CollatzResearch.WordTrace]
  refine ⟨202161174818523754400560943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134774116545682502933707295 202161174818523754400560943)
  ·
    refine ⟨303241762227785631600841415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202161174818523754400560943 303241762227785631600841415)
    ·
      refine ⟨454862643341678447401262123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303241762227785631600841415 454862643341678447401262123)
      ·
        refine ⟨682293965012517671101893185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454862643341678447401262123 682293965012517671101893185)
        ·
          refine ⟨511720473759388253326419889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682293965012517671101893185 511720473759388253326419889)
          ·
            refine ⟨383790355319541189994814917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511720473759388253326419889 383790355319541189994814917)
            ·
              refine ⟨71960691622413973124027797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 383790355319541189994814917 71960691622413973124027797)
              ·
                refine ⟨3373157419800654990188803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71960691622413973124027797 3373157419800654990188803)
                ·
                  refine ⟨5059736129700982485283205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373157419800654990188803 5059736129700982485283205)
                  ·
                    refine ⟨948700524318934215990601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059736129700982485283205 948700524318934215990601)
                    ·
                      rfl

theorem cell23_5542763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 1, 4].length) (baseStart_5542763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542763 prefixEnd_5542763 := by exact prefixLift 5542763
  have htrace : WordTrace (prefixWord ++ tailWord_5542763) baseStart_5542763 baseEnd_5542763 := by
    simpa [prefixWord, tailWord_5542763, baseEnd_5542763] using wordTrace_append hprefix tailTrace_5542763
  have hstable : (prefixWord ++ tailWord_5542763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542763).length < 2 ^ (prefixWord ++ tailWord_5542763).sum := by decide
  have hdescent : baseEnd_5542763 < baseStart_5542763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542779 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_5542779 : Nat := 118140960795 + 5542779 * 2 ^ 59
def prefixEnd_5542779 : Nat := 4983230072969 + 3 ^ 40 * 5542779 * 2
def baseEnd_5542779 : Nat := 2846109788647274585371729

theorem tailTrace_5542779 : CollatzResearch.WordTrace tailWord_5542779 prefixEnd_5542779 2846109788647274585371729 := by
  unfold tailWord_5542779
  simp only [CollatzResearch.WordTrace]
  refine ⟨202161758386465789133143391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134774505590977192755428927 202161758386465789133143391)
  ·
    refine ⟨303242637579698683699715087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202161758386465789133143391 303242637579698683699715087)
    ·
      refine ⟨454863956369548025549572631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303242637579698683699715087 454863956369548025549572631)
      ·
        refine ⟨682295934554322038324358947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454863956369548025549572631 682295934554322038324358947)
        ·
          refine ⟨1023443901831483057486538421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682295934554322038324358947 1023443901831483057486538421)
          ·
            refine ⟨95947865796701536639362977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1023443901831483057486538421 95947865796701536639362977)
            ·
              refine ⟨71960899347526152479522233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95947865796701536639362977 71960899347526152479522233)
              ·
                refine ⟨53970674510644614359641675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71960899347526152479522233 53970674510644614359641675)
                ·
                  refine ⟨80956011765966921539462513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53970674510644614359641675 80956011765966921539462513)
                  ·
                    refine ⟨60717008824475191154596885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80956011765966921539462513 60717008824475191154596885)
                    ·
                      refine ⟨2846109788647274585371729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60717008824475191154596885 2846109788647274585371729)
                      ·
                        rfl

theorem cell23_5542779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_5542779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542779 prefixEnd_5542779 := by exact prefixLift 5542779
  have htrace : WordTrace (prefixWord ++ tailWord_5542779) baseStart_5542779 baseEnd_5542779 := by
    simpa [prefixWord, tailWord_5542779, baseEnd_5542779] using wordTrace_append hprefix tailTrace_5542779
  have hstable : (prefixWord ++ tailWord_5542779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542779).length < 2 ^ (prefixWord ++ tailWord_5542779).sum := by decide
  have hdescent : baseEnd_5542779 < baseStart_5542779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542860 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5542860 : Nat := 118140960795 + 5542860 * 2 ^ 59
def prefixEnd_5542860 : Nat := 4983230072969 + 3 ^ 40 * 5542860 * 2
def baseEnd_5542860 : Nat := 2846151380580288768458857

theorem tailTrace_5542860 : CollatzResearch.WordTrace tailWord_5542860 prefixEnd_5542860 2846151380580288768458857 := by
  unfold tailWord_5542860
  simp only [CollatzResearch.WordTrace]
  refine ⟨101082356349586169983421017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134776475132781559977894689 101082356349586169983421017)
  ·
    refine ⟨75811767262189627487565763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101082356349586169983421017 75811767262189627487565763)
    ·
      refine ⟨113717650893284441231348645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75811767262189627487565763 113717650893284441231348645)
      ·
        refine ⟨21322059542490832730877871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113717650893284441231348645 21322059542490832730877871)
        ·
          refine ⟨31983089313736249096316807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21322059542490832730877871 31983089313736249096316807)
          ·
            refine ⟨47974633970604373644475211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31983089313736249096316807 47974633970604373644475211)
            ·
              refine ⟨71961950955906560466712817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47974633970604373644475211 71961950955906560466712817)
              ·
                refine ⟨53971463216929920350034613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71961950955906560466712817 53971463216929920350034613)
                ·
                  refine ⟨5059824676587180032815745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53971463216929920350034613 5059824676587180032815745)
                  ·
                    refine ⟨3794868507440385024611809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059824676587180032815745 3794868507440385024611809)
                    ·
                      refine ⟨2846151380580288768458857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794868507440385024611809 2846151380580288768458857)
                      ·
                        rfl

theorem cell23_5542860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5542860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542860 prefixEnd_5542860 := by exact prefixLift 5542860
  have htrace : WordTrace (prefixWord ++ tailWord_5542860) baseStart_5542860 baseEnd_5542860 := by
    simpa [prefixWord, tailWord_5542860, baseEnd_5542860] using wordTrace_append hprefix tailTrace_5542860
  have hstable : (prefixWord ++ tailWord_5542860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542860).length < 2 ^ (prefixWord ++ tailWord_5542860).sum := by decide
  have hdescent : baseEnd_5542860 < baseStart_5542860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542861 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 6]
def baseStart_5542861 : Nat := 118140960795 + 5542861 * 2 ^ 59
def prefixEnd_5542861 : Nat := 4983230072969 + 3 ^ 40 * 5542861 * 2
def baseEnd_5542861 : Nat := 316239099340104807171817

theorem tailTrace_5542861 : CollatzResearch.WordTrace tailWord_5542861 prefixEnd_5542861 316239099340104807171817 := by
  unfold tailWord_5542861
  simp only [CollatzResearch.WordTrace]
  refine ⟨202164749172168717137628437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134776499448112478091752291 202164749172168717137628437)
  ·
    refine ⟨9476472617445408615826333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202164749172168717137628437 9476472617445408615826333)
    ·
      refine ⟨3553677231542028230934875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9476472617445408615826333 3553677231542028230934875)
      ·
        refine ⟨5330515847313042346402313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553677231542028230934875 5330515847313042346402313)
        ·
          refine ⟨3997886885484781759801735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5330515847313042346402313 3997886885484781759801735)
          ·
            refine ⟨5996830328227172639702603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997886885484781759801735 5996830328227172639702603)
            ·
              refine ⟨8995245492340758959553905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996830328227172639702603 8995245492340758959553905)
              ·
                refine ⟨6746434119255569219665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8995245492340758959553905 6746434119255569219665429)
                ·
                  refine ⟨316239099340104807171817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6746434119255569219665429 316239099340104807171817)
                  ·
                    rfl

theorem cell23_5542861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_5542861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542861 prefixEnd_5542861 := by exact prefixLift 5542861
  have htrace : WordTrace (prefixWord ++ tailWord_5542861) baseStart_5542861 baseEnd_5542861 := by
    simpa [prefixWord, tailWord_5542861, baseEnd_5542861] using wordTrace_append hprefix tailTrace_5542861
  have hstable : (prefixWord ++ tailWord_5542861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542861).length < 2 ^ (prefixWord ++ tailWord_5542861).sum := by decide
  have hdescent : baseEnd_5542861 < baseStart_5542861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542877 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_5542877 : Nat := 118140960795 + 5542877 * 2 ^ 59
def prefixEnd_5542877 : Nat := 4983230072969 + 3 ^ 40 * 5542877 * 2
def baseEnd_5542877 : Nat := 2846160109751415201946279

theorem tailTrace_5542877 : CollatzResearch.WordTrace tailWord_5542877 prefixEnd_5542877 2846160109751415201946279 := by
  unfold tailWord_5542877
  simp only [CollatzResearch.WordTrace]
  refine ⟨202165332740110751870210885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134776888493407167913473923 202165332740110751870210885)
  ·
    refine ⟨37905999888770765975664541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202165332740110751870210885 37905999888770765975664541)
    ·
      refine ⟨14214749958289037240874203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37905999888770765975664541 14214749958289037240874203)
      ·
        refine ⟨21322124937433555861311305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14214749958289037240874203 21322124937433555861311305)
        ·
          refine ⟨15991593703075166895983479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21322124937433555861311305 15991593703075166895983479)
          ·
            refine ⟨23987390554612750343975219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15991593703075166895983479 23987390554612750343975219)
            ·
              refine ⟨35981085831919125515962829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23987390554612750343975219 35981085831919125515962829)
              ·
                refine ⟨13492907186969672068486061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35981085831919125515962829 13492907186969672068486061)
                ·
                  refine ⟨5059840195113627025682273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13492907186969672068486061 5059840195113627025682273)
                  ·
                    refine ⟨3794880146335220269261705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5059840195113627025682273 3794880146335220269261705)
                    ·
                      refine ⟨2846160109751415201946279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794880146335220269261705 2846160109751415201946279)
                      ·
                        rfl

theorem cell23_5542877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_5542877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542877 prefixEnd_5542877 := by exact prefixLift 5542877
  have htrace : WordTrace (prefixWord ++ tailWord_5542877) baseStart_5542877 baseEnd_5542877 := by
    simpa [prefixWord, tailWord_5542877, baseEnd_5542877] using wordTrace_append hprefix tailTrace_5542877
  have hstable : (prefixWord ++ tailWord_5542877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542877).length < 2 ^ (prefixWord ++ tailWord_5542877).sum := by decide
  have hdescent : baseEnd_5542877 < baseStart_5542877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542887 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 2, 4]
def baseStart_5542887 : Nat := 118140960795 + 5542887 * 2 ^ 59
def prefixEnd_5542887 : Nat := 4983230072969 + 3 ^ 40 * 5542887 * 2
def baseEnd_5542887 : Nat := 948721748185986720940411

theorem tailTrace_5542887 : CollatzResearch.WordTrace tailWord_5542887 prefixEnd_5542887 948721748185986720940411 := by
  unfold tailWord_5542887
  simp only [CollatzResearch.WordTrace]
  refine ⟨202165697470074523578074915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134777131646716349052049943 202165697470074523578074915)
  ·
    refine ⟨303248546205111785367112373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202165697470074523578074915 303248546205111785367112373)
    ·
      refine ⟨28429551206729229878166785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303248546205111785367112373 28429551206729229878166785)
      ·
        refine ⟨21322163405046922408625089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28429551206729229878166785 21322163405046922408625089)
        ·
          refine ⟨15991622553785191806468817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21322163405046922408625089 15991622553785191806468817)
          ·
            refine ⟨11993716915338893854851613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15991622553785191806468817 11993716915338893854851613)
            ·
              refine ⟨4497643843252085195569355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11993716915338893854851613 4497643843252085195569355)
              ·
                refine ⟨6746465764878127793354033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497643843252085195569355 6746465764878127793354033)
                ·
                  refine ⟨5059849323658595845015525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6746465764878127793354033 5059849323658595845015525)
                  ·
                    refine ⟨948721748185986720940411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059849323658595845015525 948721748185986720940411)
                    ·
                      rfl

theorem cell23_5542887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_5542887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542887 prefixEnd_5542887 := by exact prefixLift 5542887
  have htrace : WordTrace (prefixWord ++ tailWord_5542887) baseStart_5542887 baseEnd_5542887 := by
    simpa [prefixWord, tailWord_5542887, baseEnd_5542887] using wordTrace_append hprefix tailTrace_5542887
  have hstable : (prefixWord ++ tailWord_5542887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542887).length < 2 ^ (prefixWord ++ tailWord_5542887).sum := by decide
  have hdescent : baseEnd_5542887 < baseStart_5542887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542890 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_5542890 : Nat := 118140960795 + 5542890 * 2 ^ 59
def prefixEnd_5542890 : Nat := 4983230072969 + 3 ^ 40 * 5542890 * 2
def baseEnd_5542890 : Nat := 2846166784999923651083719

theorem tailTrace_5542890 : CollatzResearch.WordTrace tailWord_5542890 prefixEnd_5542890 2846166784999923651083719 := by
  unfold tailWord_5542890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50541451722265913772608531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134777204592709103393622749 50541451722265913772608531)
  ·
    refine ⟨75812177583398870658912797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50541451722265913772608531 75812177583398870658912797)
    ·
      refine ⟨28429566593774576497092299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75812177583398870658912797 28429566593774576497092299)
      ·
        refine ⟨42644349890661864745638449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28429566593774576497092299 42644349890661864745638449)
        ·
          refine ⟨31983262417996398559228837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42644349890661864745638449 31983262417996398559228837)
          ·
            refine ⟨5996861703374324729855407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31983262417996398559228837 5996861703374324729855407)
            ·
              refine ⟨8995292555061487094783111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996861703374324729855407 8995292555061487094783111)
              ·
                refine ⟨13492938832592230642174667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8995292555061487094783111 13492938832592230642174667)
                ·
                  refine ⟨20239408248888345963262001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13492938832592230642174667 20239408248888345963262001)
                  ·
                    refine ⟨15179556186666259472446501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20239408248888345963262001 15179556186666259472446501)
                    ·
                      refine ⟨2846166784999923651083719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15179556186666259472446501 2846166784999923651083719)
                      ·
                        rfl

theorem cell23_5542890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_5542890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542890 prefixEnd_5542890 := by exact prefixLift 5542890
  have htrace : WordTrace (prefixWord ++ tailWord_5542890) baseStart_5542890 baseEnd_5542890 := by
    simpa [prefixWord, tailWord_5542890, baseEnd_5542890] using wordTrace_append hprefix tailTrace_5542890
  have hstable : (prefixWord ++ tailWord_5542890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542890).length < 2 ^ (prefixWord ++ tailWord_5542890).sum := by decide
  have hdescent : baseEnd_5542890 < baseStart_5542890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542944 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5542944 : Nat := 118140960795 + 5542944 * 2 ^ 59
def prefixEnd_5542944 : Nat := 4983230072969 + 3 ^ 40 * 5542944 * 2
def baseEnd_5542944 : Nat := 2846194512955266439808471

theorem tailTrace_5542944 : CollatzResearch.WordTrace tailWord_5542944 prefixEnd_5542944 2846194512955266439808471 := by
  unfold tailWord_5542944
  simp only [CollatzResearch.WordTrace]
  refine ⟨101083888215434011156449943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134778517620578681541933257 101083888215434011156449943)
  ·
    refine ⟨151625832323151016734674915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101083888215434011156449943 151625832323151016734674915)
    ·
      refine ⟨227438748484726525102012373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151625832323151016734674915 227438748484726525102012373)
      ·
        refine ⟨5330595667610777932078415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 227438748484726525102012373 5330595667610777932078415)
        ·
          refine ⟨7995893501416166898117623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330595667610777932078415 7995893501416166898117623)
          ·
            refine ⟨11993840252124250347176435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7995893501416166898117623 11993840252124250347176435)
            ·
              refine ⟨17990760378186375520764653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11993840252124250347176435 17990760378186375520764653)
              ·
                refine ⟨6746535141819890820286745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17990760378186375520764653 6746535141819890820286745)
                ·
                  refine ⟨5059901356364918115215059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6746535141819890820286745 5059901356364918115215059)
                  ·
                    refine ⟨7589852034547377172822589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5059901356364918115215059 7589852034547377172822589)
                    ·
                      refine ⟨2846194512955266439808471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7589852034547377172822589 2846194512955266439808471)
                      ·
                        rfl

theorem cell23_5542944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5542944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542944 prefixEnd_5542944 := by exact prefixLift 5542944
  have htrace : WordTrace (prefixWord ++ tailWord_5542944) baseStart_5542944 baseEnd_5542944 := by
    simpa [prefixWord, tailWord_5542944, baseEnd_5542944] using wordTrace_append hprefix tailTrace_5542944
  have hstable : (prefixWord ++ tailWord_5542944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542944).length < 2 ^ (prefixWord ++ tailWord_5542944).sum := by decide
  have hdescent : baseEnd_5542944 < baseStart_5542944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542956 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 9]
def baseStart_5542956 : Nat := 118140960795 + 5542956 * 2 ^ 59
def prefixEnd_5542956 : Nat := 4983230072969 + 3 ^ 40 * 5542956 * 2
def baseEnd_5542956 : Nat := 316244519413680043650935

theorem tailTrace_5542956 : CollatzResearch.WordTrace tailWord_5542956 prefixEnd_5542956 316244519413680043650935 := by
  unfold tailWord_5542956
  simp only [CollatzResearch.WordTrace]
  refine ⟨101084107053412274181168361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134778809404549698908224481 101084107053412274181168361)
  ·
    refine ⟨75813080290059205635876271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101084107053412274181168361 75813080290059205635876271)
    ·
      refine ⟨113719620435088808453814407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75813080290059205635876271 113719620435088808453814407)
      ·
        refine ⟨170579430652633212680721611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113719620435088808453814407 170579430652633212680721611)
        ·
          refine ⟨255869145978949819021082417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170579430652633212680721611 255869145978949819021082417)
          ·
            refine ⟨191901859484212364265811813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255869145978949819021082417 191901859484212364265811813)
            ·
              refine ⟨35981598653289818299839715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191901859484212364265811813 35981598653289818299839715)
              ·
                refine ⟨53972397979934727449759573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35981598653289818299839715 53972397979934727449759573)
                ·
                  refine ⟨316244519413680043650935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53972397979934727449759573 316244519413680043650935)
                  ·
                    rfl

theorem cell23_5542956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_5542956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542956 prefixEnd_5542956 := by exact prefixLift 5542956
  have htrace : WordTrace (prefixWord ++ tailWord_5542956) baseStart_5542956 baseEnd_5542956 := by
    simpa [prefixWord, tailWord_5542956, baseEnd_5542956] using wordTrace_append hprefix tailTrace_5542956
  have hstable : (prefixWord ++ tailWord_5542956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542956).length < 2 ^ (prefixWord ++ tailWord_5542956).sum := by decide
  have hdescent : baseEnd_5542956 < baseStart_5542956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5542990 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_5542990 : Nat := 118140960795 + 5542990 * 2 ^ 59
def prefixEnd_5542990 : Nat := 4983230072969 + 3 ^ 40 * 5542990 * 2
def baseEnd_5542990 : Nat := 316246459229485917759251

theorem tailTrace_5542990 : CollatzResearch.WordTrace tailWord_5542990 prefixEnd_5542990 316246459229485917759251 := by
  unfold tailWord_5542990
  simp only [CollatzResearch.WordTrace]
  refine ⟨25271181773587671521134303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134779636125800914779382949 25271181773587671521134303)
  ·
    refine ⟨37906772660381507281701455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25271181773587671521134303 37906772660381507281701455)
    ·
      refine ⟨56860158990572260922552183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37906772660381507281701455 56860158990572260922552183)
      ·
        refine ⟨85290238485858391383828275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56860158990572260922552183 85290238485858391383828275)
        ·
          refine ⟨127935357728787587075742413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85290238485858391383828275 127935357728787587075742413)
          ·
            refine ⟨47975759148295345153403405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127935357728787587075742413 47975759148295345153403405)
            ·
              refine ⟨17990909680610754432526277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47975759148295345153403405 17990909680610754432526277)
              ·
                refine ⟨3373295565114516456098677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17990909680610754432526277 3373295565114516456098677)
                ·
                  refine ⟨316246459229485917759251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373295565114516456098677 316246459229485917759251)
                  ·
                    rfl

theorem cell23_5542990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_5542990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5542990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5542990 prefixEnd_5542990 := by exact prefixLift 5542990
  have htrace : WordTrace (prefixWord ++ tailWord_5542990) baseStart_5542990 baseEnd_5542990 := by
    simpa [prefixWord, tailWord_5542990, baseEnd_5542990] using wordTrace_append hprefix tailTrace_5542990
  have hstable : (prefixWord ++ tailWord_5542990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5542990).length < 2 ^ (prefixWord ++ tailWord_5542990).sum := by decide
  have hdescent : baseEnd_5542990 < baseStart_5542990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5542990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543023 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_5543023 : Nat := 118140960795 + 5543023 * 2 ^ 59
def prefixEnd_5543023 : Nat := 4983230072969 + 3 ^ 40 * 5543023 * 2
def baseEnd_5543023 : Nat := 2846235077926971630720607

theorem tailTrace_5543023 : CollatzResearch.WordTrace tailWord_5543023 prefixEnd_5543023 2846235077926971630720607 := by
  unfold tailWord_5543023
  simp only [CollatzResearch.WordTrace]
  refine ⟨202170657797581818805025723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134780438531721212536683815 202170657797581818805025723)
  ·
    refine ⟨303255986696372728207538585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202170657797581818805025723 303255986696372728207538585)
    ·
      refine ⟨227441990022279546155653939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303255986696372728207538585 227441990022279546155653939)
      ·
        refine ⟨341162985033419319233480909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227441990022279546155653939 341162985033419319233480909)
        ·
          refine ⟨127936119387532244712555341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341162985033419319233480909 127936119387532244712555341)
          ·
            refine ⟨47976044770324591767208253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127936119387532244712555341 47976044770324591767208253)
            ·
              refine ⟨17991016788871721912703095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47976044770324591767208253 17991016788871721912703095)
              ·
                refine ⟨26986525183307582869054643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17991016788871721912703095 26986525183307582869054643)
                ·
                  refine ⟨40479787774961374303581965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26986525183307582869054643 40479787774961374303581965)
                  ·
                    refine ⟨15179920415610515363843237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40479787774961374303581965 15179920415610515363843237)
                    ·
                      refine ⟨2846235077926971630720607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15179920415610515363843237 2846235077926971630720607)
                      ·
                        rfl

theorem cell23_5543023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_5543023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543023 prefixEnd_5543023 := by exact prefixLift 5543023
  have htrace : WordTrace (prefixWord ++ tailWord_5543023) baseStart_5543023 baseEnd_5543023 := by
    simpa [prefixWord, tailWord_5543023, baseEnd_5543023] using wordTrace_append hprefix tailTrace_5543023
  have hstable : (prefixWord ++ tailWord_5543023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543023).length < 2 ^ (prefixWord ++ tailWord_5543023).sum := by decide
  have hdescent : baseEnd_5543023 < baseStart_5543023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543040 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2]
def baseStart_5543040 : Nat := 118140960795 + 5543040 * 2 ^ 59
def prefixEnd_5543040 : Nat := 4983230072969 + 3 ^ 40 * 5543040 * 2
def baseEnd_5543040 : Nat := 2846243807098098064208029

theorem tailTrace_5543040 : CollatzResearch.WordTrace tailWord_5543040 prefixEnd_5543040 2846243807098098064208029 := by
  unfold tailWord_5543040
  simp only [CollatzResearch.WordTrace]
  refine ⟨101085638919260115354197287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134780851892346820472263049 101085638919260115354197287)
  ·
    refine ⟨151628458378890173031295931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101085638919260115354197287 151628458378890173031295931)
    ·
      refine ⟨227442687568335259546943897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151628458378890173031295931 227442687568335259546943897)
      ·
        refine ⟨170582015676251444660207923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227442687568335259546943897 170582015676251444660207923)
        ·
          refine ⟨255873023514377166990311885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170582015676251444660207923 255873023514377166990311885)
          ·
            refine ⟨95952383817891437621366957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255873023514377166990311885 95952383817891437621366957)
            ·
              refine ⟨35982143931709289108012609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95952383817891437621366957 35982143931709289108012609)
              ·
                refine ⟨26986607948781966831009457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35982143931709289108012609 26986607948781966831009457)
                ·
                  refine ⟨20239955961586475123257093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26986607948781966831009457 20239955961586475123257093)
                  ·
                    refine ⟨3794991742797464085610705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20239955961586475123257093 3794991742797464085610705)
                    ·
                      refine ⟨2846243807098098064208029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3794991742797464085610705 2846243807098098064208029)
                      ·
                        rfl

theorem cell23_5543040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_5543040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543040 prefixEnd_5543040 := by exact prefixLift 5543040
  have htrace : WordTrace (prefixWord ++ tailWord_5543040) baseStart_5543040 baseEnd_5543040 := by
    simpa [prefixWord, tailWord_5543040, baseEnd_5543040] using wordTrace_append hprefix tailTrace_5543040
  have hstable : (prefixWord ++ tailWord_5543040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543040).length < 2 ^ (prefixWord ++ tailWord_5543040).sum := by decide
  have hdescent : baseEnd_5543040 < baseStart_5543040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543140 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_5543140 : Nat := 118140960795 + 5543140 * 2 ^ 59
def prefixEnd_5543140 : Nat := 4983230072969 + 3 ^ 40 * 5543140 * 2
def baseEnd_5543140 : Nat := 948765051721182557652523

theorem tailTrace_5543140 : CollatzResearch.WordTrace tailWord_5543140 prefixEnd_5543140 948765051721182557652523 := by
  unfold tailWord_5543140
  simp only [CollatzResearch.WordTrace]
  refine ⟨101087462569078973893517437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134783283425438631858023249 101087462569078973893517437)
  ·
    refine ⟨37907798463404615210069039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101087462569078973893517437 37907798463404615210069039)
    ·
      refine ⟨56861697695106922815103559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37907798463404615210069039 56861697695106922815103559)
      ·
        refine ⟨85292546542660384222655339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56861697695106922815103559 85292546542660384222655339)
        ·
          refine ⟨127938819813990576333983009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85292546542660384222655339 127938819813990576333983009)
          ·
            refine ⟨95954114860492932250487257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127938819813990576333983009 95954114860492932250487257)
            ·
              refine ⟨71965586145369699187865443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95954114860492932250487257 71965586145369699187865443)
              ·
                refine ⟨107948379218054548781798165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71965586145369699187865443 107948379218054548781798165)
                ·
                  refine ⟨5060080275846306974146789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107948379218054548781798165 5060080275846306974146789)
                  ·
                    refine ⟨948765051721182557652523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060080275846306974146789 948765051721182557652523)
                    ·
                      rfl

theorem cell23_5543140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_5543140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543140 prefixEnd_5543140 := by exact prefixLift 5543140
  have htrace : WordTrace (prefixWord ++ tailWord_5543140) baseStart_5543140 baseEnd_5543140 := by
    simpa [prefixWord, tailWord_5543140, baseEnd_5543140] using wordTrace_append hprefix tailTrace_5543140
  have hstable : (prefixWord ++ tailWord_5543140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543140).length < 2 ^ (prefixWord ++ tailWord_5543140).sum := by decide
  have hdescent : baseEnd_5543140 < baseStart_5543140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543231 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 2, 1, 3]
def baseStart_5543231 : Nat := 118140960795 + 5543231 * 2 ^ 59
def prefixEnd_5543231 : Nat := 4983230072969 + 3 ^ 40 * 5543231 * 2
def baseEnd_5543231 : Nat := 2846341881903106816919651

theorem tailTrace_5543231 : CollatzResearch.WordTrace tailWord_5543231 prefixEnd_5543231 2846341881903106816919651 := by
  unfold tailWord_5543231
  simp only [CollatzResearch.WordTrace]
  refine ⟨202178244180828270328597547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134785496120552180219065031 202178244180828270328597547)
  ·
    refine ⟨303267366271242405492896321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202178244180828270328597547 303267366271242405492896321)
    ·
      refine ⟨227450524703431804119672241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303267366271242405492896321 227450524703431804119672241)
      ·
        refine ⟨170587893527573853089754181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227450524703431804119672241 170587893527573853089754181)
        ·
          refine ⟨31985230036420097454328909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170587893527573853089754181 31985230036420097454328909)
          ·
            refine ⟨11994461263657536545373341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31985230036420097454328909 11994461263657536545373341)
            ·
              refine ⟨4497922973871576204515003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11994461263657536545373341 4497922973871576204515003)
              ·
                refine ⟨6746884460807364306772505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497922973871576204515003 6746884460807364306772505)
                ·
                  refine ⟨5060163345605523230079379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6746884460807364306772505 5060163345605523230079379)
                  ·
                    refine ⟨7590245018408284845119069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060163345605523230079379 7590245018408284845119069)
                    ·
                      refine ⟨2846341881903106816919651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7590245018408284845119069 2846341881903106816919651)
                      ·
                        rfl

theorem cell23_5543231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_5543231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543231 prefixEnd_5543231 := by exact prefixLift 5543231
  have htrace : WordTrace (prefixWord ++ tailWord_5543231) baseStart_5543231 baseEnd_5543231 := by
    simpa [prefixWord, tailWord_5543231, baseEnd_5543231] using wordTrace_append hprefix tailTrace_5543231
  have hstable : (prefixWord ++ tailWord_5543231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543231).length < 2 ^ (prefixWord ++ tailWord_5543231).sum := by decide
  have hdescent : baseEnd_5543231 < baseStart_5543231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543238 : List Nat := [6, 1, 1, 3, 1, 2, 2, 7]
def baseStart_5543238 : Nat := 118140960795 + 5543238 * 2 ^ 59
def prefixEnd_5543238 : Nat := 4983230072969 + 3 ^ 40 * 5543238 * 2
def baseEnd_5543238 : Nat := 105420202824729195908597

theorem tailTrace_5543238 : CollatzResearch.WordTrace tailWord_5543238 prefixEnd_5543238 105420202824729195908597 := by
  unfold tailWord_5543238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318078109118840953878199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134785666327868607016068245 6318078109118840953878199)
  ·
    refine ⟨9477117163678261430817299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6318078109118840953878199 9477117163678261430817299)
    ·
      refine ⟨14215675745517392146225949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9477117163678261430817299 14215675745517392146225949)
      ·
        refine ⟨5330878404569022054834731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14215675745517392146225949 5330878404569022054834731)
        ·
          refine ⟨7996317606853533082252097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330878404569022054834731 7996317606853533082252097)
          ·
            refine ⟨5997238205140149811689073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7996317606853533082252097 5997238205140149811689073)
            ·
              refine ⟨4497928653855112358766805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5997238205140149811689073 4497928653855112358766805)
              ·
                refine ⟨105420202824729195908597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4497928653855112358766805 105420202824729195908597)
                ·
                  rfl

theorem cell23_5543238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_5543238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543238 prefixEnd_5543238 := by exact prefixLift 5543238
  have htrace : WordTrace (prefixWord ++ tailWord_5543238) baseStart_5543238 baseEnd_5543238 := by
    simpa [prefixWord, tailWord_5543238, baseEnd_5543238] using wordTrace_append hprefix tailTrace_5543238
  have hstable : (prefixWord ++ tailWord_5543238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543238).length < 2 ^ (prefixWord ++ tailWord_5543238).sum := by decide
  have hdescent : baseEnd_5543238 < baseStart_5543238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543240 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_5543240 : Nat := 118140960795 + 5543240 * 2 ^ 59
def prefixEnd_5543240 : Nat := 4983230072969 + 3 ^ 40 * 5543240 * 2
def baseEnd_5543240 : Nat := 2846346503228997281707109

theorem tailTrace_5543240 : CollatzResearch.WordTrace tailWord_5543240 prefixEnd_5543240 2846346503228997281707109 := by
  unfold tailWord_5543240
  simp only [CollatzResearch.WordTrace]
  refine ⟨101089286218897832432837587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134785714958530443243783449 101089286218897832432837587)
  ·
    refine ⟨151633929328346748649256381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101089286218897832432837587 151633929328346748649256381)
    ·
      refine ⟨56862723498130030743471143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151633929328346748649256381 56862723498130030743471143)
      ·
        refine ⟨85294085247195046115206715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56862723498130030743471143 85294085247195046115206715)
        ·
          refine ⟨127941127870792569172810073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85294085247195046115206715 127941127870792569172810073)
          ·
            refine ⟨95955845903094426879607555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127941127870792569172810073 95955845903094426879607555)
            ·
              refine ⟨143933768854641640319411333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95955845903094426879607555 143933768854641640319411333)
              ·
                refine ⟨26987581660245307559889625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143933768854641640319411333 26987581660245307559889625)
                ·
                  refine ⟨20240686245183980669917219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26987581660245307559889625 20240686245183980669917219)
                  ·
                    refine ⟨30361029367775971004875829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20240686245183980669917219 30361029367775971004875829)
                    ·
                      refine ⟨2846346503228997281707109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30361029367775971004875829 2846346503228997281707109)
                      ·
                        rfl

theorem cell23_5543240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_5543240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543240 prefixEnd_5543240 := by exact prefixLift 5543240
  have htrace : WordTrace (prefixWord ++ tailWord_5543240) baseStart_5543240 baseEnd_5543240 := by
    simpa [prefixWord, tailWord_5543240, baseEnd_5543240] using wordTrace_append hprefix tailTrace_5543240
  have hstable : (prefixWord ++ tailWord_5543240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543240).length < 2 ^ (prefixWord ++ tailWord_5543240).sum := by decide
  have hdescent : baseEnd_5543240 < baseStart_5543240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543277 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 7]
def baseStart_5543277 : Nat := 118140960795 + 5543277 * 2 ^ 59
def prefixEnd_5543277 : Nat := 4983230072969 + 3 ^ 40 * 5543277 * 2
def baseEnd_5543277 : Nat := 316262833557023737438271

theorem tailTrace_5543277 : CollatzResearch.WordTrace tailWord_5543277 prefixEnd_5543277 316262833557023737438271 := by
  unfold tailWord_5543277
  simp only [CollatzResearch.WordTrace]
  refine ⟨202179921938661620184772085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134786614625774413456514723 202179921938661620184772085)
  ·
    refine ⟨18954367681749526892322383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202179921938661620184772085 18954367681749526892322383)
    ·
      refine ⟨28431551522624290338483575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18954367681749526892322383 28431551522624290338483575)
      ·
        refine ⟨42647327283936435507725363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28431551522624290338483575 42647327283936435507725363)
        ·
          refine ⟨63970990925904653261588045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42647327283936435507725363 63970990925904653261588045)
          ·
            refine ⟨23989121597214244973095517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63970990925904653261588045 23989121597214244973095517)
            ·
              refine ⟨8995920598955341864910819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23989121597214244973095517 8995920598955341864910819)
              ·
                refine ⟨13493880898433012797366229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8995920598955341864910819 13493880898433012797366229)
                ·
                  refine ⟨316262833557023737438271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13493880898433012797366229 316262833557023737438271)
                  ·
                    rfl

theorem cell23_5543277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_5543277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543277 prefixEnd_5543277 := by exact prefixLift 5543277
  have htrace : WordTrace (prefixWord ++ tailWord_5543277) baseStart_5543277 baseEnd_5543277 := by
    simpa [prefixWord, tailWord_5543277, baseEnd_5543277] using wordTrace_append hprefix tailTrace_5543277
  have hstable : (prefixWord ++ tailWord_5543277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543277).length < 2 ^ (prefixWord ++ tailWord_5543277).sum := by decide
  have hdescent : baseEnd_5543277 < baseStart_5543277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543307 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 2, 5]
def baseStart_5543307 : Nat := 118140960795 + 5543307 * 2 ^ 59
def prefixEnd_5543307 : Nat := 4983230072969 + 3 ^ 40 * 5543307 * 2
def baseEnd_5543307 : Nat := 948793635477616173189767

theorem tailTrace_5543307 : CollatzResearch.WordTrace tailWord_5543307 prefixEnd_5543307 948793635477616173189767 := by
  unfold tailWord_5543307
  simp only [CollatzResearch.WordTrace]
  refine ⟨202181016128552935308364175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134787344085701956872242783 202181016128552935308364175)
  ·
    refine ⟨303271524192829402962546263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202181016128552935308364175 303271524192829402962546263)
    ·
      refine ⟨454907286289244104443819395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303271524192829402962546263 454907286289244104443819395)
      ·
        refine ⟨682360929433866156665729093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454907286289244104443819395 682360929433866156665729093)
        ·
          refine ⟨127942674268849904374824205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 682360929433866156665729093 127942674268849904374824205)
          ·
            refine ⟨47978502850818714140559077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127942674268849904374824205 47978502850818714140559077)
            ·
              refine ⟨8995969284528508901354827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47978502850818714140559077 8995969284528508901354827)
              ·
                refine ⟨13493953926792763352032241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8995969284528508901354827 13493953926792763352032241)
                ·
                  refine ⟨10120465445094572514024181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13493953926792763352032241 10120465445094572514024181)
                  ·
                    refine ⟨948793635477616173189767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10120465445094572514024181 948793635477616173189767)
                    ·
                      rfl

theorem cell23_5543307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 5].length) (baseStart_5543307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543307 prefixEnd_5543307 := by exact prefixLift 5543307
  have htrace : WordTrace (prefixWord ++ tailWord_5543307) baseStart_5543307 baseEnd_5543307 := by
    simpa [prefixWord, tailWord_5543307, baseEnd_5543307] using wordTrace_append hprefix tailTrace_5543307
  have hstable : (prefixWord ++ tailWord_5543307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543307).length < 2 ^ (prefixWord ++ tailWord_5543307).sum := by decide
  have hdescent : baseEnd_5543307 < baseStart_5543307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543347 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3]
def baseStart_5543347 : Nat := 118140960795 + 5543347 * 2 ^ 59
def prefixEnd_5543347 : Nat := 4983230072969 + 3 ^ 40 * 5543347 * 2
def baseEnd_5543347 : Nat := 2846401445659028363069117

theorem tailTrace_5543347 : CollatzResearch.WordTrace tailWord_5543347 prefixEnd_5543347 2846401445659028363069117 := by
  unfold tailWord_5543347
  simp only [CollatzResearch.WordTrace]
  refine ⟨202182475048408022139820295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134788316698938681426546863 202182475048408022139820295)
  ·
    refine ⟨303273712572612033209730443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202182475048408022139820295 303273712572612033209730443)
    ·
      refine ⟨454910568858918049814595665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303273712572612033209730443 454910568858918049814595665)
      ·
        refine ⟨341182926644188537360946749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454910568858918049814595665 341182926644188537360946749)
        ·
          refine ⟨127943597491570701510355031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341182926644188537360946749 127943597491570701510355031)
          ·
            refine ⟨191915396237356052265532547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127943597491570701510355031 191915396237356052265532547)
            ·
              refine ⟨287873094356034078398298821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191915396237356052265532547 287873094356034078398298821)
              ·
                refine ⟨53976205191756389699681029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287873094356034078398298821 53976205191756389699681029)
                ·
                  refine ⟨10120538473454323068690193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53976205191756389699681029 10120538473454323068690193)
                  ·
                    refine ⟨7590403855090742301517645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10120538473454323068690193 7590403855090742301517645)
                    ·
                      refine ⟨2846401445659028363069117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7590403855090742301517645 2846401445659028363069117)
                      ·
                        rfl

theorem cell23_5543347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_5543347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543347 prefixEnd_5543347 := by exact prefixLift 5543347
  have htrace : WordTrace (prefixWord ++ tailWord_5543347) baseStart_5543347 baseEnd_5543347 := by
    simpa [prefixWord, tailWord_5543347, baseEnd_5543347] using wordTrace_append hprefix tailTrace_5543347
  have hstable : (prefixWord ++ tailWord_5543347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543347).length < 2 ^ (prefixWord ++ tailWord_5543347).sum := by decide
  have hdescent : baseEnd_5543347 < baseStart_5543347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543362 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5543362 : Nat := 118140960795 + 5543362 * 2 ^ 59
def prefixEnd_5543362 : Nat := 4983230072969 + 3 ^ 40 * 5543362 * 2
def baseEnd_5543362 : Nat := 316267683096538422709061

theorem tailTrace_5543362 : CollatzResearch.WordTrace tailWord_5543362 prefixEnd_5543362 316267683096538422709061 := by
  unfold tailWord_5543362
  simp only [CollatzResearch.WordTrace]
  refine ⟨50545755535838419925404085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134788681428902453134410893 50545755535838419925404085)
  ·
    refine ⟨4738664581484851868006633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50545755535838419925404085 4738664581484851868006633)
    ·
      refine ⟨3553998436113638901004975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4738664581484851868006633 3553998436113638901004975)
      ·
        refine ⟨5330997654170458351507463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553998436113638901004975 5330997654170458351507463)
        ·
          refine ⟨7996496481255687527261195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330997654170458351507463 7996496481255687527261195)
          ·
            refine ⟨11994744721883531290891793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996496481255687527261195 11994744721883531290891793)
            ·
              refine ⟨8996058541412648468168845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11994744721883531290891793 8996058541412648468168845)
              ·
                refine ⟨3373521953029743175563317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8996058541412648468168845 3373521953029743175563317)
                ·
                  refine ⟨316267683096538422709061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373521953029743175563317 316267683096538422709061)
                  ·
                    rfl

theorem cell23_5543362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5543362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543362 prefixEnd_5543362 := by exact prefixLift 5543362
  have htrace : WordTrace (prefixWord ++ tailWord_5543362) baseStart_5543362 baseEnd_5543362 := by
    simpa [prefixWord, tailWord_5543362, baseEnd_5543362] using wordTrace_append hprefix tailTrace_5543362
  have hstable : (prefixWord ++ tailWord_5543362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543362).length < 2 ^ (prefixWord ++ tailWord_5543362).sum := by decide
  have hdescent : baseEnd_5543362 < baseStart_5543362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543404 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 6, 3, 2]
def baseStart_5543404 : Nat := 118140960795 + 5543404 * 2 ^ 59
def prefixEnd_5543404 : Nat := 4983230072969 + 3 ^ 40 * 5543404 * 2
def baseEnd_5543404 : Nat := 2846430714056334640056355

theorem tailTrace_5543404 : CollatzResearch.WordTrace tailWord_5543404 prefixEnd_5543404 2846430714056334640056355 := by
  unfold tailWord_5543404
  simp only [CollatzResearch.WordTrace]
  refine ⟨101092277004600760437322633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134789702672801013916430177 101092277004600760437322633)
  ·
    refine ⟨75819207753450570327991975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101092277004600760437322633 75819207753450570327991975)
    ·
      refine ⟨113728811630175855491987963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75819207753450570327991975 113728811630175855491987963)
      ·
        refine ⟨170593217445263783237981945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113728811630175855491987963 170593217445263783237981945)
        ·
          refine ⟨127944913083947837428486459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170593217445263783237981945 127944913083947837428486459)
          ·
            refine ⟨191917369625921756142729689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127944913083947837428486459 191917369625921756142729689)
            ·
              refine ⟨143938027219441317107047267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191917369625921756142729689 143938027219441317107047267)
              ·
                refine ⟨215907040829161975660570901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143938027219441317107047267 215907040829161975660570901)
                ·
                  refine ⟨10120642538866967609089261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215907040829161975660570901 10120642538866967609089261)
                  ·
                    refine ⟨3795240952075112853408473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10120642538866967609089261 3795240952075112853408473)
                    ·
                      refine ⟨2846430714056334640056355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795240952075112853408473 2846430714056334640056355)
                      ·
                        rfl

theorem cell23_5543404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 3, 2].length) (baseStart_5543404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543404 prefixEnd_5543404 := by exact prefixLift 5543404
  have htrace : WordTrace (prefixWord ++ tailWord_5543404) baseStart_5543404 baseEnd_5543404 := by
    simpa [prefixWord, tailWord_5543404, baseEnd_5543404] using wordTrace_append hprefix tailTrace_5543404
  have hstable : (prefixWord ++ tailWord_5543404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543404).length < 2 ^ (prefixWord ++ tailWord_5543404).sum := by decide
  have hdescent : baseEnd_5543404 < baseStart_5543404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543422 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_5543422 : Nat := 118140960795 + 5543422 * 2 ^ 59
def prefixEnd_5543422 : Nat := 4983230072969 + 3 ^ 40 * 5543422 * 2
def baseEnd_5543422 : Nat := 948813318902705189877091

theorem tailTrace_5543422 : CollatzResearch.WordTrace tailWord_5543422 prefixEnd_5543422 948813318902705189877091 := by
  unfold tailWord_5543422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25273151315392038743600065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134790140348757539965867013 25273151315392038743600065)
  ·
    refine ⟨18954863486544029057700049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25273151315392038743600065 18954863486544029057700049)
    ·
      refine ⟨14216147614908021793275037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18954863486544029057700049 14216147614908021793275037)
      ·
        refine ⟨5331055355590508172478139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14216147614908021793275037 5331055355590508172478139)
        ·
          refine ⟨7996583033385762258717209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331055355590508172478139 7996583033385762258717209)
          ·
            refine ⟨5997437275039321694037907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7996583033385762258717209 5997437275039321694037907)
            ·
              refine ⟨8996155912558982541056861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997437275039321694037907 8996155912558982541056861)
              ·
                refine ⟨3373558467209618452896323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8996155912558982541056861 3373558467209618452896323)
                ·
                  refine ⟨5060337700814427679344485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373558467209618452896323 5060337700814427679344485)
                  ·
                    refine ⟨948813318902705189877091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060337700814427679344485 948813318902705189877091)
                    ·
                      rfl

theorem cell23_5543422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_5543422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543422 prefixEnd_5543422 := by exact prefixLift 5543422
  have htrace : WordTrace (prefixWord ++ tailWord_5543422) baseStart_5543422 baseEnd_5543422 := by
    simpa [prefixWord, tailWord_5543422, baseEnd_5543422] using wordTrace_append hprefix tailTrace_5543422
  have hstable : (prefixWord ++ tailWord_5543422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543422).length < 2 ^ (prefixWord ++ tailWord_5543422).sum := by decide
  have hdescent : baseEnd_5543422 < baseStart_5543422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543438 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5543438 : Nat := 118140960795 + 5543438 * 2 ^ 59
def prefixEnd_5543438 : Nat := 4983230072969 + 3 ^ 40 * 5543438 * 2
def baseEnd_5543438 : Nat := 2846448172398587507031199

theorem tailTrace_5543438 : CollatzResearch.WordTrace tailWord_5543438 prefixEnd_5543438 2846448172398587507031199 := by
  unfold tailWord_5543438
  simp only [CollatzResearch.WordTrace]
  refine ⟨25273224261384793085172871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134790529394052229787588645 25273224261384793085172871)
  ·
    refine ⟨37909836392077189627759307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25273224261384793085172871 37909836392077189627759307)
    ·
      refine ⟨56864754588115784441638961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37909836392077189627759307 56864754588115784441638961)
      ·
        refine ⟨42648565941086838331229221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56864754588115784441638961 42648565941086838331229221)
        ·
          refine ⟨7996606113953782187105479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42648565941086838331229221 7996606113953782187105479)
          ·
            refine ⟨11994909170930673280658219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996606113953782187105479 11994909170930673280658219)
            ·
              refine ⟨17992363756396009920987329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11994909170930673280658219 17992363756396009920987329)
              ·
                refine ⟨13494272817297007440740497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17992363756396009920987329 13494272817297007440740497)
                ·
                  refine ⟨10120704612972755580555373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13494272817297007440740497 10120704612972755580555373)
                  ·
                    refine ⟨3795264229864783342708265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10120704612972755580555373 3795264229864783342708265)
                    ·
                      refine ⟨2846448172398587507031199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795264229864783342708265 2846448172398587507031199)
                      ·
                        rfl

theorem cell23_5543438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5543438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543438 prefixEnd_5543438 := by exact prefixLift 5543438
  have htrace : WordTrace (prefixWord ++ tailWord_5543438) baseStart_5543438 baseEnd_5543438 := by
    simpa [prefixWord, tailWord_5543438, baseEnd_5543438] using wordTrace_append hprefix tailTrace_5543438
  have hstable : (prefixWord ++ tailWord_5543438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543438).length < 2 ^ (prefixWord ++ tailWord_5543438).sum := by decide
  have hdescent : baseEnd_5543438 < baseStart_5543438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543445 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_5543445 : Nat := 118140960795 + 5543445 * 2 ^ 59
def prefixEnd_5543445 : Nat := 4983230072969 + 3 ^ 40 * 5543445 * 2
def baseEnd_5543445 : Nat := 2846451766763168979643667

theorem tailTrace_5543445 : CollatzResearch.WordTrace tailWord_5543445 prefixEnd_5543445 2846451766763168979643667 := by
  unfold tailWord_5543445
  simp only [CollatzResearch.WordTrace]
  refine ⟨202186049402052984876887789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134790699601368656584591859 202186049402052984876887789)
  ·
    refine ⟨75819768525769869328832921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202186049402052984876887789 75819768525769869328832921)
    ·
      refine ⟨56864826394327401996624691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75819768525769869328832921 56864826394327401996624691)
      ·
        refine ⟨85297239591491102994937037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56864826394327401996624691 85297239591491102994937037)
        ·
          refine ⟨31986464846809163623101389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85297239591491102994937037 31986464846809163623101389)
          ·
            refine ⟨11994924317553436358663021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31986464846809163623101389 11994924317553436358663021)
            ·
              refine ⟨4498096619082538634498633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11994924317553436358663021 4498096619082538634498633)
              ·
                refine ⟨3373572464311903975873975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4498096619082538634498633 3373572464311903975873975)
                ·
                  refine ⟨5060358696467855963810963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373572464311903975873975 5060358696467855963810963)
                  ·
                    refine ⟨7590538044701783945716445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060358696467855963810963 7590538044701783945716445)
                    ·
                      refine ⟨2846451766763168979643667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7590538044701783945716445 2846451766763168979643667)
                      ·
                        rfl

theorem cell23_5543445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_5543445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543445 prefixEnd_5543445 := by exact prefixLift 5543445
  have htrace : WordTrace (prefixWord ++ tailWord_5543445) baseStart_5543445 baseEnd_5543445 := by
    simpa [prefixWord, tailWord_5543445, baseEnd_5543445] using wordTrace_append hprefix tailTrace_5543445
  have hstable : (prefixWord ++ tailWord_5543445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543445).length < 2 ^ (prefixWord ++ tailWord_5543445).sum := by decide
  have hdescent : baseEnd_5543445 < baseStart_5543445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543457 : List Nat := [1, 2, 3, 2, 2, 2, 1, 10]
def baseStart_5543457 : Nat := 118140960795 + 5543457 * 2 ^ 59
def prefixEnd_5543457 : Nat := 4983230072969 + 3 ^ 40 * 5543457 * 2
def baseEnd_5543457 : Nat := 105424367723371219729393

theorem tailTrace_5543457 : CollatzResearch.WordTrace tailWord_5543457 prefixEnd_5543457 105424367723371219729393 := by
  unfold tailWord_5543457
  simp only [CollatzResearch.WordTrace]
  refine ⟨202186487078009510926324625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134790991385339673950883083 202186487078009510926324625)
  ·
    refine ⟨151639865308507133194743469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202186487078009510926324625 151639865308507133194743469)
    ·
      refine ⟨56864949490690174948028801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151639865308507133194743469 56864949490690174948028801)
      ·
        refine ⟨42648712118017631211021601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56864949490690174948028801 42648712118017631211021601)
        ·
          refine ⟨31986534088513223408266201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42648712118017631211021601 31986534088513223408266201)
          ·
            refine ⟨23989900566384917556199651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31986534088513223408266201 23989900566384917556199651)
            ·
              refine ⟨35984850849577376334299477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23989900566384917556199651 35984850849577376334299477)
              ·
                refine ⟨105424367723371219729393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35984850849577376334299477 105424367723371219729393)
                ·
                  rfl

theorem cell23_5543457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 10].length) (baseStart_5543457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543457 prefixEnd_5543457 := by exact prefixLift 5543457
  have htrace : WordTrace (prefixWord ++ tailWord_5543457) baseStart_5543457 baseEnd_5543457 := by
    simpa [prefixWord, tailWord_5543457, baseEnd_5543457] using wordTrace_append hprefix tailTrace_5543457
  have hstable : (prefixWord ++ tailWord_5543457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543457).length < 2 ^ (prefixWord ++ tailWord_5543457).sum := by decide
  have hdescent : baseEnd_5543457 < baseStart_5543457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543497 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_5543497 : Nat := 118140960795 + 5543497 * 2 ^ 59
def prefixEnd_5543497 : Nat := 4983230072969 + 3 ^ 40 * 5543497 * 2
def baseEnd_5543497 : Nat := 2846478467757202776193427

theorem tailTrace_5543497 : CollatzResearch.WordTrace tailWord_5543497 prefixEnd_5543497 2846478467757202776193427 := by
  unfold tailWord_5543497
  simp only [CollatzResearch.WordTrace]
  refine ⟨202187945997864597757780745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134791963998576398505187163 202187945997864597757780745)
  ·
    refine ⟨151640959498398448318335559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202187945997864597757780745 151640959498398448318335559)
    ·
      refine ⟨227461439247597672477503339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151640959498398448318335559 227461439247597672477503339)
      ·
        refine ⟨341192158871396508716255009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227461439247597672477503339 341192158871396508716255009)
        ·
          refine ⟨255894119153547381537191257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341192158871396508716255009 255894119153547381537191257)
          ·
            refine ⟨191920589365160536152893443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255894119153547381537191257 191920589365160536152893443)
            ·
              refine ⟨287880884047740804229340165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191920589365160536152893443 287880884047740804229340165)
              ·
                refine ⟨53977665758951400793001281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287880884047740804229340165 53977665758951400793001281)
                ·
                  refine ⟨40483249319213550594750961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53977665758951400793001281 40483249319213550594750961)
                  ·
                    refine ⟨30362436989410162946063221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40483249319213550594750961 30362436989410162946063221)
                    ·
                      refine ⟨2846478467757202776193427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30362436989410162946063221 2846478467757202776193427)
                      ·
                        rfl

theorem cell23_5543497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_5543497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543497 prefixEnd_5543497 := by exact prefixLift 5543497
  have htrace : WordTrace (prefixWord ++ tailWord_5543497) baseStart_5543497 baseEnd_5543497 := by
    simpa [prefixWord, tailWord_5543497, baseEnd_5543497] using wordTrace_append hprefix tailTrace_5543497
  have hstable : (prefixWord ++ tailWord_5543497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543497).length < 2 ^ (prefixWord ++ tailWord_5543497).sum := by decide
  have hdescent : baseEnd_5543497 < baseStart_5543497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543511 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_5543511 : Nat := 118140960795 + 5543511 * 2 ^ 59
def prefixEnd_5543511 : Nat := 4983230072969 + 3 ^ 40 * 5543511 * 2
def baseEnd_5543511 : Nat := 2846485656486365721418363

theorem tailTrace_5543511 : CollatzResearch.WordTrace tailWord_5543511 prefixEnd_5543511 2846485656486365721418363 := by
  unfold tailWord_5543511
  simp only [CollatzResearch.WordTrace]
  refine ⟨202188456619813878148790387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134792304413209252099193591 202188456619813878148790387)
  ·
    refine ⟨303282684929720817223185581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202188456619813878148790387 303282684929720817223185581)
    ·
      refine ⟨113731006848645306458694593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303282684929720817223185581 113731006848645306458694593)
      ·
        refine ⟨85298255136483979844020945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113731006848645306458694593 85298255136483979844020945)
        ·
          refine ⟨63973691352362984883015709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85298255136483979844020945 63973691352362984883015709)
          ·
            refine ⟨23990134257136119331130891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63973691352362984883015709 23990134257136119331130891)
            ·
              refine ⟨35985201385704178996696337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23990134257136119331130891 35985201385704178996696337)
              ·
                refine ⟨26988901039278134247522253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35985201385704178996696337 26988901039278134247522253)
                ·
                  refine ⟨10120837889729300342820845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26988901039278134247522253 10120837889729300342820845)
                  ·
                    refine ⟨3795314208648487628557817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10120837889729300342820845 3795314208648487628557817)
                    ·
                      refine ⟨2846485656486365721418363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795314208648487628557817 2846485656486365721418363)
                      ·
                        rfl

theorem cell23_5543511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_5543511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543511 prefixEnd_5543511 := by exact prefixLift 5543511
  have htrace : WordTrace (prefixWord ++ tailWord_5543511) baseStart_5543511 baseEnd_5543511 := by
    simpa [prefixWord, tailWord_5543511, baseEnd_5543511] using wordTrace_append hprefix tailTrace_5543511
  have hstable : (prefixWord ++ tailWord_5543511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543511).length < 2 ^ (prefixWord ++ tailWord_5543511).sum := by decide
  have hdescent : baseEnd_5543511 < baseStart_5543511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543528 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5543528 : Nat := 118140960795 + 5543528 * 2 ^ 59
def prefixEnd_5543528 : Nat := 4983230072969 + 3 ^ 40 * 5543528 * 2
def baseEnd_5543528 : Nat := 2846494385657492154905785

theorem tailTrace_5543528 : CollatzResearch.WordTrace tailWord_5543528 prefixEnd_5543528 2846494385657492154905785 := by
  unfold tailWord_5543528
  simp only [CollatzResearch.WordTrace]
  refine ⟨101094538330376145026079619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134792717773834860034772825 101094538330376145026079619)
  ·
    refine ⟨151641807495564217539119429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101094538330376145026079619 151641807495564217539119429)
    ·
      refine ⟨28432838905418290788584893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151641807495564217539119429 28432838905418290788584893)
      ·
        refine ⟨10662314589531859045719335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28432838905418290788584893 10662314589531859045719335)
        ·
          refine ⟨15993471884297788568579003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10662314589531859045719335 15993471884297788568579003)
          ·
            refine ⟨23990207826446682852868505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15993471884297788568579003 23990207826446682852868505)
            ·
              refine ⟨17992655869835012139651379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23990207826446682852868505 17992655869835012139651379)
              ·
                refine ⟨26988983804752518209477069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17992655869835012139651379 26988983804752518209477069)
                ·
                  refine ⟨10120868926782194328553901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26988983804752518209477069 10120868926782194328553901)
                  ·
                    refine ⟨3795325847543322873207713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10120868926782194328553901 3795325847543322873207713)
                    ·
                      refine ⟨2846494385657492154905785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795325847543322873207713 2846494385657492154905785)
                      ·
                        rfl

theorem cell23_5543528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5543528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543528 prefixEnd_5543528 := by exact prefixLift 5543528
  have htrace : WordTrace (prefixWord ++ tailWord_5543528) baseStart_5543528 baseEnd_5543528 := by
    simpa [prefixWord, tailWord_5543528, baseEnd_5543528] using wordTrace_append hprefix tailTrace_5543528
  have hstable : (prefixWord ++ tailWord_5543528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543528).length < 2 ^ (prefixWord ++ tailWord_5543528).sum := by decide
  have hdescent : baseEnd_5543528 < baseStart_5543528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543547 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 9]
def baseStart_5543547 : Nat := 118140960795 + 5543547 * 2 ^ 59
def prefixEnd_5543547 : Nat := 4983230072969 + 3 ^ 40 * 5543547 * 2
def baseEnd_5543547 : Nat := 316278237976658620063133

theorem tailTrace_5543547 : CollatzResearch.WordTrace tailWord_5543547 prefixEnd_5543547 316278237976658620063133 := by
  unfold tailWord_5543547
  simp only [CollatzResearch.WordTrace]
  refine ⟨202189769647683456297100895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134793179765122304198067263 202189769647683456297100895)
  ·
    refine ⟨303284654471525184445651343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202189769647683456297100895 303284654471525184445651343)
    ·
      refine ⟨454926981707287776668477015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303284654471525184445651343 454926981707287776668477015)
      ·
        refine ⟨682390472560931665002715523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454926981707287776668477015 682390472560931665002715523)
        ·
          refine ⟨1023585708841397497504073285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682390472560931665002715523 1023585708841397497504073285)
          ·
            refine ⟨191922320407762030782013741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1023585708841397497504073285 191922320407762030782013741)
            ·
              refine ⟨71970870152910761543255153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191922320407762030782013741 71970870152910761543255153)
              ·
                refine ⟨53978152614683071157441365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71970870152910761543255153 53978152614683071157441365)
                ·
                  refine ⟨316278237976658620063133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53978152614683071157441365 316278237976658620063133)
                  ·
                    rfl

theorem cell23_5543547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 9].length) (baseStart_5543547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543547 prefixEnd_5543547 := by exact prefixLift 5543547
  have htrace : WordTrace (prefixWord ++ tailWord_5543547) baseStart_5543547 baseEnd_5543547 := by
    simpa [prefixWord, tailWord_5543547, baseEnd_5543547] using wordTrace_append hprefix tailTrace_5543547
  have hstable : (prefixWord ++ tailWord_5543547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543547).length < 2 ^ (prefixWord ++ tailWord_5543547).sum := by decide
  have hdescent : baseEnd_5543547 < baseStart_5543547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543564 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 7]
def baseStart_5543564 : Nat := 118140960795 + 5543564 * 2 ^ 59
def prefixEnd_5543564 : Nat := 4983230072969 + 3 ^ 40 * 5543564 * 2
def baseEnd_5543564 : Nat := 316279207884561557117291

theorem tailTrace_5543564 : CollatzResearch.WordTrace tailWord_5543564 prefixEnd_5543564 316279207884561557117291 := by
  unfold tailWord_5543564
  simp only [CollatzResearch.WordTrace]
  refine ⟨101095194844310934100234873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134793593125747912133646497 101095194844310934100234873)
  ·
    refine ⟨75821396133233200575176155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101095194844310934100234873 75821396133233200575176155)
    ·
      refine ⟨113732094199849800862764233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75821396133233200575176155 113732094199849800862764233)
      ·
        refine ⟨85299070649887350647073175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113732094199849800862764233 85299070649887350647073175)
        ·
          refine ⟨127948605974831025970609763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85299070649887350647073175 127948605974831025970609763)
          ·
            refine ⟨191922908962246538955914645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127948605974831025970609763 191922908962246538955914645)
            ·
              refine ⟨8996386357605306513558499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 191922908962246538955914645 8996386357605306513558499)
              ·
                refine ⟨13494579536407959770337749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8996386357605306513558499 13494579536407959770337749)
                ·
                  refine ⟨316279207884561557117291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13494579536407959770337749 316279207884561557117291)
                  ·
                    rfl

theorem cell23_5543564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_5543564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543564 prefixEnd_5543564 := by exact prefixLift 5543564
  have htrace : WordTrace (prefixWord ++ tailWord_5543564) baseStart_5543564 baseEnd_5543564 := by
    simpa [prefixWord, tailWord_5543564, baseEnd_5543564] using wordTrace_append hprefix tailTrace_5543564
  have hstable : (prefixWord ++ tailWord_5543564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543564).length < 2 ^ (prefixWord ++ tailWord_5543564).sum := by decide
  have hdescent : baseEnd_5543564 < baseStart_5543564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543567 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_5543567 : Nat := 118140960795 + 5543567 * 2 ^ 59
def prefixEnd_5543567 : Nat := 4983230072969 + 3 ^ 40 * 5543567 * 2
def baseEnd_5543567 : Nat := 2846514411403017502318105

theorem tailTrace_5543567 : CollatzResearch.WordTrace tailWord_5543567 prefixEnd_5543567 2846514411403017502318105 := by
  unfold tailWord_5543567
  simp only [CollatzResearch.WordTrace]
  refine ⟨202190499107610999712828955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134793666071740666475219303 202190499107610999712828955)
  ·
    refine ⟨303285748661416499569243433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202190499107610999712828955 303285748661416499569243433)
    ·
      refine ⟨227464311496062374676932575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303285748661416499569243433 227464311496062374676932575)
      ·
        refine ⟨341196467244093562015398863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227464311496062374676932575 341196467244093562015398863)
        ·
          refine ⟨511794700866140343023098295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341196467244093562015398863 511794700866140343023098295)
          ·
            refine ⟨767692051299210514534647443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511794700866140343023098295 767692051299210514534647443)
            ·
              refine ⟨1151538076948815771801971165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767692051299210514534647443 1151538076948815771801971165)
              ·
                refine ⟨431826778855805914425739187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151538076948815771801971165 431826778855805914425739187)
                ·
                  refine ⟨647740168283708871638608781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431826778855805914425739187 647740168283708871638608781)
                  ·
                    refine ⟨242902563106390826864478293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647740168283708871638608781 242902563106390826864478293)
                    ·
                      refine ⟨2846514411403017502318105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 242902563106390826864478293 2846514411403017502318105)
                      ·
                        rfl

theorem cell23_5543567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_5543567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543567 prefixEnd_5543567 := by exact prefixLift 5543567
  have htrace : WordTrace (prefixWord ++ tailWord_5543567) baseStart_5543567 baseEnd_5543567 := by
    simpa [prefixWord, tailWord_5543567, baseEnd_5543567] using wordTrace_append hprefix tailTrace_5543567
  have hstable : (prefixWord ++ tailWord_5543567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543567).length < 2 ^ (prefixWord ++ tailWord_5543567).sum := by decide
  have hdescent : baseEnd_5543567 < baseStart_5543567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543631 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 2, 4, 2]
def baseStart_5543631 : Nat := 118140960795 + 5543631 * 2 ^ 59
def prefixEnd_5543631 : Nat := 4983230072969 + 3 ^ 40 * 5543631 * 2
def baseEnd_5543631 : Nat := 2846547274164905251917811

theorem tailTrace_5543631 : CollatzResearch.WordTrace tailWord_5543631 prefixEnd_5543631 2846547274164905251917811 := by
  unfold tailWord_5543631
  simp only [CollatzResearch.WordTrace]
  refine ⟨202192833379379138643158747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134795222252919425762105831 202192833379379138643158747)
  ·
    refine ⟨303289250069068707964738121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202192833379379138643158747 303289250069068707964738121)
    ·
      refine ⟨227466937551801530973553591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303289250069068707964738121 227466937551801530973553591)
      ·
        refine ⟨341200406327702296460330387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227466937551801530973553591 341200406327702296460330387)
        ·
          refine ⟨511800609491553444690495581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341200406327702296460330387 511800609491553444690495581)
          ·
            refine ⟨191925228559332541758935843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511800609491553444690495581 191925228559332541758935843)
            ·
              refine ⟨287887842838998812638403765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191925228559332541758935843 287887842838998812638403765)
              ·
                refine ⟨26989485266156138684850353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287887842838998812638403765 26989485266156138684850353)
                ·
                  refine ⟨20242113949617104013637765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26989485266156138684850353 20242113949617104013637765)
                  ·
                    refine ⟨3795396365553207002557081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20242113949617104013637765 3795396365553207002557081)
                    ·
                      refine ⟨2846547274164905251917811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795396365553207002557081 2846547274164905251917811)
                      ·
                        rfl

theorem cell23_5543631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4, 2].length) (baseStart_5543631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543631 prefixEnd_5543631 := by exact prefixLift 5543631
  have htrace : WordTrace (prefixWord ++ tailWord_5543631) baseStart_5543631 baseEnd_5543631 := by
    simpa [prefixWord, tailWord_5543631, baseEnd_5543631] using wordTrace_append hprefix tailTrace_5543631
  have hstable : (prefixWord ++ tailWord_5543631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543631).length < 2 ^ (prefixWord ++ tailWord_5543631).sum := by decide
  have hdescent : baseEnd_5543631 < baseStart_5543631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543645 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5543645 : Nat := 118140960795 + 5543645 * 2 ^ 59
def prefixEnd_5543645 : Nat := 4983230072969 + 3 ^ 40 * 5543645 * 2
def baseEnd_5543645 : Nat := 948851487631356065714249

theorem tailTrace_5543645 : CollatzResearch.WordTrace tailWord_5543645 prefixEnd_5543645 948851487631356065714249 := by
  unfold tailWord_5543645
  simp only [CollatzResearch.WordTrace]
  refine ⟨202193344001328419034168389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134795562667552279356112259 202193344001328419034168389)
  ·
    refine ⟨37911252000249078568906573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202193344001328419034168389 37911252000249078568906573)
    ·
      refine ⟨14216719500093404463339965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37911252000249078568906573 14216719500093404463339965)
      ·
        refine ⟨5331269812535026673752487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14216719500093404463339965 5331269812535026673752487)
        ·
          refine ⟨7996904718802540010628731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331269812535026673752487 7996904718802540010628731)
          ·
            refine ⟨11995357078203810015943097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996904718802540010628731 11995357078203810015943097)
            ·
              refine ⟨8996517808652857511957323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11995357078203810015943097 8996517808652857511957323)
              ·
                refine ⟨13494776712979286267935985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8996517808652857511957323 13494776712979286267935985)
                ·
                  refine ⟨10121082534734464700951989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13494776712979286267935985 10121082534734464700951989)
                  ·
                    refine ⟨948851487631356065714249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10121082534734464700951989 948851487631356065714249)
                    ·
                      rfl

theorem cell23_5543645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5543645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543645 prefixEnd_5543645 := by exact prefixLift 5543645
  have htrace : WordTrace (prefixWord ++ tailWord_5543645) baseStart_5543645 baseEnd_5543645 := by
    simpa [prefixWord, tailWord_5543645, baseEnd_5543645] using wordTrace_append hprefix tailTrace_5543645
  have hstable : (prefixWord ++ tailWord_5543645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543645).length < 2 ^ (prefixWord ++ tailWord_5543645).sum := by decide
  have hdescent : baseEnd_5543645 < baseStart_5543645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543674 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_5543674 : Nat := 118140960795 + 5543674 * 2 ^ 59
def prefixEnd_5543674 : Nat := 4983230072969 + 3 ^ 40 * 5543674 * 2
def baseEnd_5543674 : Nat := 2846569353833048583680113

theorem tailTrace_5543674 : CollatzResearch.WordTrace tailWord_5543674 prefixEnd_5543674 2846569353833048583680113 := by
  unfold tailWord_5543674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548600429555839246743519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134796267812148904657982717 50548600429555839246743519)
  ·
    refine ⟨75822900644333758870115279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50548600429555839246743519 75822900644333758870115279)
    ·
      refine ⟨113734350966500638305172919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75822900644333758870115279 113734350966500638305172919)
      ·
        refine ⟨170601526449750957457759379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113734350966500638305172919 170601526449750957457759379)
        ·
          refine ⟨255902289674626436186639069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170601526449750957457759379 255902289674626436186639069)
          ·
            refine ⟨95963358627984913569989651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255902289674626436186639069 95963358627984913569989651)
            ·
              refine ⟨143945037941977370354984477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95963358627984913569989651 143945037941977370354984477)
              ·
                refine ⟨53979389228241513883119179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143945037941977370354984477 53979389228241513883119179)
                ·
                  refine ⟨80969083842362270824678769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53979389228241513883119179 80969083842362270824678769)
                  ·
                    refine ⟨60726812881771703118509077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80969083842362270824678769 60726812881771703118509077)
                    ·
                      refine ⟨2846569353833048583680113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60726812881771703118509077 2846569353833048583680113)
                      ·
                        rfl

theorem cell23_5543674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_5543674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543674 prefixEnd_5543674 := by exact prefixLift 5543674
  have htrace : WordTrace (prefixWord ++ tailWord_5543674) baseStart_5543674 baseEnd_5543674 := by
    simpa [prefixWord, tailWord_5543674, baseEnd_5543674] using wordTrace_append hprefix tailTrace_5543674
  have hstable : (prefixWord ++ tailWord_5543674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543674).length < 2 ^ (prefixWord ++ tailWord_5543674).sum := by decide
  have hdescent : baseEnd_5543674 < baseStart_5543674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543701 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_5543701 : Nat := 118140960795 + 5543701 * 2 ^ 59
def prefixEnd_5543701 : Nat := 4983230072969 + 3 ^ 40 * 5543701 * 2
def baseEnd_5543701 : Nat := 948861072603573326014163

theorem tailTrace_5543701 : CollatzResearch.WordTrace tailWord_5543701 prefixEnd_5543701 948861072603573326014163 := by
  unfold tailWord_5543701
  simp only [CollatzResearch.WordTrace]
  refine ⟨202195386489125540598206957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134796924326083693732137971 202195386489125540598206957)
  ·
    refine ⟨75823269933422077724327609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202195386489125540598206957 75823269933422077724327609)
    ·
      refine ⟨56867452450066558293245707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75823269933422077724327609 56867452450066558293245707)
      ·
        refine ⟨85301178675099837439868561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56867452450066558293245707 85301178675099837439868561)
        ·
          refine ⟨63975884006324878079901421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85301178675099837439868561 63975884006324878079901421)
          ·
            refine ⟨23990956502371829279963033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63975884006324878079901421 23990956502371829279963033)
            ·
              refine ⟨17993217376778871959972275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23990956502371829279963033 17993217376778871959972275)
              ·
                refine ⟨26989826065168307939958413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17993217376778871959972275 26989826065168307939958413)
                ·
                  refine ⟨10121184774438115477484405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26989826065168307939958413 10121184774438115477484405)
                  ·
                    refine ⟨948861072603573326014163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10121184774438115477484405 948861072603573326014163)
                    ·
                      rfl

theorem cell23_5543701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_5543701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543701 prefixEnd_5543701 := by exact prefixLift 5543701
  have htrace : WordTrace (prefixWord ++ tailWord_5543701) baseStart_5543701 baseEnd_5543701 := by
    simpa [prefixWord, tailWord_5543701, baseEnd_5543701] using wordTrace_append hprefix tailTrace_5543701
  have hstable : (prefixWord ++ tailWord_5543701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543701).length < 2 ^ (prefixWord ++ tailWord_5543701).sum := by decide
  have hdescent : baseEnd_5543701 < baseStart_5543701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543708 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_5543708 : Nat := 118140960795 + 5543708 * 2 ^ 59
def prefixEnd_5543708 : Nat := 4983230072969 + 3 ^ 40 * 5543708 * 2
def baseEnd_5543708 : Nat := 2846586812175301450654957

theorem tailTrace_5543708 : CollatzResearch.WordTrace tailWord_5543708 prefixEnd_5543708 2846586812175301450654957 := by
  unfold tailWord_5543708
  simp only [CollatzResearch.WordTrace]
  refine ⟨101097820900050090396855889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134797094533400120529141185 101097820900050090396855889)
  ·
    refine ⟨75823365675037567797641917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101097820900050090396855889 75823365675037567797641917)
    ·
      refine ⟨28433762128139087924115719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75823365675037567797641917 28433762128139087924115719)
      ·
        refine ⟨42650643192208631886173579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28433762128139087924115719 42650643192208631886173579)
        ·
          refine ⟨63975964788312947829260369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42650643192208631886173579 63975964788312947829260369)
          ·
            refine ⟨47981973591234710871945277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63975964788312947829260369 47981973591234710871945277)
            ·
              refine ⟨17993240096713016576979479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47981973591234710871945277 17993240096713016576979479)
              ·
                refine ⟨26989860145069524865469219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17993240096713016576979479 26989860145069524865469219)
                ·
                  refine ⟨40484790217604287298203829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26989860145069524865469219 40484790217604287298203829)
                  ·
                    refine ⟨3795449082900401934206609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40484790217604287298203829 3795449082900401934206609)
                    ·
                      refine ⟨2846586812175301450654957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795449082900401934206609 2846586812175301450654957)
                      ·
                        rfl

theorem cell23_5543708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_5543708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543708 prefixEnd_5543708 := by exact prefixLift 5543708
  have htrace : WordTrace (prefixWord ++ tailWord_5543708) baseStart_5543708 baseEnd_5543708 := by
    simpa [prefixWord, tailWord_5543708, baseEnd_5543708] using wordTrace_append hprefix tailTrace_5543708
  have hstable : (prefixWord ++ tailWord_5543708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543708).length < 2 ^ (prefixWord ++ tailWord_5543708).sum := by decide
  have hdescent : baseEnd_5543708 < baseStart_5543708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543715 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 1, 1, 3]
def baseStart_5543715 : Nat := 118140960795 + 5543715 * 2 ^ 59
def prefixEnd_5543715 : Nat := 4983230072969 + 3 ^ 40 * 5543715 * 2
def baseEnd_5543715 : Nat := 2846590406539882923267425

theorem tailTrace_5543715 : CollatzResearch.WordTrace tailWord_5543715 prefixEnd_5543715 2846590406539882923267425 := by
  unfold tailWord_5543715
  simp only [CollatzResearch.WordTrace]
  refine ⟨202195897111074820989216599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134797264740716547326144399 202195897111074820989216599)
  ·
    refine ⟨303293845666612231483824899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202195897111074820989216599 303293845666612231483824899)
    ·
      refine ⟨454940768499918347225737349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303293845666612231483824899 454940768499918347225737349)
      ·
        refine ⟨85301394093734690104825753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 454940768499918347225737349 85301394093734690104825753)
        ·
          refine ⟨63976045570301017578619315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85301394093734690104825753 63976045570301017578619315)
          ·
            refine ⟨95964068355451526367928973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63976045570301017578619315 95964068355451526367928973)
            ·
              refine ⟨35986525633294322387973365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95964068355451526367928973 35986525633294322387973365)
              ·
                refine ⟨3373736778121342723872503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35986525633294322387973365 3373736778121342723872503)
                ·
                  refine ⟨5060605167182014085808755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373736778121342723872503 5060605167182014085808755)
                  ·
                    refine ⟨7590907750773021128713133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060605167182014085808755 7590907750773021128713133)
                    ·
                      refine ⟨2846590406539882923267425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7590907750773021128713133 2846590406539882923267425)
                      ·
                        rfl

theorem cell23_5543715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_5543715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543715 prefixEnd_5543715 := by exact prefixLift 5543715
  have htrace : WordTrace (prefixWord ++ tailWord_5543715) baseStart_5543715 baseEnd_5543715 := by
    simpa [prefixWord, tailWord_5543715, baseEnd_5543715] using wordTrace_append hprefix tailTrace_5543715
  have hstable : (prefixWord ++ tailWord_5543715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543715).length < 2 ^ (prefixWord ++ tailWord_5543715).sum := by decide
  have hdescent : baseEnd_5543715 < baseStart_5543715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543732 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5543732 : Nat := 118140960795 + 5543732 * 2 ^ 59
def prefixEnd_5543732 : Nat := 4983230072969 + 3 ^ 40 * 5543732 * 2
def baseEnd_5543732 : Nat := 2846599135711009356754847

theorem tailTrace_5543732 : CollatzResearch.WordTrace tailWord_5543732 prefixEnd_5543732 2846599135711009356754847 := by
  unfold tailWord_5543732
  simp only [CollatzResearch.WordTrace]
  refine ⟨101098258576006616446292725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134797678101342155261723633 101098258576006616446292725)
  ·
    refine ⟨9477961741500620291839943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101098258576006616446292725 9477961741500620291839943)
    ·
      refine ⟨14216942612250930437759915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9477961741500620291839943 14216942612250930437759915)
      ·
        refine ⟨21325413918376395656639873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14216942612250930437759915 21325413918376395656639873)
        ·
          refine ⟨15994060438782296742479905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21325413918376395656639873 15994060438782296742479905)
          ·
            refine ⟨11995545329086722556859929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15994060438782296742479905 11995545329086722556859929)
            ·
              refine ⟨8996658996815041917644947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11995545329086722556859929 8996658996815041917644947)
              ·
                refine ⟨13494988495222562876467421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8996658996815041917644947 13494988495222562876467421)
                ·
                  refine ⟨5060620685708461078675283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13494988495222562876467421 5060620685708461078675283)
                  ·
                    refine ⟨7590931028562691618012925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060620685708461078675283 7590931028562691618012925)
                    ·
                      refine ⟨2846599135711009356754847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7590931028562691618012925 2846599135711009356754847)
                      ·
                        rfl

theorem cell23_5543732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5543732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543732 prefixEnd_5543732 := by exact prefixLift 5543732
  have htrace : WordTrace (prefixWord ++ tailWord_5543732) baseStart_5543732 baseEnd_5543732 := by
    simpa [prefixWord, tailWord_5543732, baseEnd_5543732] using wordTrace_append hprefix tailTrace_5543732
  have hstable : (prefixWord ++ tailWord_5543732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543732).length < 2 ^ (prefixWord ++ tailWord_5543732).sum := by decide
  have hdescent : baseEnd_5543732 < baseStart_5543732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543761 : List Nat := [1, 2, 2, 1, 5, 2, 1, 9]
def baseStart_5543761 : Nat := 118140960795 + 5543761 * 2 ^ 59
def prefixEnd_5543761 : Nat := 4983230072969 + 3 ^ 40 * 5543761 * 2
def baseEnd_5543761 : Nat := 105430149135184805307119

theorem tailTrace_5543761 : CollatzResearch.WordTrace tailWord_5543761 prefixEnd_5543761 105430149135184805307119 := by
  unfold tailWord_5543761
  simp only [CollatzResearch.WordTrace]
  refine ⟨202197574868908170845391137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134798383245938780563594091 202197574868908170845391137)
  ·
    refine ⟨151648181151681128134043353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202197574868908170845391137 151648181151681128134043353)
    ·
      refine ⟨113736135863760846100532515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151648181151681128134043353 113736135863760846100532515)
      ·
        refine ⟨170604203795641269150798773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113736135863760846100532515 170604203795641269150798773)
        ·
          refine ⟨15994144105841368982887385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170604203795641269150798773 15994144105841368982887385)
          ·
            refine ⟨11995608079381026737165539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15994144105841368982887385 11995608079381026737165539)
            ·
              refine ⟨17993412119071540105748309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11995608079381026737165539 17993412119071540105748309)
              ·
                refine ⟨105430149135184805307119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17993412119071540105748309 105430149135184805307119)
                ·
                  rfl

theorem cell23_5543761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 9].length) (baseStart_5543761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543761 prefixEnd_5543761 := by exact prefixLift 5543761
  have htrace : WordTrace (prefixWord ++ tailWord_5543761) baseStart_5543761 baseEnd_5543761 := by
    simpa [prefixWord, tailWord_5543761, baseEnd_5543761] using wordTrace_append hprefix tailTrace_5543761
  have hstable : (prefixWord ++ tailWord_5543761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543761).length < 2 ^ (prefixWord ++ tailWord_5543761).sum := by decide
  have hdescent : baseEnd_5543761 < baseStart_5543761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543778 : List Nat := [3, 3, 2, 1, 2, 3, 9]
def baseStart_5543778 : Nat := 118140960795 + 5543778 * 2 ^ 59
def prefixEnd_5543778 : Nat := 4983230072969 + 3 ^ 40 * 5543778 * 2
def baseEnd_5543778 : Nat := 35143490812606372552835

theorem tailTrace_5543778 : CollatzResearch.WordTrace tailWord_5543778 prefixEnd_5543778 35143490812606372552835 := by
  unfold tailWord_5543778
  simp only [CollatzResearch.WordTrace]
  refine ⟨50549548727461645687189997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134798796606564388499173325 50549548727461645687189997)
  ·
    refine ⟨18956080772798117132696249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50549548727461645687189997 18956080772798117132696249)
    ·
      refine ⟨14217060579598587849522187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18956080772798117132696249 14217060579598587849522187)
      ·
        refine ⟨21325590869397881774283281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217060579598587849522187 21325590869397881774283281)
        ·
          refine ⟨15994193152048411330712461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21325590869397881774283281 15994193152048411330712461)
          ·
            refine ⟨5997822432018154249017173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15994193152048411330712461 5997822432018154249017173)
            ·
              refine ⟨35143490812606372552835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5997822432018154249017173 35143490812606372552835)
              ·
                rfl

theorem cell23_5543778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 9].length) (baseStart_5543778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543778 prefixEnd_5543778 := by exact prefixLift 5543778
  have htrace : WordTrace (prefixWord ++ tailWord_5543778) baseStart_5543778 baseEnd_5543778 := by
    simpa [prefixWord, tailWord_5543778, baseEnd_5543778] using wordTrace_append hprefix tailTrace_5543778
  have hstable : (prefixWord ++ tailWord_5543778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543778).length < 2 ^ (prefixWord ++ tailWord_5543778).sum := by decide
  have hdescent : baseEnd_5543778 < baseStart_5543778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543809 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5543809 : Nat := 118140960795 + 5543809 * 2 ^ 59
def prefixEnd_5543809 : Nat := 4983230072969 + 3 ^ 40 * 5543809 * 2
def baseEnd_5543809 : Nat := 2846638673721405555491993

theorem tailTrace_5543809 : CollatzResearch.WordTrace tailWord_5543809 prefixEnd_5543809 2846638673721405555491993 := by
  unfold tailWord_5543809
  simp only [CollatzResearch.WordTrace]
  refine ⟨202199325572734275043138481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134799550381822850028758987 202199325572734275043138481)
  ·
    refine ⟨151649494179550706282353861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202199325572734275043138481 151649494179550706282353861)
    ·
      refine ⟨28434280158665757427941349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151649494179550706282353861 28434280158665757427941349)
      ·
        refine ⟨5331427529749829517739003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28434280158665757427941349 5331427529749829517739003)
        ·
          refine ⟨7997141294624744276608505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331427529749829517739003 7997141294624744276608505)
          ·
            refine ⟨5997855970968558207456379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997141294624744276608505 5997855970968558207456379)
            ·
              refine ⟨8996783956452837311184569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997855970968558207456379 8996783956452837311184569)
              ·
                refine ⟨6747587967339627983388427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8996783956452837311184569 6747587967339627983388427)
                ·
                  refine ⟨10121381951009441975082641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6747587967339627983388427 10121381951009441975082641)
                  ·
                    refine ⟨7591036463257081481311981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10121381951009441975082641 7591036463257081481311981)
                    ·
                      refine ⟨2846638673721405555491993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7591036463257081481311981 2846638673721405555491993)
                      ·
                        rfl

theorem cell23_5543809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5543809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543809 prefixEnd_5543809 := by exact prefixLift 5543809
  have htrace : WordTrace (prefixWord ++ tailWord_5543809) baseStart_5543809 baseEnd_5543809 := by
    simpa [prefixWord, tailWord_5543809, baseEnd_5543809] using wordTrace_append hprefix tailTrace_5543809
  have hstable : (prefixWord ++ tailWord_5543809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543809).length < 2 ^ (prefixWord ++ tailWord_5543809).sum := by decide
  have hdescent : baseEnd_5543809 < baseStart_5543809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543822 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5543822 : Nat := 118140960795 + 5543822 * 2 ^ 59
def prefixEnd_5543822 : Nat := 4983230072969 + 3 ^ 40 * 5543822 * 2
def baseEnd_5543822 : Nat := 2846645348969914004629433

theorem tailTrace_5543822 : CollatzResearch.WordTrace tailWord_5543822 prefixEnd_5543822 2846645348969914004629433 := by
  unfold tailWord_5543822
  simp only [CollatzResearch.WordTrace]
  refine ⟨25274974965210897282920215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134799866481124785508907813 25274974965210897282920215)
  ·
    refine ⟨37912462447816345924380323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25274974965210897282920215 37912462447816345924380323)
    ·
      refine ⟨56868693671724518886570485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37912462447816345924380323 56868693671724518886570485)
      ·
        refine ⟨5331440031724173645615983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56868693671724518886570485 5331440031724173645615983)
        ·
          refine ⟨7997160047586260468423975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331440031724173645615983 7997160047586260468423975)
          ·
            refine ⟨11995740071379390702635963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7997160047586260468423975 11995740071379390702635963)
            ·
              refine ⟨17993610107069086053953945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11995740071379390702635963 17993610107069086053953945)
              ·
                refine ⟨13495207580301814540465459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17993610107069086053953945 13495207580301814540465459)
                ·
                  refine ⟨20242811370452721810698189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13495207580301814540465459 20242811370452721810698189)
                  ·
                    refine ⟨7591054263919770679011821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20242811370452721810698189 7591054263919770679011821)
                    ·
                      refine ⟨2846645348969914004629433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7591054263919770679011821 2846645348969914004629433)
                      ·
                        rfl

theorem cell23_5543822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5543822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543822 prefixEnd_5543822 := by exact prefixLift 5543822
  have htrace : WordTrace (prefixWord ++ tailWord_5543822) baseStart_5543822 baseEnd_5543822 := by
    simpa [prefixWord, tailWord_5543822, baseEnd_5543822] using wordTrace_append hprefix tailTrace_5543822
  have hstable : (prefixWord ++ tailWord_5543822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543822).length < 2 ^ (prefixWord ++ tailWord_5543822).sum := by decide
  have hdescent : baseEnd_5543822 < baseStart_5543822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543845 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_5543845 : Nat := 118140960795 + 5543845 * 2 ^ 59
def prefixEnd_5543845 : Nat := 4983230072969 + 3 ^ 40 * 5543845 * 2
def baseEnd_5543845 : Nat := 2846657159024967414641827

theorem tailTrace_5543845 : CollatzResearch.WordTrace tailWord_5543845 prefixEnd_5543845 2846657159024967414641827 := by
  unfold tailWord_5543845
  simp only [CollatzResearch.WordTrace]
  refine ⟨202200638600603853191448989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134800425733735902127632659 202200638600603853191448989)
  ·
    refine ⟨75825239475226444946793371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202200638600603853191448989 75825239475226444946793371)
    ·
      refine ⟨113737859212839667420190057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75825239475226444946793371 113737859212839667420190057)
      ·
        refine ⟨85303394409629750565142543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113737859212839667420190057 85303394409629750565142543)
        ·
          refine ⟨127955091614444625847713815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85303394409629750565142543 127955091614444625847713815)
          ·
            refine ⟨191932637421666938771570723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127955091614444625847713815 191932637421666938771570723)
            ·
              refine ⟨287898956132500408157356085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191932637421666938771570723 287898956132500408157356085)
              ·
                refine ⟨26990527137421913264752133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287898956132500408157356085 26990527137421913264752133)
                ·
                  refine ⟨5060723838266608737141025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26990527137421913264752133 5060723838266608737141025)
                  ·
                    refine ⟨3795542878699956552855769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5060723838266608737141025 3795542878699956552855769)
                    ·
                      refine ⟨2846657159024967414641827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795542878699956552855769 2846657159024967414641827)
                      ·
                        rfl

theorem cell23_5543845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_5543845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543845 prefixEnd_5543845 := by exact prefixLift 5543845
  have htrace : WordTrace (prefixWord ++ tailWord_5543845) baseStart_5543845 baseEnd_5543845 := by
    simpa [prefixWord, tailWord_5543845, baseEnd_5543845] using wordTrace_append hprefix tailTrace_5543845
  have hstable : (prefixWord ++ tailWord_5543845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543845).length < 2 ^ (prefixWord ++ tailWord_5543845).sum := by decide
  have hdescent : baseEnd_5543845 < baseStart_5543845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543881 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_5543881 : Nat := 118140960795 + 5543881 * 2 ^ 59
def prefixEnd_5543881 : Nat := 4983230072969 + 3 ^ 40 * 5543881 * 2
def baseEnd_5543881 : Nat := 948891881442843091263887

theorem tailTrace_5543881 : CollatzResearch.WordTrace tailWord_5543881 prefixEnd_5543881 948891881442843091263887 := by
  unfold tailWord_5543881
  simp only [CollatzResearch.WordTrace]
  refine ⟨202201951628473431339759497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134801301085648954226506331 202201951628473431339759497)
  ·
    refine ⟨151651463721355073504819623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202201951628473431339759497 151651463721355073504819623)
    ·
      refine ⟨227477195582032610257229435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151651463721355073504819623 227477195582032610257229435)
      ·
        refine ⟨341215793373048915385844153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227477195582032610257229435 341215793373048915385844153)
        ·
          refine ⟨255911845029786686539383115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341215793373048915385844153 255911845029786686539383115)
          ·
            refine ⟨383867767544680029809074673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255911845029786686539383115 383867767544680029809074673)
            ·
              refine ⟨287900825658510022356806005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383867767544680029809074673 287900825658510022356806005)
              ·
                refine ⟨26990702405485314595950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287900825658510022356806005 26990702405485314595950563)
                ·
                  refine ⟨40486053608227971893925845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26990702405485314595950563 40486053608227971893925845)
                  ·
                    refine ⟨948891881442843091263887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40486053608227971893925845 948891881442843091263887)
                    ·
                      rfl

theorem cell23_5543881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_5543881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543881 prefixEnd_5543881 := by exact prefixLift 5543881
  have htrace : WordTrace (prefixWord ++ tailWord_5543881) baseStart_5543881 baseEnd_5543881 := by
    simpa [prefixWord, tailWord_5543881, baseEnd_5543881] using wordTrace_append hprefix tailTrace_5543881
  have hstable : (prefixWord ++ tailWord_5543881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543881).length < 2 ^ (prefixWord ++ tailWord_5543881).sum := by decide
  have hdescent : baseEnd_5543881 < baseStart_5543881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543962 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_5543962 : Nat := 118140960795 + 5543962 * 2 ^ 59
def prefixEnd_5543962 : Nat := 4983230072969 + 3 ^ 40 * 5543962 * 2
def baseEnd_5543962 : Nat := 948905745420514485626263

theorem tailTrace_5543962 : CollatzResearch.WordTrace tailWord_5543962 prefixEnd_5543962 948905745420514485626263 := by
  unfold tailWord_5543962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50551226485294995543364535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134803270627453321448972093 50551226485294995543364535)
  ·
    refine ⟨75826839727942493315046803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50551226485294995543364535 75826839727942493315046803)
    ·
      refine ⟨113740259591913739972570205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75826839727942493315046803 113740259591913739972570205)
      ·
        refine ⟨42652597346967652489713827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113740259591913739972570205 42652597346967652489713827)
        ·
          refine ⟨63978896020451478734570741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42652597346967652489713827 63978896020451478734570741)
          ·
            refine ⟨5998021501917326131366007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63978896020451478734570741 5998021501917326131366007)
            ·
              refine ⟨8997032252875989197049011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998021501917326131366007 8997032252875989197049011)
              ·
                refine ⟨13495548379313983795573517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997032252875989197049011 13495548379313983795573517)
                ·
                  refine ⟨5060830642242743923340069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13495548379313983795573517 5060830642242743923340069)
                  ·
                    refine ⟨948905745420514485626263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060830642242743923340069 948905745420514485626263)
                    ·
                      rfl

theorem cell23_5543962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_5543962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543962 prefixEnd_5543962 := by exact prefixLift 5543962
  have htrace : WordTrace (prefixWord ++ tailWord_5543962) baseStart_5543962 baseEnd_5543962 := by
    simpa [prefixWord, tailWord_5543962, baseEnd_5543962] using wordTrace_append hprefix tailTrace_5543962
  have hstable : (prefixWord ++ tailWord_5543962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543962).length < 2 ^ (prefixWord ++ tailWord_5543962).sum := by decide
  have hdescent : baseEnd_5543962 < baseStart_5543962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5543995 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 6, 3, 2]
def baseStart_5543995 : Nat := 118140960795 + 5543995 * 2 ^ 59
def prefixEnd_5543995 : Nat := 4983230072969 + 3 ^ 40 * 5543995 * 2
def baseEnd_5543995 : Nat := 2846734181123141827766137

theorem tailTrace_5543995 : CollatzResearch.WordTrace tailWord_5543995 prefixEnd_5543995 2846734181123141827766137 := by
  unfold tailWord_5543995
  simp only [CollatzResearch.WordTrace]
  refine ⟨202206109550060428809409439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134804073033373619206272959 202206109550060428809409439)
  ·
    refine ⟨303309164325090643214114159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202206109550060428809409439 303309164325090643214114159)
    ·
      refine ⟨454963746487635964821171239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303309164325090643214114159 454963746487635964821171239)
      ·
        refine ⟨682445619731453947231756859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454963746487635964821171239 682445619731453947231756859)
        ·
          refine ⟨1023668429597180920847635289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682445619731453947231756859 1023668429597180920847635289)
          ·
            refine ⟨767751322197885690635726467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023668429597180920847635289 767751322197885690635726467)
            ·
              refine ⟨1151626983296828535953589701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767751322197885690635726467 1151626983296828535953589701)
              ·
                refine ⟨215930059368155350491298069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1151626983296828535953589701 215930059368155350491298069)
                ·
                  refine ⟨10121721532882282054279597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215930059368155350491298069 10121721532882282054279597)
                  ·
                    refine ⟨3795645574830855770354849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10121721532882282054279597 3795645574830855770354849)
                    ·
                      refine ⟨2846734181123141827766137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795645574830855770354849 2846734181123141827766137)
                      ·
                        rfl

theorem cell23_5543995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 3, 2].length) (baseStart_5543995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5543995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5543995 prefixEnd_5543995 := by exact prefixLift 5543995
  have htrace : WordTrace (prefixWord ++ tailWord_5543995) baseStart_5543995 baseEnd_5543995 := by
    simpa [prefixWord, tailWord_5543995, baseEnd_5543995] using wordTrace_append hprefix tailTrace_5543995
  have hstable : (prefixWord ++ tailWord_5543995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5543995).length < 2 ^ (prefixWord ++ tailWord_5543995).sum := by decide
  have hdescent : baseEnd_5543995 < baseStart_5543995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5543995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544012 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5544012 : Nat := 118140960795 + 5544012 * 2 ^ 59
def prefixEnd_5544012 : Nat := 4983230072969 + 3 ^ 40 * 5544012 * 2
def baseEnd_5544012 : Nat := 2846742910294268261253559

theorem tailTrace_5544012 : CollatzResearch.WordTrace tailWord_5544012 prefixEnd_5544012 2846742910294268261253559 := by
  unfold tailWord_5544012
  simp only [CollatzResearch.WordTrace]
  refine ⟨101103364795499420356389145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134804486393999227141852193 101103364795499420356389145)
  ·
    refine ⟨75827523596624565267291859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101103364795499420356389145 75827523596624565267291859)
    ·
      refine ⟨113741285394936847900937789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75827523596624565267291859 113741285394936847900937789)
      ·
        refine ⟨42652982023101317962851671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113741285394936847900937789 42652982023101317962851671)
        ·
          refine ⟨63979473034651976944277507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42652982023101317962851671 63979473034651976944277507)
          ·
            refine ⟨95969209551977965416416261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63979473034651976944277507 95969209551977965416416261)
            ·
              refine ⟨17994226790995868515578049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95969209551977965416416261 17994226790995868515578049)
              ·
                refine ⟨13495670093246901386683537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17994226790995868515578049 13495670093246901386683537)
                ·
                  refine ⟨10121752569935176040012653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13495670093246901386683537 10121752569935176040012653)
                  ·
                    refine ⟨3795657213725691015004745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10121752569935176040012653 3795657213725691015004745)
                    ·
                      refine ⟨2846742910294268261253559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795657213725691015004745 2846742910294268261253559)
                      ·
                        rfl

theorem cell23_5544012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5544012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544012 prefixEnd_5544012 := by exact prefixLift 5544012
  have htrace : WordTrace (prefixWord ++ tailWord_5544012) baseStart_5544012 baseEnd_5544012 := by
    simpa [prefixWord, tailWord_5544012, baseEnd_5544012] using wordTrace_append hprefix tailTrace_5544012
  have hstable : (prefixWord ++ tailWord_5544012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544012).length < 2 ^ (prefixWord ++ tailWord_5544012).sum := by decide
  have hdescent : baseEnd_5544012 < baseStart_5544012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544055 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_5544055 : Nat := 118140960795 + 5544055 * 2 ^ 59
def prefixEnd_5544055 : Nat := 4983230072969 + 3 ^ 40 * 5544055 * 2
def baseEnd_5544055 : Nat := 2846764989962411593015861

theorem tailTrace_5544055 : CollatzResearch.WordTrace tailWord_5544055 prefixEnd_5544055 2846764989962411593015861 := by
  unfold tailWord_5544055
  simp only [CollatzResearch.WordTrace]
  refine ⟨202208297929843059056593619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134805531953228706037729079 202208297929843059056593619)
  ·
    refine ⟨303312446894764588584890429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202208297929843059056593619 303312446894764588584890429)
    ·
      refine ⟨113742167585536720719333911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303312446894764588584890429 113742167585536720719333911)
      ·
        refine ⟨170613251378305081079000867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113742167585536720719333911 170613251378305081079000867)
        ·
          refine ⟨255919877067457621618501301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170613251378305081079000867 255919877067457621618501301)
          ·
            refine ⟨23992488475074152026734497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255919877067457621618501301 23992488475074152026734497)
            ·
              refine ⟨17994366356305614020050873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23992488475074152026734497 17994366356305614020050873)
              ·
                refine ⟨13495774767229210515038155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17994366356305614020050873 13495774767229210515038155)
                ·
                  refine ⟨20243662150843815772557233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13495774767229210515038155 20243662150843815772557233)
                  ·
                    refine ⟨15182746613132861829417925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20243662150843815772557233 15182746613132861829417925)
                    ·
                      refine ⟨2846764989962411593015861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15182746613132861829417925 2846764989962411593015861)
                      ·
                        rfl

theorem cell23_5544055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_5544055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544055 prefixEnd_5544055 := by exact prefixLift 5544055
  have htrace : WordTrace (prefixWord ++ tailWord_5544055) baseStart_5544055 baseEnd_5544055 := by
    simpa [prefixWord, tailWord_5544055, baseEnd_5544055] using wordTrace_append hprefix tailTrace_5544055
  have hstable : (prefixWord ++ tailWord_5544055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544055).length < 2 ^ (prefixWord ++ tailWord_5544055).sum := by decide
  have hdescent : baseEnd_5544055 < baseStart_5544055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544065 : List Nat := [1, 2, 4, 2, 3, 1, 10]
def baseStart_5544065 : Nat := 118140960795 + 5544065 * 2 ^ 59
def prefixEnd_5544065 : Nat := 4983230072969 + 3 ^ 40 * 5544065 * 2
def baseEnd_5544065 : Nat := 35145310182332796961615

theorem tailTrace_5544065 : CollatzResearch.WordTrace tailWord_5544065 prefixEnd_5544065 35145310182332796961615 := by
  unfold tailWord_5544065
  simp only [CollatzResearch.WordTrace]
  refine ⟨202208662659806830764457649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134805775106537887176305099 202208662659806830764457649)
  ·
    refine ⟨151656496994855123073343237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202208662659806830764457649 151656496994855123073343237)
    ·
      refine ⟨28435593186535335576251857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151656496994855123073343237 28435593186535335576251857)
      ·
        refine ⟨21326694889901501682188893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28435593186535335576251857 21326694889901501682188893)
        ·
          refine ⟨7997510583713063130820835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21326694889901501682188893 7997510583713063130820835)
          ·
            refine ⟨11996265875569594696231253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7997510583713063130820835 11996265875569594696231253)
            ·
              refine ⟨35145310182332796961615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11996265875569594696231253 35145310182332796961615)
              ·
                rfl

theorem cell23_5544065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 10].length) (baseStart_5544065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544065 prefixEnd_5544065 := by exact prefixLift 5544065
  have htrace : WordTrace (prefixWord ++ tailWord_5544065) baseStart_5544065 baseEnd_5544065 := by
    simpa [prefixWord, tailWord_5544065, baseEnd_5544065] using wordTrace_append hprefix tailTrace_5544065
  have hstable : (prefixWord ++ tailWord_5544065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544065).length < 2 ^ (prefixWord ++ tailWord_5544065).sum := by decide
  have hdescent : baseEnd_5544065 < baseStart_5544065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544069 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_5544069 : Nat := 118140960795 + 5544069 * 2 ^ 59
def prefixEnd_5544069 : Nat := 4983230072969 + 3 ^ 40 * 5544069 * 2
def baseEnd_5544069 : Nat := 948924059563858179413599

theorem tailTrace_5544069 : CollatzResearch.WordTrace tailWord_5544069 prefixEnd_5544069 948924059563858179413599 := by
  unfold tailWord_5544069
  simp only [CollatzResearch.WordTrace]
  refine ⟨202208808551792339447603261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134805872367861559631735507 202208808551792339447603261)
  ·
    refine ⟨75828303206922127292851223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202208808551792339447603261 75828303206922127292851223)
    ·
      refine ⟨113742454810383190939276835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75828303206922127292851223 113742454810383190939276835)
      ·
        refine ⟨170613682215574786408915253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113742454810383190939276835 170613682215574786408915253)
        ·
          refine ⟨15995032707710136225835805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170613682215574786408915253 15995032707710136225835805)
          ·
            refine ⟨5998137265391301084688427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15995032707710136225835805 5998137265391301084688427)
            ·
              refine ⟨8997205898086951627032641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998137265391301084688427 8997205898086951627032641)
              ·
                refine ⟨6747904423565213720274481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8997205898086951627032641 6747904423565213720274481)
                ·
                  refine ⟨5060928317673910290205861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6747904423565213720274481 5060928317673910290205861)
                  ·
                    refine ⟨948924059563858179413599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060928317673910290205861 948924059563858179413599)
                    ·
                      rfl

theorem cell23_5544069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_5544069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544069 prefixEnd_5544069 := by exact prefixLift 5544069
  have htrace : WordTrace (prefixWord ++ tailWord_5544069) baseStart_5544069 baseEnd_5544069 := by
    simpa [prefixWord, tailWord_5544069, baseEnd_5544069] using wordTrace_append hprefix tailTrace_5544069
  have hstable : (prefixWord ++ tailWord_5544069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544069).length < 2 ^ (prefixWord ++ tailWord_5544069).sum := by decide
  have hdescent : baseEnd_5544069 < baseStart_5544069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544109 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_5544109 : Nat := 118140960795 + 5544109 * 2 ^ 59
def prefixEnd_5544109 : Nat := 4983230072969 + 3 ^ 40 * 5544109 * 2
def baseEnd_5544109 : Nat := 2846792717917754381740613

theorem tailTrace_5544109 : CollatzResearch.WordTrace tailWord_5544109 prefixEnd_5544109 2846792717917754381740613 := by
  unfold tailWord_5544109
  simp only [CollatzResearch.WordTrace]
  refine ⟨202210267471647426279059381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134806844981098284186039587 202210267471647426279059381)
  ·
    refine ⟨18957212575466946213661817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202210267471647426279059381 18957212575466946213661817)
    ·
      refine ⟨14217909431600209660246363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18957212575466946213661817 14217909431600209660246363)
      ·
        refine ⟨21326864147400314490369545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217909431600209660246363 21326864147400314490369545)
        ·
          refine ⟨15995148110550235867777159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21326864147400314490369545 15995148110550235867777159)
          ·
            refine ⟨23992722165825353801665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15995148110550235867777159 23992722165825353801665739)
            ·
              refine ⟨35989083248738030702498609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23992722165825353801665739 35989083248738030702498609)
              ·
                refine ⟨26991812436553523026873957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35989083248738030702498609 26991812436553523026873957)
                ·
                  refine ⟨5060964831853785567538867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26991812436553523026873957 5060964831853785567538867)
                  ·
                    refine ⟨7591447247780678351308301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5060964831853785567538867 7591447247780678351308301)
                    ·
                      refine ⟨2846792717917754381740613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7591447247780678351308301 2846792717917754381740613)
                      ·
                        rfl

theorem cell23_5544109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_5544109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544109 prefixEnd_5544109 := by exact prefixLift 5544109
  have htrace : WordTrace (prefixWord ++ tailWord_5544109) baseStart_5544109 baseEnd_5544109 := by
    simpa [prefixWord, tailWord_5544109, baseEnd_5544109] using wordTrace_append hprefix tailTrace_5544109
  have hstable : (prefixWord ++ tailWord_5544109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544109).length < 2 ^ (prefixWord ++ tailWord_5544109).sum := by decide
  have hdescent : baseEnd_5544109 < baseStart_5544109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544116 : List Nat := [2, 5, 3, 1, 1, 2, 9]
def baseStart_5544116 : Nat := 118140960795 + 5544116 * 2 ^ 59
def prefixEnd_5544116 : Nat := 4983230072969 + 3 ^ 40 * 5544116 * 2
def baseEnd_5544116 : Nat := 35145633484967109313001

theorem tailTrace_5544116 : CollatzResearch.WordTrace tailWord_5544116 prefixEnd_5544116 35145633484967109313001 := by
  unfold tailWord_5544116
  simp only [CollatzResearch.WordTrace]
  refine ⟨101105261391311033237282101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134807015188414710983042801 101105261391311033237282101)
  ·
    refine ⟨9478618255435409365995197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101105261391311033237282101 9478618255435409365995197)
    ·
      refine ⟨3554481845788278512248199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9478618255435409365995197 3554481845788278512248199)
      ·
        refine ⟨5331722768682417768372299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554481845788278512248199 5331722768682417768372299)
        ·
          refine ⟨7997584153023626652558449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331722768682417768372299 7997584153023626652558449)
          ·
            refine ⟨5998188114767719989418837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997584153023626652558449 5998188114767719989418837)
            ·
              refine ⟨35145633484967109313001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5998188114767719989418837 35145633484967109313001)
              ·
                rfl

theorem cell23_5544116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 9].length) (baseStart_5544116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544116 prefixEnd_5544116 := by exact prefixLift 5544116
  have htrace : WordTrace (prefixWord ++ tailWord_5544116) baseStart_5544116 baseEnd_5544116 := by
    simpa [prefixWord, tailWord_5544116, baseEnd_5544116] using wordTrace_append hprefix tailTrace_5544116
  have hstable : (prefixWord ++ tailWord_5544116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544116).length < 2 ^ (prefixWord ++ tailWord_5544116).sum := by decide
  have hdescent : baseEnd_5544116 < baseStart_5544116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544119 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_5544119 : Nat := 118140960795 + 5544119 * 2 ^ 59
def prefixEnd_5544119 : Nat := 4983230072969 + 3 ^ 40 * 5544119 * 2
def baseEnd_5544119 : Nat := 2846797852724299342615567

theorem tailTrace_5544119 : CollatzResearch.WordTrace tailWord_5544119 prefixEnd_5544119 2846797852724299342615567 := by
  unfold tailWord_5544119
  simp only [CollatzResearch.WordTrace]
  refine ⟨202210632201611197986923411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134807088134407465324615607 202210632201611197986923411)
  ·
    refine ⟨303315948302416796980385117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202210632201611197986923411 303315948302416796980385117)
    ·
      refine ⟨113743480613406298867644419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303315948302416796980385117 113743480613406298867644419)
      ·
        refine ⟨170615220920109448301466629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113743480613406298867644419 170615220920109448301466629)
        ·
          refine ⟨31990353922520521556524993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170615220920109448301466629 31990353922520521556524993)
          ·
            refine ⟨23992765441890391167393745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31990353922520521556524993 23992765441890391167393745)
            ·
              refine ⟨17994574081417793375545309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23992765441890391167393745 17994574081417793375545309)
              ·
                refine ⟨6747965280531672515829491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17994574081417793375545309 6747965280531672515829491)
                ·
                  refine ⟨10121947920797508773744237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6747965280531672515829491 10121947920797508773744237)
                  ·
                    refine ⟨3795730470299065790154089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10121947920797508773744237 3795730470299065790154089)
                    ·
                      refine ⟨2846797852724299342615567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795730470299065790154089 2846797852724299342615567)
                      ·
                        rfl

theorem cell23_5544119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_5544119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544119 prefixEnd_5544119 := by exact prefixLift 5544119
  have htrace : WordTrace (prefixWord ++ tailWord_5544119) baseStart_5544119 baseEnd_5544119 := by
    simpa [prefixWord, tailWord_5544119, baseEnd_5544119] using wordTrace_append hprefix tailTrace_5544119
  have hstable : (prefixWord ++ tailWord_5544119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544119).length < 2 ^ (prefixWord ++ tailWord_5544119).sum := by decide
  have hdescent : baseEnd_5544119 < baseStart_5544119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544145 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_5544145 : Nat := 118140960795 + 5544145 * 2 ^ 59
def prefixEnd_5544145 : Nat := 4983230072969 + 3 ^ 40 * 5544145 * 2
def baseEnd_5544145 : Nat := 2846811203221316240890447

theorem tailTrace_5544145 : CollatzResearch.WordTrace tailWord_5544145 prefixEnd_5544145 2846811203221316240890447 := by
  unfold tailWord_5544145
  simp only [CollatzResearch.WordTrace]
  refine ⟨202211580499517004427369889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134807720333011336284913259 202211580499517004427369889)
  ·
    refine ⟨151658685374637753320527417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202211580499517004427369889 151658685374637753320527417)
    ·
      refine ⟨113744014030978314990395563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151658685374637753320527417 113744014030978314990395563)
      ·
        refine ⟨170616021046467472485593345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113744014030978314990395563 170616021046467472485593345)
        ·
          refine ⟨127962015784850604364195009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170616021046467472485593345 127962015784850604364195009)
          ·
            refine ⟨95971511838637953273146257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127962015784850604364195009 95971511838637953273146257)
            ·
              refine ⟨71978633878978464954859693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95971511838637953273146257 71978633878978464954859693)
              ·
                refine ⟨26991987704616924358072385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71978633878978464954859693 26991987704616924358072385)
                ·
                  refine ⟨20243990778462693268554289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26991987704616924358072385 20243990778462693268554289)
                  ·
                    refine ⟨15182993083847019951415717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20243990778462693268554289 15182993083847019951415717)
                    ·
                      refine ⟨2846811203221316240890447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15182993083847019951415717 2846811203221316240890447)
                      ·
                        rfl

theorem cell23_5544145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_5544145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544145 prefixEnd_5544145 := by exact prefixLift 5544145
  have htrace : WordTrace (prefixWord ++ tailWord_5544145) baseStart_5544145 baseEnd_5544145 := by
    simpa [prefixWord, tailWord_5544145, baseEnd_5544145] using wordTrace_append hprefix tailTrace_5544145
  have hstable : (prefixWord ++ tailWord_5544145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544145).length < 2 ^ (prefixWord ++ tailWord_5544145).sum := by decide
  have hdescent : baseEnd_5544145 < baseStart_5544145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544172 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 5]
def baseStart_5544172 : Nat := 118140960795 + 5544172 * 2 ^ 59
def prefixEnd_5544172 : Nat := 4983230072969 + 3 ^ 40 * 5544172 * 2
def baseEnd_5544172 : Nat := 316313896355443070583647

theorem tailTrace_5544172 : CollatzResearch.WordTrace tailWord_5544172 prefixEnd_5544172 316313896355443070583647 := by
  unfold tailWord_5544172
  simp only [CollatzResearch.WordTrace]
  refine ⟨101106282635209594019301385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134808376846946125359068513 101106282635209594019301385)
  ·
    refine ⟨75829711976407195514476039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101106282635209594019301385 75829711976407195514476039)
    ·
      refine ⟨113744567964610793271714059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75829711976407195514476039 113744567964610793271714059)
      ·
        refine ⟨170616851946916189907571089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113744567964610793271714059 170616851946916189907571089)
        ·
          refine ⟨127962638960187142430678317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170616851946916189907571089 127962638960187142430678317)
          ·
            refine ⟨47985989610070178411504369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127962638960187142430678317 47985989610070178411504369)
            ·
              refine ⟨35989492207552633808628277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47985989610070178411504369 35989492207552633808628277)
              ·
                refine ⟨3374014894458059419558901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35989492207552633808628277 3374014894458059419558901)
                ·
                  refine ⟨316313896355443070583647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3374014894458059419558901 316313896355443070583647)
                  ·
                    rfl

theorem cell23_5544172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_5544172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544172 prefixEnd_5544172 := by exact prefixLift 5544172
  have htrace : WordTrace (prefixWord ++ tailWord_5544172) baseStart_5544172 baseEnd_5544172 := by
    simpa [prefixWord, tailWord_5544172, baseEnd_5544172] using wordTrace_append hprefix tailTrace_5544172
  have hstable : (prefixWord ++ tailWord_5544172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544172).length < 2 ^ (prefixWord ++ tailWord_5544172).sum := by decide
  have hdescent : baseEnd_5544172 < baseStart_5544172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544185 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_5544185 : Nat := 118140960795 + 5544185 * 2 ^ 59
def prefixEnd_5544185 : Nat := 4983230072969 + 3 ^ 40 * 5544185 * 2
def baseEnd_5544185 : Nat := 948943914149165361463421

theorem tailTrace_5544185 : CollatzResearch.WordTrace tailWord_5544185 prefixEnd_5544185 948943914149165361463421 := by
  unfold tailWord_5544185
  simp only [CollatzResearch.WordTrace]
  refine ⟨202213039419372091258826009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134808692946248060839217339 202213039419372091258826009)
  ·
    refine ⟨151659779564529068444119507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202213039419372091258826009 151659779564529068444119507)
    ·
      refine ⟨227489669346793602666179261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151659779564529068444119507 227489669346793602666179261)
      ·
        refine ⟨85308626005047600999817223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227489669346793602666179261 85308626005047600999817223)
        ·
          refine ⟨127962939007571401499725835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85308626005047600999817223 127962939007571401499725835)
          ·
            refine ⟨191944408511357102249588753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127962939007571401499725835 191944408511357102249588753)
            ·
              refine ⟨143958306383517826687191565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191944408511357102249588753 143958306383517826687191565)
              ·
                refine ⟨53984364893819185007696837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143958306383517826687191565 53984364893819185007696837)
                ·
                  refine ⟨10122068417591097188943157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53984364893819185007696837 10122068417591097188943157)
                  ·
                    refine ⟨948943914149165361463421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10122068417591097188943157 948943914149165361463421)
                    ·
                      rfl

theorem cell23_5544185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_5544185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544185 prefixEnd_5544185 := by exact prefixLift 5544185
  have htrace : WordTrace (prefixWord ++ tailWord_5544185) baseStart_5544185 baseEnd_5544185 := by
    simpa [prefixWord, tailWord_5544185, baseEnd_5544185] using wordTrace_append hprefix tailTrace_5544185
  have hstable : (prefixWord ++ tailWord_5544185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544185).length < 2 ^ (prefixWord ++ tailWord_5544185).sum := by decide
  have hdescent : baseEnd_5544185 < baseStart_5544185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544192 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2]
def baseStart_5544192 : Nat := 118140960795 + 5544192 * 2 ^ 59
def prefixEnd_5544192 : Nat := 4983230072969 + 3 ^ 40 * 5544192 * 2
def baseEnd_5544192 : Nat := 2846835336812077557002731

theorem tailTrace_5544192 : CollatzResearch.WordTrace tailWord_5544192 prefixEnd_5544192 2846835336812077557002731 := by
  unfold tailWord_5544192
  simp only [CollatzResearch.WordTrace]
  refine ⟨101106647365173365727165415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134808863153564487636220553 101106647365173365727165415)
  ·
    refine ⟨151659971047760048590748123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101106647365173365727165415 151659971047760048590748123)
    ·
      refine ⟨227489956571640072886122185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151659971047760048590748123 227489956571640072886122185)
      ·
        refine ⟨170617467428730054664591639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227489956571640072886122185 170617467428730054664591639)
        ·
          refine ⟨255926201143095081996887459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170617467428730054664591639 255926201143095081996887459)
          ·
            refine ⟨383889301714642622995331189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255926201143095081996887459 383889301714642622995331189)
            ·
              refine ⟨35989622035747745905812299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383889301714642622995331189 35989622035747745905812299)
              ·
                refine ⟨53984433053621618858718449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35989622035747745905812299 53984433053621618858718449)
                ·
                  refine ⟨40488324790216214144038837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53984433053621618858718449 40488324790216214144038837)
                  ·
                    refine ⟨3795780449082770076003641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40488324790216214144038837 3795780449082770076003641)
                    ·
                      refine ⟨2846835336812077557002731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795780449082770076003641 2846835336812077557002731)
                      ·
                        rfl

theorem cell23_5544192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_5544192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544192 prefixEnd_5544192 := by exact prefixLift 5544192
  have htrace : WordTrace (prefixWord ++ tailWord_5544192) baseStart_5544192 baseEnd_5544192 := by
    simpa [prefixWord, tailWord_5544192, baseEnd_5544192] using wordTrace_append hprefix tailTrace_5544192
  have hstable : (prefixWord ++ tailWord_5544192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544192).length < 2 ^ (prefixWord ++ tailWord_5544192).sum := by decide
  have hdescent : baseEnd_5544192 < baseStart_5544192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544195 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_5544195 : Nat := 118140960795 + 5544195 * 2 ^ 59
def prefixEnd_5544195 : Nat := 4983230072969 + 3 ^ 40 * 5544195 * 2
def baseEnd_5544195 : Nat := 2846836877254041045265217

theorem tailTrace_5544195 : CollatzResearch.WordTrace tailWord_5544195 prefixEnd_5544195 2846836877254041045265217 := by
  unfold tailWord_5544195
  simp only [CollatzResearch.WordTrace]
  refine ⟨202213404149335862966690039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134808936099557241977793359 202213404149335862966690039)
  ·
    refine ⟨303320106224003794450035059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202213404149335862966690039 303320106224003794450035059)
    ·
      refine ⟨454980159336005691675052589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303320106224003794450035059 454980159336005691675052589)
      ·
        refine ⟨170617559751002134378144721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454980159336005691675052589 170617559751002134378144721)
        ·
          refine ⟨127963169813251600783608541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170617559751002134378144721 127963169813251600783608541)
          ·
            refine ⟨47986188679969350293853203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127963169813251600783608541 47986188679969350293853203)
            ·
              refine ⟨71979283019954025440779805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47986188679969350293853203 71979283019954025440779805)
              ·
                refine ⟨26992231132482759540292427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71979283019954025440779805 26992231132482759540292427)
                ·
                  refine ⟨40488346698724139310438641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26992231132482759540292427 40488346698724139310438641)
                  ·
                    refine ⟨30366260024043104482828981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40488346698724139310438641 30366260024043104482828981)
                    ·
                      refine ⟨2846836877254041045265217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30366260024043104482828981 2846836877254041045265217)
                      ·
                        rfl

theorem cell23_5544195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_5544195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544195 prefixEnd_5544195 := by exact prefixLift 5544195
  have htrace : WordTrace (prefixWord ++ tailWord_5544195) baseStart_5544195 baseEnd_5544195 := by
    simpa [prefixWord, tailWord_5544195, baseEnd_5544195] using wordTrace_append hprefix tailTrace_5544195
  have hstable : (prefixWord ++ tailWord_5544195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544195).length < 2 ^ (prefixWord ++ tailWord_5544195).sum := by decide
  have hdescent : baseEnd_5544195 < baseStart_5544195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544249 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_5544249 : Nat := 118140960795 + 5544249 * 2 ^ 59
def prefixEnd_5544249 : Nat := 4983230072969 + 3 ^ 40 * 5544249 * 2
def baseEnd_5544249 : Nat := 948954868403127944663323

theorem tailTrace_5544249 : CollatzResearch.WordTrace tailWord_5544249 prefixEnd_5544249 948954868403127944663323 := by
  unfold tailWord_5544249
  simp only [CollatzResearch.WordTrace]
  refine ⟨202215373691140230189155801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134810249127426820126103867 202215373691140230189155801)
  ·
    refine ⟨151661530268355172641866851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202215373691140230189155801 151661530268355172641866851)
    ·
      refine ⟨227492295402532758962800277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151661530268355172641866851 227492295402532758962800277)
      ·
        refine ⟨10663701346993723076381263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 227492295402532758962800277 10663701346993723076381263)
        ·
          refine ⟨15995552020490584614571895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10663701346993723076381263 15995552020490584614571895)
          ·
            refine ⟨23993328030735876921857843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15995552020490584614571895 23993328030735876921857843)
            ·
              refine ⟨35989992046103815382786765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23993328030735876921857843 35989992046103815382786765)
              ·
                refine ⟨13496247017288930768545037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35989992046103815382786765 13496247017288930768545037)
                ·
                  refine ⟨5061092631483349038204389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13496247017288930768545037 5061092631483349038204389)
                  ·
                    refine ⟨948954868403127944663323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5061092631483349038204389 948954868403127944663323)
                    ·
                      rfl

theorem cell23_5544249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_5544249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544249 prefixEnd_5544249 := by exact prefixLift 5544249
  have htrace : WordTrace (prefixWord ++ tailWord_5544249) baseStart_5544249 baseEnd_5544249 := by
    simpa [prefixWord, tailWord_5544249, baseEnd_5544249] using wordTrace_append hprefix tailTrace_5544249
  have hstable : (prefixWord ++ tailWord_5544249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544249).length < 2 ^ (prefixWord ++ tailWord_5544249).sum := by decide
  have hdescent : baseEnd_5544249 < baseStart_5544249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544265 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_5544265 : Nat := 118140960795 + 5544265 * 2 ^ 59
def prefixEnd_5544265 : Nat := 4983230072969 + 3 ^ 40 * 5544265 * 2
def baseEnd_5544265 : Nat := 2846872820899855771389895

theorem tailTrace_5544265 : CollatzResearch.WordTrace tailWord_5544265 prefixEnd_5544265 2846872820899855771389895 := by
  unfold tailWord_5544265
  simp only [CollatzResearch.WordTrace]
  refine ⟨202215957259082264921738249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134810638172721509947825499 202215957259082264921738249)
  ·
    refine ⟨151661967944311698691303687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202215957259082264921738249 151661967944311698691303687)
    ·
      refine ⟨227492951916467548036955531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151661967944311698691303687 227492951916467548036955531)
      ·
        refine ⟨341239427874701322055433297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227492951916467548036955531 341239427874701322055433297)
        ·
          refine ⟨255929570906025991541574973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341239427874701322055433297 255929570906025991541574973)
          ·
            refine ⟨95973589089759746828090615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255929570906025991541574973 95973589089759746828090615)
            ·
              refine ⟨143960383634639620242135923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95973589089759746828090615 143960383634639620242135923)
              ·
                refine ⟨215940575451959430363203885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143960383634639620242135923 215940575451959430363203885)
                ·
                  refine ⟨80977715794484786386201457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215940575451959430363203885 80977715794484786386201457)
                  ·
                    refine ⟨60733286845863589789651093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80977715794484786386201457 60733286845863589789651093)
                    ·
                      refine ⟨2846872820899855771389895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60733286845863589789651093 2846872820899855771389895)
                      ·
                        rfl

theorem cell23_5544265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_5544265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544265 prefixEnd_5544265 := by exact prefixLift 5544265
  have htrace : WordTrace (prefixWord ++ tailWord_5544265) baseStart_5544265 baseEnd_5544265 := by
    simpa [prefixWord, tailWord_5544265, baseEnd_5544265] using wordTrace_append hprefix tailTrace_5544265
  have hstable : (prefixWord ++ tailWord_5544265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544265).length < 2 ^ (prefixWord ++ tailWord_5544265).sum := by decide
  have hdescent : baseEnd_5544265 < baseStart_5544265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544299 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 2, 3, 2]
def baseStart_5544299 : Nat := 118140960795 + 5544299 * 2 ^ 59
def prefixEnd_5544299 : Nat := 4983230072969 + 3 ^ 40 * 5544299 * 2
def baseEnd_5544299 : Nat := 2846890279242108638364739

theorem tailTrace_5544299 : CollatzResearch.WordTrace tailWord_5544299 prefixEnd_5544299 2846890279242108638364739 := by
  unfold tailWord_5544299
  simp only [CollatzResearch.WordTrace]
  refine ⟨202217197340959088728475951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134811464893972725818983967 202217197340959088728475951)
  ·
    refine ⟨303325796011438633092713927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202217197340959088728475951 303325796011438633092713927)
    ·
      refine ⟨454988694017157949639070891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303325796011438633092713927 454988694017157949639070891)
      ·
        refine ⟨682483041025736924458606337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454988694017157949639070891 682483041025736924458606337)
        ·
          refine ⟨511862280769302693343954753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682483041025736924458606337 511862280769302693343954753)
          ·
            refine ⟨383896710576977020007966065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511862280769302693343954753 383896710576977020007966065)
            ·
              refine ⟨287922532932732765005974549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383896710576977020007966065 287922532932732765005974549)
              ·
                refine ⟨13496368731221848359655057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 287922532932732765005974549 13496368731221848359655057)
                ·
                  refine ⟨10122276548416386269741293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13496368731221848359655057 10122276548416386269741293)
                  ·
                    refine ⟨3795853705656144851152985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10122276548416386269741293 3795853705656144851152985)
                    ·
                      refine ⟨2846890279242108638364739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3795853705656144851152985 2846890279242108638364739)
                      ·
                        rfl

theorem cell23_5544299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 3, 2].length) (baseStart_5544299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544299 prefixEnd_5544299 := by exact prefixLift 5544299
  have htrace : WordTrace (prefixWord ++ tailWord_5544299) baseStart_5544299 baseEnd_5544299 := by
    simpa [prefixWord, tailWord_5544299, baseEnd_5544299] using wordTrace_append hprefix tailTrace_5544299
  have hstable : (prefixWord ++ tailWord_5544299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544299).length < 2 ^ (prefixWord ++ tailWord_5544299).sum := by decide
  have hdescent : baseEnd_5544299 < baseStart_5544299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544306 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_5544306 : Nat := 118140960795 + 5544306 * 2 ^ 59
def prefixEnd_5544306 : Nat := 4983230072969 + 3 ^ 40 * 5544306 * 2
def baseEnd_5544306 : Nat := 2846893873606690110977207

theorem tailTrace_5544306 : CollatzResearch.WordTrace tailWord_5544306 prefixEnd_5544306 2846893873606690110977207 := by
  unfold tailWord_5544306
  simp only [CollatzResearch.WordTrace]
  refine ⟨50554363162983432230995193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134811635101289152615987181 50554363162983432230995193)
  ·
    refine ⟨37915772372237574173246395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50554363162983432230995193 37915772372237574173246395)
    ·
      refine ⟨56873658558356361259869593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37915772372237574173246395 56873658558356361259869593)
      ·
        refine ⟨42655243918767270944902195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56873658558356361259869593 42655243918767270944902195)
        ·
          refine ⟨63982865878150906417353293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42655243918767270944902195 63982865878150906417353293)
          ·
            refine ⟨23993574704306589906507485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63982865878150906417353293 23993574704306589906507485)
            ·
              refine ⟨8997590514114971214940307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23993574704306589906507485 8997590514114971214940307)
              ·
                refine ⟨13496385771172456822410461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997590514114971214940307 13496385771172456822410461)
                ·
                  refine ⟨5061144664189671308403923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13496385771172456822410461 5061144664189671308403923)
                  ·
                    refine ⟨7591716996284506962605885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061144664189671308403923 7591716996284506962605885)
                    ·
                      refine ⟨2846893873606690110977207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7591716996284506962605885 2846893873606690110977207)
                      ·
                        rfl

theorem cell23_5544306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_5544306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544306 prefixEnd_5544306 := by exact prefixLift 5544306
  have htrace : WordTrace (prefixWord ++ tailWord_5544306) baseStart_5544306 baseEnd_5544306 := by
    simpa [prefixWord, tailWord_5544306, baseEnd_5544306] using wordTrace_append hprefix tailTrace_5544306
  have hstable : (prefixWord ++ tailWord_5544306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544306).length < 2 ^ (prefixWord ++ tailWord_5544306).sum := by decide
  have hdescent : baseEnd_5544306 < baseStart_5544306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544329 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_5544329 : Nat := 118140960795 + 5544329 * 2 ^ 59
def prefixEnd_5544329 : Nat := 4983230072969 + 3 ^ 40 * 5544329 * 2
def baseEnd_5544329 : Nat := 2846905683661743520989601

theorem tailTrace_5544329 : CollatzResearch.WordTrace tailWord_5544329 prefixEnd_5544329 2846905683661743520989601 := by
  unfold tailWord_5544329
  simp only [CollatzResearch.WordTrace]
  refine ⟨202218291530850403852068041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134812194353900269234712027 202218291530850403852068041)
  ·
    refine ⟨151663718648137802889051031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202218291530850403852068041 151663718648137802889051031)
    ·
      refine ⟨227495577972206704333576547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151663718648137802889051031 227495577972206704333576547)
      ·
        refine ⟨341243366958310056500364821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227495577972206704333576547 341243366958310056500364821)
        ·
          refine ⟨15995782826170783898454601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 341243366958310056500364821 15995782826170783898454601)
          ·
            refine ⟨11996837119628087923840951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15995782826170783898454601 11996837119628087923840951)
            ·
              refine ⟨17995255679442131885761427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11996837119628087923840951 17995255679442131885761427)
              ·
                refine ⟨26992883519163197828642141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17995255679442131885761427 26992883519163197828642141)
                ·
                  refine ⟨10122331319686199185740803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26992883519163197828642141 10122331319686199185740803)
                  ·
                    refine ⟨15183496979529298778611205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10122331319686199185740803 15183496979529298778611205)
                    ·
                      refine ⟨2846905683661743520989601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15183496979529298778611205 2846905683661743520989601)
                      ·
                        rfl

theorem cell23_5544329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_5544329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544329 prefixEnd_5544329 := by exact prefixLift 5544329
  have htrace : WordTrace (prefixWord ++ tailWord_5544329) baseStart_5544329 baseEnd_5544329 := by
    simpa [prefixWord, tailWord_5544329, baseEnd_5544329] using wordTrace_append hprefix tailTrace_5544329
  have hstable : (prefixWord ++ tailWord_5544329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544329).length < 2 ^ (prefixWord ++ tailWord_5544329).sum := by decide
  have hdescent : baseEnd_5544329 < baseStart_5544329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544369 : List Nat := [1, 2, 2, 4, 1, 4, 1, 8]
def baseStart_5544369 : Nat := 118140960795 + 5544369 * 2 ^ 59
def prefixEnd_5544369 : Nat := 4983230072969 + 3 ^ 40 * 5544369 * 2
def baseEnd_5544369 : Nat := 105441711958811976462571

theorem tailTrace_5544369 : CollatzResearch.WordTrace tailWord_5544369 prefixEnd_5544369 105441711958811976462571 := by
  unfold tailWord_5544369
  simp only [CollatzResearch.WordTrace]
  refine ⟨202219750450705490683524161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134813166967136993789016107 202219750450705490683524161)
  ·
    refine ⟨151664812838029118012643121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202219750450705490683524161 151664812838029118012643121)
    ·
      refine ⟨113748609628521838509482341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151664812838029118012643121 113748609628521838509482341)
      ·
        refine ⟨21327864305347844720527939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113748609628521838509482341 21327864305347844720527939)
        ·
          refine ⟨31991796458021767080791909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21327864305347844720527939 31991796458021767080791909)
          ·
            refine ⟨5998461835879081327648483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31991796458021767080791909 5998461835879081327648483)
            ·
              refine ⟨8997692753818621991472725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998461835879081327648483 8997692753818621991472725)
              ·
                refine ⟨105441711958811976462571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8997692753818621991472725 105441711958811976462571)
                ·
                  rfl

theorem cell23_5544369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 8].length) (baseStart_5544369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544369 prefixEnd_5544369 := by exact prefixLift 5544369
  have htrace : WordTrace (prefixWord ++ tailWord_5544369) baseStart_5544369 baseEnd_5544369 := by
    simpa [prefixWord, tailWord_5544369, baseEnd_5544369] using wordTrace_append hprefix tailTrace_5544369
  have hstable : (prefixWord ++ tailWord_5544369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544369).length < 2 ^ (prefixWord ++ tailWord_5544369).sum := by decide
  have hdescent : baseEnd_5544369 < baseStart_5544369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544430 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_5544430 : Nat := 118140960795 + 5544430 * 2 ^ 59
def prefixEnd_5544430 : Nat := 4983230072969 + 3 ^ 40 * 5544430 * 2
def baseEnd_5544430 : Nat := 2846957545207847625826637

theorem tailTrace_5544430 : CollatzResearch.WordTrace tailWord_5544430 prefixEnd_5544430 2846957545207847625826637 := by
  unfold tailWord_5544430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25277746912935562262686843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134814650202322998734329829 25277746912935562262686843)
  ·
    refine ⟨37916620369403343394030265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25277746912935562262686843 37916620369403343394030265)
    ·
      refine ⟨28437465277052507545522699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37916620369403343394030265 28437465277052507545522699)
      ·
        refine ⟨42656197915578761318284049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28437465277052507545522699 42656197915578761318284049)
        ·
          refine ⟨31992148436684070988713037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42656197915578761318284049 31992148436684070988713037)
          ·
            refine ⟨11997055663756526620767389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31992148436684070988713037 11997055663756526620767389)
            ·
              refine ⟨4498895873908697482787771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11997055663756526620767389 4498895873908697482787771)
              ·
                refine ⟨6748343810863046224181657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4498895873908697482787771 6748343810863046224181657)
                ·
                  refine ⟨5061257858147284668136243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6748343810863046224181657 5061257858147284668136243)
                  ·
                    refine ⟨7591886787220927002204365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061257858147284668136243 7591886787220927002204365)
                    ·
                      refine ⟨2846957545207847625826637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7591886787220927002204365 2846957545207847625826637)
                      ·
                        rfl

theorem cell23_5544430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_5544430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544430 prefixEnd_5544430 := by exact prefixLift 5544430
  have htrace : WordTrace (prefixWord ++ tailWord_5544430) baseStart_5544430 baseEnd_5544430 := by
    simpa [prefixWord, tailWord_5544430, baseEnd_5544430] using wordTrace_append hprefix tailTrace_5544430
  have hstable : (prefixWord ++ tailWord_5544430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544430).length < 2 ^ (prefixWord ++ tailWord_5544430).sum := by decide
  have hdescent : baseEnd_5544430 < baseStart_5544430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544442 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_5544442 : Nat := 118140960795 + 5544442 * 2 ^ 59
def prefixEnd_5544442 : Nat := 4983230072969 + 3 ^ 40 * 5544442 * 2
def baseEnd_5544442 : Nat := 316329300775077953208509

theorem tailTrace_5544442 : CollatzResearch.WordTrace tailWord_5544442 prefixEnd_5544442 316329300775077953208509 := by
  unfold tailWord_5544442
  simp only [CollatzResearch.WordTrace]
  refine ⟨50555603244860256037732895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134814941986294016100621053 50555603244860256037732895)
  ·
    refine ⟨75833404867290384056599343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50555603244860256037732895 75833404867290384056599343)
    ·
      refine ⟨113750107300935576084899015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75833404867290384056599343 113750107300935576084899015)
      ·
        refine ⟨170625160951403364127348523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113750107300935576084899015 170625160951403364127348523)
        ·
          refine ⟨255937741427105046191022785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170625160951403364127348523 255937741427105046191022785)
          ·
            refine ⟨191953306070328784643267089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255937741427105046191022785 191953306070328784643267089)
            ·
              refine ⟨143964979552746588482450317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191953306070328784643267089 143964979552746588482450317)
              ·
                refine ⟨53986867332279970680918869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143964979552746588482450317 53986867332279970680918869)
                ·
                  refine ⟨316329300775077953208509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53986867332279970680918869 316329300775077953208509)
                  ·
                    rfl

theorem cell23_5544442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_5544442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544442 prefixEnd_5544442 := by exact prefixLift 5544442
  have htrace : WordTrace (prefixWord ++ tailWord_5544442) baseStart_5544442 baseEnd_5544442 := by
    simpa [prefixWord, tailWord_5544442, baseEnd_5544442] using wordTrace_append hprefix tailTrace_5544442
  have hstable : (prefixWord ++ tailWord_5544442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544442).length < 2 ^ (prefixWord ++ tailWord_5544442).sum := by decide
  have hdescent : baseEnd_5544442 < baseStart_5544442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544476 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 7]
def baseStart_5544476 : Nat := 118140960795 + 5544476 * 2 ^ 59
def prefixEnd_5544476 : Nat := 4983230072969 + 3 ^ 40 * 5544476 * 2
def baseEnd_5544476 : Nat := 316331240590883827316825

theorem tailTrace_5544476 : CollatzResearch.WordTrace tailWord_5544476 prefixEnd_5544476 316331240590883827316825 := by
  unfold tailWord_5544476
  simp only [CollatzResearch.WordTrace]
  refine ⟨101111826530658923978834641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134815768707545231971779521 101111826530658923978834641)
  ·
    refine ⟨75833869897994192984125981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101111826530658923978834641 75833869897994192984125981)
    ·
      refine ⟨28437701211747822369047243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75833869897994192984125981 28437701211747822369047243)
      ·
        refine ⟨42656551817621733553570865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28437701211747822369047243 42656551817621733553570865)
        ·
          refine ⟨31992413863216300165178149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42656551817621733553570865 31992413863216300165178149)
          ·
            refine ⟨5998577599353056280970903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31992413863216300165178149 5998577599353056280970903)
            ·
              refine ⟨8997866399029584421456355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998577599353056280970903 8997866399029584421456355)
              ·
                refine ⟨13496799598544376632184533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997866399029584421456355 13496799598544376632184533)
                ·
                  refine ⟨316331240590883827316825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13496799598544376632184533 316331240590883827316825)
                  ·
                    rfl

theorem cell23_5544476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_5544476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544476 prefixEnd_5544476 := by exact prefixLift 5544476
  have htrace : WordTrace (prefixWord ++ tailWord_5544476) baseStart_5544476 baseEnd_5544476 := by
    simpa [prefixWord, tailWord_5544476, baseEnd_5544476] using wordTrace_append hprefix tailTrace_5544476
  have hstable : (prefixWord ++ tailWord_5544476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544476).length < 2 ^ (prefixWord ++ tailWord_5544476).sum := by decide
  have hdescent : baseEnd_5544476 < baseStart_5544476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544506 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_5544506 : Nat := 118140960795 + 5544506 * 2 ^ 59
def prefixEnd_5544506 : Nat := 4983230072969 + 3 ^ 40 * 5544506 * 2
def baseEnd_5544506 : Nat := 948998856579196442825429

theorem tailTrace_5544506 : CollatzResearch.WordTrace tailWord_5544506 prefixEnd_5544506 948998856579196442825429 := by
  unfold tailWord_5544506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50556186812802290770315343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134816498167472775387507581 50556186812802290770315343)
  ·
    refine ⟨75834280219203436155473015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50556186812802290770315343 75834280219203436155473015)
    ·
      refine ⟨113751420328805154233209523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75834280219203436155473015 113751420328805154233209523)
      ·
        refine ⟨170627130493207731349814285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113751420328805154233209523 170627130493207731349814285)
        ·
          refine ⟨63985173934952899256180357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170627130493207731349814285 63985173934952899256180357)
          ·
            refine ⟨11997220112803668610533817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63985173934952899256180357 11997220112803668610533817)
            ·
              refine ⟨8997915084602751457900363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11997220112803668610533817 8997915084602751457900363)
              ·
                refine ⟨13496872626904127186850545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997915084602751457900363 13496872626904127186850545)
                ·
                  refine ⟨10122654470178095390137909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13496872626904127186850545 10122654470178095390137909)
                  ·
                    refine ⟨948998856579196442825429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10122654470178095390137909 948998856579196442825429)
                    ·
                      rfl

theorem cell23_5544506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_5544506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544506 prefixEnd_5544506 := by exact prefixLift 5544506
  have htrace : WordTrace (prefixWord ++ tailWord_5544506) baseStart_5544506 baseEnd_5544506 := by
    simpa [prefixWord, tailWord_5544506, baseEnd_5544506] using wordTrace_append hprefix tailTrace_5544506
  have hstable : (prefixWord ++ tailWord_5544506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544506).length < 2 ^ (prefixWord ++ tailWord_5544506).sum := by decide
  have hdescent : baseEnd_5544506 < baseStart_5544506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544526 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5544526 : Nat := 118140960795 + 5544526 * 2 ^ 59
def prefixEnd_5544526 : Nat := 4983230072969 + 3 ^ 40 * 5544526 * 2
def baseEnd_5544526 : Nat := 2847006839350679250226195

theorem tailTrace_5544526 : CollatzResearch.WordTrace tailWord_5544526 prefixEnd_5544526 2847006839350679250226195 := by
  unfold tailWord_5544526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25278184588892088312123679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134816984474091137664659621 25278184588892088312123679)
  ·
    refine ⟨37917276883338132468185519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25278184588892088312123679 37917276883338132468185519)
    ·
      refine ⟨56875915325007198702278279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37917276883338132468185519 56875915325007198702278279)
      ·
        refine ⟨85313872987510798053417419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56875915325007198702278279 85313872987510798053417419)
        ·
          refine ⟨127970809481266197080126129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85313872987510798053417419 127970809481266197080126129)
          ·
            refine ⟨95978107110949647810094597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127970809481266197080126129 95978107110949647810094597)
            ·
              refine ⟨17995895083303058964392737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95978107110949647810094597 17995895083303058964392737)
              ·
                refine ⟨13496921312477294223294553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17995895083303058964392737 13496921312477294223294553)
                ·
                  refine ⟨10122690984357970667470915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13496921312477294223294553 10122690984357970667470915)
                  ·
                    refine ⟨15184036476536956001206373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10122690984357970667470915 15184036476536956001206373)
                    ·
                      refine ⟨2847006839350679250226195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15184036476536956001206373 2847006839350679250226195)
                      ·
                        rfl

theorem cell23_5544526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5544526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544526 prefixEnd_5544526 := by exact prefixLift 5544526
  have htrace : WordTrace (prefixWord ++ tailWord_5544526) baseStart_5544526 baseEnd_5544526 := by
    simpa [prefixWord, tailWord_5544526, baseEnd_5544526] using wordTrace_append hprefix tailTrace_5544526
  have hstable : (prefixWord ++ tailWord_5544526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544526).length < 2 ^ (prefixWord ++ tailWord_5544526).sum := by decide
  have hdescent : baseEnd_5544526 < baseStart_5544526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544560 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4]
def baseStart_5544560 : Nat := 118140960795 + 5544560 * 2 ^ 59
def prefixEnd_5544560 : Nat := 4983230072969 + 3 ^ 40 * 5544560 * 2
def baseEnd_5544560 : Nat := 2847024297692932117201039

theorem tailTrace_5544560 : CollatzResearch.WordTrace tailWord_5544560 prefixEnd_5544560 2847024297692932117201039 := by
  unfold tailWord_5544560
  simp only [CollatzResearch.WordTrace]
  refine ⟨101113358396506765151863567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134817811195342353535818089 101113358396506765151863567)
  ·
    refine ⟨151670037594760147727795351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101113358396506765151863567 151670037594760147727795351)
    ·
      refine ⟨227505056392140221591693027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151670037594760147727795351 227505056392140221591693027)
      ·
        refine ⟨341257584588210332387539541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227505056392140221591693027 341257584588210332387539541)
        ·
          refine ⟨3999112319393089832666479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 341257584588210332387539541 3999112319393089832666479)
          ·
            refine ⟨5998668479089634748999719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999112319393089832666479 5998668479089634748999719)
            ·
              refine ⟨8998002718634452123499579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998668479089634748999719 8998002718634452123499579)
              ·
                refine ⟨13497004077951678185249369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998002718634452123499579 13497004077951678185249369)
                ·
                  refine ⟨10122753058463758638937027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13497004077951678185249369 10122753058463758638937027)
                  ·
                    refine ⟨15184129587695637958405541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10122753058463758638937027 15184129587695637958405541)
                    ·
                      refine ⟨2847024297692932117201039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15184129587695637958405541 2847024297692932117201039)
                      ·
                        rfl

theorem cell23_5544560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 1, 4].length) (baseStart_5544560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544560 prefixEnd_5544560 := by exact prefixLift 5544560
  have htrace : WordTrace (prefixWord ++ tailWord_5544560) baseStart_5544560 baseEnd_5544560 := by
    simpa [prefixWord, tailWord_5544560, baseEnd_5544560] using wordTrace_append hprefix tailTrace_5544560
  have hstable : (prefixWord ++ tailWord_5544560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544560).length < 2 ^ (prefixWord ++ tailWord_5544560).sum := by decide
  have hdescent : baseEnd_5544560 < baseStart_5544560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544627 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 1, 1, 3]
def baseStart_5544627 : Nat := 118140960795 + 5544627 * 2 ^ 59
def prefixEnd_5544627 : Nat := 4983230072969 + 3 ^ 40 * 5544627 * 2
def baseEnd_5544627 : Nat := 2847058700896783355063231

theorem tailTrace_5544627 : CollatzResearch.WordTrace tailWord_5544627 prefixEnd_5544627 2847058700896783355063231 := by
  unfold tailWord_5544627
  simp only [CollatzResearch.WordTrace]
  refine ⟨202229160483770800746416135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134819440322513867164277423 202229160483770800746416135)
  ·
    refine ⟨303343740725656201119624203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202229160483770800746416135 303343740725656201119624203)
    ·
      refine ⟨455015611088484301679436305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303343740725656201119624203 455015611088484301679436305)
      ·
        refine ⟨341261708316363226259577229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455015611088484301679436305 341261708316363226259577229)
        ·
          refine ⟨127973140618636209847341461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341261708316363226259577229 127973140618636209847341461)
          ·
            refine ⟨5998740966498572336594131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127973140618636209847341461 5998740966498572336594131)
            ·
              refine ⟨8998111449747858504891197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998740966498572336594131 8998111449747858504891197)
              ·
                refine ⟨3374291793655446939334199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8998111449747858504891197 3374291793655446939334199)
                ·
                  refine ⟨5061437690483170409001299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374291793655446939334199 5061437690483170409001299)
                  ·
                    refine ⟨7592156535724755613501949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061437690483170409001299 7592156535724755613501949)
                    ·
                      refine ⟨2847058700896783355063231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7592156535724755613501949 2847058700896783355063231)
                      ·
                        rfl

theorem cell23_5544627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 1, 3].length) (baseStart_5544627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544627 prefixEnd_5544627 := by exact prefixLift 5544627
  have htrace : WordTrace (prefixWord ++ tailWord_5544627) baseStart_5544627 baseEnd_5544627 := by
    simpa [prefixWord, tailWord_5544627, baseEnd_5544627] using wordTrace_append hprefix tailTrace_5544627
  have hstable : (prefixWord ++ tailWord_5544627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544627).length < 2 ^ (prefixWord ++ tailWord_5544627).sum := by decide
  have hdescent : baseEnd_5544627 < baseStart_5544627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544639 : List Nat := [1, 1, 2, 2, 2, 4, 11]
def baseStart_5544639 : Nat := 118140960795 + 5544639 * 2 ^ 59
def prefixEnd_5544639 : Nat := 4983230072969 + 3 ^ 40 * 5544639 * 2
def baseEnd_5544639 : Nat := 35148948921785645779175

theorem tailTrace_5544639 : CollatzResearch.WordTrace tailWord_5544639 prefixEnd_5544639 35148948921785645779175 := by
  unfold tailWord_5544639
  simp only [CollatzResearch.WordTrace]
  refine ⟨202229598159727326795852971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134819732106484884530568647 202229598159727326795852971)
  ·
    refine ⟨303344397239590990193779457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202229598159727326795852971 303344397239590990193779457)
    ·
      refine ⟨227508297929693242645334593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303344397239590990193779457 227508297929693242645334593)
      ·
        refine ⟨170631223447269931984000945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227508297929693242645334593 170631223447269931984000945)
        ·
          refine ⟨127973417585452448988000709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170631223447269931984000945 127973417585452448988000709)
          ·
            refine ⟨23995015797272334185250133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127973417585452448988000709 23995015797272334185250133)
            ·
              refine ⟨35148948921785645779175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23995015797272334185250133 35148948921785645779175)
              ·
                rfl

theorem cell23_5544639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 11].length) (baseStart_5544639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544639 prefixEnd_5544639 := by exact prefixLift 5544639
  have htrace : WordTrace (prefixWord ++ tailWord_5544639) baseStart_5544639 baseEnd_5544639 := by
    simpa [prefixWord, tailWord_5544639, baseEnd_5544639] using wordTrace_append hprefix tailTrace_5544639
  have hstable : (prefixWord ++ tailWord_5544639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544639).length < 2 ^ (prefixWord ++ tailWord_5544639).sum := by decide
  have hdescent : baseEnd_5544639 < baseStart_5544639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544644 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_5544644 : Nat := 118140960795 + 5544644 * 2 ^ 59
def prefixEnd_5544644 : Nat := 4983230072969 + 3 ^ 40 * 5544644 * 2
def baseEnd_5544644 : Nat := 2847067430067909788550653

theorem tailTrace_5544644 : CollatzResearch.WordTrace tailWord_5544644 prefixEnd_5544644 2847067430067909788550653 := by
  unfold tailWord_5544644
  simp only [CollatzResearch.WordTrace]
  refine ⟨101114890262354606324892493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134819853683139475099856657 101114890262354606324892493)
  ·
    refine ⟨37918083848382977371834685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101114890262354606324892493 37918083848382977371834685)
    ·
      refine ⟨14219281443143616514438007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37918083848382977371834685 14219281443143616514438007)
      ·
        refine ⟨21328922164715424771657011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14219281443143616514438007 21328922164715424771657011)
        ·
          refine ⟨31993383247073137157485517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21328922164715424771657011 31993383247073137157485517)
          ·
            refine ⟨11997518717652426434057069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31993383247073137157485517 11997518717652426434057069)
            ·
              refine ⟨4499069519119659912771401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11997518717652426434057069 4499069519119659912771401)
              ·
                refine ⟨3374302139339744934578551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499069519119659912771401 3374302139339744934578551)
                ·
                  refine ⟨5061453209009617401867827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374302139339744934578551 5061453209009617401867827)
                  ·
                    refine ⟨7592179813514426102801741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061453209009617401867827 7592179813514426102801741)
                    ·
                      refine ⟨2847067430067909788550653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7592179813514426102801741 2847067430067909788550653)
                      ·
                        rfl

theorem cell23_5544644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_5544644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544644 prefixEnd_5544644 := by exact prefixLift 5544644
  have htrace : WordTrace (prefixWord ++ tailWord_5544644) baseStart_5544644 baseEnd_5544644 := by
    simpa [prefixWord, tailWord_5544644, baseEnd_5544644] using wordTrace_append hprefix tailTrace_5544644
  have hstable : (prefixWord ++ tailWord_5544644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544644).length < 2 ^ (prefixWord ++ tailWord_5544644).sum := by decide
  have hdescent : baseEnd_5544644 < baseStart_5544644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544700 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_5544700 : Nat := 118140960795 + 5544700 * 2 ^ 59
def prefixEnd_5544700 : Nat := 4983230072969 + 3 ^ 40 * 5544700 * 2
def baseEnd_5544700 : Nat := 2847096184984561569450395

theorem tailTrace_5544700 : CollatzResearch.WordTrace tailWord_5544700 prefixEnd_5544700 2847096184984561569450395 := by
  unfold tailWord_5544700
  simp only [CollatzResearch.WordTrace]
  refine ⟨101115911506253167106911777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134821215341670889475882369 101115911506253167106911777)
  ·
    refine ⟨75836933629689875330183833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101115911506253167106911777 75836933629689875330183833)
    ·
      refine ⟨56877700222267406497637875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75836933629689875330183833 56877700222267406497637875)
      ·
        refine ⟨85316550333401109746456813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56877700222267406497637875 85316550333401109746456813)
        ·
          refine ⟨31993706375025416154921305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85316550333401109746456813 31993706375025416154921305)
          ·
            refine ⟨23995279781269062116190979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31993706375025416154921305 23995279781269062116190979)
            ·
              refine ⟨35992919671903593174286469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23995279781269062116190979 35992919671903593174286469)
              ·
                refine ⟨6748672438481923720178713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35992919671903593174286469 6748672438481923720178713)
                ·
                  refine ⟨5061504328861442790134035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6748672438481923720178713 5061504328861442790134035)
                  ·
                    refine ⟨7592256493292164185201053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061504328861442790134035 7592256493292164185201053)
                    ·
                      refine ⟨2847096184984561569450395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7592256493292164185201053 2847096184984561569450395)
                      ·
                        rfl

theorem cell23_5544700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_5544700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544700 prefixEnd_5544700 := by exact prefixLift 5544700
  have htrace : WordTrace (prefixWord ++ tailWord_5544700) baseStart_5544700 baseEnd_5544700 := by
    simpa [prefixWord, tailWord_5544700, baseEnd_5544700] using wordTrace_append hprefix tailTrace_5544700
  have hstable : (prefixWord ++ tailWord_5544700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544700).length < 2 ^ (prefixWord ++ tailWord_5544700).sum := by decide
  have hdescent : baseEnd_5544700 < baseStart_5544700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544757 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_5544757 : Nat := 118140960795 + 5544757 * 2 ^ 59
def prefixEnd_5544757 : Nat := 4983230072969 + 3 ^ 40 * 5544757 * 2
def baseEnd_5544757 : Nat := 2847125453381867846437633

theorem tailTrace_5544757 : CollatzResearch.WordTrace tailWord_5544757 prefixEnd_5544757 2847125453381867846437633 := by
  unfold tailWord_5544757
  simp only [CollatzResearch.WordTrace]
  refine ⟨202233901973299832948648525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134822601315533221965765683 202233901973299832948648525)
  ·
    refine ⟨75837713239987437355743197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202233901973299832948648525 75837713239987437355743197)
    ·
      refine ⟨28439142464995289008403699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75837713239987437355743197 28439142464995289008403699)
      ·
        refine ⟨42658713697492933512605549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28439142464995289008403699 42658713697492933512605549)
        ·
          refine ⟨15997017636559850067227081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42658713697492933512605549 15997017636559850067227081)
          ·
            refine ⟨11997763227419887550420311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15997017636559850067227081 11997763227419887550420311)
            ·
              refine ⟨17996644841129831325630467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11997763227419887550420311 17996644841129831325630467)
              ·
                refine ⟨26994967261694746988445701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17996644841129831325630467 26994967261694746988445701)
                ·
                  refine ⟨5061556361567765060333569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26994967261694746988445701 5061556361567765060333569)
                  ·
                    refine ⟨3796167271175823795250177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5061556361567765060333569 3796167271175823795250177)
                    ·
                      refine ⟨2847125453381867846437633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796167271175823795250177 2847125453381867846437633)
                      ·
                        rfl

theorem cell23_5544757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_5544757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544757 prefixEnd_5544757 := by exact prefixLift 5544757
  have htrace : WordTrace (prefixWord ++ tailWord_5544757) baseStart_5544757 baseEnd_5544757 := by
    simpa [prefixWord, tailWord_5544757, baseEnd_5544757] using wordTrace_append hprefix tailTrace_5544757
  have hstable : (prefixWord ++ tailWord_5544757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544757).length < 2 ^ (prefixWord ++ tailWord_5544757).sum := by decide
  have hdescent : baseEnd_5544757 < baseStart_5544757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544776 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_5544776 : Nat := 118140960795 + 5544776 * 2 ^ 59
def prefixEnd_5544776 : Nat := 4983230072969 + 3 ^ 40 * 5544776 * 2
def baseEnd_5544776 : Nat := 949045069838101090700015

theorem tailTrace_5544776 : CollatzResearch.WordTrace tailWord_5544776 prefixEnd_5544776 949045069838101090700015 := by
  unfold tailWord_5544776
  simp only [CollatzResearch.WordTrace]
  refine ⟨101117297480115499596795091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134823063306820666129060121 101117297480115499596795091)
  ·
    refine ⟨151675946220173249395192637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101117297480115499596795091 151675946220173249395192637)
    ·
      refine ⟨56878479832564968523197239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151675946220173249395192637 56878479832564968523197239)
      ·
        refine ⟨85317719748847452784795859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56878479832564968523197239 85317719748847452784795859)
        ·
          refine ⟨127976579623271179177193789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85317719748847452784795859 127976579623271179177193789)
          ·
            refine ⟨47991217358726692191447671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127976579623271179177193789 47991217358726692191447671)
            ·
              refine ⟨71986826038090038287171507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47991217358726692191447671 71986826038090038287171507)
              ·
                refine ⟨107980239057135057430757261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71986826038090038287171507 107980239057135057430757261)
                ·
                  refine ⟨40492589646425646536533973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107980239057135057430757261 40492589646425646536533973)
                  ·
                    refine ⟨949045069838101090700015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40492589646425646536533973 949045069838101090700015)
                    ·
                      rfl

theorem cell23_5544776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_5544776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544776 prefixEnd_5544776 := by exact prefixLift 5544776
  have htrace : WordTrace (prefixWord ++ tailWord_5544776) baseStart_5544776 baseEnd_5544776 := by
    simpa [prefixWord, tailWord_5544776, baseEnd_5544776] using wordTrace_append hprefix tailTrace_5544776
  have hstable : (prefixWord ++ tailWord_5544776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544776).length < 2 ^ (prefixWord ++ tailWord_5544776).sum := by decide
  have hdescent : baseEnd_5544776 < baseStart_5544776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544814 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_5544814 : Nat := 118140960795 + 5544814 * 2 ^ 59
def prefixEnd_5544814 : Nat := 4983230072969 + 3 ^ 40 * 5544814 * 2
def baseEnd_5544814 : Nat := 316350524642130458158319

theorem tailTrace_5544814 : CollatzResearch.WordTrace tailWord_5544814 prefixEnd_5544814 316350524642130458158319 := by
  unfold tailWord_5544814
  simp only [CollatzResearch.WordTrace]
  refine ⟨25279497616761666460434187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134823987289395554455648997 25279497616761666460434187)
  ·
    refine ⟨37919246425142499690651281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25279497616761666460434187 37919246425142499690651281)
    ·
      refine ⟨28439434818856874767988461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37919246425142499690651281 28439434818856874767988461)
      ·
        refine ⟨10664788057071328037995673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28439434818856874767988461 10664788057071328037995673)
        ·
          refine ⟨7998591042803496028496755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10664788057071328037995673 7998591042803496028496755)
          ·
            refine ⟨11997886564205244042745133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998591042803496028496755 11997886564205244042745133)
            ·
              refine ⟨4499207461576966516029425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11997886564205244042745133 4499207461576966516029425)
              ·
                refine ⟨3374405596182724887022069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499207461576966516029425 3374405596182724887022069)
                ·
                  refine ⟨316350524642130458158319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3374405596182724887022069 316350524642130458158319)
                  ·
                    rfl

theorem cell23_5544814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_5544814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544814 prefixEnd_5544814 := by exact prefixLift 5544814
  have htrace : WordTrace (prefixWord ++ tailWord_5544814) baseStart_5544814 baseEnd_5544814 := by
    simpa [prefixWord, tailWord_5544814, baseEnd_5544814] using wordTrace_append hprefix tailTrace_5544814
  have hstable : (prefixWord ++ tailWord_5544814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544814).length < 2 ^ (prefixWord ++ tailWord_5544814).sum := by decide
  have hdescent : baseEnd_5544814 < baseStart_5544814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544890 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2]
def baseStart_5544890 : Nat := 118140960795 + 5544890 * 2 ^ 59
def prefixEnd_5544890 : Nat := 4983230072969 + 3 ^ 40 * 5544890 * 2
def baseEnd_5544890 : Nat := 2847193746308915826074521

theorem tailTrace_5544890 : CollatzResearch.WordTrace tailWord_5544890 prefixEnd_5544890 2847193746308915826074521 := by
  unfold tailWord_5544890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50559688220454499165810031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134825835254545331108826749 50559688220454499165810031)
  ·
    refine ⟨75839532330681748748715047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50559688220454499165810031 75839532330681748748715047)
    ·
      refine ⟨113759298496022623123072571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75839532330681748748715047 113759298496022623123072571)
      ·
        refine ⟨170638947744033934684608857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113759298496022623123072571 170638947744033934684608857)
        ·
          refine ⟨127979210808025451013456643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170638947744033934684608857 127979210808025451013456643)
          ·
            refine ⟨191968816212038176520184965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127979210808025451013456643 191968816212038176520184965)
            ·
              refine ⟨35994153039757158097534681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191968816212038176520184965 35994153039757158097534681)
              ·
                refine ⟨26995614779817868573151011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35994153039757158097534681 26995614779817868573151011)
                ·
                  refine ⟨40493422169726802859726517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26995614779817868573151011 40493422169726802859726517)
                  ·
                    refine ⟨3796258328411887768099361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40493422169726802859726517 3796258328411887768099361)
                    ·
                      refine ⟨2847193746308915826074521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796258328411887768099361 2847193746308915826074521)
                      ·
                        rfl

theorem cell23_5544890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_5544890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544890 prefixEnd_5544890 := by exact prefixLift 5544890
  have htrace : WordTrace (prefixWord ++ tailWord_5544890) baseStart_5544890 baseEnd_5544890 := by
    simpa [prefixWord, tailWord_5544890, baseEnd_5544890] using wordTrace_append hprefix tailTrace_5544890
  have hstable : (prefixWord ++ tailWord_5544890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544890).length < 2 ^ (prefixWord ++ tailWord_5544890).sum := by decide
  have hdescent : baseEnd_5544890 < baseStart_5544890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544907 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 2, 3, 2]
def baseStart_5544907 : Nat := 118140960795 + 5544907 * 2 ^ 59
def prefixEnd_5544907 : Nat := 4983230072969 + 3 ^ 40 * 5544907 * 2
def baseEnd_5544907 : Nat := 2847202475480042259561943

theorem tailTrace_5544907 : CollatzResearch.WordTrace tailWord_5544907 prefixEnd_5544907 2847202475480042259561943 := by
  unfold tailWord_5544907
  simp only [CollatzResearch.WordTrace]
  refine ⟨202239372922756408566608975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134826248615170939044405983 202239372922756408566608975)
  ·
    refine ⟨303359059384134612849913463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202239372922756408566608975 303359059384134612849913463)
    ·
      refine ⟨455038589076201919274870195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303359059384134612849913463 455038589076201919274870195)
      ·
        refine ⟨682557883614302878912305293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455038589076201919274870195 682557883614302878912305293)
        ·
          refine ⟨255959206355363579592114485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 682557883614302878912305293 255959206355363579592114485)
          ·
            refine ⟨23996175595815335586760733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 255959206355363579592114485 23996175595815335586760733)
            ·
              refine ⟨8998565848430750845035275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23996175595815335586760733 8998565848430750845035275)
              ·
                refine ⟨13497848772646126267552913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998565848430750845035275 13497848772646126267552913)
                ·
                  refine ⟨10123386579484594700664685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13497848772646126267552913 10123386579484594700664685)
                  ·
                    refine ⟨3796269967306723012749257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10123386579484594700664685 3796269967306723012749257)
                    ·
                      refine ⟨2847202475480042259561943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796269967306723012749257 2847202475480042259561943)
                      ·
                        rfl

theorem cell23_5544907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3, 2].length) (baseStart_5544907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544907 prefixEnd_5544907 := by exact prefixLift 5544907
  have htrace : WordTrace (prefixWord ++ tailWord_5544907) baseStart_5544907 baseEnd_5544907 := by
    simpa [prefixWord, tailWord_5544907, baseEnd_5544907] using wordTrace_append hprefix tailTrace_5544907
  have hstable : (prefixWord ++ tailWord_5544907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544907).length < 2 ^ (prefixWord ++ tailWord_5544907).sum := by decide
  have hdescent : baseEnd_5544907 < baseStart_5544907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544913 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_5544913 : Nat := 118140960795 + 5544913 * 2 ^ 59
def prefixEnd_5544913 : Nat := 4983230072969 + 3 ^ 40 * 5544913 * 2
def baseEnd_5544913 : Nat := 949068518787989745362305

theorem tailTrace_5544913 : CollatzResearch.WordTrace tailWord_5544913 prefixEnd_5544913 949068518787989745362305 := by
  unfold tailWord_5544913
  simp only [CollatzResearch.WordTrace]
  refine ⟨202239591760734671591327393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134826394507156447727551595 202239591760734671591327393)
  ·
    refine ⟨151679693820551003693495545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202239591760734671591327393 151679693820551003693495545)
    ·
      refine ⟨113759770365413252770121659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151679693820551003693495545 113759770365413252770121659)
      ·
        refine ⟨170639655548119879155182489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113759770365413252770121659 170639655548119879155182489)
        ·
          refine ⟨127979741661089909366386867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170639655548119879155182489 127979741661089909366386867)
          ·
            refine ⟨191969612491634864049580301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127979741661089909366386867 191969612491634864049580301)
            ·
              refine ⟨71988604684363074018592613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191969612491634864049580301 71988604684363074018592613)
              ·
                refine ⟨13497863378318076378486115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71988604684363074018592613 13497863378318076378486115)
                ·
                  refine ⟨20246795067477114567729173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13497863378318076378486115 20246795067477114567729173)
                  ·
                    refine ⟨949068518787989745362305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20246795067477114567729173 949068518787989745362305)
                    ·
                      rfl

theorem cell23_5544913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_5544913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544913 prefixEnd_5544913 := by exact prefixLift 5544913
  have htrace : WordTrace (prefixWord ++ tailWord_5544913) baseStart_5544913 baseEnd_5544913 := by
    simpa [prefixWord, tailWord_5544913, baseEnd_5544913] using wordTrace_append hprefix tailTrace_5544913
  have hstable : (prefixWord ++ tailWord_5544913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544913).length < 2 ^ (prefixWord ++ tailWord_5544913).sum := by decide
  have hdescent : baseEnd_5544913 < baseStart_5544913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544917 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_5544917 : Nat := 118140960795 + 5544917 * 2 ^ 59
def prefixEnd_5544917 : Nat := 4983230072969 + 3 ^ 40 * 5544917 * 2
def baseEnd_5544917 : Nat := 949069203428862406812299

theorem tailTrace_5544917 : CollatzResearch.WordTrace tailWord_5544917 prefixEnd_5544917 949069203428862406812299 := by
  unfold tailWord_5544917
  simp only [CollatzResearch.WordTrace]
  refine ⟨202239737652720180274473005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134826491768480120182982003 202239737652720180274473005)
  ·
    refine ⟨75839901619770067602927377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202239737652720180274473005 75839901619770067602927377)
    ·
      refine ⟨56879926214827550702195533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75839901619770067602927377 56879926214827550702195533)
      ·
        refine ⟨21329972330560331513323325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56879926214827550702195533 21329972330560331513323325)
        ·
          refine ⟨7998739623960124317496247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21329972330560331513323325 7998739623960124317496247)
          ·
            refine ⟨11998109435940186476244371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998739623960124317496247 11998109435940186476244371)
            ·
              refine ⟨17997164153910279714366557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998109435940186476244371 17997164153910279714366557)
              ·
                refine ⟨6748936557716354892887459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17997164153910279714366557 6748936557716354892887459)
                ·
                  refine ⟨10123404836574532339331189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748936557716354892887459 10123404836574532339331189)
                  ·
                    refine ⟨949069203428862406812299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10123404836574532339331189 949069203428862406812299)
                    ·
                      rfl

theorem cell23_5544917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_5544917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544917 prefixEnd_5544917 := by exact prefixLift 5544917
  have htrace : WordTrace (prefixWord ++ tailWord_5544917) baseStart_5544917 baseEnd_5544917 := by
    simpa [prefixWord, tailWord_5544917, baseEnd_5544917] using wordTrace_append hprefix tailTrace_5544917
  have hstable : (prefixWord ++ tailWord_5544917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544917).length < 2 ^ (prefixWord ++ tailWord_5544917).sum := by decide
  have hdescent : baseEnd_5544917 < baseStart_5544917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544971 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 1, 2, 2]
def baseStart_5544971 : Nat := 118140960795 + 5544971 * 2 ^ 59
def prefixEnd_5544971 : Nat := 4983230072969 + 3 ^ 40 * 5544971 * 2
def baseEnd_5544971 : Nat := 2847235338241930009161649

theorem tailTrace_5544971 : CollatzResearch.WordTrace tailWord_5544971 prefixEnd_5544971 2847235338241930009161649 := by
  unfold tailWord_5544971
  simp only [CollatzResearch.WordTrace]
  refine ⟨202241707194524547496938767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134827804796349698331292511 202241707194524547496938767)
  ·
    refine ⟨303362560791786821245408151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202241707194524547496938767 303362560791786821245408151)
    ·
      refine ⟨455043841187680231868112227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303362560791786821245408151 455043841187680231868112227)
      ·
        refine ⟨682565761781520347802168341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455043841187680231868112227 682565761781520347802168341)
        ·
          refine ⟨31995270083508766303226641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 682565761781520347802168341 31995270083508766303226641)
          ·
            refine ⟨23996452562631574727419981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31995270083508766303226641 23996452562631574727419981)
            ·
              refine ⟨8998669710986840522782493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23996452562631574727419981 8998669710986840522782493)
              ·
                refine ⟨3374501141620065196043435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8998669710986840522782493 3374501141620065196043435)
                ·
                  refine ⟨5061751712430097794065153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374501141620065196043435 5061751712430097794065153)
                  ·
                    refine ⟨3796313784322573345548865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5061751712430097794065153 3796313784322573345548865)
                    ·
                      refine ⟨2847235338241930009161649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796313784322573345548865 2847235338241930009161649)
                      ·
                        rfl

theorem cell23_5544971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 2, 2].length) (baseStart_5544971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544971 prefixEnd_5544971 := by exact prefixLift 5544971
  have htrace : WordTrace (prefixWord ++ tailWord_5544971) baseStart_5544971 baseEnd_5544971 := by
    simpa [prefixWord, tailWord_5544971, baseEnd_5544971] using wordTrace_append hprefix tailTrace_5544971
  have hstable : (prefixWord ++ tailWord_5544971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544971).length < 2 ^ (prefixWord ++ tailWord_5544971).sum := by decide
  have hdescent : baseEnd_5544971 < baseStart_5544971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544988 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_5544988 : Nat := 118140960795 + 5544988 * 2 ^ 59
def prefixEnd_5544988 : Nat := 4983230072969 + 3 ^ 40 * 5544988 * 2
def baseEnd_5544988 : Nat := 2847244067413056442649071

theorem tailTrace_5544988 : CollatzResearch.WordTrace tailWord_5544988 prefixEnd_5544988 2847244067413056442649071 := by
  unfold tailWord_5544988
  simp only [CollatzResearch.WordTrace]
  refine ⟨101121163617731479700153809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134828218156975306266871745 101121163617731479700153809)
  ·
    refine ⟨75840872713298609775115357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101121163617731479700153809 75840872713298609775115357)
    ·
      refine ⟨28440327267486978665668259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75840872713298609775115357 28440327267486978665668259)
      ·
        refine ⟨42660490901230467998502389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28440327267486978665668259 42660490901230467998502389)
        ·
          refine ⟨3999421021990356374859599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42660490901230467998502389 3999421021990356374859599)
          ·
            refine ⟨5999131532985534562289399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999421021990356374859599 5999131532985534562289399)
            ·
              refine ⟨8998697299478301843434099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5999131532985534562289399 8998697299478301843434099)
              ·
                refine ⟨13498045949217452765151149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998697299478301843434099 13498045949217452765151149)
                ·
                  refine ⟨5061767230956544786931681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13498045949217452765151149 5061767230956544786931681)
                  ·
                    refine ⟨3796325423217408590198761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5061767230956544786931681 3796325423217408590198761)
                    ·
                      refine ⟨2847244067413056442649071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796325423217408590198761 2847244067413056442649071)
                      ·
                        rfl

theorem cell23_5544988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_5544988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544988 prefixEnd_5544988 := by exact prefixLift 5544988
  have htrace : WordTrace (prefixWord ++ tailWord_5544988) baseStart_5544988 baseEnd_5544988 := by
    simpa [prefixWord, tailWord_5544988, baseEnd_5544988] using wordTrace_append hprefix tailTrace_5544988
  have hstable : (prefixWord ++ tailWord_5544988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544988).length < 2 ^ (prefixWord ++ tailWord_5544988).sum := by decide
  have hdescent : baseEnd_5544988 < baseStart_5544988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5544997 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_5544997 : Nat := 118140960795 + 5544997 * 2 ^ 59
def prefixEnd_5544997 : Nat := 4983230072969 + 3 ^ 40 * 5544997 * 2
def baseEnd_5544997 : Nat := 2847248688738946907436529

theorem tailTrace_5544997 : CollatzResearch.WordTrace tailWord_5544997 prefixEnd_5544997 2847248688738946907436529 := by
  unfold tailWord_5544997
  simp only [CollatzResearch.WordTrace]
  refine ⟨202242655492430353937385245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134828436994953569291590163 202242655492430353937385245)
  ·
    refine ⟨75840995809661382726519467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202242655492430353937385245 75840995809661382726519467)
    ·
      refine ⟨113761493714492074089779201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75840995809661382726519467 113761493714492074089779201)
      ·
        refine ⟨85321120285869055567334401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113761493714492074089779201 85321120285869055567334401)
        ·
          refine ⟨63990840214401791675500801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85321120285869055567334401 63990840214401791675500801)
          ·
            refine ⟨47993130160801343756625601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63990840214401791675500801 47993130160801343756625601)
            ·
              refine ⟨35994847620601007817469201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47993130160801343756625601 35994847620601007817469201)
              ·
                refine ⟨26996135715450755863101901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35994847620601007817469201 26996135715450755863101901)
                ·
                  refine ⟨10123550893294033448663213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26996135715450755863101901 10123550893294033448663213)
                  ·
                    refine ⟨3796331584985262543248705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10123550893294033448663213 3796331584985262543248705)
                    ·
                      refine ⟨2847248688738946907436529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796331584985262543248705 2847248688738946907436529)
                      ·
                        rfl

theorem cell23_5544997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_5544997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5544997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5544997 prefixEnd_5544997 := by exact prefixLift 5544997
  have htrace : WordTrace (prefixWord ++ tailWord_5544997) baseStart_5544997 baseEnd_5544997 := by
    simpa [prefixWord, tailWord_5544997, baseEnd_5544997] using wordTrace_append hprefix tailTrace_5544997
  have hstable : (prefixWord ++ tailWord_5544997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5544997).length < 2 ^ (prefixWord ++ tailWord_5544997).sum := by decide
  have hdescent : baseEnd_5544997 < baseStart_5544997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5544997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545003 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 8]
def baseStart_5545003 : Nat := 118140960795 + 5545003 * 2 ^ 59
def prefixEnd_5545003 : Nat := 4983230072969 + 3 ^ 40 * 5545003 * 2
def baseEnd_5545003 : Nat := 949083923207624627987167

theorem tailTrace_5545003 : CollatzResearch.WordTrace tailWord_5545003 prefixEnd_5545003 949083923207624627987167 := by
  unfold tailWord_5545003
  simp only [CollatzResearch.WordTrace]
  refine ⟨202242874330408616962103663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134828582886939077974735775 202242874330408616962103663)
  ·
    refine ⟨303364311495612925443155495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202242874330408616962103663 303364311495612925443155495)
    ·
      refine ⟨455046467243419388164733243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303364311495612925443155495 455046467243419388164733243)
      ·
        refine ⟨682569700865129082247099865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455046467243419388164733243 682569700865129082247099865)
        ·
          refine ⟨511927275648846811685324899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682569700865129082247099865 511927275648846811685324899)
          ·
            refine ⟨767890913473270217527987349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511927275648846811685324899 767890913473270217527987349)
            ·
              refine ⟨35994886569059541446624407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 767890913473270217527987349 35994886569059541446624407)
              ·
                refine ⟨53992329853589312169936611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35994886569059541446624407 53992329853589312169936611)
                ·
                  refine ⟨80988494780383968254904917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53992329853589312169936611 80988494780383968254904917)
                  ·
                    refine ⟨949083923207624627987167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80988494780383968254904917 949083923207624627987167)
                    ·
                      rfl

theorem cell23_5545003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_5545003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545003 prefixEnd_5545003 := by exact prefixLift 5545003
  have htrace : WordTrace (prefixWord ++ tailWord_5545003) baseStart_5545003 baseEnd_5545003 := by
    simpa [prefixWord, tailWord_5545003, baseEnd_5545003] using wordTrace_append hprefix tailTrace_5545003
  have hstable : (prefixWord ++ tailWord_5545003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545003).length < 2 ^ (prefixWord ++ tailWord_5545003).sum := by decide
  have hdescent : baseEnd_5545003 < baseStart_5545003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545027 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 1, 4, 2]
def baseStart_5545027 : Nat := 118140960795 + 5545027 * 2 ^ 59
def prefixEnd_5545027 : Nat := 4983230072969 + 3 ^ 40 * 5545027 * 2
def baseEnd_5545027 : Nat := 2847264093158581790061391

theorem tailTrace_5545027 : CollatzResearch.WordTrace tailWord_5545027 prefixEnd_5545027 2847264093158581790061391 := by
  unfold tailWord_5545027
  simp only [CollatzResearch.WordTrace]
  refine ⟨202243749682321669060977335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134829166454881112707318223 202243749682321669060977335)
  ·
    refine ⟨303365624523482503591466003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202243749682321669060977335 303365624523482503591466003)
    ·
      refine ⟨455048436785223755387199005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303365624523482503591466003 455048436785223755387199005)
      ·
        refine ⟨170643163794458908270199627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455048436785223755387199005 170643163794458908270199627)
        ·
          refine ⟨255964745691688362405299441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170643163794458908270199627 255964745691688362405299441)
          ·
            refine ⟨191973559268766271803974581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255964745691688362405299441 191973559268766271803974581)
            ·
              refine ⟨17997521181446837981622617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191973559268766271803974581 17997521181446837981622617)
              ·
                refine ⟨13498140886085128486216963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17997521181446837981622617 13498140886085128486216963)
                ·
                  refine ⟨20247211329127692729325445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13498140886085128486216963 20247211329127692729325445)
                  ·
                    refine ⟨3796352124211442386748521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20247211329127692729325445 3796352124211442386748521)
                    ·
                      refine ⟨2847264093158581790061391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796352124211442386748521 2847264093158581790061391)
                      ·
                        rfl

theorem cell23_5545027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_5545027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545027 prefixEnd_5545027 := by exact prefixLift 5545027
  have htrace : WordTrace (prefixWord ++ tailWord_5545027) baseStart_5545027 baseEnd_5545027 := by
    simpa [prefixWord, tailWord_5545027, baseEnd_5545027] using wordTrace_append hprefix tailTrace_5545027
  have hstable : (prefixWord ++ tailWord_5545027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545027).length < 2 ^ (prefixWord ++ tailWord_5545027).sum := by decide
  have hdescent : baseEnd_5545027 < baseStart_5545027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545031 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_5545031 : Nat := 118140960795 + 5545031 * 2 ^ 59
def prefixEnd_5545031 : Nat := 4983230072969 + 3 ^ 40 * 5545031 * 2
def baseEnd_5545031 : Nat := 2847266147081199774411373

theorem tailTrace_5545031 : CollatzResearch.WordTrace tailWord_5545031 prefixEnd_5545031 2847266147081199774411373 := by
  unfold tailWord_5545031
  simp only [CollatzResearch.WordTrace]
  refine ⟨202243895574307177744122947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134829263716204785162748631 202243895574307177744122947)
  ·
    refine ⟨303365843361460766616184421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202243895574307177744122947 303365843361460766616184421)
    ·
      refine ⟨56881095630273893740534579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303365843361460766616184421 56881095630273893740534579)
      ·
        refine ⟨85321643445410840610801869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56881095630273893740534579 85321643445410840610801869)
        ·
          refine ⟨31995616292029065229050701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85321643445410840610801869 31995616292029065229050701)
          ·
            refine ⟨11998356109510899460894013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31995616292029065229050701 11998356109510899460894013)
            ·
              refine ⟨4499383541066587297835255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11998356109510899460894013 4499383541066587297835255)
              ·
                refine ⟨6749075311599880946752883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499383541066587297835255 6749075311599880946752883)
                ·
                  refine ⟨10123612967399821420129325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749075311599880946752883 10123612967399821420129325)
                  ·
                    refine ⟨3796354862774933032548497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10123612967399821420129325 3796354862774933032548497)
                    ·
                      refine ⟨2847266147081199774411373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796354862774933032548497 2847266147081199774411373)
                      ·
                        rfl

theorem cell23_5545031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_5545031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545031 prefixEnd_5545031 := by exact prefixLift 5545031
  have htrace : WordTrace (prefixWord ++ tailWord_5545031) baseStart_5545031 baseEnd_5545031 := by
    simpa [prefixWord, tailWord_5545031, baseEnd_5545031] using wordTrace_append hprefix tailTrace_5545031
  have hstable : (prefixWord ++ tailWord_5545031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545031).length < 2 ^ (prefixWord ++ tailWord_5545031).sum := by decide
  have hdescent : baseEnd_5545031 < baseStart_5545031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545033 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 11]
def baseStart_5545033 : Nat := 118140960795 + 5545033 * 2 ^ 59
def prefixEnd_5545033 : Nat := 4983230072969 + 3 ^ 40 * 5545033 * 2
def baseEnd_5545033 : Nat := 316363019338056529620707

theorem tailTrace_5545033 : CollatzResearch.WordTrace tailWord_5545033 prefixEnd_5545033 316363019338056529620707 := by
  unfold tailWord_5545033
  simp only [CollatzResearch.WordTrace]
  refine ⟨202243968520299932085695753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134829312346866621390463835 202243968520299932085695753)
  ·
    refine ⟨151682976390224949064271815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202243968520299932085695753 151682976390224949064271815)
    ·
      refine ⟨227524464585337423596407723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151682976390224949064271815 227524464585337423596407723)
      ·
        refine ⟨341286696878006135394611585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227524464585337423596407723 341286696878006135394611585)
        ·
          refine ⟨255965022658504601545958689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341286696878006135394611585 255965022658504601545958689)
          ·
            refine ⟨191973766993878451159469017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255965022658504601545958689 191973766993878451159469017)
            ·
              refine ⟨143980325245408838369601763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191973766993878451159469017 143980325245408838369601763)
              ·
                refine ⟨215970487868113257554402645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143980325245408838369601763 215970487868113257554402645)
                ·
                  refine ⟨316363019338056529620707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 215970487868113257554402645 316363019338056529620707)
                  ·
                    rfl

theorem cell23_5545033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_5545033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545033 prefixEnd_5545033 := by exact prefixLift 5545033
  have htrace : WordTrace (prefixWord ++ tailWord_5545033) baseStart_5545033 baseEnd_5545033 := by
    simpa [prefixWord, tailWord_5545033, baseEnd_5545033] using wordTrace_append hprefix tailTrace_5545033
  have hstable : (prefixWord ++ tailWord_5545033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545033).length < 2 ^ (prefixWord ++ tailWord_5545033).sum := by decide
  have hdescent : baseEnd_5545033 < baseStart_5545033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545043 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_5545043 : Nat := 118140960795 + 5545043 * 2 ^ 59
def prefixEnd_5545043 : Nat := 4983230072969 + 3 ^ 40 * 5545043 * 2
def baseEnd_5545043 : Nat := 2847272308849053727461317

theorem tailTrace_5545043 : CollatzResearch.WordTrace tailWord_5545043 prefixEnd_5545043 2847272308849053727461317 := by
  unfold tailWord_5545043
  simp only [CollatzResearch.WordTrace]
  refine ⟨202244333250263703793559783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134829555500175802529039855 202244333250263703793559783)
  ·
    refine ⟨303366499875395555690339675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202244333250263703793559783 303366499875395555690339675)
    ·
      refine ⟨455049749813093333535509513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303366499875395555690339675 455049749813093333535509513)
      ·
        refine ⟨341287312359820000151632135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455049749813093333535509513 341287312359820000151632135)
        ·
          refine ⟨511930968539730000227448203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341287312359820000151632135 511930968539730000227448203)
          ·
            refine ⟨767896452809595000341172305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511930968539730000227448203 767896452809595000341172305)
            ·
              refine ⟨575922339607196250255879229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767896452809595000341172305 575922339607196250255879229)
              ·
                refine ⟨215970877352698593845954711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575922339607196250255879229 215970877352698593845954711)
                ·
                  refine ⟨323956316029047890768932067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215970877352698593845954711 323956316029047890768932067)
                  ·
                    refine ⟨485934474043571836153398101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323956316029047890768932067 485934474043571836153398101)
                    ·
                      refine ⟨2847272308849053727461317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 485934474043571836153398101 2847272308849053727461317)
                      ·
                        rfl

theorem cell23_5545043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_5545043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545043 prefixEnd_5545043 := by exact prefixLift 5545043
  have htrace : WordTrace (prefixWord ++ tailWord_5545043) baseStart_5545043 baseEnd_5545043 := by
    simpa [prefixWord, tailWord_5545043, baseEnd_5545043] using wordTrace_append hprefix tailTrace_5545043
  have hstable : (prefixWord ++ tailWord_5545043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545043).length < 2 ^ (prefixWord ++ tailWord_5545043).sum := by decide
  have hdescent : baseEnd_5545043 < baseStart_5545043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545044 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_5545044 : Nat := 118140960795 + 5545044 * 2 ^ 59
def prefixEnd_5545044 : Nat := 4983230072969 + 3 ^ 40 * 5545044 * 2
def baseEnd_5545044 : Nat := 2847272822329708223548813

theorem tailTrace_5545044 : CollatzResearch.WordTrace tailWord_5545044 prefixEnd_5545044 2847272822329708223548813 := by
  unfold tailWord_5545044
  simp only [CollatzResearch.WordTrace]
  refine ⟨101122184861630040482173093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134829579815506720642897457 101122184861630040482173093)
  ·
    refine ⟨18960409661555632590407455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101122184861630040482173093 18960409661555632590407455)
    ·
      refine ⟨28440614492333448885611183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18960409661555632590407455 28440614492333448885611183)
      ·
        refine ⟨42660921738500173328416775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28440614492333448885611183 42660921738500173328416775)
        ·
          refine ⟨63991382607750259992625163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42660921738500173328416775 63991382607750259992625163)
          ·
            refine ⟨95987073911625389988937745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63991382607750259992625163 95987073911625389988937745)
            ·
              refine ⟨71990305433719042491703309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95987073911625389988937745 71990305433719042491703309)
              ·
                refine ⟨26996364537644640934388741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71990305433719042491703309 26996364537644640934388741)
                ·
                  refine ⟨5061818350808370175197889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26996364537644640934388741 5061818350808370175197889)
                  ·
                    refine ⟨3796363763106277631398417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5061818350808370175197889 3796363763106277631398417)
                    ·
                      refine ⟨2847272822329708223548813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796363763106277631398417 2847272822329708223548813)
                      ·
                        rfl

theorem cell23_5545044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_5545044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545044 prefixEnd_5545044 := by exact prefixLift 5545044
  have htrace : WordTrace (prefixWord ++ tailWord_5545044) baseStart_5545044 baseEnd_5545044 := by
    simpa [prefixWord, tailWord_5545044, baseEnd_5545044] using wordTrace_append hprefix tailTrace_5545044
  have hstable : (prefixWord ++ tailWord_5545044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545044).length < 2 ^ (prefixWord ++ tailWord_5545044).sum := by decide
  have hdescent : baseEnd_5545044 < baseStart_5545044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545054 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_5545054 : Nat := 118140960795 + 5545054 * 2 ^ 59
def prefixEnd_5545054 : Nat := 4983230072969 + 3 ^ 40 * 5545054 * 2
def baseEnd_5545054 : Nat := 949092652378751061474589

theorem tailTrace_5545054 : CollatzResearch.WordTrace tailWord_5545054 prefixEnd_5545054 949092652378751061474589 := by
  unfold tailWord_5545054
  simp only [CollatzResearch.WordTrace]
  refine ⟨25280591806652981584026277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134829822968815901781473477 25280591806652981584026277)
  ·
    refine ⟨4740110963747434047004927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25280591806652981584026277 4740110963747434047004927)
    ·
      refine ⟨7110166445621151070507391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740110963747434047004927 7110166445621151070507391)
      ·
        refine ⟨10665249668431726605761087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110166445621151070507391 10665249668431726605761087)
        ·
          refine ⟨15997874502647589908641631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665249668431726605761087 15997874502647589908641631)
          ·
            refine ⟨23996811753971384862962447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15997874502647589908641631 23996811753971384862962447)
            ·
              refine ⟨35995217630957077294443671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23996811753971384862962447 35995217630957077294443671)
              ·
                refine ⟨53992826446435615941665507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35995217630957077294443671 53992826446435615941665507)
                ·
                  refine ⟨80989239669653423912498261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53992826446435615941665507 80989239669653423912498261)
                  ·
                    refine ⟨949092652378751061474589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80989239669653423912498261 949092652378751061474589)
                    ·
                      rfl

theorem cell23_5545054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_5545054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545054 prefixEnd_5545054 := by exact prefixLift 5545054
  have htrace : WordTrace (prefixWord ++ tailWord_5545054) baseStart_5545054 baseEnd_5545054 := by
    simpa [prefixWord, tailWord_5545054, baseEnd_5545054] using wordTrace_append hprefix tailTrace_5545054
  have hstable : (prefixWord ++ tailWord_5545054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545054).length < 2 ^ (prefixWord ++ tailWord_5545054).sum := by decide
  have hdescent : baseEnd_5545054 < baseStart_5545054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545144 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 1, 4]
def baseStart_5545144 : Nat := 118140960795 + 5545144 * 2 ^ 59
def prefixEnd_5545144 : Nat := 4983230072969 + 3 ^ 40 * 5545144 * 2
def baseEnd_5545144 : Nat := 949108056798385944099451

theorem tailTrace_5545144 : CollatzResearch.WordTrace tailWord_5545144 prefixEnd_5545144 949108056798385944099451 := by
  unfold tailWord_5545144
  simp only [CollatzResearch.WordTrace]
  refine ⟨101124008511448899021493243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134832011348598532028657657 101124008511448899021493243)
  ·
    refine ⟨151686012767173348532239865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101124008511448899021493243 151686012767173348532239865)
    ·
      refine ⟨113764509575380011399179899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151686012767173348532239865 113764509575380011399179899)
      ·
        refine ⟨170646764363070017098769849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113764509575380011399179899 170646764363070017098769849)
        ·
          refine ⟨127985073272302512824077387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170646764363070017098769849 127985073272302512824077387)
          ·
            refine ⟨191977609908453769236116081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127985073272302512824077387 191977609908453769236116081)
            ·
              refine ⟨143983207431340326927087061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191977609908453769236116081 143983207431340326927087061)
              ·
                refine ⟨3374606424172038912353603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143983207431340326927087061 3374606424172038912353603)
                ·
                  refine ⟨5061909636258058368530405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374606424172038912353603 5061909636258058368530405)
                  ·
                    refine ⟨949108056798385944099451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5061909636258058368530405 949108056798385944099451)
                    ·
                      rfl

theorem cell23_5545144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_5545144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545144 prefixEnd_5545144 := by exact prefixLift 5545144
  have htrace : WordTrace (prefixWord ++ tailWord_5545144) baseStart_5545144 baseEnd_5545144 := by
    simpa [prefixWord, tailWord_5545144, baseEnd_5545144] using wordTrace_append hprefix tailTrace_5545144
  have hstable : (prefixWord ++ tailWord_5545144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545144).length < 2 ^ (prefixWord ++ tailWord_5545144).sum := by decide
  have hdescent : baseEnd_5545144 < baseStart_5545144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545158 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5545158 : Nat := 118140960795 + 5545158 * 2 ^ 59
def prefixEnd_5545158 : Nat := 4983230072969 + 3 ^ 40 * 5545158 * 2
def baseEnd_5545158 : Nat := 2847331359124320777523289

theorem tailTrace_5545158 : CollatzResearch.WordTrace tailWord_5545158 prefixEnd_5545158 2847331359124320777523289 := by
  unfold tailWord_5545158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320266488901471201062379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134832351763231385622664085 6320266488901471201062379)
  ·
    refine ⟨9480399733352206801593569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6320266488901471201062379 9480399733352206801593569)
    ·
      refine ⟨7110299800014155101195177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9480399733352206801593569 7110299800014155101195177)
      ·
        refine ⟨5332724850010616325896383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7110299800014155101195177 5332724850010616325896383)
        ·
          refine ⟨7999087275015924488844575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332724850010616325896383 7999087275015924488844575)
          ·
            refine ⟨11998630912523886733266863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999087275015924488844575 11998630912523886733266863)
            ·
              refine ⟨17997946368785830099900295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998630912523886733266863 17997946368785830099900295)
              ·
                refine ⟨26996919553178745149850443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17997946368785830099900295 26996919553178745149850443)
                ·
                  refine ⟨40495379329768117724775665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26996919553178745149850443 40495379329768117724775665)
                  ·
                    refine ⟨30371534497326088293581749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40495379329768117724775665 30371534497326088293581749)
                    ·
                      refine ⟨2847331359124320777523289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30371534497326088293581749 2847331359124320777523289)
                      ·
                        rfl

theorem cell23_5545158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5545158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545158 prefixEnd_5545158 := by exact prefixLift 5545158
  have htrace : WordTrace (prefixWord ++ tailWord_5545158) baseStart_5545158 baseEnd_5545158 := by
    simpa [prefixWord, tailWord_5545158, baseEnd_5545158] using wordTrace_append hprefix tailTrace_5545158
  have hstable : (prefixWord ++ tailWord_5545158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545158).length < 2 ^ (prefixWord ++ tailWord_5545158).sum := by decide
  have hdescent : baseEnd_5545158 < baseStart_5545158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545160 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_5545160 : Nat := 118140960795 + 5545160 * 2 ^ 59
def prefixEnd_5545160 : Nat := 4983230072969 + 3 ^ 40 * 5545160 * 2
def baseEnd_5545160 : Nat := 2847332386085629769698279

theorem tailTrace_5545160 : CollatzResearch.WordTrace tailWord_5545160 prefixEnd_5545160 2847332386085629769698279 := by
  unfold tailWord_5545160
  simp only [CollatzResearch.WordTrace]
  refine ⟨101124300295419916387784467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134832400393893221850379289 101124300295419916387784467)
  ·
    refine ⟨151686450443129874581676701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101124300295419916387784467 151686450443129874581676701)
    ·
      refine ⟨56882418916173702968128763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151686450443129874581676701 56882418916173702968128763)
      ·
        refine ⟨85323628374260554452193145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56882418916173702968128763 85323628374260554452193145)
        ·
          refine ⟨63992721280695415839144859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85323628374260554452193145 63992721280695415839144859)
          ·
            refine ⟨95989081921043123758717289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63992721280695415839144859 95989081921043123758717289)
            ·
              refine ⟨71991811440782342819037967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95989081921043123758717289 71991811440782342819037967)
              ·
                refine ⟨107987717161173514228556951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71991811440782342819037967 107987717161173514228556951)
                ·
                  refine ⟨161981575741760271342835427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107987717161173514228556951 161981575741760271342835427)
                  ·
                    refine ⟨242972363612640407014253141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161981575741760271342835427 242972363612640407014253141)
                    ·
                      refine ⟨2847332386085629769698279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 242972363612640407014253141 2847332386085629769698279)
                      ·
                        rfl

theorem cell23_5545160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_5545160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545160 prefixEnd_5545160 := by exact prefixLift 5545160
  have htrace : WordTrace (prefixWord ++ tailWord_5545160) baseStart_5545160 baseEnd_5545160 := by
    simpa [prefixWord, tailWord_5545160, baseEnd_5545160] using wordTrace_append hprefix tailTrace_5545160
  have hstable : (prefixWord ++ tailWord_5545160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545160).length < 2 ^ (prefixWord ++ tailWord_5545160).sum := by decide
  have hdescent : baseEnd_5545160 < baseStart_5545160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545201 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 1, 1, 3]
def baseStart_5545201 : Nat := 118140960795 + 5545201 * 2 ^ 59
def prefixEnd_5545201 : Nat := 4983230072969 + 3 ^ 40 * 5545201 * 2
def baseEnd_5545201 : Nat := 2847353438792464109285591

theorem tailTrace_5545201 : CollatzResearch.WordTrace tailWord_5545201 prefixEnd_5545201 2847353438792464109285591 := by
  unfold tailWord_5545201
  simp only [CollatzResearch.WordTrace]
  refine ⟨202250095983691296777811457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134833397322460864518540971 202250095983691296777811457)
  ·
    refine ⟨151687571987768472583358593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202250095983691296777811457 151687571987768472583358593)
    ·
      refine ⟨113765678990826354437518945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151687571987768472583358593 113765678990826354437518945)
      ·
        refine ⟨85324259243119765828139209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113765678990826354437518945 85324259243119765828139209)
        ·
          refine ⟨63993194432339824371104407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85324259243119765828139209 63993194432339824371104407)
          ·
            refine ⟨95989791648509736556656611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63993194432339824371104407 95989791648509736556656611)
            ·
              refine ⟨143984687472764604834984917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95989791648509736556656611 143984687472764604834984917)
              ·
                refine ⟨3374641112642920425819959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143984687472764604834984917 3374641112642920425819959)
                ·
                  refine ⟨5061961668964380638729939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374641112642920425819959 5061961668964380638729939)
                  ·
                    refine ⟨7592942503446570958094909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5061961668964380638729939 7592942503446570958094909)
                    ·
                      refine ⟨2847353438792464109285591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7592942503446570958094909 2847353438792464109285591)
                      ·
                        rfl

theorem cell23_5545201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_5545201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545201 prefixEnd_5545201 := by exact prefixLift 5545201
  have htrace : WordTrace (prefixWord ++ tailWord_5545201) baseStart_5545201 baseEnd_5545201 := by
    simpa [prefixWord, tailWord_5545201, baseEnd_5545201] using wordTrace_append hprefix tailTrace_5545201
  have hstable : (prefixWord ++ tailWord_5545201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545201).length < 2 ^ (prefixWord ++ tailWord_5545201).sum := by decide
  have hdescent : baseEnd_5545201 < baseStart_5545201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545244 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 3, 2, 3]
def baseStart_5545244 : Nat := 118140960795 + 5545244 * 2 ^ 59
def prefixEnd_5545244 : Nat := 4983230072969 + 3 ^ 40 * 5545244 * 2
def baseEnd_5545244 : Nat := 2847375518460607441047893

theorem tailTrace_5545244 : CollatzResearch.WordTrace tailWord_5545244 prefixEnd_5545244 2847375518460607441047893 := by
  unfold tailWord_5545244
  simp only [CollatzResearch.WordTrace]
  refine ⟨101125832161267757560813393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134834442881690343414417857 101125832161267757560813393)
  ·
    refine ⟨75844374120950818170610045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101125832161267757560813393 75844374120950818170610045)
    ·
      refine ⟨28441640295356556813978767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75844374120950818170610045 28441640295356556813978767)
      ·
        refine ⟨42662460443034835220968151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28441640295356556813978767 42662460443034835220968151)
        ·
          refine ⟨63993690664552252831452227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42662460443034835220968151 63993690664552252831452227)
          ·
            refine ⟨95990535996828379247178341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63993690664552252831452227 95990535996828379247178341)
            ·
              refine ⟨17998225499405321108845939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95990535996828379247178341 17998225499405321108845939)
              ·
                refine ⟨26997338249107981663268909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17998225499405321108845939 26997338249107981663268909)
                ·
                  refine ⟨10124001843415493123725841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26997338249107981663268909 10124001843415493123725841)
                  ·
                    refine ⟨7593001382561619842794381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10124001843415493123725841 7593001382561619842794381)
                    ·
                      refine ⟨2847375518460607441047893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593001382561619842794381 2847375518460607441047893)
                      ·
                        rfl

theorem cell23_5545244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_5545244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545244 prefixEnd_5545244 := by exact prefixLift 5545244
  have htrace : WordTrace (prefixWord ++ tailWord_5545244) baseStart_5545244 baseEnd_5545244 := by
    simpa [prefixWord, tailWord_5545244, baseEnd_5545244] using wordTrace_append hprefix tailTrace_5545244
  have hstable : (prefixWord ++ tailWord_5545244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545244).length < 2 ^ (prefixWord ++ tailWord_5545244).sum := by decide
  have hdescent : baseEnd_5545244 < baseStart_5545244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545257 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_5545257 : Nat := 118140960795 + 5545257 * 2 ^ 59
def prefixEnd_5545257 : Nat := 4983230072969 + 3 ^ 40 * 5545257 * 2
def baseEnd_5545257 : Nat := 2847382193709115890185333

theorem tailTrace_5545257 : CollatzResearch.WordTrace tailWord_5545257 prefixEnd_5545257 2847382193709115890185333 := by
  unfold tailWord_5545257
  simp only [CollatzResearch.WordTrace]
  refine ⟨202252138471488418341850025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134834758980992278894566683 202252138471488418341850025)
  ·
    refine ⟨151689103853616313756387519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202252138471488418341850025 151689103853616313756387519)
    ·
      refine ⟨227533655780424470634581279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151689103853616313756387519 227533655780424470634581279)
      ·
        refine ⟨341300483670636705951871919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227533655780424470634581279 341300483670636705951871919)
        ·
          refine ⟨511950725505955058927807879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341300483670636705951871919 511950725505955058927807879)
          ·
            refine ⟨767926088258932588391711819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511950725505955058927807879 767926088258932588391711819)
            ·
              refine ⟨1151889132388398882587567729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767926088258932588391711819 1151889132388398882587567729)
              ·
                refine ⟨863916849291299161940675797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151889132388398882587567729 863916849291299161940675797)
                ·
                  refine ⟨20248051155264824107984589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 863916849291299161940675797 20248051155264824107984589)
                  ·
                    refine ⟨7593019183224309040494221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20248051155264824107984589 7593019183224309040494221)
                    ·
                      refine ⟨2847382193709115890185333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593019183224309040494221 2847382193709115890185333)
                      ·
                        rfl

theorem cell23_5545257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_5545257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545257 prefixEnd_5545257 := by exact prefixLift 5545257
  have htrace : WordTrace (prefixWord ++ tailWord_5545257) baseStart_5545257 baseEnd_5545257 := by
    simpa [prefixWord, tailWord_5545257, baseEnd_5545257] using wordTrace_append hprefix tailTrace_5545257
  have hstable : (prefixWord ++ tailWord_5545257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545257).length < 2 ^ (prefixWord ++ tailWord_5545257).sum := by decide
  have hdescent : baseEnd_5545257 < baseStart_5545257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545258 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5545258 : Nat := 118140960795 + 5545258 * 2 ^ 59
def prefixEnd_5545258 : Nat := 4983230072969 + 3 ^ 40 * 5545258 * 2
def baseEnd_5545258 : Nat := 2847382707189770386272829

theorem tailTrace_5545258 : CollatzResearch.WordTrace tailWord_5545258 prefixEnd_5545258 2847382707189770386272829 := by
  unfold tailWord_5545258
  simp only [CollatzResearch.WordTrace]
  refine ⟨50563043736121198878159107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134834783296323197008424285 50563043736121198878159107)
  ·
    refine ⟨75844565604181798317238661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50563043736121198878159107 75844565604181798317238661)
    ·
      refine ⟨14220856050784087184482249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75844565604181798317238661 14220856050784087184482249)
      ·
        refine ⟨10665642038088065388361687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14220856050784087184482249 10665642038088065388361687)
        ·
          refine ⟨15998463057132098082542531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10665642038088065388361687 15998463057132098082542531)
          ·
            refine ⟨23997694585698147123813797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15998463057132098082542531 23997694585698147123813797)
            ·
              refine ⟨4499567734818402585715087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23997694585698147123813797 4499567734818402585715087)
              ·
                refine ⟨6749351602227603878572631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499567734818402585715087 6749351602227603878572631)
                ·
                  refine ⟨10124027403341405817858947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749351602227603878572631 10124027403341405817858947)
                  ·
                    refine ⟨15186041105012108726788421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10124027403341405817858947 15186041105012108726788421)
                    ·
                      refine ⟨2847382707189770386272829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15186041105012108726788421 2847382707189770386272829)
                      ·
                        rfl

theorem cell23_5545258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5545258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545258 prefixEnd_5545258 := by exact prefixLift 5545258
  have htrace : WordTrace (prefixWord ++ tailWord_5545258) baseStart_5545258 baseEnd_5545258 := by
    simpa [prefixWord, tailWord_5545258, baseEnd_5545258] using wordTrace_append hprefix tailTrace_5545258
  have hstable : (prefixWord ++ tailWord_5545258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545258).length < 2 ^ (prefixWord ++ tailWord_5545258).sum := by decide
  have hdescent : baseEnd_5545258 < baseStart_5545258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545342 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5545342 : Nat := 118140960795 + 5545342 * 2 ^ 59
def prefixEnd_5545342 : Nat := 4983230072969 + 3 ^ 40 * 5545342 * 2
def baseEnd_5545342 : Nat := 2847425839564748057622443

theorem tailTrace_5545342 : CollatzResearch.WordTrace tailWord_5545342 prefixEnd_5545342 2847425839564748057622443 := by
  unfold tailWord_5545342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25281904834522559732336785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134836825784120318572462853 25281904834522559732336785)
  ·
    refine ⟨18961428625891919799252589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25281904834522559732336785 18961428625891919799252589)
    ·
      refine ⟨7110535734709469924719721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18961428625891919799252589 7110535734709469924719721)
      ·
        refine ⟨5332901801032102443539791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7110535734709469924719721 5332901801032102443539791)
        ·
          refine ⟨7999352701548153665309687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332901801032102443539791 7999352701548153665309687)
          ·
            refine ⟨11999029052322230497964531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999352701548153665309687 11999029052322230497964531)
            ·
              refine ⟨17998543578483345746946797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11999029052322230497964531 17998543578483345746946797)
              ·
                refine ⟨6749453841931254655105049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17998543578483345746946797 6749453841931254655105049)
                ·
                  refine ⟨5062090381448440991328787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6749453841931254655105049 5062090381448440991328787)
                  ·
                    refine ⟨7593135572172661486993181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062090381448440991328787 7593135572172661486993181)
                    ·
                      refine ⟨2847425839564748057622443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593135572172661486993181 2847425839564748057622443)
                      ·
                        rfl

theorem cell23_5545342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5545342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545342 prefixEnd_5545342 := by exact prefixLift 5545342
  have htrace : WordTrace (prefixWord ++ tailWord_5545342) baseStart_5545342 baseEnd_5545342 := by
    simpa [prefixWord, tailWord_5545342, baseEnd_5545342] using wordTrace_append hprefix tailTrace_5545342
  have hstable : (prefixWord ++ tailWord_5545342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545342).length < 2 ^ (prefixWord ++ tailWord_5545342).sum := by decide
  have hdescent : baseEnd_5545342 < baseStart_5545342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545424 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_5545424 : Nat := 118140960795 + 5545424 * 2 ^ 59
def prefixEnd_5545424 : Nat := 4983230072969 + 3 ^ 40 * 5545424 * 2
def baseEnd_5545424 : Nat := 2847467944978416736797065

theorem tailTrace_5545424 : CollatzResearch.WordTrace tailWord_5545424 prefixEnd_5545424 2847467944978416736797065 := by
  unfold tailWord_5545424
  simp only [CollatzResearch.WordTrace]
  refine ⟨101129114730941702931589663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134838819641255603908786217 101129114730941702931589663)
  ·
    refine ⟨151693672096412554397384495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101129114730941702931589663 151693672096412554397384495)
    ·
      refine ⟨227540508144618831596076743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151693672096412554397384495 227540508144618831596076743)
      ·
        refine ⟨341310762216928247394115115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227540508144618831596076743 341310762216928247394115115)
        ·
          refine ⟨511966143325392371091172673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341310762216928247394115115 511966143325392371091172673)
          ·
            refine ⟨383974607494044278318379505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511966143325392371091172673 383974607494044278318379505)
            ·
              refine ⟨287980955620533208738784629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383974607494044278318379505 287980955620533208738784629)
              ·
                refine ⟨26998214589424988319261059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287980955620533208738784629 26998214589424988319261059)
                ·
                  refine ⟨40497321884137482478891589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26998214589424988319261059 40497321884137482478891589)
                  ·
                    refine ⟨7593247853275777964792173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40497321884137482478891589 7593247853275777964792173)
                    ·
                      refine ⟨2847467944978416736797065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593247853275777964792173 2847467944978416736797065)
                      ·
                        rfl

theorem cell23_5545424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_5545424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545424 prefixEnd_5545424 := by exact prefixLift 5545424
  have htrace : WordTrace (prefixWord ++ tailWord_5545424) baseStart_5545424 baseEnd_5545424 := by
    simpa [prefixWord, tailWord_5545424, baseEnd_5545424] using wordTrace_append hprefix tailTrace_5545424
  have hstable : (prefixWord ++ tailWord_5545424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545424).length < 2 ^ (prefixWord ++ tailWord_5545424).sum := by decide
  have hdescent : baseEnd_5545424 < baseStart_5545424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545434 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_5545434 : Nat := 118140960795 + 5545434 * 2 ^ 59
def prefixEnd_5545434 : Nat := 4983230072969 + 3 ^ 40 * 5545434 * 2
def baseEnd_5545434 : Nat := 2847473079784961697672019

theorem tailTrace_5545434 : CollatzResearch.WordTrace tailWord_5545434 prefixEnd_5545434 2847473079784961697672019 := by
  unfold tailWord_5545434
  simp only [CollatzResearch.WordTrace]
  refine ⟨50564648547961794392760839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134839062794564785047362237 50564648547961794392760839)
  ·
    refine ⟨75846972821942691589141259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50564648547961794392760839 75846972821942691589141259)
    ·
      refine ⟨113770459232914037383711889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75846972821942691589141259 113770459232914037383711889)
      ·
        refine ⟨85327844424685528037783917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113770459232914037383711889 85327844424685528037783917)
        ·
          refine ⟨31997941659257073014168969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85327844424685528037783917 31997941659257073014168969)
          ·
            refine ⟨23998456244442804760626727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31997941659257073014168969 23998456244442804760626727)
            ·
              refine ⟨35997684366664207140940091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23998456244442804760626727 35997684366664207140940091)
              ·
                refine ⟨53996526549996310711410137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35997684366664207140940091 53996526549996310711410137)
                ·
                  refine ⟨40497394912497233033557603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53996526549996310711410137 40497394912497233033557603)
                  ·
                    refine ⟨60746092368745849550336405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40497394912497233033557603 60746092368745849550336405)
                    ·
                      refine ⟨2847473079784961697672019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60746092368745849550336405 2847473079784961697672019)
                      ·
                        rfl

theorem cell23_5545434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_5545434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545434 prefixEnd_5545434 := by exact prefixLift 5545434
  have htrace : WordTrace (prefixWord ++ tailWord_5545434) baseStart_5545434 baseEnd_5545434 := by
    simpa [prefixWord, tailWord_5545434, baseEnd_5545434] using wordTrace_append hprefix tailTrace_5545434
  have hstable : (prefixWord ++ tailWord_5545434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545434).length < 2 ^ (prefixWord ++ tailWord_5545434).sum := by decide
  have hdescent : baseEnd_5545434 < baseStart_5545434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545448 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5545448 : Nat := 118140960795 + 5545448 * 2 ^ 59
def prefixEnd_5545448 : Nat := 4983230072969 + 3 ^ 40 * 5545448 * 2
def baseEnd_5545448 : Nat := 949160089504708214298985

theorem tailTrace_5545448 : CollatzResearch.WordTrace tailWord_5545448 prefixEnd_5545448 949160089504708214298985 := by
  unfold tailWord_5545448
  simp only [CollatzResearch.WordTrace]
  refine ⟨101129552406898228981026499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134839403209197638641368665 101129552406898228981026499)
  ·
    refine ⟨151694328610347343471539749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101129552406898228981026499 151694328610347343471539749)
    ·
      refine ⟨28442686614440126900913703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151694328610347343471539749 28442686614440126900913703)
      ·
        refine ⟨42664029921660190351370555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28442686614440126900913703 42664029921660190351370555)
        ·
          refine ⟨63996044882490285527055833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42664029921660190351370555 63996044882490285527055833)
          ·
            refine ⟨47997033661867714145291875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63996044882490285527055833 47997033661867714145291875)
            ·
              refine ⟨71995550492801571217937813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47997033661867714145291875 71995550492801571217937813)
              ·
                refine ⟨3374791429350073650840835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71995550492801571217937813 3374791429350073650840835)
                ·
                  refine ⟨5062187144025110476261253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374791429350073650840835 5062187144025110476261253)
                  ·
                    refine ⟨949160089504708214298985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062187144025110476261253 949160089504708214298985)
                    ·
                      rfl

theorem cell23_5545448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5545448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545448 prefixEnd_5545448 := by exact prefixLift 5545448
  have htrace : WordTrace (prefixWord ++ tailWord_5545448) baseStart_5545448 baseEnd_5545448 := by
    simpa [prefixWord, tailWord_5545448, baseEnd_5545448] using wordTrace_append hprefix tailTrace_5545448
  have hstable : (prefixWord ++ tailWord_5545448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545448).length < 2 ^ (prefixWord ++ tailWord_5545448).sum := by decide
  have hdescent : baseEnd_5545448 < baseStart_5545448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545471 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 3]
def baseStart_5545471 : Nat := 118140960795 + 5545471 * 2 ^ 59
def prefixEnd_5545471 : Nat := 4983230072969 + 3 ^ 40 * 5545471 * 2
def baseEnd_5545471 : Nat := 2847492078569178052909349

theorem tailTrace_5545471 : CollatzResearch.WordTrace tailWord_5545471 prefixEnd_5545471 2847492078569178052909349 := by
  unfold tailWord_5545471
  simp only [CollatzResearch.WordTrace]
  refine ⟨202259943692713132890140267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134839962461808755260093511 202259943692713132890140267)
  ·
    refine ⟨303389915539069699335210401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202259943692713132890140267 303389915539069699335210401)
    ·
      refine ⟨227542436654302274501407801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303389915539069699335210401 227542436654302274501407801)
      ·
        refine ⟨170656827490726705876055851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227542436654302274501407801 170656827490726705876055851)
        ·
          refine ⟨255985241236090058814083777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170656827490726705876055851 255985241236090058814083777)
          ·
            refine ⟨191988930927067544110562833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255985241236090058814083777 191988930927067544110562833)
            ·
              refine ⟨143991698195300658082922125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191988930927067544110562833 143991698195300658082922125)
              ·
                refine ⟨53996886823237746781095797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143991698195300658082922125 53996886823237746781095797)
                ·
                  refine ⟨5062208139678538760727731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53996886823237746781095797 5062208139678538760727731)
                  ·
                    refine ⟨7593312209517808141091597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062208139678538760727731 7593312209517808141091597)
                    ·
                      refine ⟨2847492078569178052909349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593312209517808141091597 2847492078569178052909349)
                      ·
                        rfl

theorem cell23_5545471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_5545471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545471 prefixEnd_5545471 := by exact prefixLift 5545471
  have htrace : WordTrace (prefixWord ++ tailWord_5545471) baseStart_5545471 baseEnd_5545471 := by
    simpa [prefixWord, tailWord_5545471, baseEnd_5545471] using wordTrace_append hprefix tailTrace_5545471
  have hstable : (prefixWord ++ tailWord_5545471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545471).length < 2 ^ (prefixWord ++ tailWord_5545471).sum := by decide
  have hdescent : baseEnd_5545471 < baseStart_5545471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545481 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 5, 2]
def baseStart_5545481 : Nat := 118140960795 + 5545481 * 2 ^ 59
def prefixEnd_5545481 : Nat := 4983230072969 + 3 ^ 40 * 5545481 * 2
def baseEnd_5545481 : Nat := 2847497213375723013784303

theorem tailTrace_5545481 : CollatzResearch.WordTrace tailWord_5545481 prefixEnd_5545481 2847497213375723013784303 := by
  unfold tailWord_5545481
  simp only [CollatzResearch.WordTrace]
  refine ⟨202260308422676904598004297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134840205615117936398669531 202260308422676904598004297)
  ·
    refine ⟨151695231317007678448503223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202260308422676904598004297 151695231317007678448503223)
    ·
      refine ⟨227542846975511517672754835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151695231317007678448503223 227542846975511517672754835)
      ·
        refine ⟨341314270463267276509132253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227542846975511517672754835 341314270463267276509132253)
        ·
          refine ⟨127992851423725228690924595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341314270463267276509132253 127992851423725228690924595)
          ·
            refine ⟨191989277135587843036386893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127992851423725228690924595 191989277135587843036386893)
            ·
              refine ⟨71995978925845441138645085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191989277135587843036386893 71995978925845441138645085)
              ·
                refine ⟨26998492097192040426991907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71995978925845441138645085 26998492097192040426991907)
                ·
                  refine ⟨40497738145788060640487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26998492097192040426991907 40497738145788060640487861)
                  ·
                    refine ⟨3796662951167630685045737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40497738145788060640487861 3796662951167630685045737)
                    ·
                      refine ⟨2847497213375723013784303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796662951167630685045737 2847497213375723013784303)
                      ·
                        rfl

theorem cell23_5545481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 5, 2].length) (baseStart_5545481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545481 prefixEnd_5545481 := by exact prefixLift 5545481
  have htrace : WordTrace (prefixWord ++ tailWord_5545481) baseStart_5545481 baseEnd_5545481 := by
    simpa [prefixWord, tailWord_5545481, baseEnd_5545481] using wordTrace_append hprefix tailTrace_5545481
  have hstable : (prefixWord ++ tailWord_5545481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545481).length < 2 ^ (prefixWord ++ tailWord_5545481).sum := by decide
  have hdescent : baseEnd_5545481 < baseStart_5545481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545491 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 1, 5]
def baseStart_5545491 : Nat := 118140960795 + 5545491 * 2 ^ 59
def prefixEnd_5545491 : Nat := 4983230072969 + 3 ^ 40 * 5545491 * 2
def baseEnd_5545491 : Nat := 949167449394089324886419

theorem tailTrace_5545491 : CollatzResearch.WordTrace tailWord_5545491 prefixEnd_5545491 949167449394089324886419 := by
  unfold tailWord_5545491
  simp only [CollatzResearch.WordTrace]
  refine ⟨202260673152640676305868327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134840448768427117537245551 202260673152640676305868327)
  ·
    refine ⟨303391009728961014458802491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202260673152640676305868327 303391009728961014458802491)
    ·
      refine ⟨455086514593441521688203737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303391009728961014458802491 455086514593441521688203737)
      ·
        refine ⟨341314885945081141266152803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455086514593441521688203737 341314885945081141266152803)
        ·
          refine ⟨511972328917621711899229205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341314885945081141266152803 511972328917621711899229205)
          ·
            refine ⟨23998702918013517745276369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 511972328917621711899229205 23998702918013517745276369)
            ·
              refine ⟨17999027188510138308957277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23998702918013517745276369 17999027188510138308957277)
              ·
                refine ⟨6749635195691301865858979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17999027188510138308957277 6749635195691301865858979)
                ·
                  refine ⟨10124452793536952798788469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749635195691301865858979 10124452793536952798788469)
                  ·
                    refine ⟨949167449394089324886419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10124452793536952798788469 949167449394089324886419)
                    ·
                      rfl

theorem cell23_5545491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 5].length) (baseStart_5545491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545491 prefixEnd_5545491 := by exact prefixLift 5545491
  have htrace : WordTrace (prefixWord ++ tailWord_5545491) baseStart_5545491 baseEnd_5545491 := by
    simpa [prefixWord, tailWord_5545491, baseEnd_5545491] using wordTrace_append hprefix tailTrace_5545491
  have hstable : (prefixWord ++ tailWord_5545491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545491).length < 2 ^ (prefixWord ++ tailWord_5545491).sum := by decide
  have hdescent : baseEnd_5545491 < baseStart_5545491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545505 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5545505 : Nat := 118140960795 + 5545505 * 2 ^ 59
def prefixEnd_5545505 : Nat := 4983230072969 + 3 ^ 40 * 5545505 * 2
def baseEnd_5545505 : Nat := 2847509536911430919884193

theorem tailTrace_5545505 : CollatzResearch.WordTrace tailWord_5545505 prefixEnd_5545505 2847509536911430919884193 := by
  unfold tailWord_5545505
  simp only [CollatzResearch.WordTrace]
  refine ⟨202261183774589956696877969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134840789183059971131251979 202261183774589956696877969)
  ·
    refine ⟨151695887830942467522658477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202261183774589956696877969 151695887830942467522658477)
    ·
      refine ⟨56885957936603425320996929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151695887830942467522658477 56885957936603425320996929)
      ·
        refine ⟨42664468452452568990747697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56885957936603425320996929 42664468452452568990747697)
        ·
          refine ⟨31998351339339426743060773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42664468452452568990747697 31998351339339426743060773)
          ·
            refine ⟨5999690876126142514323895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31998351339339426743060773 5999690876126142514323895)
            ·
              refine ⟨8999536314189213771485843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5999690876126142514323895 8999536314189213771485843)
              ·
                refine ⟨13499304471283820657228765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8999536314189213771485843 13499304471283820657228765)
                ·
                  refine ⟨5062239176731432746460787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13499304471283820657228765 5062239176731432746460787)
                  ·
                    refine ⟨7593358765097149119691181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062239176731432746460787 7593358765097149119691181)
                    ·
                      refine ⟨2847509536911430919884193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593358765097149119691181 2847509536911430919884193)
                      ·
                        rfl

theorem cell23_5545505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5545505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545505 prefixEnd_5545505 := by exact prefixLift 5545505
  have htrace : WordTrace (prefixWord ++ tailWord_5545505) baseStart_5545505 baseEnd_5545505 := by
    simpa [prefixWord, tailWord_5545505, baseEnd_5545505] using wordTrace_append hprefix tailTrace_5545505
  have hstable : (prefixWord ++ tailWord_5545505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545505).length < 2 ^ (prefixWord ++ tailWord_5545505).sum := by decide
  have hdescent : baseEnd_5545505 < baseStart_5545505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545512 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 6]
def baseStart_5545512 : Nat := 118140960795 + 5545512 * 2 ^ 59
def prefixEnd_5545512 : Nat := 4983230072969 + 3 ^ 40 * 5545512 * 2
def baseEnd_5545512 : Nat := 316390347919556932499629

theorem tailTrace_5545512 : CollatzResearch.WordTrace tailWord_5545512 prefixEnd_5545512 316390347919556932499629 := by
  unfold tailWord_5545512
  simp only [CollatzResearch.WordTrace]
  refine ⟨101130719542782298446191395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134840959390376397928255193 101130719542782298446191395)
  ·
    refine ⟨151696079314173447669287093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101130719542782298446191395 151696079314173447669287093)
    ·
      refine ⟨14221507435703760718995665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151696079314173447669287093 14221507435703760718995665)
      ·
        refine ⟨10666130576777820539246749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14221507435703760718995665 10666130576777820539246749)
        ·
          refine ⟨3999798966291682702217531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10666130576777820539246749 3999798966291682702217531)
          ·
            refine ⟨5999698449437524053326297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999798966291682702217531 5999698449437524053326297)
            ·
              refine ⟨4499773837078143039994723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999698449437524053326297 4499773837078143039994723)
              ·
                refine ⟨6749660755617214559992085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499773837078143039994723 6749660755617214559992085)
                ·
                  refine ⟨316390347919556932499629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6749660755617214559992085 316390347919556932499629)
                  ·
                    rfl

theorem cell23_5545512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 6].length) (baseStart_5545512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545512 prefixEnd_5545512 := by exact prefixLift 5545512
  have htrace : WordTrace (prefixWord ++ tailWord_5545512) baseStart_5545512 baseEnd_5545512 := by
    simpa [prefixWord, tailWord_5545512, baseEnd_5545512] using wordTrace_append hprefix tailTrace_5545512
  have hstable : (prefixWord ++ tailWord_5545512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545512).length < 2 ^ (prefixWord ++ tailWord_5545512).sum := by decide
  have hdescent : baseEnd_5545512 < baseStart_5545512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545528 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_5545528 : Nat := 118140960795 + 5545528 * 2 ^ 59
def prefixEnd_5545528 : Nat := 4983230072969 + 3 ^ 40 * 5545528 * 2
def baseEnd_5545528 : Nat := 2847521346966484329896587

theorem tailTrace_5545528 : CollatzResearch.WordTrace tailWord_5545528 prefixEnd_5545528 2847521346966484329896587 := by
  unfold tailWord_5545528
  simp only [CollatzResearch.WordTrace]
  refine ⟨101131011326753315812482619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134841348435671087749976825 101131011326753315812482619)
  ·
    refine ⟨151696516990129973718723929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101131011326753315812482619 151696516990129973718723929)
    ·
      refine ⟨113772387742597480289042947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151696516990129973718723929 113772387742597480289042947)
      ·
        refine ⟨170658581613896220433564421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113772387742597480289042947 170658581613896220433564421)
        ·
          refine ⟨31998484052605541331293329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170658581613896220433564421 31998484052605541331293329)
          ·
            refine ⟨23998863039454155998469997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31998484052605541331293329 23998863039454155998469997)
            ·
              refine ⟨8999573639795308499426249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23998863039454155998469997 8999573639795308499426249)
              ·
                refine ⟨6749680229846481374569687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8999573639795308499426249 6749680229846481374569687)
                ·
                  refine ⟨10124520344769722061854531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749680229846481374569687 10124520344769722061854531)
                  ·
                    refine ⟨15186780517154583092781797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10124520344769722061854531 15186780517154583092781797)
                    ·
                      refine ⟨2847521346966484329896587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15186780517154583092781797 2847521346966484329896587)
                      ·
                        rfl

theorem cell23_5545528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_5545528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545528 prefixEnd_5545528 := by exact prefixLift 5545528
  have htrace : WordTrace (prefixWord ++ tailWord_5545528) baseStart_5545528 baseEnd_5545528 := by
    simpa [prefixWord, tailWord_5545528, baseEnd_5545528] using wordTrace_append hprefix tailTrace_5545528
  have hstable : (prefixWord ++ tailWord_5545528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545528).length < 2 ^ (prefixWord ++ tailWord_5545528).sum := by decide
  have hdescent : baseEnd_5545528 < baseStart_5545528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545541 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_5545541 : Nat := 118140960795 + 5545541 * 2 ^ 59
def prefixEnd_5545541 : Nat := 4983230072969 + 3 ^ 40 * 5545541 * 2
def baseEnd_5545541 : Nat := 2847528022214992779034027

theorem tailTrace_5545541 : CollatzResearch.WordTrace tailWord_5545541 prefixEnd_5545541 2847528022214992779034027 := by
  unfold tailWord_5545541
  simp only [CollatzResearch.WordTrace]
  refine ⟨202262496802459534845188477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134841664534973023230125651 202262496802459534845188477)
  ·
    refine ⟨75848436300922325566945679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202262496802459534845188477 75848436300922325566945679)
    ·
      refine ⟨113772654451383488350418519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75848436300922325566945679 113772654451383488350418519)
      ·
        refine ⟨170658981677075232525627779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113772654451383488350418519 170658981677075232525627779)
        ·
          refine ⟨255988472515612848788441669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170658981677075232525627779 255988472515612848788441669)
          ·
            refine ⟨47997838596677409147832813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255988472515612848788441669 47997838596677409147832813)
            ·
              refine ⟨17999189473754028430437305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47997838596677409147832813 17999189473754028430437305)
              ·
                refine ⟨13499392105315521322827979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17999189473754028430437305 13499392105315521322827979)
                ·
                  refine ⟨20249088157973281984241969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13499392105315521322827979 20249088157973281984241969)
                  ·
                    refine ⟨15186816118479961488181477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20249088157973281984241969 15186816118479961488181477)
                    ·
                      refine ⟨2847528022214992779034027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15186816118479961488181477 2847528022214992779034027)
                      ·
                        rfl

theorem cell23_5545541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_5545541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545541 prefixEnd_5545541 := by exact prefixLift 5545541
  have htrace : WordTrace (prefixWord ++ tailWord_5545541) baseStart_5545541 baseEnd_5545541 := by
    simpa [prefixWord, tailWord_5545541, baseEnd_5545541] using wordTrace_append hprefix tailTrace_5545541
  have hstable : (prefixWord ++ tailWord_5545541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545541).length < 2 ^ (prefixWord ++ tailWord_5545541).sum := by decide
  have hdescent : baseEnd_5545541 < baseStart_5545541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545548 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5545548 : Nat := 118140960795 + 5545548 * 2 ^ 59
def prefixEnd_5545548 : Nat := 4983230072969 + 3 ^ 40 * 5545548 * 2
def baseEnd_5545548 : Nat := 2847531616579574251646495

theorem tailTrace_5545548 : CollatzResearch.WordTrace tailWord_5545548 prefixEnd_5545548 2847531616579574251646495 := by
  unfold tailWord_5545548
  simp only [CollatzResearch.WordTrace]
  refine ⟨101131376056717087520346649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134841834742289450027128865 101131376056717087520346649)
  ·
    refine ⟨75848532042537815640259987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101131376056717087520346649 75848532042537815640259987)
    ·
      refine ⟨113772798063806723460389981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75848532042537815640259987 113772798063806723460389981)
      ·
        refine ⟨42664799273927521297646243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113772798063806723460389981 42664799273927521297646243)
        ·
          refine ⟨63997198910891281946469365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42664799273927521297646243 63997198910891281946469365)
          ·
            refine ⟨5999737397896057682481503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63997198910891281946469365 5999737397896057682481503)
            ·
              refine ⟨8999606096844086523722255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5999737397896057682481503 8999606096844086523722255)
              ·
                refine ⟨13499409145266129785583383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8999606096844086523722255 13499409145266129785583383)
                ·
                  refine ⟨20249113717899194678375075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13499409145266129785583383 20249113717899194678375075)
                  ·
                    refine ⟨30373670576848792017562613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20249113717899194678375075 30373670576848792017562613)
                    ·
                      refine ⟨2847531616579574251646495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30373670576848792017562613 2847531616579574251646495)
                      ·
                        rfl

theorem cell23_5545548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5545548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545548 prefixEnd_5545548 := by exact prefixLift 5545548
  have htrace : WordTrace (prefixWord ++ tailWord_5545548) baseStart_5545548 baseEnd_5545548 := by
    simpa [prefixWord, tailWord_5545548, baseEnd_5545548] using wordTrace_append hprefix tailTrace_5545548
  have hstable : (prefixWord ++ tailWord_5545548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545548).length < 2 ^ (prefixWord ++ tailWord_5545548).sum := by decide
  have hdescent : baseEnd_5545548 < baseStart_5545548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545578 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_5545578 : Nat := 118140960795 + 5545578 * 2 ^ 59
def prefixEnd_5545578 : Nat := 4983230072969 + 3 ^ 40 * 5545578 * 2
def baseEnd_5545578 : Nat := 2847547020999209134271357

theorem tailTrace_5545578 : CollatzResearch.WordTrace tailWord_5545578 prefixEnd_5545578 2847547020999209134271357 := by
  unfold tailWord_5545578
  simp only [CollatzResearch.WordTrace]
  refine ⟨50565961575831372541071347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134842564202216993442856925 50565961575831372541071347)
  ·
    refine ⟨75848942363747058811607021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50565961575831372541071347 75848942363747058811607021)
    ·
      refine ⟨28443353386405147054352633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75848942363747058811607021 28443353386405147054352633)
      ·
        refine ⟨21332515039803860290764475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28443353386405147054352633 21332515039803860290764475)
        ·
          refine ⟨31998772559705790436146713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21332515039803860290764475 31998772559705790436146713)
          ·
            refine ⟨23999079419779342827110035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31998772559705790436146713 23999079419779342827110035)
            ·
              refine ⟨35998619129669014240665053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23999079419779342827110035 35998619129669014240665053)
              ·
                refine ⟨13499482173625880340249395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35998619129669014240665053 13499482173625880340249395)
                ·
                  refine ⟨20249223260438820510374093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13499482173625880340249395 20249223260438820510374093)
                  ·
                    refine ⟨7593458722664557691390285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20249223260438820510374093 7593458722664557691390285)
                    ·
                      refine ⟨2847547020999209134271357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593458722664557691390285 2847547020999209134271357)
                      ·
                        rfl

theorem cell23_5545578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_5545578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545578 prefixEnd_5545578 := by exact prefixLift 5545578
  have htrace : WordTrace (prefixWord ++ tailWord_5545578) baseStart_5545578 baseEnd_5545578 := by
    simpa [prefixWord, tailWord_5545578, baseEnd_5545578] using wordTrace_append hprefix tailTrace_5545578
  have hstable : (prefixWord ++ tailWord_5545578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545578).length < 2 ^ (prefixWord ++ tailWord_5545578).sum := by decide
  have hdescent : baseEnd_5545578 < baseStart_5545578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545605 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_5545605 : Nat := 118140960795 + 5545605 * 2 ^ 59
def prefixEnd_5545605 : Nat := 4983230072969 + 3 ^ 40 * 5545605 * 2
def baseEnd_5545605 : Nat := 2847560884976880528633733

theorem tailTrace_5545605 : CollatzResearch.WordTrace tailWord_5545605 prefixEnd_5545605 2847560884976880528633733 := by
  unfold tailWord_5545605
  simp only [CollatzResearch.WordTrace]
  refine ⟨202264831074227673775518269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134843220716151782517012179 202264831074227673775518269)
  ·
    refine ⟨75849311652835377665819351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202264831074227673775518269 75849311652835377665819351)
    ·
      refine ⟨113773967479253066498729027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75849311652835377665819351 113773967479253066498729027)
      ·
        refine ⟨170660951218879599748093541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113773967479253066498729027 170660951218879599748093541)
        ·
          refine ⟨31998928353539924952767539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170660951218879599748093541 31998928353539924952767539)
          ·
            refine ⟨47998392530309887429151309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31998928353539924952767539 47998392530309887429151309)
            ·
              refine ⟨17999397198866207785931741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47998392530309887429151309 17999397198866207785931741)
              ·
                refine ⟨6749773949574827919724403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17999397198866207785931741 6749773949574827919724403)
                ·
                  refine ⟨10124660924362241879586605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6749773949574827919724403 10124660924362241879586605)
                  ·
                    refine ⟨3796747846635840704844977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10124660924362241879586605 3796747846635840704844977)
                    ·
                      refine ⟨2847560884976880528633733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3796747846635840704844977 2847560884976880528633733)
                      ·
                        rfl

theorem cell23_5545605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_5545605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545605 prefixEnd_5545605 := by exact prefixLift 5545605
  have htrace : WordTrace (prefixWord ++ tailWord_5545605) baseStart_5545605 baseEnd_5545605 := by
    simpa [prefixWord, tailWord_5545605, baseEnd_5545605] using wordTrace_append hprefix tailTrace_5545605
  have hstable : (prefixWord ++ tailWord_5545605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545605).length < 2 ^ (prefixWord ++ tailWord_5545605).sum := by decide
  have hdescent : baseEnd_5545605 < baseStart_5545605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545621 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_5545621 : Nat := 118140960795 + 5545621 * 2 ^ 59
def prefixEnd_5545621 : Nat := 4983230072969 + 3 ^ 40 * 5545621 * 2
def baseEnd_5545621 : Nat := 2847569100667352466033659

theorem tailTrace_5545621 : CollatzResearch.WordTrace tailWord_5545621 prefixEnd_5545621 2847569100667352466033659 := by
  unfold tailWord_5545621
  simp only [CollatzResearch.WordTrace]
  refine ⟨202265414642169708508100717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134843609761446472338733811 202265414642169708508100717)
  ·
    refine ⟨75849530490813640690537769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202265414642169708508100717 75849530490813640690537769)
    ·
      refine ⟨56887147868110230517903327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75849530490813640690537769 56887147868110230517903327)
      ·
        refine ⟨85330721802165345776854991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56887147868110230517903327 85330721802165345776854991)
        ·
          refine ⟨127996082703248018665282487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85330721802165345776854991 127996082703248018665282487)
          ·
            refine ⟨191994124054872027997923731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127996082703248018665282487 191994124054872027997923731)
            ·
              refine ⟨287991186082308041996885597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191994124054872027997923731 287991186082308041996885597)
              ·
                refine ⟨107996694780865515748832099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287991186082308041996885597 107996694780865515748832099)
                ·
                  refine ⟨161995042171298273623248149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107996694780865515748832099 161995042171298273623248149)
                  ·
                    refine ⟨7593517601779606576089757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161995042171298273623248149 7593517601779606576089757)
                    ·
                      refine ⟨2847569100667352466033659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7593517601779606576089757 2847569100667352466033659)
                      ·
                        rfl

theorem cell23_5545621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_5545621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545621 prefixEnd_5545621 := by exact prefixLift 5545621
  have htrace : WordTrace (prefixWord ++ tailWord_5545621) baseStart_5545621 baseEnd_5545621 := by
    simpa [prefixWord, tailWord_5545621, baseEnd_5545621] using wordTrace_append hprefix tailTrace_5545621
  have hstable : (prefixWord ++ tailWord_5545621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545621).length < 2 ^ (prefixWord ++ tailWord_5545621).sum := by decide
  have hdescent : baseEnd_5545621 < baseStart_5545621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545681 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_5545681 : Nat := 118140960795 + 5545681 * 2 ^ 59
def prefixEnd_5545681 : Nat := 4983230072969 + 3 ^ 40 * 5545681 * 2
def baseEnd_5545681 : Nat := 2847599909506622231283383

theorem tailTrace_5545681 : CollatzResearch.WordTrace tailWord_5545681 prefixEnd_5545681 2847599909506622231283383 := by
  unfold tailWord_5545681
  simp only [CollatzResearch.WordTrace]
  refine ⟨202267603021952338755284897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134845068681301559170189931 202267603021952338755284897)
  ·
    refine ⟨151700702266464254066463673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202267603021952338755284897 151700702266464254066463673)
    ·
      refine ⟨113775526699848190549847755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151700702266464254066463673 113775526699848190549847755)
      ·
        refine ⟨170663290049772285824771633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113775526699848190549847755 170663290049772285824771633)
        ·
          refine ⟨127997467537329214368578725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170663290049772285824771633 127997467537329214368578725)
          ·
            refine ⟨23999525163249227694108511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127997467537329214368578725 23999525163249227694108511)
            ·
              refine ⟨35999287744873841541162767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23999525163249227694108511 35999287744873841541162767)
              ·
                refine ⟨53998931617310762311744151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35999287744873841541162767 53998931617310762311744151)
                ·
                  refine ⟨80998397425966143467616227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53998931617310762311744151 80998397425966143467616227)
                  ·
                    refine ⟨121497596138949215201424341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80998397425966143467616227 121497596138949215201424341)
                    ·
                      refine ⟨2847599909506622231283383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121497596138949215201424341 2847599909506622231283383)
                      ·
                        rfl

theorem cell23_5545681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_5545681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545681 prefixEnd_5545681 := by exact prefixLift 5545681
  have htrace : WordTrace (prefixWord ++ tailWord_5545681) baseStart_5545681 baseEnd_5545681 := by
    simpa [prefixWord, tailWord_5545681, baseEnd_5545681] using wordTrace_append hprefix tailTrace_5545681
  have hstable : (prefixWord ++ tailWord_5545681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545681).length < 2 ^ (prefixWord ++ tailWord_5545681).sum := by decide
  have hdescent : baseEnd_5545681 < baseStart_5545681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545708 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_5545708 : Nat := 118140960795 + 5545708 * 2 ^ 59
def prefixEnd_5545708 : Nat := 4983230072969 + 3 ^ 40 * 5545708 * 2
def baseEnd_5545708 : Nat := 2847613773484293625645759

theorem tailTrace_5545708 : CollatzResearch.WordTrace tailWord_5545708 prefixEnd_5545708 2847613773484293625645759 := by
  unfold tailWord_5545708
  simp only [CollatzResearch.WordTrace]
  refine ⟨101134293896427261183258889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134845725195236348244345185 101134293896427261183258889)
  ·
    refine ⟨75850720422320445887444167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101134293896427261183258889 75850720422320445887444167)
    ·
      refine ⟨113776080633480668831166251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75850720422320445887444167 113776080633480668831166251)
      ·
        refine ⟨170664120950221003246749377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113776080633480668831166251 170664120950221003246749377)
        ·
          refine ⟨127998090712665752435062033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170664120950221003246749377 127998090712665752435062033)
          ·
            refine ⟨95998568034499314326296525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127998090712665752435062033 95998568034499314326296525)
            ·
              refine ⟨35999463012937242872361197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95998568034499314326296525 35999463012937242872361197)
              ·
                refine ⟨13499798629851466077135449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35999463012937242872361197 13499798629851466077135449)
                ·
                  refine ⟨10124848972388599557851587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13499798629851466077135449 10124848972388599557851587)
                  ·
                    refine ⟨15187273458582899336777381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10124848972388599557851587 15187273458582899336777381)
                    ·
                      refine ⟨2847613773484293625645759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15187273458582899336777381 2847613773484293625645759)
                      ·
                        rfl

theorem cell23_5545708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_5545708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545708 prefixEnd_5545708 := by exact prefixLift 5545708
  have htrace : WordTrace (prefixWord ++ tailWord_5545708) baseStart_5545708 baseEnd_5545708 := by
    simpa [prefixWord, tailWord_5545708, baseEnd_5545708] using wordTrace_append hprefix tailTrace_5545708
  have hstable : (prefixWord ++ tailWord_5545708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545708).length < 2 ^ (prefixWord ++ tailWord_5545708).sum := by decide
  have hdescent : baseEnd_5545708 < baseStart_5545708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545726 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_5545726 : Nat := 118140960795 + 5545726 * 2 ^ 59
def prefixEnd_5545726 : Nat := 4983230072969 + 3 ^ 40 * 5545726 * 2
def baseEnd_5545726 : Nat := 316402557348452728357853

theorem tailTrace_5545726 : CollatzResearch.WordTrace tailWord_5545726 prefixEnd_5545726 316402557348452728357853 := by
  unfold tailWord_5545726
  simp only [CollatzResearch.WordTrace]
  refine ⟨25283655538348663930084129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134846162871192874293782021 25283655538348663930084129)
  ·
    refine ⟨18962741653761497947563097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25283655538348663930084129 18962741653761497947563097)
    ·
      refine ⟨14222056240321123460672323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18962741653761497947563097 14222056240321123460672323)
      ·
        refine ⟨21333084360481685191008485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222056240321123460672323 21333084360481685191008485)
        ·
          refine ⟨3999953317590315973314091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21333084360481685191008485 3999953317590315973314091)
          ·
            refine ⟨5999929976385473959971137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999953317590315973314091 5999929976385473959971137)
            ·
              refine ⟨4499947482289105469978353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999929976385473959971137 4499947482289105469978353)
              ·
                refine ⟨3374960611716829102483765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499947482289105469978353 3374960611716829102483765)
                ·
                  refine ⟨316402557348452728357853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3374960611716829102483765 316402557348452728357853)
                  ·
                    rfl

theorem cell23_5545726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_5545726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545726 prefixEnd_5545726 := by exact prefixLift 5545726
  have htrace : WordTrace (prefixWord ++ tailWord_5545726) baseStart_5545726 baseEnd_5545726 := by
    simpa [prefixWord, tailWord_5545726, baseEnd_5545726] using wordTrace_append hprefix tailTrace_5545726
  have hstable : (prefixWord ++ tailWord_5545726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545726).length < 2 ^ (prefixWord ++ tailWord_5545726).sum := by decide
  have hdescent : baseEnd_5545726 < baseStart_5545726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545731 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 8]
def baseStart_5545731 : Nat := 118140960795 + 5545731 * 2 ^ 59
def prefixEnd_5545731 : Nat := 4983230072969 + 3 ^ 40 * 5545731 * 2
def baseEnd_5545731 : Nat := 316402842615483003962017

theorem tailTrace_5545731 : CollatzResearch.WordTrace tailWord_5545731 prefixEnd_5545731 316402842615483003962017 := by
  unfold tailWord_5545731
  simp only [CollatzResearch.WordTrace]
  refine ⟨202269426671771197294605047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134846284447847464863070031 202269426671771197294605047)
  ·
    refine ⟨303404140007656795941907571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202269426671771197294605047 303404140007656795941907571)
    ·
      refine ⟨455106210011485193912861357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303404140007656795941907571 455106210011485193912861357)
      ·
        refine ⟨170664828754306947717323009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455106210011485193912861357 170664828754306947717323009)
        ·
          refine ⟨127998621565730210787992257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170664828754306947717323009 127998621565730210787992257)
          ·
            refine ⟨95998966174297658090994193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127998621565730210787992257 95998966174297658090994193)
            ·
              refine ⟨71999224630723243568245645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95998966174297658090994193 71999224630723243568245645)
              ·
                refine ⟨26999709236521216338092117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71999224630723243568245645 26999709236521216338092117)
                ·
                  refine ⟨316402842615483003962017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26999709236521216338092117 316402842615483003962017)
                  ·
                    rfl

theorem cell23_5545731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 8].length) (baseStart_5545731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545731 prefixEnd_5545731 := by exact prefixLift 5545731
  have htrace : WordTrace (prefixWord ++ tailWord_5545731) baseStart_5545731 baseEnd_5545731 := by
    simpa [prefixWord, tailWord_5545731, baseEnd_5545731] using wordTrace_append hprefix tailTrace_5545731
  have hstable : (prefixWord ++ tailWord_5545731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545731).length < 2 ^ (prefixWord ++ tailWord_5545731).sum := by decide
  have hdescent : baseEnd_5545731 < baseStart_5545731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545771 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_5545771 : Nat := 118140960795 + 5545771 * 2 ^ 59
def prefixEnd_5545771 : Nat := 4983230072969 + 3 ^ 40 * 5545771 * 2
def baseEnd_5545771 : Nat := 2847646122765526879157969

theorem tailTrace_5545771 : CollatzResearch.WordTrace tailWord_5545771 prefixEnd_5545771 2847646122765526879157969 := by
  unfold tailWord_5545771
  simp only [CollatzResearch.WordTrace]
  refine ⟨202270885591626284126061167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134847257061084189417374111 202270885591626284126061167)
  ·
    refine ⟨303406328387439426189091751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202270885591626284126061167 303406328387439426189091751)
    ·
      refine ⟨455109492581159139283637627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303406328387439426189091751 455109492581159139283637627)
      ·
        refine ⟨682664238871738708925456441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455109492581159139283637627 682664238871738708925456441)
        ·
          refine ⟨511998179153804031694092331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682664238871738708925456441 511998179153804031694092331)
          ·
            refine ⟨767997268730706047541138497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511998179153804031694092331 767997268730706047541138497)
            ·
              refine ⟨575997951548029535655853873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767997268730706047541138497 575997951548029535655853873)
              ·
                refine ⟨431998463661022151741890405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575997951548029535655853873 431998463661022151741890405)
                ·
                  refine ⟨80999711936441653451604451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431998463661022151741890405 80999711936441653451604451)
                  ·
                    refine ⟨121499567904662480177406677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80999711936441653451604451 121499567904662480177406677)
                    ·
                      refine ⟨2847646122765526879157969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121499567904662480177406677 2847646122765526879157969)
                      ·
                        rfl

theorem cell23_5545771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_5545771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545771 prefixEnd_5545771 := by exact prefixLift 5545771
  have htrace : WordTrace (prefixWord ++ tailWord_5545771) baseStart_5545771 baseEnd_5545771 := by
    simpa [prefixWord, tailWord_5545771, baseEnd_5545771] using wordTrace_append hprefix tailTrace_5545771
  have hstable : (prefixWord ++ tailWord_5545771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545771).length < 2 ^ (prefixWord ++ tailWord_5545771).sum := by decide
  have hdescent : baseEnd_5545771 < baseStart_5545771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5545782 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_5545782 : Nat := 118140960795 + 5545782 * 2 ^ 59
def prefixEnd_5545782 : Nat := 4983230072969 + 3 ^ 40 * 5545782 * 2
def baseEnd_5545782 : Nat := 316405752339191815124491

theorem tailTrace_5545782 : CollatzResearch.WordTrace tailWord_5545782 prefixEnd_5545782 316405752339191815124491 := by
  unfold tailWord_5545782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641955424661652062794475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134847524529724288669807733 12641955424661652062794475)
  ·
    refine ⟨18962933136992478094191713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641955424661652062794475 18962933136992478094191713)
    ·
      refine ⟨14222199852744358570643785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18962933136992478094191713 14222199852744358570643785)
      ·
        refine ⟨10666649889558268927982839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14222199852744358570643785 10666649889558268927982839)
        ·
          refine ⟨15999974834337403391974259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666649889558268927982839 15999974834337403391974259)
          ·
            refine ⟨23999962251506105087961389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15999974834337403391974259 23999962251506105087961389)
            ·
              refine ⟨8999985844314789407985521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23999962251506105087961389 8999985844314789407985521)
              ·
                refine ⟨6749989383236092055989141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8999985844314789407985521 6749989383236092055989141)
                ·
                  refine ⟨316405752339191815124491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6749989383236092055989141 316405752339191815124491)
                  ·
                    rfl

theorem cell23_5545782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_5545782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5545782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5545782 prefixEnd_5545782 := by exact prefixLift 5545782
  have htrace : WordTrace (prefixWord ++ tailWord_5545782) baseStart_5545782 baseEnd_5545782 := by
    simpa [prefixWord, tailWord_5545782, baseEnd_5545782] using wordTrace_append hprefix tailTrace_5545782
  have hstable : (prefixWord ++ tailWord_5545782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5545782).length < 2 ^ (prefixWord ++ tailWord_5545782).sum := by decide
  have hdescent : baseEnd_5545782 < baseStart_5545782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5545782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
