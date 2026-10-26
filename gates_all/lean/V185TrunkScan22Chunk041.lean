import V185TrunkScan22Chunk040

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_367641 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_367641 : Nat := 118140960795 + 367641 * 2 ^ 59
def prefixEnd_367641 : Nat := 4983230072969 + 3 ^ 40 * 367641 * 2
def baseEnd_367641 : Nat := 125851027533134224397837

theorem tailTrace_367641 : CollatzResearch.WordTrace tailWord_367641 prefixEnd_367641 125851027533134224397837 := by
  unfold tailWord_367641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408968861106919929094777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8939312574071279952729851 13408968861106919929094777)
  ·
    refine ⟨10056726645830189946821083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13408968861106919929094777 10056726645830189946821083)
    ·
      refine ⟨15085089968745284920231625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10056726645830189946821083 15085089968745284920231625)
      ·
        refine ⟨11313817476558963690173719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15085089968745284920231625 11313817476558963690173719)
        ·
          refine ⟨16970726214838445535260579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11313817476558963690173719 16970726214838445535260579)
          ·
            refine ⟨25456089322257668302890869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16970726214838445535260579 25456089322257668302890869)
            ·
              refine ⟨2386508373961656403396019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25456089322257668302890869 2386508373961656403396019)
              ·
                refine ⟨3579762560942484605094029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386508373961656403396019 3579762560942484605094029)
                ·
                  refine ⟨1342410960353431726910261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3579762560942484605094029 1342410960353431726910261)
                  ·
                    refine ⟨125851027533134224397837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1342410960353431726910261 125851027533134224397837)
                    ·
                      rfl

theorem cell22_367641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_367641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367641 prefixEnd_367641 := by exact prefixLift 367641
  have htrace : WordTrace (prefixWord ++ tailWord_367641) baseStart_367641 baseEnd_367641 := by
    simpa [prefixWord, tailWord_367641, baseEnd_367641] using wordTrace_append hprefix tailTrace_367641
  have hstable : (prefixWord ++ tailWord_367641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367641).length < 2 ^ (prefixWord ++ tailWord_367641).sum := by decide
  have hdescent : baseEnd_367641 < baseStart_367641 := by decide
  rcases family_descends (prefixWord ++ tailWord_367641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367688 : List Nat := [2, 1, 3, 1, 1, 1, 7, 6]
def baseStart_367688 : Nat := 118140960795 + 367688 * 2 ^ 59
def prefixEnd_367688 : Nat := 4983230072969 + 3 ^ 40 * 367688 * 2
def baseEnd_367688 : Nat := 13985235177071307608077

theorem tailTrace_367688 : CollatzResearch.WordTrace tailWord_367688 prefixEnd_367688 13985235177071307608077 := by
  unfold tailWord_367688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705341545968323478027859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8940455394624431304037145 6705341545968323478027859)
  ·
    refine ⟨10058012318952485217041789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6705341545968323478027859 10058012318952485217041789)
    ·
      refine ⟨3771754619607181956390671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10058012318952485217041789 3771754619607181956390671)
      ·
        refine ⟨5657631929410772934586007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771754619607181956390671 5657631929410772934586007)
        ·
          refine ⟨8486447894116159401879011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657631929410772934586007 8486447894116159401879011)
          ·
            refine ⟨12729671841174239102818517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8486447894116159401879011 12729671841174239102818517)
            ·
              refine ⟨298351683777521228972309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12729671841174239102818517 298351683777521228972309)
              ·
                refine ⟨13985235177071307608077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 298351683777521228972309 13985235177071307608077)
                ·
                  rfl

theorem cell22_367688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_367688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367688 prefixEnd_367688 := by exact prefixLift 367688
  have htrace : WordTrace (prefixWord ++ tailWord_367688) baseStart_367688 baseEnd_367688 := by
    simpa [prefixWord, tailWord_367688, baseEnd_367688] using wordTrace_append hprefix tailTrace_367688
  have hstable : (prefixWord ++ tailWord_367688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367688).length < 2 ^ (prefixWord ++ tailWord_367688).sum := by decide
  have hdescent : baseEnd_367688 < baseStart_367688 := by decide
  rcases family_descends (prefixWord ++ tailWord_367688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367703 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 7, 3]
def baseStart_367703 : Nat := 118140960795 + 367703 * 2 ^ 59
def prefixEnd_367703 : Nat := 4983230072969 + 3 ^ 40 * 367703 * 2
def baseEnd_367703 : Nat := 125872251400186729347647

theorem tailTrace_367703 : CollatzResearch.WordTrace tailWord_367703 prefixEnd_367703 125872251400186729347647 := by
  unfold tailWord_367703
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411230186882304517851763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8940820124588203011901175 13411230186882304517851763)
  ·
    refine ⟨20116845280323456776777645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13411230186882304517851763 20116845280323456776777645)
    ·
      refine ⟨7543816980121296291291617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20116845280323456776777645 7543816980121296291291617)
      ·
        refine ⟨5657862735090972218468713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7543816980121296291291617 5657862735090972218468713)
        ·
          refine ⟨4243397051318229163851535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5657862735090972218468713 4243397051318229163851535)
          ·
            refine ⟨6365095576977343745777303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243397051318229163851535 6365095576977343745777303)
            ·
              refine ⟨9547643365466015618665955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365095576977343745777303 9547643365466015618665955)
              ·
                refine ⟨14321465048199023427998933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9547643365466015618665955 14321465048199023427998933)
                ·
                  refine ⟨335659337067164611593725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14321465048199023427998933 335659337067164611593725)
                  ·
                    refine ⟨125872251400186729347647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335659337067164611593725 125872251400186729347647)
                    ·
                      rfl

theorem cell22_367703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_367703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367703 prefixEnd_367703 := by exact prefixLift 367703
  have htrace : WordTrace (prefixWord ++ tailWord_367703) baseStart_367703 baseEnd_367703 := by
    simpa [prefixWord, tailWord_367703, baseEnd_367703] using wordTrace_append hprefix tailTrace_367703
  have hstable : (prefixWord ++ tailWord_367703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367703).length < 2 ^ (prefixWord ++ tailWord_367703).sum := by decide
  have hdescent : baseEnd_367703 < baseStart_367703 := by decide
  rcases family_descends (prefixWord ++ tailWord_367703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367829 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 4]
def baseStart_367829 : Nat := 118140960795 + 367829 * 2 ^ 59
def prefixEnd_367829 : Nat := 4983230072969 + 3 ^ 40 * 367829 * 2
def baseEnd_367829 : Nat := 41971794591721466899087

theorem tailTrace_367829 : CollatzResearch.WordTrace tailWord_367829 prefixEnd_367829 41971794591721466899087 := by
  unfold tailWord_367829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415825784425828036938541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8943883856283885357959027 13415825784425828036938541)
  ·
    refine ⟨5030934669159685513851953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13415825784425828036938541 5030934669159685513851953)
    ·
      refine ⟨3773201001869764135388965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5030934669159685513851953 3773201001869764135388965)
      ·
        refine ⟨707475187850580775385431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3773201001869764135388965 707475187850580775385431)
        ·
          refine ⟨1061212781775871163078147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707475187850580775385431 1061212781775871163078147)
          ·
            refine ⟨1591819172663806744617221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061212781775871163078147 1591819172663806744617221)
            ·
              refine ⟨298466094874463764615729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1591819172663806744617221 298466094874463764615729)
              ·
                refine ⟨223849571155847823461797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298466094874463764615729 223849571155847823461797)
                ·
                  refine ⟨41971794591721466899087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223849571155847823461797 41971794591721466899087)
                  ·
                    rfl

theorem cell22_367829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_367829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367829 prefixEnd_367829 := by exact prefixLift 367829
  have htrace : WordTrace (prefixWord ++ tailWord_367829) baseStart_367829 baseEnd_367829 := by
    simpa [prefixWord, tailWord_367829, baseEnd_367829] using wordTrace_append hprefix tailTrace_367829
  have hstable : (prefixWord ++ tailWord_367829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367829).length < 2 ^ (prefixWord ++ tailWord_367829).sum := by decide
  have hdescent : baseEnd_367829 < baseStart_367829 := by decide
  rcases family_descends (prefixWord ++ tailWord_367829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367840 : List Nat := [2, 1, 1, 3, 1, 6, 1, 7]
def baseStart_367840 : Nat := 118140960795 + 367840 * 2 ^ 59
def prefixEnd_367840 : Nat := 4983230072969 + 3 ^ 40 * 367840 * 2
def baseEnd_367840 : Nat := 13991016588884893185803

theorem tailTrace_367840 : CollatzResearch.WordTrace tailWord_367840 prefixEnd_367840 13991016588884893185803 := by
  unfold tailWord_367840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708113493692988457794487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8944151324923984610392649 6708113493692988457794487)
  ·
    refine ⟨10062170240539482686691731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6708113493692988457794487 10062170240539482686691731)
    ·
      refine ⟨15093255360809224030037597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10062170240539482686691731 15093255360809224030037597)
      ·
        refine ⟨5659970760303459011264099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15093255360809224030037597 5659970760303459011264099)
        ·
          refine ⟨8489956140455188516896149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659970760303459011264099 8489956140455188516896149)
          ·
            refine ⟨397966694083836961729507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8489956140455188516896149 397966694083836961729507)
            ·
              refine ⟨596950041125755442594261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397966694083836961729507 596950041125755442594261)
              ·
                refine ⟨13991016588884893185803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 596950041125755442594261 13991016588884893185803)
                ·
                  rfl

theorem cell22_367840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 7].length) (baseStart_367840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367840 prefixEnd_367840 := by exact prefixLift 367840
  have htrace : WordTrace (prefixWord ++ tailWord_367840) baseStart_367840 baseEnd_367840 := by
    simpa [prefixWord, tailWord_367840, baseEnd_367840] using wordTrace_append hprefix tailTrace_367840
  have hstable : (prefixWord ++ tailWord_367840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367840).length < 2 ^ (prefixWord ++ tailWord_367840).sum := by decide
  have hdescent : baseEnd_367840 < baseStart_367840 := by decide
  rcases family_descends (prefixWord ++ tailWord_367840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367900 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_367900 : Nat := 118140960795 + 367900 * 2 ^ 59
def prefixEnd_367900 : Nat := 4983230072969 + 3 ^ 40 * 367900 * 2
def baseEnd_367900 : Nat := 125939688526143882172043

theorem tailTrace_367900 : CollatzResearch.WordTrace tailWord_367900 prefixEnd_367900 125939688526143882172043 := by
  unfold tailWord_367900
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709207683584303581386577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8945610244779071441848769 6709207683584303581386577)
  ·
    refine ⟨5031905762688227686039933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6709207683584303581386577 5031905762688227686039933)
    ·
      refine ⟨1886964661008085382264975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5031905762688227686039933 1886964661008085382264975)
      ·
        refine ⟨2830446991512128073397463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886964661008085382264975 2830446991512128073397463)
        ·
          refine ⟨4245670487268192110096195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830446991512128073397463 4245670487268192110096195)
          ·
            refine ⟨6368505730902288165144293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245670487268192110096195 6368505730902288165144293)
            ·
              refine ⟨1194094824544179030964555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6368505730902288165144293 1194094824544179030964555)
              ·
                refine ⟨1791142236816268546446833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194094824544179030964555 1791142236816268546446833)
                ·
                  refine ⟨1343356677612201409835125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791142236816268546446833 1343356677612201409835125)
                  ·
                    refine ⟨125939688526143882172043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1343356677612201409835125 125939688526143882172043)
                    ·
                      rfl

theorem cell22_367900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_367900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367900 prefixEnd_367900 := by exact prefixLift 367900
  have htrace : WordTrace (prefixWord ++ tailWord_367900) baseStart_367900 baseEnd_367900 := by
    simpa [prefixWord, tailWord_367900, baseEnd_367900] using wordTrace_append hprefix tailTrace_367900
  have hstable : (prefixWord ++ tailWord_367900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367900).length < 2 ^ (prefixWord ++ tailWord_367900).sum := by decide
  have hdescent : baseEnd_367900 < baseStart_367900 := by decide
  rcases family_descends (prefixWord ++ tailWord_367900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367913 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 12]
def baseStart_367913 : Nat := 118140960795 + 367913 * 2 ^ 59
def prefixEnd_367913 : Nat := 4983230072969 + 3 ^ 40 * 367913 * 2
def baseEnd_367913 : Nat := 41981379563938727199001

theorem tailTrace_367913 : CollatzResearch.WordTrace tailWord_367913 prefixEnd_367913 41981379563938727199001 := by
  unfold tailWord_367913
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418889516121510382996393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8945926344081006921997595 13418889516121510382996393)
  ·
    refine ⟨10064167137091132787247295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13418889516121510382996393 10064167137091132787247295)
    ·
      refine ⟨15096250705636699180870943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10064167137091132787247295 15096250705636699180870943)
      ·
        refine ⟨22644376058455048771306415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15096250705636699180870943 22644376058455048771306415)
        ·
          refine ⟨33966564087682573156959623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22644376058455048771306415 33966564087682573156959623)
          ·
            refine ⟨50949846131523859735439435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33966564087682573156959623 50949846131523859735439435)
            ·
              refine ⟨76424769197285789603159153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50949846131523859735439435 76424769197285789603159153)
              ·
                refine ⟨57318576897964342202369365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76424769197285789603159153 57318576897964342202369365)
                ·
                  refine ⟨41981379563938727199001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 57318576897964342202369365 41981379563938727199001)
                  ·
                    rfl

theorem cell22_367913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_367913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367913 prefixEnd_367913 := by exact prefixLift 367913
  have htrace : WordTrace (prefixWord ++ tailWord_367913) baseStart_367913 baseEnd_367913 := by
    simpa [prefixWord, tailWord_367913, baseEnd_367913] using wordTrace_append hprefix tailTrace_367913
  have hstable : (prefixWord ++ tailWord_367913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367913).length < 2 ^ (prefixWord ++ tailWord_367913).sum := by decide
  have hdescent : baseEnd_367913 < baseStart_367913 := by decide
  rcases family_descends (prefixWord ++ tailWord_367913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367932 : List Nat := [2, 2, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_367932 : Nat := 118140960795 + 367932 * 2 ^ 59
def prefixEnd_367932 : Nat := 4983230072969 + 3 ^ 40 * 367932 * 2
def baseEnd_367932 : Nat := 125950642780106465371945

theorem tailTrace_367932 : CollatzResearch.WordTrace tailWord_367932 prefixEnd_367932 125950642780106465371945 := by
  unfold tailWord_367932
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709791251526338313969025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8946388335368451085292033 6709791251526338313969025)
  ·
    refine ⟨5032343438644753735476769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6709791251526338313969025 5032343438644753735476769)
    ·
      refine ⟨3774257578983565301607577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5032343438644753735476769 3774257578983565301607577)
      ·
        refine ⟨2830693184237673976205683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3774257578983565301607577 2830693184237673976205683)
        ·
          refine ⟨4246039776356510964308525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830693184237673976205683 4246039776356510964308525)
          ·
            refine ⟨1592264916133691611615697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4246039776356510964308525 1592264916133691611615697)
            ·
              refine ⟨1194198687100268708711773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592264916133691611615697 1194198687100268708711773)
              ·
                refine ⟨447824507662600765766915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194198687100268708711773 447824507662600765766915)
                ·
                  refine ⟨671736761493901148650373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447824507662600765766915 671736761493901148650373)
                  ·
                    refine ⟨125950642780106465371945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 671736761493901148650373 125950642780106465371945)
                    ·
                      rfl

theorem cell22_367932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_367932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367932 prefixEnd_367932 := by exact prefixLift 367932
  have htrace : WordTrace (prefixWord ++ tailWord_367932) baseStart_367932 baseEnd_367932 := by
    simpa [prefixWord, tailWord_367932, baseEnd_367932] using wordTrace_append hprefix tailTrace_367932
  have hstable : (prefixWord ++ tailWord_367932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367932).length < 2 ^ (prefixWord ++ tailWord_367932).sum := by decide
  have hdescent : baseEnd_367932 < baseStart_367932 := by decide
  rcases family_descends (prefixWord ++ tailWord_367932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367960 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_367960 : Nat := 118140960795 + 367960 * 2 ^ 59
def prefixEnd_367960 : Nat := 4983230072969 + 3 ^ 40 * 367960 * 2
def baseEnd_367960 : Nat := 125960227752323725671859

theorem tailTrace_367960 : CollatzResearch.WordTrace tailWord_367960 prefixEnd_367960 125960227752323725671859 := by
  unfold tailWord_367960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710301873475618704978667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8947069164634158273304889 6710301873475618704978667)
  ·
    refine ⟨10065452810213428057468001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6710301873475618704978667 10065452810213428057468001)
    ·
      refine ⟨7549089607660071043101001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10065452810213428057468001 7549089607660071043101001)
      ·
        refine ⟨5661817205745053282325751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7549089607660071043101001 5661817205745053282325751)
        ·
          refine ⟨8492725808617579923488627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661817205745053282325751 8492725808617579923488627)
          ·
            refine ⟨12739088712926369885232941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492725808617579923488627 12739088712926369885232941)
            ·
              refine ⟨4777158267347388706962353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12739088712926369885232941 4777158267347388706962353)
              ·
                refine ⟨3582868700510541530221765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777158267347388706962353 3582868700510541530221765)
                ·
                  refine ⟨671787881345726536916581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3582868700510541530221765 671787881345726536916581)
                  ·
                    refine ⟨125960227752323725671859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 671787881345726536916581 125960227752323725671859)
                    ·
                      rfl

theorem cell22_367960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_367960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367960 prefixEnd_367960 := by exact prefixLift 367960
  have htrace : WordTrace (prefixWord ++ tailWord_367960) baseStart_367960 baseEnd_367960 := by
    simpa [prefixWord, tailWord_367960, baseEnd_367960] using wordTrace_append hprefix tailTrace_367960
  have hstable : (prefixWord ++ tailWord_367960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367960).length < 2 ^ (prefixWord ++ tailWord_367960).sum := by decide
  have hdescent : baseEnd_367960 < baseStart_367960 := by decide
  rcases family_descends (prefixWord ++ tailWord_367960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367998 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_367998 : Nat := 118140960795 + 367998 * 2 ^ 59
def prefixEnd_367998 : Nat := 4983230072969 + 3 ^ 40 * 367998 * 2
def baseEnd_367998 : Nat := 41991078642968097740581

theorem tailTrace_367998 : CollatzResearch.WordTrace tailWord_367998 prefixEnd_367998 41991078642968097740581 := by
  unfold tailWord_367998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677748715101696237480081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8947993147209046599893765 1677748715101696237480081)
  ·
    refine ⟨1258311536326272178110061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1677748715101696237480081 1258311536326272178110061)
    ·
      refine ⟨471866826122352066791273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1258311536326272178110061 471866826122352066791273)
      ·
        refine ⟨353900119591764050093455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471866826122352066791273 353900119591764050093455)
        ·
          refine ⟨530850179387646075140183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353900119591764050093455 530850179387646075140183)
          ·
            refine ⟨796275269081469112710275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530850179387646075140183 796275269081469112710275)
            ·
              refine ⟨1194412903622203669065413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796275269081469112710275 1194412903622203669065413)
              ·
                refine ⟨223952419429163187949765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1194412903622203669065413 223952419429163187949765)
                ·
                  refine ⟨41991078642968097740581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223952419429163187949765 41991078642968097740581)
                  ·
                    rfl

theorem cell22_367998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_367998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367998 prefixEnd_367998 := by exact prefixLift 367998
  have htrace : WordTrace (prefixWord ++ tailWord_367998) baseStart_367998 baseEnd_367998 := by
    simpa [prefixWord, tailWord_367998, baseEnd_367998] using wordTrace_append hprefix tailTrace_367998
  have hstable : (prefixWord ++ tailWord_367998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367998).length < 2 ^ (prefixWord ++ tailWord_367998).sum := by decide
  have hdescent : baseEnd_367998 < baseStart_367998 := by decide
  rcases family_descends (prefixWord ++ tailWord_367998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368005 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_368005 : Nat := 118140960795 + 368005 * 2 ^ 59
def prefixEnd_368005 : Nat := 4983230072969 + 3 ^ 40 * 368005 * 2
def baseEnd_368005 : Nat := 125975632171958608296721

theorem tailTrace_368005 : CollatzResearch.WordTrace tailWord_368005 prefixEnd_368005 125975632171958608296721 := by
  unfold tailWord_368005
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422245031788210095345469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8948163354525473396896979 13422245031788210095345469)
  ·
    refine ⟨5033341886920578785754551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13422245031788210095345469 5033341886920578785754551)
    ·
      refine ⟨7550012830380868178631827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033341886920578785754551 7550012830380868178631827)
      ·
        refine ⟨11325019245571302267947741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550012830380868178631827 11325019245571302267947741)
        ·
          refine ⟨4246882217089238350480403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11325019245571302267947741 4246882217089238350480403)
          ·
            refine ⟨6370323325633857525720605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246882217089238350480403 6370323325633857525720605)
            ·
              refine ⟨2388871247112696572145227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6370323325633857525720605 2388871247112696572145227)
              ·
                refine ⟨3583306870669044858217841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388871247112696572145227 3583306870669044858217841)
                ·
                  refine ⟨2687480153001783643663381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583306870669044858217841 2687480153001783643663381)
                  ·
                    refine ⟨125975632171958608296721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2687480153001783643663381 125975632171958608296721)
                    ·
                      rfl

theorem cell22_368005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_368005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368005 prefixEnd_368005 := by exact prefixLift 368005
  have htrace : WordTrace (prefixWord ++ tailWord_368005) baseStart_368005 baseEnd_368005 := by
    simpa [prefixWord, tailWord_368005, baseEnd_368005] using wordTrace_append hprefix tailTrace_368005
  have hstable : (prefixWord ++ tailWord_368005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368005).length < 2 ^ (prefixWord ++ tailWord_368005).sum := by decide
  have hdescent : baseEnd_368005 < baseStart_368005 := by decide
  rcases family_descends (prefixWord ++ tailWord_368005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368009 : List Nat := [1, 2, 1, 1, 8, 1, 1, 7]
def baseStart_368009 : Nat := 118140960795 + 368009 * 2 ^ 59
def prefixEnd_368009 : Nat := 4983230072969 + 3 ^ 40 * 368009 * 2
def baseEnd_368009 : Nat := 13997444605967103466301

theorem tailTrace_368009 : CollatzResearch.WordTrace tailWord_368009 prefixEnd_368009 13997444605967103466301 := by
  unfold tailWord_368009
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422390923773718778491081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8948260615849145852327387 13422390923773718778491081)
  ·
    refine ⟨10066793192830289083868311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13422390923773718778491081 10066793192830289083868311)
    ·
      refine ⟨15100189789245433625802467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10066793192830289083868311 15100189789245433625802467)
      ·
        refine ⟨22650284683868150438703701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15100189789245433625802467 22650284683868150438703701)
        ·
          refine ⟨265433023639079887953559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 22650284683868150438703701 265433023639079887953559)
          ·
            refine ⟨398149535458619831930339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265433023639079887953559 398149535458619831930339)
            ·
              refine ⟨597224303187929747895509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398149535458619831930339 597224303187929747895509)
              ·
                refine ⟨13997444605967103466301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 597224303187929747895509 13997444605967103466301)
                ·
                  rfl

theorem cell22_368009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 7].length) (baseStart_368009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368009 prefixEnd_368009 := by exact prefixLift 368009
  have htrace : WordTrace (prefixWord ++ tailWord_368009) baseStart_368009 baseEnd_368009 := by
    simpa [prefixWord, tailWord_368009, baseEnd_368009] using wordTrace_append hprefix tailTrace_368009
  have hstable : (prefixWord ++ tailWord_368009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368009).length < 2 ^ (prefixWord ++ tailWord_368009).sum := by decide
  have hdescent : baseEnd_368009 < baseStart_368009 := by decide
  rcases family_descends (prefixWord ++ tailWord_368009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368028 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_368028 : Nat := 118140960795 + 368028 * 2 ^ 59
def prefixEnd_368028 : Nat := 4983230072969 + 3 ^ 40 * 368028 * 2
def baseEnd_368028 : Nat := 125983505541994214971651

theorem tailTrace_368028 : CollatzResearch.WordTrace tailWord_368028 prefixEnd_368028 125983505541994214971651 := by
  unfold tailWord_368028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711541955352442511716369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8948722607136590015621825 6711541955352442511716369)
  ·
    refine ⟨5033656466514331883787277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6711541955352442511716369 5033656466514331883787277)
    ·
      refine ⟨1887621174942874456420229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5033656466514331883787277 1887621174942874456420229)
      ·
        refine ⟨353928970301788960578793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1887621174942874456420229 353928970301788960578793)
        ·
          refine ⟨265446727726341720434095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353928970301788960578793 265446727726341720434095)
          ·
            refine ⟨398170091589512580651143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265446727726341720434095 398170091589512580651143)
            ·
              refine ⟨597255137384268870976715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398170091589512580651143 597255137384268870976715)
              ·
                refine ⟨895882706076403306465073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597255137384268870976715 895882706076403306465073)
                ·
                  refine ⟨671912029557302479848805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 895882706076403306465073 671912029557302479848805)
                  ·
                    refine ⟨125983505541994214971651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 671912029557302479848805 125983505541994214971651)
                    ·
                      rfl

theorem cell22_368028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_368028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368028 prefixEnd_368028 := by exact prefixLift 368028
  have htrace : WordTrace (prefixWord ++ tailWord_368028) baseStart_368028 baseEnd_368028 := by
    simpa [prefixWord, tailWord_368028, baseEnd_368028] using wordTrace_append hprefix tailTrace_368028
  have hstable : (prefixWord ++ tailWord_368028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368028).length < 2 ^ (prefixWord ++ tailWord_368028).sum := by decide
  have hdescent : baseEnd_368028 < baseStart_368028 := by decide
  rcases family_descends (prefixWord ++ tailWord_368028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368035 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_368035 : Nat := 118140960795 + 368035 * 2 ^ 59
def prefixEnd_368035 : Nat := 4983230072969 + 3 ^ 40 * 368035 * 2
def baseEnd_368035 : Nat := 125985901785048530046629

theorem tailTrace_368035 : CollatzResearch.WordTrace tailWord_368035 prefixEnd_368035 125985901785048530046629 := by
  unfold tailWord_368035
  simp only [CollatzResearch.WordTrace]
  refine ⟨13423339221679525218937559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8948892814453016812625039 13423339221679525218937559)
  ·
    refine ⟨20135008832519287828406339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13423339221679525218937559 20135008832519287828406339)
    ·
      refine ⟨30202513248778931742609509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20135008832519287828406339 30202513248778931742609509)
      ·
        refine ⟨5662971234146049701739283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30202513248778931742609509 5662971234146049701739283)
        ·
          refine ⟨8494456851219074552608925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662971234146049701739283 8494456851219074552608925)
          ·
            refine ⟨3185421319207152957228347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8494456851219074552608925 3185421319207152957228347)
            ·
              refine ⟨4778131978810729435842521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3185421319207152957228347 4778131978810729435842521)
              ·
                refine ⟨3583598984108047076881891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778131978810729435842521 3583598984108047076881891)
                ·
                  refine ⟨5375398476162070615322837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583598984108047076881891 5375398476162070615322837)
                  ·
                    refine ⟨125985901785048530046629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5375398476162070615322837 125985901785048530046629)
                    ·
                      rfl

theorem cell22_368035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_368035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368035 prefixEnd_368035 := by exact prefixLift 368035
  have htrace : WordTrace (prefixWord ++ tailWord_368035) baseStart_368035 baseEnd_368035 := by
    simpa [prefixWord, tailWord_368035, baseEnd_368035] using wordTrace_append hprefix tailTrace_368035
  have hstable : (prefixWord ++ tailWord_368035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368035).length < 2 ^ (prefixWord ++ tailWord_368035).sum := by decide
  have hdescent : baseEnd_368035 < baseStart_368035 := by decide
  rcases family_descends (prefixWord ++ tailWord_368035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368112 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 4, 4]
def baseStart_368112 : Nat := 118140960795 + 368112 * 2 ^ 59
def prefixEnd_368112 : Nat := 4983230072969 + 3 ^ 40 * 368112 * 2
def baseEnd_368112 : Nat := 126012260458645995871393

theorem tailTrace_368112 : CollatzResearch.WordTrace tailWord_368112 prefixEnd_368112 126012260458645995871393 := by
  unfold tailWord_368112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6713073821200283684745295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8950765094933711579660393 6713073821200283684745295)
  ·
    refine ⟨10069610731800425527117943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6713073821200283684745295 10069610731800425527117943)
    ·
      refine ⟨15104416097700638290676915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10069610731800425527117943 15104416097700638290676915)
      ·
        refine ⟨22656624146550957436015373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15104416097700638290676915 22656624146550957436015373)
        ·
          refine ⟨8496234054956609038505765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22656624146550957436015373 8496234054956609038505765)
          ·
            refine ⟨1593043885304364194719831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8496234054956609038505765 1593043885304364194719831)
            ·
              refine ⟨2389565827956546292079747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593043885304364194719831 2389565827956546292079747)
              ·
                refine ⟨3584348741934819438119621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389565827956546292079747 3584348741934819438119621)
                ·
                  refine ⟨672065389112778644647429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3584348741934819438119621 672065389112778644647429)
                  ·
                    refine ⟨126012260458645995871393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672065389112778644647429 126012260458645995871393)
                    ·
                      rfl

theorem cell22_368112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_368112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368112 prefixEnd_368112 := by exact prefixLift 368112
  have htrace : WordTrace (prefixWord ++ tailWord_368112) baseStart_368112 baseEnd_368112 := by
    simpa [prefixWord, tailWord_368112, baseEnd_368112] using wordTrace_append hprefix tailTrace_368112
  have hstable : (prefixWord ++ tailWord_368112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368112).length < 2 ^ (prefixWord ++ tailWord_368112).sum := by decide
  have hdescent : baseEnd_368112 < baseStart_368112 := by decide
  rcases family_descends (prefixWord ++ tailWord_368112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368174 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_368174 : Nat := 118140960795 + 368174 * 2 ^ 59
def prefixEnd_368174 : Nat := 4983230072969 + 3 ^ 40 * 368174 * 2
def baseEnd_368174 : Nat := 126033484325698500821203

theorem tailTrace_368174 : CollatzResearch.WordTrace tailWord_368174 prefixEnd_368174 126033484325698500821203 := by
  unfold tailWord_368174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678551121021993994780947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8952272645450634638831717 1678551121021993994780947)
  ·
    refine ⟨2517826681532990992171421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1678551121021993994780947 2517826681532990992171421)
    ·
      refine ⟨944185005574871622064283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2517826681532990992171421 944185005574871622064283)
      ·
        refine ⟨1416277508362307433096425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944185005574871622064283 1416277508362307433096425)
        ·
          refine ⟨1062208131271730574822319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1416277508362307433096425 1062208131271730574822319)
          ·
            refine ⟨1593312196907595862233479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062208131271730574822319 1593312196907595862233479)
            ·
              refine ⟨2389968295361393793350219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593312196907595862233479 2389968295361393793350219)
              ·
                refine ⟨3584952443042090690025329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389968295361393793350219 3584952443042090690025329)
                ·
                  refine ⟨2688714332281568017518997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3584952443042090690025329 2688714332281568017518997)
                  ·
                    refine ⟨126033484325698500821203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2688714332281568017518997 126033484325698500821203)
                    ·
                      rfl

theorem cell22_368174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_368174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368174 prefixEnd_368174 := by exact prefixLift 368174
  have htrace : WordTrace (prefixWord ++ tailWord_368174) baseStart_368174 baseEnd_368174 := by
    simpa [prefixWord, tailWord_368174, baseEnd_368174] using wordTrace_append hprefix tailTrace_368174
  have hstable : (prefixWord ++ tailWord_368174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368174).length < 2 ^ (prefixWord ++ tailWord_368174).sum := by decide
  have hdescent : baseEnd_368174 < baseStart_368174 := by decide
  rcases family_descends (prefixWord ++ tailWord_368174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368234 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_368234 : Nat := 118140960795 + 368234 * 2 ^ 59
def prefixEnd_368234 : Nat := 4983230072969 + 3 ^ 40 * 368234 * 2
def baseEnd_368234 : Nat := 42018007850626114773673

theorem tailTrace_368234 : CollatzResearch.WordTrace tailWord_368234 prefixEnd_368234 42018007850626114773673 := by
  unfold tailWord_368234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357649336989645551357939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8953731565305721470287837 3357649336989645551357939)
  ·
    refine ⟨5036474005484468327036909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357649336989645551357939 5036474005484468327036909)
    ·
      refine ⟨1888677752056675622638841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5036474005484468327036909 1888677752056675622638841)
      ·
        refine ⟨1416508314042506716979131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888677752056675622638841 1416508314042506716979131)
        ·
          refine ⟨2124762471063760075468697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416508314042506716979131 2124762471063760075468697)
          ·
            refine ⟨1593571853297820056601523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124762471063760075468697 1593571853297820056601523)
            ·
              refine ⟨2390357779946730084902285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593571853297820056601523 2390357779946730084902285)
              ·
                refine ⟨896384167480023781838357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2390357779946730084902285 896384167480023781838357)
                ·
                  refine ⟨42018007850626114773673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 896384167480023781838357 42018007850626114773673)
                  ·
                    rfl

theorem cell22_368234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_368234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368234 prefixEnd_368234 := by exact prefixLift 368234
  have htrace : WordTrace (prefixWord ++ tailWord_368234) baseStart_368234 baseEnd_368234 := by
    simpa [prefixWord, tailWord_368234, baseEnd_368234] using wordTrace_append hprefix tailTrace_368234
  have hstable : (prefixWord ++ tailWord_368234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368234).length < 2 ^ (prefixWord ++ tailWord_368234).sum := by decide
  have hdescent : baseEnd_368234 < baseStart_368234 := by decide
  rcases family_descends (prefixWord ++ tailWord_368234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368266 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_368266 : Nat := 118140960795 + 368266 * 2 ^ 59
def prefixEnd_368266 : Nat := 4983230072969 + 3 ^ 40 * 368266 * 2
def baseEnd_368266 : Nat := 126064977805840927520921

theorem tailTrace_368266 : CollatzResearch.WordTrace tailWord_368266 prefixEnd_368266 126064977805840927520921 := by
  unfold tailWord_368266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357941120960662917649163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8954509655895101113731101 3357941120960662917649163)
  ·
    refine ⟨5036911681440994376473745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357941120960662917649163 5036911681440994376473745)
    ·
      refine ⟨3777683761080745782355309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5036911681440994376473745 3777683761080745782355309)
      ·
        refine ⟨1416631410405279668383241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3777683761080745782355309 1416631410405279668383241)
        ·
          refine ⟨1062473557803959751287431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1416631410405279668383241 1062473557803959751287431)
          ·
            refine ⟨1593710336705939626931147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062473557803959751287431 1593710336705939626931147)
            ·
              refine ⟨2390565505058909440396721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593710336705939626931147 2390565505058909440396721)
              ·
                refine ⟨1792924128794182080297541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390565505058909440396721 1792924128794182080297541)
                ·
                  refine ⟨336173274148909140055789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792924128794182080297541 336173274148909140055789)
                  ·
                    refine ⟨126064977805840927520921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336173274148909140055789 126064977805840927520921)
                    ·
                      rfl

theorem cell22_368266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_368266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368266 prefixEnd_368266 := by exact prefixLift 368266
  have htrace : WordTrace (prefixWord ++ tailWord_368266) baseStart_368266 baseEnd_368266 := by
    simpa [prefixWord, tailWord_368266, baseEnd_368266] using wordTrace_append hprefix tailTrace_368266
  have hstable : (prefixWord ++ tailWord_368266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368266).length < 2 ^ (prefixWord ++ tailWord_368266).sum := by decide
  have hdescent : baseEnd_368266 < baseStart_368266 := by decide
  rcases family_descends (prefixWord ++ tailWord_368266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368279 : List Nat := [1, 1, 3, 3, 2, 4, 8]
def baseStart_368279 : Nat := 118140960795 + 368279 * 2 ^ 59
def prefixEnd_368279 : Nat := 4983230072969 + 3 ^ 40 * 368279 * 2
def baseEnd_368279 : Nat := 4669238073019008405403

theorem tailTrace_368279 : CollatzResearch.WordTrace tailWord_368279 prefixEnd_368279 4669238073019008405403 := by
  unfold tailWord_368279
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432238632795554890819891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8954825755197036593879927 13432238632795554890819891)
  ·
    refine ⟨20148357949193332336229837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13432238632795554890819891 20148357949193332336229837)
    ·
      refine ⟨7555634230947499626086189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20148357949193332336229837 7555634230947499626086189)
      ·
        refine ⟨2833362836605312359782321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7555634230947499626086189 2833362836605312359782321)
        ·
          refine ⟨2125022127453984269836741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2833362836605312359782321 2125022127453984269836741)
          ·
            refine ⟨398441648897622050594389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2125022127453984269836741 398441648897622050594389)
            ·
              refine ⟨4669238073019008405403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 398441648897622050594389 4669238073019008405403)
              ·
                rfl

theorem cell22_368279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 8].length) (baseStart_368279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368279 prefixEnd_368279 := by exact prefixLift 368279
  have htrace : WordTrace (prefixWord ++ tailWord_368279) baseStart_368279 baseEnd_368279 := by
    simpa [prefixWord, tailWord_368279, baseEnd_368279] using wordTrace_append hprefix tailTrace_368279
  have hstable : (prefixWord ++ tailWord_368279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368279).length < 2 ^ (prefixWord ++ tailWord_368279).sum := by decide
  have hdescent : baseEnd_368279 < baseStart_368279 := by decide
  rcases family_descends (prefixWord ++ tailWord_368279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368328 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 1, 3]
def baseStart_368328 : Nat := 118140960795 + 368328 * 2 ^ 59
def prefixEnd_368328 : Nat := 4983230072969 + 3 ^ 40 * 368328 * 2
def baseEnd_368328 : Nat := 126086201672893432470731

theorem tailTrace_368328 : CollatzResearch.WordTrace tailWord_368328 prefixEnd_368328 126086201672893432470731 := by
  unfold tailWord_368328
  simp only [CollatzResearch.WordTrace]
  refine ⟨6717012904809018129676819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8956017206412024172902425 6717012904809018129676819)
  ·
    refine ⟨10075519357213527194515229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6717012904809018129676819 10075519357213527194515229)
    ·
      refine ⟨3778319758955072697943211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10075519357213527194515229 3778319758955072697943211)
      ·
        refine ⟨5667479638432609046914817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778319758955072697943211 5667479638432609046914817)
        ·
          refine ⟨4250609728824456785186113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5667479638432609046914817 4250609728824456785186113)
          ·
            refine ⟨3187957296618342588889585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4250609728824456785186113 3187957296618342588889585)
            ·
              refine ⟨2390967972463756941667189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187957296618342588889585 2390967972463756941667189)
              ·
                refine ⟨224153247418477213281299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2390967972463756941667189 224153247418477213281299)
                ·
                  refine ⟨336229871127715819921949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224153247418477213281299 336229871127715819921949)
                  ·
                    refine ⟨126086201672893432470731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336229871127715819921949 126086201672893432470731)
                    ·
                      rfl

theorem cell22_368328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_368328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368328 prefixEnd_368328 := by exact prefixLift 368328
  have htrace : WordTrace (prefixWord ++ tailWord_368328) baseStart_368328 baseEnd_368328 := by
    simpa [prefixWord, tailWord_368328, baseEnd_368328] using wordTrace_append hprefix tailTrace_368328
  have hstable : (prefixWord ++ tailWord_368328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368328).length < 2 ^ (prefixWord ++ tailWord_368328).sum := by decide
  have hdescent : baseEnd_368328 < baseStart_368328 := by decide
  rcases family_descends (prefixWord ++ tailWord_368328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368345 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 1, 3]
def baseStart_368345 : Nat := 118140960795 + 368345 * 2 ^ 59
def prefixEnd_368345 : Nat := 4983230072969 + 3 ^ 40 * 368345 * 2
def baseEnd_368345 : Nat := 126092021120311054795679

theorem tailTrace_368345 : CollatzResearch.WordTrace tailWord_368345 prefixEnd_368345 126092021120311054795679 := by
  unfold tailWord_368345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13434645850556448162722489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8956430567037632108481659 13434645850556448162722489)
  ·
    refine ⟨10075984387917336122041867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13434645850556448162722489 10075984387917336122041867)
    ·
      refine ⟨15113976581876004183062801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075984387917336122041867 15113976581876004183062801)
      ·
        refine ⟨11335482436407003137297101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15113976581876004183062801 11335482436407003137297101)
        ·
          refine ⟨4250805913652626176486413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11335482436407003137297101 4250805913652626176486413)
          ·
            refine ⟨1594052217619734816182405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4250805913652626176486413 1594052217619734816182405)
            ·
              refine ⟨298884790803700278034201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1594052217619734816182405 298884790803700278034201)
              ·
                refine ⟨224163593102775208525651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298884790803700278034201 224163593102775208525651)
                ·
                  refine ⟨336245389654162812788477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224163593102775208525651 336245389654162812788477)
                  ·
                    refine ⟨126092021120311054795679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336245389654162812788477 126092021120311054795679)
                    ·
                      rfl

theorem cell22_368345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_368345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368345 prefixEnd_368345 := by exact prefixLift 368345
  have htrace : WordTrace (prefixWord ++ tailWord_368345) baseStart_368345 baseEnd_368345 := by
    simpa [prefixWord, tailWord_368345, baseEnd_368345] using wordTrace_append hprefix tailTrace_368345
  have hstable : (prefixWord ++ tailWord_368345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368345).length < 2 ^ (prefixWord ++ tailWord_368345).sum := by decide
  have hdescent : baseEnd_368345 < baseStart_368345 := by decide
  rcases family_descends (prefixWord ++ tailWord_368345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368369 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 8]
def baseStart_368369 : Nat := 118140960795 + 368369 * 2 ^ 59
def prefixEnd_368369 : Nat := 4983230072969 + 3 ^ 40 * 368369 * 2
def baseEnd_368369 : Nat := 42033412270260997398535

theorem tailTrace_368369 : CollatzResearch.WordTrace tailWord_368369 prefixEnd_368369 42033412270260997398535 := by
  unfold tailWord_368369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435521202469500261596161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8957014134979666841064107 13435521202469500261596161)
  ·
    refine ⟨10076640901852125196197121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13435521202469500261596161 10076640901852125196197121)
    ·
      refine ⟨7557480676389093897147841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10076640901852125196197121 7557480676389093897147841)
      ·
        refine ⟨5668110507291820422860881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7557480676389093897147841 5668110507291820422860881)
        ·
          refine ⟨4251082880468865317145661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668110507291820422860881 4251082880468865317145661)
          ·
            refine ⟨1594156080175824493929623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251082880468865317145661 1594156080175824493929623)
            ·
              refine ⟨2391234120263736740894435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594156080175824493929623 2391234120263736740894435)
              ·
                refine ⟨3586851180395605111341653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391234120263736740894435 3586851180395605111341653)
                ·
                  refine ⟨42033412270260997398535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3586851180395605111341653 42033412270260997398535)
                  ·
                    rfl

theorem cell22_368369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_368369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368369 prefixEnd_368369 := by exact prefixLift 368369
  have htrace : WordTrace (prefixWord ++ tailWord_368369) baseStart_368369 baseEnd_368369 := by
    simpa [prefixWord, tailWord_368369, baseEnd_368369] using wordTrace_append hprefix tailTrace_368369
  have hstable : (prefixWord ++ tailWord_368369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368369).length < 2 ^ (prefixWord ++ tailWord_368369).sum := by decide
  have hdescent : baseEnd_368369 < baseStart_368369 := by decide
  rcases family_descends (prefixWord ++ tailWord_368369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368386 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_368386 : Nat := 118140960795 + 368386 * 2 ^ 59
def prefixEnd_368386 : Nat := 4983230072969 + 3 ^ 40 * 368386 * 2
def baseEnd_368386 : Nat := 42035352086066871506851

theorem tailTrace_368386 : CollatzResearch.WordTrace tailWord_368386 prefixEnd_368386 42035352086066871506851 := by
  unfold tailWord_368386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359035310851978041241253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8957427495605274776643341 3359035310851978041241253)
  ·
    refine ⟨629819120784745882732735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3359035310851978041241253 629819120784745882732735)
    ·
      refine ⟨944728681177118824099103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629819120784745882732735 944728681177118824099103)
      ·
        refine ⟨1417093021765678236148655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944728681177118824099103 1417093021765678236148655)
        ·
          refine ⟨2125639532648517354222983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417093021765678236148655 2125639532648517354222983)
          ·
            refine ⟨3188459298972776031334475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125639532648517354222983 3188459298972776031334475)
            ·
              refine ⟨4782688948459164047001713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188459298972776031334475 4782688948459164047001713)
              ·
                refine ⟨3587016711344373035251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4782688948459164047001713 3587016711344373035251285)
                ·
                  refine ⟨42035352086066871506851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3587016711344373035251285 42035352086066871506851)
                  ·
                    rfl

theorem cell22_368386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_368386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368386 prefixEnd_368386 := by exact prefixLift 368386
  have htrace : WordTrace (prefixWord ++ tailWord_368386) baseStart_368386 baseEnd_368386 := by
    simpa [prefixWord, tailWord_368386, baseEnd_368386] using wordTrace_append hprefix tailTrace_368386
  have hstable : (prefixWord ++ tailWord_368386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368386).length < 2 ^ (prefixWord ++ tailWord_368386).sum := by decide
  have hdescent : baseEnd_368386 < baseStart_368386 := by decide
  rcases family_descends (prefixWord ++ tailWord_368386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368388 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_368388 : Nat := 118140960795 + 368388 * 2 ^ 59
def prefixEnd_368388 : Nat := 4983230072969 + 3 ^ 40 * 368388 * 2
def baseEnd_368388 : Nat := 126106740899073275970547

theorem tailTrace_368388 : CollatzResearch.WordTrace tailWord_368388 prefixEnd_368388 126106740899073275970547 := by
  unfold tailWord_368388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718107094700333253268909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8957476126267111004358545 6718107094700333253268909)
  ·
    refine ⟨2519290160512624969975841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6718107094700333253268909 2519290160512624969975841)
    ·
      refine ⟨1889467620384468727481881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2519290160512624969975841 1889467620384468727481881)
      ·
        refine ⟨1417100715288351545611411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1889467620384468727481881 1417100715288351545611411)
        ·
          refine ⟨2125651072932527318417117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417100715288351545611411 2125651072932527318417117)
          ·
            refine ⟨797119152349697744406419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2125651072932527318417117 797119152349697744406419)
            ·
              refine ⟨1195678728524546616609629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797119152349697744406419 1195678728524546616609629)
              ·
                refine ⟨448379523196704981228611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195678728524546616609629 448379523196704981228611)
                ·
                  refine ⟨672569284795057471842917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448379523196704981228611 672569284795057471842917)
                  ·
                    refine ⟨126106740899073275970547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672569284795057471842917 126106740899073275970547)
                    ·
                      rfl

theorem cell22_368388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_368388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368388 prefixEnd_368388 := by exact prefixLift 368388
  have htrace : WordTrace (prefixWord ++ tailWord_368388) baseStart_368388 baseEnd_368388 := by
    simpa [prefixWord, tailWord_368388, baseEnd_368388] using wordTrace_append hprefix tailTrace_368388
  have hstable : (prefixWord ++ tailWord_368388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368388).length < 2 ^ (prefixWord ++ tailWord_368388).sum := by decide
  have hdescent : baseEnd_368388 < baseStart_368388 := by decide
  rcases family_descends (prefixWord ++ tailWord_368388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368437 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 4]
def baseStart_368437 : Nat := 118140960795 + 368437 * 2 ^ 59
def prefixEnd_368437 : Nat := 4983230072969 + 3 ^ 40 * 368437 * 2
def baseEnd_368437 : Nat := 42041171533484493831799

theorem tailTrace_368437 : CollatzResearch.WordTrace tailWord_368437 prefixEnd_368437 42041171533484493831799 := by
  unfold tailWord_368437
  simp only [CollatzResearch.WordTrace]
  refine ⟨13438001366223147875071565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8958667577482098583381043 13438001366223147875071565)
  ·
    refine ⟨5039250512333680453151837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13438001366223147875071565 5039250512333680453151837)
    ·
      refine ⟨1889718942125130169931939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5039250512333680453151837 1889718942125130169931939)
      ·
        refine ⟨2834578413187695254897909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889718942125130169931939 2834578413187695254897909)
        ·
          refine ⟨265741726236346430146679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2834578413187695254897909 265741726236346430146679)
          ·
            refine ⟨398612589354519645220019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265741726236346430146679 398612589354519645220019)
            ·
              refine ⟨597918884031779467830029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398612589354519645220019 597918884031779467830029)
              ·
                refine ⟨224219581511917300436261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597918884031779467830029 224219581511917300436261)
                ·
                  refine ⟨42041171533484493831799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224219581511917300436261 42041171533484493831799)
                  ·
                    rfl

theorem cell22_368437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_368437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368437 prefixEnd_368437 := by exact prefixLift 368437
  have htrace : WordTrace (prefixWord ++ tailWord_368437) baseStart_368437 baseEnd_368437 := by
    simpa [prefixWord, tailWord_368437, baseEnd_368437] using wordTrace_append hprefix tailTrace_368437
  have hstable : (prefixWord ++ tailWord_368437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368437).length < 2 ^ (prefixWord ++ tailWord_368437).sum := by decide
  have hdescent : baseEnd_368437 < baseStart_368437 := by decide
  rcases family_descends (prefixWord ++ tailWord_368437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368454 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_368454 : Nat := 118140960795 + 368454 * 2 ^ 59
def prefixEnd_368454 : Nat := 4983230072969 + 3 ^ 40 * 368454 * 2
def baseEnd_368454 : Nat := 42043111349290367940115

theorem tailTrace_368454 : CollatzResearch.WordTrace tailWord_368454 prefixEnd_368454 42043111349290367940115 := by
  unfold tailWord_368454
  simp only [CollatzResearch.WordTrace]
  refine ⟨419956918973798743076263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8959080938107706518960277 419956918973798743076263)
  ·
    refine ⟨629935378460698114614395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419956918973798743076263 629935378460698114614395)
    ·
      refine ⟨944903067691047171921593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 629935378460698114614395 944903067691047171921593)
      ·
        refine ⟨708677300768285378941195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944903067691047171921593 708677300768285378941195)
        ·
          refine ⟨1063015951152428068411793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708677300768285378941195 1063015951152428068411793)
          ·
            refine ⟨797261963364321051308845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063015951152428068411793 797261963364321051308845)
            ·
              refine ⟨298973236261620394240817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 797261963364321051308845 298973236261620394240817)
              ·
                refine ⟨224229927196215295680613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298973236261620394240817 224229927196215295680613)
                ·
                  refine ⟨42043111349290367940115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224229927196215295680613 42043111349290367940115)
                  ·
                    rfl

theorem cell22_368454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_368454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368454 prefixEnd_368454 := by exact prefixLift 368454
  have htrace : WordTrace (prefixWord ++ tailWord_368454) baseStart_368454 baseEnd_368454 := by
    simpa [prefixWord, tailWord_368454, baseEnd_368454] using wordTrace_append hprefix tailTrace_368454
  have hstable : (prefixWord ++ tailWord_368454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368454).length < 2 ^ (prefixWord ++ tailWord_368454).sum := by decide
  have hdescent : baseEnd_368454 < baseStart_368454 := by decide
  rcases family_descends (prefixWord ++ tailWord_368454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368510 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_368510 : Nat := 118140960795 + 368510 * 2 ^ 59
def prefixEnd_368510 : Nat := 4983230072969 + 3 ^ 40 * 368510 * 2
def baseEnd_368510 : Nat := 42049501330768541473391

theorem tailTrace_368510 : CollatzResearch.WordTrace tailWord_368510 prefixEnd_368510 42049501330768541473391 := by
  unfold tailWord_368510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680082986869835167809873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8960442596639120894985989 1680082986869835167809873)
  ·
    refine ⟨1260062240152376375857405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1680082986869835167809873 1260062240152376375857405)
    ·
      refine ⟨472523340057141140946527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1260062240152376375857405 472523340057141140946527)
      ·
        refine ⟨708785010085711711419791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472523340057141140946527 708785010085711711419791)
        ·
          refine ⟨1063177515128567567129687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708785010085711711419791 1063177515128567567129687)
          ·
            refine ⟨1594766272692851350694531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063177515128567567129687 1594766272692851350694531)
            ·
              refine ⟨2392149409039277026041797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594766272692851350694531 2392149409039277026041797)
              ·
                refine ⟨448528014194864442382837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2392149409039277026041797 448528014194864442382837)
                ·
                  refine ⟨42049501330768541473391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 448528014194864442382837 42049501330768541473391)
                  ·
                    rfl

theorem cell22_368510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_368510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368510 prefixEnd_368510 := by exact prefixLift 368510
  have htrace : WordTrace (prefixWord ++ tailWord_368510) baseStart_368510 baseEnd_368510 := by
    simpa [prefixWord, tailWord_368510, baseEnd_368510] using wordTrace_append hprefix tailTrace_368510
  have hstable : (prefixWord ++ tailWord_368510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368510).length < 2 ^ (prefixWord ++ tailWord_368510).sum := by decide
  have hdescent : baseEnd_368510 < baseStart_368510 := by decide
  rcases family_descends (prefixWord ++ tailWord_368510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368521 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 6]
def baseStart_368521 : Nat := 118140960795 + 368521 * 2 ^ 59
def prefixEnd_368521 : Nat := 4983230072969 + 3 ^ 40 * 368521 * 2
def baseEnd_368521 : Nat := 42050756505701754131713

theorem tailTrace_368521 : CollatzResearch.WordTrace tailWord_368521 prefixEnd_368521 42050756505701754131713 := by
  unfold tailWord_368521
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441065097918830221129417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8960710065279220147419611 13441065097918830221129417)
  ·
    refine ⟨10080798823439122665847063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13441065097918830221129417 10080798823439122665847063)
    ·
      refine ⟨15121198235158683998770595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10080798823439122665847063 15121198235158683998770595)
      ·
        refine ⟨22681797352738025998155893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15121198235158683998770595 22681797352738025998155893)
        ·
          refine ⟨2126418501819189937327115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22681797352738025998155893 2126418501819189937327115)
          ·
            refine ⟨3189627752728784905990673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126418501819189937327115 3189627752728784905990673)
            ·
              refine ⟨2392220814546588679493005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3189627752728784905990673 2392220814546588679493005)
              ·
                refine ⟨897082805454970754809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2392220814546588679493005 897082805454970754809877)
                ·
                  refine ⟨42050756505701754131713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 897082805454970754809877 42050756505701754131713)
                  ·
                    rfl

theorem cell22_368521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_368521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368521 prefixEnd_368521 := by exact prefixLift 368521
  have htrace : WordTrace (prefixWord ++ tailWord_368521) baseStart_368521 baseEnd_368521 := by
    simpa [prefixWord, tailWord_368521, baseEnd_368521] using wordTrace_append hprefix tailTrace_368521
  have hstable : (prefixWord ++ tailWord_368521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368521).length < 2 ^ (prefixWord ++ tailWord_368521).sum := by decide
  have hdescent : baseEnd_368521 < baseStart_368521 := by decide
  rcases family_descends (prefixWord ++ tailWord_368521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368538 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_368538 : Nat := 118140960795 + 368538 * 2 ^ 59
def prefixEnd_368538 : Nat := 4983230072969 + 3 ^ 40 * 368538 * 2
def baseEnd_368538 : Nat := 42052696321507628240029

theorem tailTrace_368538 : CollatzResearch.WordTrace tailWord_368538 prefixEnd_368538 42052696321507628240029 := by
  unfold tailWord_368538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360421284714310531124567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8961123425904828082998845 3360421284714310531124567)
  ·
    refine ⟨5040631927071465796686851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3360421284714310531124567 5040631927071465796686851)
    ·
      refine ⟨7560947890607198695030277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040631927071465796686851 7560947890607198695030277)
      ·
        refine ⟨1417677729488849755318177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7560947890607198695030277 1417677729488849755318177)
        ·
          refine ⟨1063258297116637316488633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1417677729488849755318177 1063258297116637316488633)
          ·
            refine ⟨797443722837477987366475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063258297116637316488633 797443722837477987366475)
            ·
              refine ⟨1196165584256216981049713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797443722837477987366475 1196165584256216981049713)
              ·
                refine ⟨897124188192162735787285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196165584256216981049713 897124188192162735787285)
                ·
                  refine ⟨42052696321507628240029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 897124188192162735787285 42052696321507628240029)
                  ·
                    rfl

theorem cell22_368538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_368538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368538 prefixEnd_368538 := by exact prefixLift 368538
  have htrace : WordTrace (prefixWord ++ tailWord_368538) baseStart_368538 baseEnd_368538 := by
    simpa [prefixWord, tailWord_368538, baseEnd_368538] using wordTrace_append hprefix tailTrace_368538
  have hstable : (prefixWord ++ tailWord_368538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368538).length < 2 ^ (prefixWord ++ tailWord_368538).sum := by decide
  have hdescent : baseEnd_368538 < baseStart_368538 := by decide
  rcases family_descends (prefixWord ++ tailWord_368538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368645 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 5]
def baseStart_368645 : Nat := 118140960795 + 368645 * 2 ^ 59
def prefixEnd_368645 : Nat := 4983230072969 + 3 ^ 40 * 368645 * 2
def baseEnd_368645 : Nat := 42064905750403424098253

theorem tailTrace_368645 : CollatzResearch.WordTrace tailWord_368645 prefixEnd_368645 42064905750403424098253 := by
  unfold tailWord_368645
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445587749469599398643389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8963725166313066265762259 13445587749469599398643389)
  ·
    refine ⟨5042095406051099774491271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13445587749469599398643389 5042095406051099774491271)
    ·
      refine ⟨7563143109076649661736907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5042095406051099774491271 7563143109076649661736907)
      ·
        refine ⟨11344714663614974492605361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563143109076649661736907 11344714663614974492605361)
        ·
          refine ⟨8508535997711230869454021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11344714663614974492605361 8508535997711230869454021)
          ·
            refine ⟨1595350499570855788022629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8508535997711230869454021 1595350499570855788022629)
            ·
              refine ⟨299128218669535460254243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1595350499570855788022629 299128218669535460254243)
              ·
                refine ⟨448692328004303190381365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299128218669535460254243 448692328004303190381365)
                ·
                  refine ⟨42064905750403424098253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 448692328004303190381365 42064905750403424098253)
                  ·
                    rfl

theorem cell22_368645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_368645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368645 prefixEnd_368645 := by exact prefixLift 368645
  have htrace : WordTrace (prefixWord ++ tailWord_368645) baseStart_368645 baseEnd_368645 := by
    simpa [prefixWord, tailWord_368645, baseEnd_368645] using wordTrace_append hprefix tailTrace_368645
  have hstable : (prefixWord ++ tailWord_368645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368645).length < 2 ^ (prefixWord ++ tailWord_368645).sum := by decide
  have hdescent : baseEnd_368645 < baseStart_368645 := by decide
  rcases family_descends (prefixWord ++ tailWord_368645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368703 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_368703 : Nat := 118140960795 + 368703 * 2 ^ 59
def prefixEnd_368703 : Nat := 4983230072969 + 3 ^ 40 * 368703 * 2
def baseEnd_368703 : Nat := 126214571836517454344581

theorem tailTrace_368703 : CollatzResearch.WordTrace tailWord_368703 prefixEnd_368703 126214571836517454344581 := by
  unfold tailWord_368703
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447703183259475304254763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8965135455506316869503175 13447703183259475304254763)
  ·
    refine ⟨20171554774889212956382145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13447703183259475304254763 20171554774889212956382145)
    ·
      refine ⟨15128666081166909717286609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20171554774889212956382145 15128666081166909717286609)
      ·
        refine ⟨11346499560875182287964957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15128666081166909717286609 11346499560875182287964957)
        ·
          refine ⟨4254937335328193357986859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11346499560875182287964957 4254937335328193357986859)
          ·
            refine ⟨6382406002992290036980289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254937335328193357986859 6382406002992290036980289)
            ·
              refine ⟨4786804502244217527735217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6382406002992290036980289 4786804502244217527735217)
              ·
                refine ⟨3590103376683163145801413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4786804502244217527735217 3590103376683163145801413)
                ·
                  refine ⟨673144383128093089837765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3590103376683163145801413 673144383128093089837765)
                  ·
                    refine ⟨126214571836517454344581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673144383128093089837765 126214571836517454344581)
                    ·
                      rfl

theorem cell22_368703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_368703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368703 prefixEnd_368703 := by exact prefixLift 368703
  have htrace : WordTrace (prefixWord ++ tailWord_368703) baseStart_368703 baseEnd_368703 := by
    simpa [prefixWord, tailWord_368703, baseEnd_368703] using wordTrace_append hprefix tailTrace_368703
  have hstable : (prefixWord ++ tailWord_368703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368703).length < 2 ^ (prefixWord ++ tailWord_368703).sum := by decide
  have hdescent : baseEnd_368703 < baseStart_368703 := by decide
  rcases family_descends (prefixWord ++ tailWord_368703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368705 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_368705 : Nat := 118140960795 + 368705 * 2 ^ 59
def prefixEnd_368705 : Nat := 4983230072969 + 3 ^ 40 * 368705 * 2
def baseEnd_368705 : Nat := 126215256477390115794575

theorem tailTrace_368705 : CollatzResearch.WordTrace tailWord_368705 prefixEnd_368705 126215256477390115794575 := by
  unfold tailWord_368705
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447776129252229645827569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8965184086168153097218379 13447776129252229645827569)
  ·
    refine ⟨10085832096939172234370677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13447776129252229645827569 10085832096939172234370677)
    ·
      refine ⟨945546759088047396972251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10085832096939172234370677 945546759088047396972251)
      ·
        refine ⟨1418320138632071095458377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945546759088047396972251 1418320138632071095458377)
        ·
          refine ⟨1063740103974053321593783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418320138632071095458377 1063740103974053321593783)
          ·
            refine ⟨1595610155961079982390675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063740103974053321593783 1595610155961079982390675)
            ·
              refine ⟨2393415233941619973586013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595610155961079982390675 2393415233941619973586013)
              ·
                refine ⟨897530712728107490094755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2393415233941619973586013 897530712728107490094755)
                ·
                  refine ⟨1346296069092161235142133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897530712728107490094755 1346296069092161235142133)
                  ·
                    refine ⟨126215256477390115794575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1346296069092161235142133 126215256477390115794575)
                    ·
                      rfl

theorem cell22_368705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_368705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368705 prefixEnd_368705 := by exact prefixLift 368705
  have htrace : WordTrace (prefixWord ++ tailWord_368705) baseStart_368705 baseEnd_368705 := by
    simpa [prefixWord, tailWord_368705, baseEnd_368705] using wordTrace_append hprefix tailTrace_368705
  have hstable : (prefixWord ++ tailWord_368705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368705).length < 2 ^ (prefixWord ++ tailWord_368705).sum := by decide
  have hdescent : baseEnd_368705 < baseStart_368705 := by decide
  rcases family_descends (prefixWord ++ tailWord_368705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368726 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_368726 : Nat := 118140960795 + 368726 * 2 ^ 59
def prefixEnd_368726 : Nat := 4983230072969 + 3 ^ 40 * 368726 * 2
def baseEnd_368726 : Nat := 126222445206553061019511

theorem tailTrace_368726 : CollatzResearch.WordTrace tailWord_368726 prefixEnd_368726 126222445206553061019511 := by
  unfold tailWord_368726
  simp only [CollatzResearch.WordTrace]
  refine ⟨840533878886009389521377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8965694708117433488228021 840533878886009389521377)
  ·
    refine ⟨630400409164507042141033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 840533878886009389521377 630400409164507042141033)
    ·
      refine ⟨472800306873380281605775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630400409164507042141033 472800306873380281605775)
      ·
        refine ⟨709200460310070422408663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472800306873380281605775 709200460310070422408663)
        ·
          refine ⟨1063800690465105633612995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709200460310070422408663 1063800690465105633612995)
          ·
            refine ⟨1595701035697658450419493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063800690465105633612995 1595701035697658450419493)
            ·
              refine ⟨299193944193310959453655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1595701035697658450419493 299193944193310959453655)
              ·
                refine ⟨448790916289966439180483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299193944193310959453655 448790916289966439180483)
                ·
                  refine ⟨673186374434949658770725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448790916289966439180483 673186374434949658770725)
                  ·
                    refine ⟨126222445206553061019511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673186374434949658770725 126222445206553061019511)
                    ·
                      rfl

theorem cell22_368726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_368726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368726 prefixEnd_368726 := by exact prefixLift 368726
  have htrace : WordTrace (prefixWord ++ tailWord_368726) baseStart_368726 baseEnd_368726 := by
    simpa [prefixWord, tailWord_368726, baseEnd_368726] using wordTrace_append hprefix tailTrace_368726
  have hstable : (prefixWord ++ tailWord_368726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368726).length < 2 ^ (prefixWord ++ tailWord_368726).sum := by decide
  have hdescent : baseEnd_368726 < baseStart_368726 := by decide
  rcases family_descends (prefixWord ++ tailWord_368726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368769 : List Nat := [1, 2, 4, 2, 4, 1, 2, 6]
def baseStart_368769 : Nat := 118140960795 + 368769 * 2 ^ 59
def prefixEnd_368769 : Nat := 4983230072969 + 3 ^ 40 * 368769 * 2
def baseEnd_368769 : Nat := 14026351665035031354931

theorem tailTrace_368769 : CollatzResearch.WordTrace tailWord_368769 prefixEnd_368769 14026351665035031354931 := by
  unfold tailWord_368769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450110401020368576157361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8966740267346912384104907 13450110401020368576157361)
  ·
    refine ⟨10087582800765276432118021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13450110401020368576157361 10087582800765276432118021)
    ·
      refine ⟨1891421775143489331022129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10087582800765276432118021 1891421775143489331022129)
      ·
        refine ⟨1418566331357616998266597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1891421775143489331022129 1418566331357616998266597)
        ·
          refine ⟨265981187129553187174987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1418566331357616998266597 265981187129553187174987)
          ·
            refine ⟨398971780694329780762481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265981187129553187174987 398971780694329780762481)
            ·
              refine ⟨299228835520747335571861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398971780694329780762481 299228835520747335571861)
              ·
                refine ⟨14026351665035031354931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 299228835520747335571861 14026351665035031354931)
                ·
                  rfl

theorem cell22_368769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 6].length) (baseStart_368769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368769 prefixEnd_368769 := by exact prefixLift 368769
  have htrace : WordTrace (prefixWord ++ tailWord_368769) baseStart_368769 baseEnd_368769 := by
    simpa [prefixWord, tailWord_368769, baseEnd_368769] using wordTrace_append hprefix tailTrace_368769
  have hstable : (prefixWord ++ tailWord_368769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368769).length < 2 ^ (prefixWord ++ tailWord_368769).sum := by decide
  have hdescent : baseEnd_368769 < baseStart_368769 := by decide
  rcases family_descends (prefixWord ++ tailWord_368769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368801 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 1, 3]
def baseStart_368801 : Nat := 118140960795 + 368801 * 2 ^ 59
def prefixEnd_368801 : Nat := 4983230072969 + 3 ^ 40 * 368801 * 2
def baseEnd_368801 : Nat := 126248119239277865394281

theorem tailTrace_368801 : CollatzResearch.WordTrace tailWord_368801 prefixEnd_368801 126248119239277865394281 := by
  unfold tailWord_368801
  simp only [CollatzResearch.WordTrace]
  refine ⟨13451277536904438041322257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8967518357936292027548171 13451277536904438041322257)
  ·
    refine ⟨10088458152678328530991693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13451277536904438041322257 10088458152678328530991693)
    ·
      refine ⟨3783171807254373199121885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10088458152678328530991693 3783171807254373199121885)
      ·
        refine ⟨1418689427720389949670707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3783171807254373199121885 1418689427720389949670707)
        ·
          refine ⟨2128034141580584924506061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418689427720389949670707 2128034141580584924506061)
          ·
            refine ⟨798012803092719346689773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2128034141580584924506061 798012803092719346689773)
            ·
              refine ⟨299254801159769755008665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798012803092719346689773 299254801159769755008665)
              ·
                refine ⟨224441100869827316256499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299254801159769755008665 224441100869827316256499)
                ·
                  refine ⟨336661651304740974384749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224441100869827316256499 336661651304740974384749)
                  ·
                    refine ⟨126248119239277865394281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336661651304740974384749 126248119239277865394281)
                    ·
                      rfl

theorem cell22_368801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_368801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368801 prefixEnd_368801 := by exact prefixLift 368801
  have htrace : WordTrace (prefixWord ++ tailWord_368801) baseStart_368801 baseEnd_368801 := by
    simpa [prefixWord, tailWord_368801, baseEnd_368801] using wordTrace_append hprefix tailTrace_368801
  have hstable : (prefixWord ++ tailWord_368801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368801).length < 2 ^ (prefixWord ++ tailWord_368801).sum := by decide
  have hdescent : baseEnd_368801 < baseStart_368801 := by decide
  rcases family_descends (prefixWord ++ tailWord_368801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368842 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_368842 : Nat := 118140960795 + 368842 * 2 ^ 59
def prefixEnd_368842 : Nat := 4983230072969 + 3 ^ 40 * 368842 * 2
def baseEnd_368842 : Nat := 42087384792389141706385

theorem tailTrace_368842 : CollatzResearch.WordTrace tailWord_368842 prefixEnd_368842 42087384792389141706385 := by
  unfold tailWord_368842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3363193232438975510891195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8968515286503934695709853 3363193232438975510891195)
  ·
    refine ⟨5044789848658463266336793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3363193232438975510891195 5044789848658463266336793)
    ·
      refine ⟨3783592386493847449752595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5044789848658463266336793 3783592386493847449752595)
      ·
        refine ⟨5675388579740771174628893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3783592386493847449752595 5675388579740771174628893)
        ·
          refine ⟨2128270717402789190485835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5675388579740771174628893 2128270717402789190485835)
          ·
            refine ⟨3192406076104183785728753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128270717402789190485835 3192406076104183785728753)
            ·
              refine ⟨2394304557078137839296565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192406076104183785728753 2394304557078137839296565)
              ·
                refine ⟨224466052226075422434053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2394304557078137839296565 224466052226075422434053)
                ·
                  refine ⟨42087384792389141706385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224466052226075422434053 42087384792389141706385)
                  ·
                    rfl

theorem cell22_368842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_368842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368842 prefixEnd_368842 := by exact prefixLift 368842
  have htrace : WordTrace (prefixWord ++ tailWord_368842) baseStart_368842 baseEnd_368842 := by
    simpa [prefixWord, tailWord_368842, baseEnd_368842] using wordTrace_append hprefix tailTrace_368842
  have hstable : (prefixWord ++ tailWord_368842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368842).length < 2 ^ (prefixWord ++ tailWord_368842).sum := by decide
  have hdescent : baseEnd_368842 < baseStart_368842 := by decide
  rcases family_descends (prefixWord ++ tailWord_368842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368857 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 2, 3]
def baseStart_368857 : Nat := 118140960795 + 368857 * 2 ^ 59
def prefixEnd_368857 : Nat := 4983230072969 + 3 ^ 40 * 368857 * 2
def baseEnd_368857 : Nat := 126267289183712385994109

theorem tailTrace_368857 : CollatzResearch.WordTrace tailWord_368857 prefixEnd_368857 126267289183712385994109 := by
  unfold tailWord_368857
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453320024701559605360825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8968880016467706403573883 13453320024701559605360825)
  ·
    refine ⟨10089990018526169704020619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13453320024701559605360825 10089990018526169704020619)
    ·
      refine ⟨15134985027789254556030929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10089990018526169704020619 15134985027789254556030929)
      ·
        refine ⟨11351238770841940917023197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15134985027789254556030929 11351238770841940917023197)
        ·
          refine ⟨4256714539065727843883699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11351238770841940917023197 4256714539065727843883699)
          ·
            refine ⟨6385071808598591765825549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256714539065727843883699 6385071808598591765825549)
            ·
              refine ⟨2394401928224471912184581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6385071808598591765825549 2394401928224471912184581)
              ·
                refine ⟨448950361542088483534609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2394401928224471912184581 448950361542088483534609)
                ·
                  refine ⟨336712771156566362650957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448950361542088483534609 336712771156566362650957)
                  ·
                    refine ⟨126267289183712385994109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336712771156566362650957 126267289183712385994109)
                    ·
                      rfl

theorem cell22_368857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_368857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368857 prefixEnd_368857 := by exact prefixLift 368857
  have htrace : WordTrace (prefixWord ++ tailWord_368857) baseStart_368857 baseEnd_368857 := by
    simpa [prefixWord, tailWord_368857, baseEnd_368857] using wordTrace_append hprefix tailTrace_368857
  have hstable : (prefixWord ++ tailWord_368857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368857).length < 2 ^ (prefixWord ++ tailWord_368857).sum := by decide
  have hdescent : baseEnd_368857 < baseStart_368857 := by decide
  rcases family_descends (prefixWord ++ tailWord_368857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368919 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 3, 3]
def baseStart_368919 : Nat := 118140960795 + 368919 * 2 ^ 59
def prefixEnd_368919 : Nat := 4983230072969 + 3 ^ 40 * 368919 * 2
def baseEnd_368919 : Nat := 126288513050764890943919

theorem tailTrace_368919 : CollatzResearch.WordTrace tailWord_368919 prefixEnd_368919 126288513050764890943919 := by
  unfold tailWord_368919
  simp only [CollatzResearch.WordTrace]
  refine ⟨13455581350476944194117811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8970387566984629462745207 13455581350476944194117811)
  ·
    refine ⟨20183372025715416291176717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13455581350476944194117811 20183372025715416291176717)
    ·
      refine ⟨7568764509643281109191269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20183372025715416291176717 7568764509643281109191269)
      ·
        refine ⟨1419143345558115207973363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7568764509643281109191269 1419143345558115207973363)
        ·
          refine ⟨2128715018337172811960045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419143345558115207973363 2128715018337172811960045)
          ·
            refine ⟨798268131876439804485017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2128715018337172811960045 798268131876439804485017)
            ·
              refine ⟨598701098907329853363763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798268131876439804485017 598701098907329853363763)
              ·
                refine ⟨898051648360994780045645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598701098907329853363763 898051648360994780045645)
                ·
                  refine ⟨336769368135373042517117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898051648360994780045645 336769368135373042517117)
                  ·
                    refine ⟨126288513050764890943919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336769368135373042517117 126288513050764890943919)
                    ·
                      rfl

theorem cell22_368919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_368919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368919 prefixEnd_368919 := by exact prefixLift 368919
  have htrace : WordTrace (prefixWord ++ tailWord_368919) baseStart_368919 baseEnd_368919 := by
    simpa [prefixWord, tailWord_368919, baseEnd_368919] using wordTrace_append hprefix tailTrace_368919
  have hstable : (prefixWord ++ tailWord_368919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368919).length < 2 ^ (prefixWord ++ tailWord_368919).sum := by decide
  have hdescent : baseEnd_368919 < baseStart_368919 := by decide
  rcases family_descends (prefixWord ++ tailWord_368919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368953 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 1, 3]
def baseStart_368953 : Nat := 118140960795 + 368953 * 2 ^ 59
def prefixEnd_368953 : Nat := 4983230072969 + 3 ^ 40 * 368953 * 2
def baseEnd_368953 : Nat := 126300151945600135593815

theorem tailTrace_368953 : CollatzResearch.WordTrace tailWord_368953 prefixEnd_368953 126300151945600135593815 := by
  unfold tailWord_368953
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456821432353768000855513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971214288235845333903675 13456821432353768000855513)
  ·
    refine ⟨10092616074265326000641635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13456821432353768000855513 10092616074265326000641635)
    ·
      refine ⟨15138924111397989000962453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10092616074265326000641635 15138924111397989000962453)
      ·
        refine ⟨709637067721780734420115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15138924111397989000962453 709637067721780734420115)
        ·
          refine ⟨1064455601582671101630173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709637067721780734420115 1064455601582671101630173)
          ·
            refine ⟨399170850593501663111315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1064455601582671101630173 399170850593501663111315)
            ·
              refine ⟨598756275890252494666973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399170850593501663111315 598756275890252494666973)
              ·
                refine ⟨224533603458844685500115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598756275890252494666973 224533603458844685500115)
                ·
                  refine ⟨336800405188267028250173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224533603458844685500115 336800405188267028250173)
                  ·
                    refine ⟨126300151945600135593815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336800405188267028250173 126300151945600135593815)
                    ·
                      rfl

theorem cell22_368953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_368953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368953 prefixEnd_368953 := by exact prefixLift 368953
  have htrace : WordTrace (prefixWord ++ tailWord_368953) baseStart_368953 baseEnd_368953 := by
    simpa [prefixWord, tailWord_368953, baseEnd_368953] using wordTrace_append hprefix tailTrace_368953
  have hstable : (prefixWord ++ tailWord_368953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368953).length < 2 ^ (prefixWord ++ tailWord_368953).sum := by decide
  have hdescent : baseEnd_368953 < baseStart_368953 := by decide
  rcases family_descends (prefixWord ++ tailWord_368953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368975 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_368975 : Nat := 118140960795 + 368975 * 2 ^ 59
def prefixEnd_368975 : Nat := 4983230072969 + 3 ^ 40 * 368975 * 2
def baseEnd_368975 : Nat := 126307682995199411543747

theorem tailTrace_368975 : CollatzResearch.WordTrace tailWord_368975 prefixEnd_368975 126307682995199411543747 := by
  unfold tailWord_368975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457623838274065758156379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971749225516043838770919 13457623838274065758156379)
  ·
    refine ⟨20186435757411098637234569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13457623838274065758156379 20186435757411098637234569)
    ·
      refine ⟨15139826818058323977925927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20186435757411098637234569 15139826818058323977925927)
      ·
        refine ⟨22709740227087485966888891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15139826818058323977925927 22709740227087485966888891)
        ·
          refine ⟨34064610340631228950333337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22709740227087485966888891 34064610340631228950333337)
          ·
            refine ⟨25548457755473421712750003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34064610340631228950333337 25548457755473421712750003)
            ·
              refine ⟨38322686633210132569125005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548457755473421712750003 38322686633210132569125005)
              ·
                refine ⟨14371007487453799713421877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38322686633210132569125005 14371007487453799713421877)
                ·
                  refine ⟨1347281951948793723133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14371007487453799713421877 1347281951948793723133301)
                  ·
                    refine ⟨126307682995199411543747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1347281951948793723133301 126307682995199411543747)
                    ·
                      rfl

theorem cell22_368975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_368975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368975 prefixEnd_368975 := by exact prefixLift 368975
  have htrace : WordTrace (prefixWord ++ tailWord_368975) baseStart_368975 baseEnd_368975 := by
    simpa [prefixWord, tailWord_368975, baseEnd_368975] using wordTrace_append hprefix tailTrace_368975
  have hstable : (prefixWord ++ tailWord_368975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368975).length < 2 ^ (prefixWord ++ tailWord_368975).sum := by decide
  have hdescent : baseEnd_368975 < baseStart_368975 := by decide
  rcases family_descends (prefixWord ++ tailWord_368975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368977 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 6]
def baseStart_368977 : Nat := 118140960795 + 368977 * 2 ^ 59
def prefixEnd_368977 : Nat := 4983230072969 + 3 ^ 40 * 368977 * 2
def baseEnd_368977 : Nat := 42102789212024024331247

theorem tailTrace_368977 : CollatzResearch.WordTrace tailWord_368977 prefixEnd_368977 42102789212024024331247 := by
  unfold tailWord_368977
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457696784266820099729185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971797856177880066486123 13457696784266820099729185)
  ·
    refine ⟨10093272588200115074796889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13457696784266820099729185 10093272588200115074796889)
    ·
      refine ⟨7569954441150086306097667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10093272588200115074796889 7569954441150086306097667)
      ·
        refine ⟨11354931661725129459146501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569954441150086306097667 11354931661725129459146501)
        ·
          refine ⟨2129049686573461773589969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11354931661725129459146501 2129049686573461773589969)
          ·
            refine ⟨1596787264930096330192477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129049686573461773589969 1596787264930096330192477)
            ·
              refine ⟨598795224348786123822179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596787264930096330192477 598795224348786123822179)
              ·
                refine ⟨898192836523179185733269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598795224348786123822179 898192836523179185733269)
                ·
                  refine ⟨42102789212024024331247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 898192836523179185733269 42102789212024024331247)
                  ·
                    rfl

theorem cell22_368977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_368977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_368977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_368977 prefixEnd_368977 := by exact prefixLift 368977
  have htrace : WordTrace (prefixWord ++ tailWord_368977) baseStart_368977 baseEnd_368977 := by
    simpa [prefixWord, tailWord_368977, baseEnd_368977] using wordTrace_append hprefix tailTrace_368977
  have hstable : (prefixWord ++ tailWord_368977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368977).length < 2 ^ (prefixWord ++ tailWord_368977).sum := by decide
  have hdescent : baseEnd_368977 < baseStart_368977 := by decide
  rcases family_descends (prefixWord ++ tailWord_368977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369022 : List Nat := [4, 2, 3, 13]
def baseStart_369022 : Nat := 118140960795 + 369022 * 2 ^ 59
def prefixEnd_369022 : Nat := 4983230072969 + 3 ^ 40 * 369022 * 2
def baseEnd_369022 : Nat := 173283637936497881507

theorem tailTrace_369022 : CollatzResearch.WordTrace tailWord_369022 prefixEnd_369022 173283637936497881507 := by
  unfold tailWord_369022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682417258637974098139665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8972892046069195190078213 1682417258637974098139665)
  ·
    refine ⟨1261812943978480573604749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1682417258637974098139665 1261812943978480573604749)
    ·
      refine ⟨473179853991930215101781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1261812943978480573604749 473179853991930215101781)
      ·
        refine ⟨173283637936497881507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 473179853991930215101781 173283637936497881507)
        ·
          rfl

theorem cell22_369022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 13].length) (baseStart_369022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369022 prefixEnd_369022 := by exact prefixLift 369022
  have htrace : WordTrace (prefixWord ++ tailWord_369022) baseStart_369022 baseEnd_369022 := by
    simpa [prefixWord, tailWord_369022, baseEnd_369022] using wordTrace_append hprefix tailTrace_369022
  have hstable : (prefixWord ++ tailWord_369022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369022).length < 2 ^ (prefixWord ++ tailWord_369022).sum := by decide
  have hdescent : baseEnd_369022 < baseStart_369022 := by decide
  rcases family_descends (prefixWord ++ tailWord_369022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369084 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_369084 : Nat := 118140960795 + 369084 * 2 ^ 59
def prefixEnd_369084 : Nat := 4983230072969 + 3 ^ 40 * 369084 * 2
def baseEnd_369084 : Nat := 42114998640919820189471

theorem tailTrace_369084 : CollatzResearch.WordTrace tailWord_369084 prefixEnd_369084 42114998640919820189471 := by
  unfold tailWord_369084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730799697439588686937153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8974399596586118249249537 6730799697439588686937153)
  ·
    refine ⟨5048099773079691515202865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6730799697439588686937153 5048099773079691515202865)
    ·
      refine ⟨3786074829809768636402149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048099773079691515202865 3786074829809768636402149)
      ·
        refine ⟨709889030589331619325403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3786074829809768636402149 709889030589331619325403)
        ·
          refine ⟨1064833545883997428988105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709889030589331619325403 1064833545883997428988105)
          ·
            refine ⟨798625159412998071741079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064833545883997428988105 798625159412998071741079)
            ·
              refine ⟨1197937739119497107611619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798625159412998071741079 1197937739119497107611619)
              ·
                refine ⟨1796906608679245661417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197937739119497107611619 1796906608679245661417429)
                ·
                  refine ⟨42114998640919820189471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1796906608679245661417429 42114998640919820189471)
                  ·
                    rfl

theorem cell22_369084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_369084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369084 prefixEnd_369084 := by exact prefixLift 369084
  have htrace : WordTrace (prefixWord ++ tailWord_369084) baseStart_369084 baseEnd_369084 := by
    simpa [prefixWord, tailWord_369084, baseEnd_369084] using wordTrace_append hprefix tailTrace_369084
  have hstable : (prefixWord ++ tailWord_369084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369084).length < 2 ^ (prefixWord ++ tailWord_369084).sum := by decide
  have hdescent : baseEnd_369084 < baseStart_369084 := by decide
  rcases family_descends (prefixWord ++ tailWord_369084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369097 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_369097 : Nat := 118140960795 + 369097 * 2 ^ 59
def prefixEnd_369097 : Nat := 4983230072969 + 3 ^ 40 * 369097 * 2
def baseEnd_369097 : Nat := 126349446088431759993373

theorem tailTrace_369097 : CollatzResearch.WordTrace tailWord_369097 prefixEnd_369097 126349446088431759993373 := by
  unfold tailWord_369097
  simp only [CollatzResearch.WordTrace]
  refine ⟨13462073543832080594097545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8974715695888053729398363 13462073543832080594097545)
  ·
    refine ⟨10096555157874060445573159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13462073543832080594097545 10096555157874060445573159)
    ·
      refine ⟨15144832736811090668359739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10096555157874060445573159 15144832736811090668359739)
      ·
        refine ⟨22717249105216636002539609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15144832736811090668359739 22717249105216636002539609)
        ·
          refine ⟨17037936828912477001904707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22717249105216636002539609 17037936828912477001904707)
          ·
            refine ⟨25556905243368715502857061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037936828912477001904707 25556905243368715502857061)
            ·
              refine ⟨4791919733131634156785699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25556905243368715502857061 4791919733131634156785699)
              ·
                refine ⟨7187879599697451235178549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4791919733131634156785699 7187879599697451235178549)
                ·
                  refine ⟨673863712471636053297989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7187879599697451235178549 673863712471636053297989)
                  ·
                    refine ⟨126349446088431759993373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673863712471636053297989 126349446088431759993373)
                    ·
                      rfl

theorem cell22_369097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_369097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369097 prefixEnd_369097 := by exact prefixLift 369097
  have htrace : WordTrace (prefixWord ++ tailWord_369097) baseStart_369097 baseEnd_369097 := by
    simpa [prefixWord, tailWord_369097, baseEnd_369097] using wordTrace_append hprefix tailTrace_369097
  have hstable : (prefixWord ++ tailWord_369097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369097).length < 2 ^ (prefixWord ++ tailWord_369097).sum := by decide
  have hdescent : baseEnd_369097 < baseStart_369097 := by decide
  rcases family_descends (prefixWord ++ tailWord_369097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369129 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 4]
def baseStart_369129 : Nat := 118140960795 + 369129 * 2 ^ 59
def prefixEnd_369129 : Nat := 4983230072969 + 3 ^ 40 * 369129 * 2
def baseEnd_369129 : Nat := 42120133447464781064425

theorem tailTrace_369129 : CollatzResearch.WordTrace tailWord_369129 prefixEnd_369129 42120133447464781064425 := by
  unfold tailWord_369129
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463240679716150059262441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8975493786477433372841627 13463240679716150059262441)
  ·
    refine ⟨10097430509787112544446831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13463240679716150059262441 10097430509787112544446831)
    ·
      refine ⟨15146145764680668816670247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10097430509787112544446831 15146145764680668816670247)
      ·
        refine ⟨22719218647021003225005371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15146145764680668816670247 22719218647021003225005371)
        ·
          refine ⟨34078827970531504837508057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22719218647021003225005371 34078827970531504837508057)
          ·
            refine ⟨25559120977898628628131043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34078827970531504837508057 25559120977898628628131043)
            ·
              refine ⟨38338681466847942942196565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25559120977898628628131043 38338681466847942942196565)
              ·
                refine ⟨224640711719812165676933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 38338681466847942942196565 224640711719812165676933)
                ·
                  refine ⟨42120133447464781064425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224640711719812165676933 42120133447464781064425)
                  ·
                    rfl

theorem cell22_369129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_369129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369129 prefixEnd_369129 := by exact prefixLift 369129
  have htrace : WordTrace (prefixWord ++ tailWord_369129) baseStart_369129 baseEnd_369129 := by
    simpa [prefixWord, tailWord_369129, baseEnd_369129] using wordTrace_append hprefix tailTrace_369129
  have hstable : (prefixWord ++ tailWord_369129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369129).length < 2 ^ (prefixWord ++ tailWord_369129).sum := by decide
  have hdescent : baseEnd_369129 < baseStart_369129 := by decide
  rcases family_descends (prefixWord ++ tailWord_369129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369144 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_369144 : Nat := 118140960795 + 369144 * 2 ^ 59
def prefixEnd_369144 : Nat := 4983230072969 + 3 ^ 40 * 369144 * 2
def baseEnd_369144 : Nat := 126365535148939304068229

theorem tailTrace_369144 : CollatzResearch.WordTrace tailWord_369144 prefixEnd_369144 126365535148939304068229 := by
  unfold tailWord_369144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731893887330903810529243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8975858516441205080705657 6731893887330903810529243)
  ·
    refine ⟨10097840830996355715793865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6731893887330903810529243 10097840830996355715793865)
    ·
      refine ⟨7573380623247266786845399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10097840830996355715793865 7573380623247266786845399)
      ·
        refine ⟨11360070934870900180268099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573380623247266786845399 11360070934870900180268099)
        ·
          refine ⟨17040106402306350270402149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11360070934870900180268099 17040106402306350270402149)
          ·
            refine ⟨3195019950432440675700403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17040106402306350270402149 3195019950432440675700403)
            ·
              refine ⟨4792529925648661013550605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195019950432440675700403 4792529925648661013550605)
              ·
                refine ⟨1797198722118247880081477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792529925648661013550605 1797198722118247880081477)
                ·
                  refine ⟨336974760397171477515277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797198722118247880081477 336974760397171477515277)
                  ·
                    refine ⟨126365535148939304068229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336974760397171477515277 126365535148939304068229)
                    ·
                      rfl

theorem cell22_369144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_369144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369144 prefixEnd_369144 := by exact prefixLift 369144
  have htrace : WordTrace (prefixWord ++ tailWord_369144) baseStart_369144 baseEnd_369144 := by
    simpa [prefixWord, tailWord_369144, baseEnd_369144] using wordTrace_append hprefix tailTrace_369144
  have hstable : (prefixWord ++ tailWord_369144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369144).length < 2 ^ (prefixWord ++ tailWord_369144).sum := by decide
  have hdescent : baseEnd_369144 < baseStart_369144 := by decide
  rcases family_descends (prefixWord ++ tailWord_369144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369157 : List Nat := [1, 3, 1, 1, 2, 2, 3, 9]
def baseStart_369157 : Nat := 118140960795 + 369157 * 2 ^ 59
def prefixEnd_369157 : Nat := 4983230072969 + 3 ^ 40 * 369157 * 2
def baseEnd_369157 : Nat := 14041109479401289277021

theorem tailTrace_369157 : CollatzResearch.WordTrace tailWord_369157 prefixEnd_369157 14041109479401289277021 := by
  unfold tailWord_369157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13464261923614710841281725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8976174615743140560854483 13464261923614710841281725)
  ·
    refine ⟨5049098221355516565480647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13464261923614710841281725 5049098221355516565480647)
    ·
      refine ⟨7573647332033274848220971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5049098221355516565480647 7573647332033274848220971)
      ·
        refine ⟨11360470998049912272331457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573647332033274848220971 11360470998049912272331457)
        ·
          refine ⟨8520353248537434204248593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11360470998049912272331457 8520353248537434204248593)
          ·
            refine ⟨6390264936403075653186445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8520353248537434204248593 6390264936403075653186445)
            ·
              refine ⟨2396349351151153369944917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6390264936403075653186445 2396349351151153369944917)
              ·
                refine ⟨14041109479401289277021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2396349351151153369944917 14041109479401289277021)
                ·
                  rfl

theorem cell22_369157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 9].length) (baseStart_369157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369157 prefixEnd_369157 := by exact prefixLift 369157
  have htrace : WordTrace (prefixWord ++ tailWord_369157) baseStart_369157 baseEnd_369157 := by
    simpa [prefixWord, tailWord_369157, baseEnd_369157] using wordTrace_append hprefix tailTrace_369157
  have hstable : (prefixWord ++ tailWord_369157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369157).length < 2 ^ (prefixWord ++ tailWord_369157).sum := by decide
  have hdescent : baseEnd_369157 < baseStart_369157 := by decide
  rcases family_descends (prefixWord ++ tailWord_369157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369165 : List Nat := [1, 7, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_369165 : Nat := 118140960795 + 369165 * 2 ^ 59
def prefixEnd_369165 : Nat := 4983230072969 + 3 ^ 40 * 369165 * 2
def baseEnd_369165 : Nat := 126372723878102249293165

theorem tailTrace_369165 : CollatzResearch.WordTrace tailWord_369165 prefixEnd_369165 126372723878102249293165 := by
  unfold tailWord_369165
  simp only [CollatzResearch.WordTrace]
  refine ⟨13464553707585728207572949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8976369138390485471715299 13464553707585728207572949)
  ·
    refine ⟨315575477521540504864991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13464553707585728207572949 315575477521540504864991)
    ·
      refine ⟨473363216282310757297487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315575477521540504864991 473363216282310757297487)
      ·
        refine ⟨710044824423466135946231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473363216282310757297487 710044824423466135946231)
        ·
          refine ⟨1065067236635199203919347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710044824423466135946231 1065067236635199203919347)
          ·
            refine ⟨1597600854952798805879021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065067236635199203919347 1597600854952798805879021)
            ·
              refine ⟨599100320607299552204633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1597600854952798805879021 599100320607299552204633)
              ·
                refine ⟨449325240455474664153475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599100320607299552204633 449325240455474664153475)
                ·
                  refine ⟨673987860683211996230213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449325240455474664153475 673987860683211996230213)
                  ·
                    refine ⟨126372723878102249293165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 673987860683211996230213 126372723878102249293165)
                    ·
                      rfl

theorem cell22_369165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_369165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369165 prefixEnd_369165 := by exact prefixLift 369165
  have htrace : WordTrace (prefixWord ++ tailWord_369165) baseStart_369165 baseEnd_369165 := by
    simpa [prefixWord, tailWord_369165, baseEnd_369165] using wordTrace_append hprefix tailTrace_369165
  have hstable : (prefixWord ++ tailWord_369165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369165).length < 2 ^ (prefixWord ++ tailWord_369165).sum := by decide
  have hdescent : baseEnd_369165 < baseStart_369165 := by decide
  rcases family_descends (prefixWord ++ tailWord_369165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369176 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_369176 : Nat := 118140960795 + 369176 * 2 ^ 59
def prefixEnd_369176 : Nat := 4983230072969 + 3 ^ 40 * 369176 * 2
def baseEnd_369176 : Nat := 126376489402901887268131

theorem tailTrace_369176 : CollatzResearch.WordTrace tailWord_369176 prefixEnd_369176 126376489402901887268131 := by
  unfold tailWord_369176
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732477455272938543111691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8976636607030584724148921 6732477455272938543111691)
  ·
    refine ⟨10098716182909407814667537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6732477455272938543111691 10098716182909407814667537)
    ·
      refine ⟨7574037137182055861000653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10098716182909407814667537 7574037137182055861000653)
      ·
        refine ⟨2840263926443270947875245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7574037137182055861000653 2840263926443270947875245)
        ·
          refine ⟨1065098972416226605453217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2840263926443270947875245 1065098972416226605453217)
          ·
            refine ⟨798824229312169954089913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065098972416226605453217 798824229312169954089913)
            ·
              refine ⟨599118171984127465567435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798824229312169954089913 599118171984127465567435)
              ·
                refine ⟨898677257976191198351153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599118171984127465567435 898677257976191198351153)
                ·
                  refine ⟨674007943482143398763365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898677257976191198351153 674007943482143398763365)
                  ·
                    refine ⟨126376489402901887268131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674007943482143398763365 126376489402901887268131)
                    ·
                      rfl

theorem cell22_369176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_369176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369176 prefixEnd_369176 := by exact prefixLift 369176
  have htrace : WordTrace (prefixWord ++ tailWord_369176) baseStart_369176 baseEnd_369176 := by
    simpa [prefixWord, tailWord_369176, baseEnd_369176] using wordTrace_append hprefix tailTrace_369176
  have hstable : (prefixWord ++ tailWord_369176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369176).length < 2 ^ (prefixWord ++ tailWord_369176).sum := by decide
  have hdescent : baseEnd_369176 < baseStart_369176 := by decide
  rcases family_descends (prefixWord ++ tailWord_369176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369191 : List Nat := [1, 1, 7, 2, 1, 10]
def baseStart_369191 : Nat := 118140960795 + 369191 * 2 ^ 59
def prefixEnd_369191 : Nat := 4983230072969 + 3 ^ 40 * 369191 * 2
def baseEnd_369191 : Nat := 1560266965548726520285

theorem tailTrace_369191 : CollatzResearch.WordTrace tailWord_369191 prefixEnd_369191 1560266965548726520285 := by
  unfold tailWord_369191
  simp only [CollatzResearch.WordTrace]
  refine ⟨13465502005491534648019427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8977001336994356432012951 13465502005491534648019427)
  ·
    refine ⟨20198253008237301972029141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13465502005491534648019427 20198253008237301972029141)
    ·
      refine ⟨473396554880561764969433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20198253008237301972029141 473396554880561764969433)
      ·
        refine ⟨355047416160421323727075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473396554880561764969433 355047416160421323727075)
        ·
          refine ⟨532571124240631985590613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355047416160421323727075 532571124240631985590613)
          ·
            refine ⟨1560266965548726520285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 532571124240631985590613 1560266965548726520285)
            ·
              rfl

theorem cell22_369191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 10].length) (baseStart_369191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369191 prefixEnd_369191 := by exact prefixLift 369191
  have htrace : WordTrace (prefixWord ++ tailWord_369191) baseStart_369191 baseEnd_369191 := by
    simpa [prefixWord, tailWord_369191, baseEnd_369191] using wordTrace_append hprefix tailTrace_369191
  have hstable : (prefixWord ++ tailWord_369191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369191).length < 2 ^ (prefixWord ++ tailWord_369191).sum := by decide
  have hdescent : baseEnd_369191 < baseStart_369191 := by decide
  rcases family_descends (prefixWord ++ tailWord_369191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369197 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 4]
def baseStart_369197 : Nat := 118140960795 + 369197 * 2 ^ 59
def prefixEnd_369197 : Nat := 4983230072969 + 3 ^ 40 * 369197 * 2
def baseEnd_369197 : Nat := 42127892710688277497689

theorem tailTrace_369197 : CollatzResearch.WordTrace tailWord_369197 prefixEnd_369197 42127892710688277497689 := by
  unfold tailWord_369197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13465720843469797672737845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8977147228979865115158563 13465720843469797672737845)
  ·
    refine ⟨1262411329075293531819173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13465720843469797672737845 1262411329075293531819173)
    ·
      refine ⟨236702124201617537216095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1262411329075293531819173 236702124201617537216095)
      ·
        refine ⟨355053186302426305824143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236702124201617537216095 355053186302426305824143)
        ·
          refine ⟨532579779453639458736215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355053186302426305824143 532579779453639458736215)
          ·
            refine ⟨798869669180459188104323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532579779453639458736215 798869669180459188104323)
            ·
              refine ⟨1198304503770688782156485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798869669180459188104323 1198304503770688782156485)
              ·
                refine ⟨224682094457004146654341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1198304503770688782156485 224682094457004146654341)
                ·
                  refine ⟨42127892710688277497689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224682094457004146654341 42127892710688277497689)
                  ·
                    rfl

theorem cell22_369197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_369197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369197 prefixEnd_369197 := by exact prefixLift 369197
  have htrace : WordTrace (prefixWord ++ tailWord_369197) baseStart_369197 baseEnd_369197 := by
    simpa [prefixWord, tailWord_369197, baseEnd_369197] using wordTrace_append hprefix tailTrace_369197
  have hstable : (prefixWord ++ tailWord_369197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369197).length < 2 ^ (prefixWord ++ tailWord_369197).sum := by decide
  have hdescent : baseEnd_369197 < baseStart_369197 := by decide
  rcases family_descends (prefixWord ++ tailWord_369197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369234 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_369234 : Nat := 118140960795 + 369234 * 2 ^ 59
def prefixEnd_369234 : Nat := 4983230072969 + 3 ^ 40 * 369234 * 2
def baseEnd_369234 : Nat := 126396343988209069317953

theorem tailTrace_369234 : CollatzResearch.WordTrace tailWord_369234 prefixEnd_369234 126396343988209069317953 := by
  unfold tailWord_369234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366767586083938247958689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8978046896223835327889837 3366767586083938247958689)
  ·
    refine ⟨2525075689562953685969017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3366767586083938247958689 2525075689562953685969017)
    ·
      refine ⟨1893806767172215264476763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2525075689562953685969017 1893806767172215264476763)
      ·
        refine ⟨2840710150758322896715145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893806767172215264476763 2840710150758322896715145)
        ·
          refine ⟨2130532613068742172536359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2840710150758322896715145 2130532613068742172536359)
          ·
            refine ⟨3195798919603113258804539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130532613068742172536359 3195798919603113258804539)
            ·
              refine ⟨4793698379404669888206809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195798919603113258804539 4793698379404669888206809)
              ·
                refine ⟨3595273784553502416155107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4793698379404669888206809 3595273784553502416155107)
                ·
                  refine ⟨5392910676830253624232661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3595273784553502416155107 5392910676830253624232661)
                  ·
                    refine ⟨126396343988209069317953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5392910676830253624232661 126396343988209069317953)
                    ·
                      rfl

theorem cell22_369234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_369234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369234 prefixEnd_369234 := by exact prefixLift 369234
  have htrace : WordTrace (prefixWord ++ tailWord_369234) baseStart_369234 baseEnd_369234 := by
    simpa [prefixWord, tailWord_369234, baseEnd_369234] using wordTrace_append hprefix tailTrace_369234
  have hstable : (prefixWord ++ tailWord_369234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369234).length < 2 ^ (prefixWord ++ tailWord_369234).sum := by decide
  have hdescent : baseEnd_369234 < baseStart_369234 := by decide
  rcases family_descends (prefixWord ++ tailWord_369234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369246 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_369246 : Nat := 118140960795 + 369246 * 2 ^ 59
def prefixEnd_369246 : Nat := 4983230072969 + 3 ^ 40 * 369246 * 2
def baseEnd_369246 : Nat := 126400451833445038017917

theorem tailTrace_369246 : CollatzResearch.WordTrace tailWord_369246 prefixEnd_369246 126400451833445038017917 := by
  unfold tailWord_369246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683438502536534880158949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8978338680194852694181061 1683438502536534880158949)
  ·
    refine ⟨315644719225600290029803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1683438502536534880158949 315644719225600290029803)
    ·
      refine ⟨473467078838400435044705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315644719225600290029803 473467078838400435044705)
      ·
        refine ⟨355100309128800326283529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473467078838400435044705 355100309128800326283529)
        ·
          refine ⟨266325231846600244712647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355100309128800326283529 266325231846600244712647)
          ·
            refine ⟨399487847769900367068971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266325231846600244712647 399487847769900367068971)
            ·
              refine ⟨599231771654850550603457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399487847769900367068971 599231771654850550603457)
              ·
                refine ⟨449423828741137912952593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599231771654850550603457 449423828741137912952593)
                ·
                  refine ⟨337067871555853434714445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449423828741137912952593 337067871555853434714445)
                  ·
                    refine ⟨126400451833445038017917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337067871555853434714445 126400451833445038017917)
                    ·
                      rfl

theorem cell22_369246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_369246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369246 prefixEnd_369246 := by exact prefixLift 369246
  have htrace : WordTrace (prefixWord ++ tailWord_369246) baseStart_369246 baseEnd_369246 := by
    simpa [prefixWord, tailWord_369246, baseEnd_369246] using wordTrace_append hprefix tailTrace_369246
  have hstable : (prefixWord ++ tailWord_369246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369246).length < 2 ^ (prefixWord ++ tailWord_369246).sum := by decide
  have hdescent : baseEnd_369246 < baseStart_369246 := by decide
  rcases family_descends (prefixWord ++ tailWord_369246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369253 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 5]
def baseStart_369253 : Nat := 118140960795 + 369253 * 2 ^ 59
def prefixEnd_369253 : Nat := 4983230072969 + 3 ^ 40 * 369253 * 2
def baseEnd_369253 : Nat := 42134282692166451030965

theorem tailTrace_369253 : CollatzResearch.WordTrace tailWord_369253 prefixEnd_369253 42134282692166451030965 := by
  unfold tailWord_369253
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467763331266919236776413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8978508887511279491184275 13467763331266919236776413)
  ·
    refine ⟨5050411249225094713791155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13467763331266919236776413 5050411249225094713791155)
    ·
      refine ⟨7575616873837642070686733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050411249225094713791155 7575616873837642070686733)
      ·
        refine ⟨2840856327689115776507525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7575616873837642070686733 2840856327689115776507525)
        ·
          refine ⟨532660561441709208095161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2840856327689115776507525 532660561441709208095161)
          ·
            refine ⟨399495421081281906071371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532660561441709208095161 399495421081281906071371)
            ·
              refine ⟨599243131621922859107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399495421081281906071371 599243131621922859107057)
              ·
                refine ⟨449432348716442144330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599243131621922859107057 449432348716442144330293)
                ·
                  refine ⟨42134282692166451030965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449432348716442144330293 42134282692166451030965)
                  ·
                    rfl

theorem cell22_369253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_369253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369253 prefixEnd_369253 := by exact prefixLift 369253
  have htrace : WordTrace (prefixWord ++ tailWord_369253) baseStart_369253 baseEnd_369253 := by
    simpa [prefixWord, tailWord_369253, baseEnd_369253] using wordTrace_append hprefix tailTrace_369253
  have hstable : (prefixWord ++ tailWord_369253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369253).length < 2 ^ (prefixWord ++ tailWord_369253).sum := by decide
  have hdescent : baseEnd_369253 < baseStart_369253 := by decide
  rcases family_descends (prefixWord ++ tailWord_369253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369270 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_369270 : Nat := 118140960795 + 369270 * 2 ^ 59
def prefixEnd_369270 : Nat := 4983230072969 + 3 ^ 40 * 369270 * 2
def baseEnd_369270 : Nat := 42136222507972325139281

theorem tailTrace_369270 : CollatzResearch.WordTrace tailWord_369270 prefixEnd_369270 42136222507972325139281 := by
  unfold tailWord_369270
  simp only [CollatzResearch.WordTrace]
  refine ⟨841773960762833196259079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8978922248136887426763509 841773960762833196259079)
  ·
    refine ⟨1262660941144249794388619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841773960762833196259079 1262660941144249794388619)
    ·
      refine ⟨1893991411716374691582929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262660941144249794388619 1893991411716374691582929)
      ·
        refine ⟨1420493558787281018687197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1893991411716374691582929 1420493558787281018687197)
        ·
          refine ⟨532685084545230382007699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1420493558787281018687197 532685084545230382007699)
          ·
            refine ⟨799027626817845573011549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532685084545230382007699 799027626817845573011549)
            ·
              refine ⟨299635360056692089879331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799027626817845573011549 299635360056692089879331)
              ·
                refine ⟨449453040085038134818997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299635360056692089879331 449453040085038134818997)
                ·
                  refine ⟨42136222507972325139281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449453040085038134818997 42136222507972325139281)
                  ·
                    rfl

theorem cell22_369270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_369270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369270 prefixEnd_369270 := by exact prefixLift 369270
  have htrace : WordTrace (prefixWord ++ tailWord_369270) baseStart_369270 baseEnd_369270 := by
    simpa [prefixWord, tailWord_369270, baseEnd_369270] using wordTrace_append hprefix tailTrace_369270
  have hstable : (prefixWord ++ tailWord_369270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369270).length < 2 ^ (prefixWord ++ tailWord_369270).sum := by decide
  have hdescent : baseEnd_369270 < baseStart_369270 := by decide
  rcases family_descends (prefixWord ++ tailWord_369270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369279 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_369279 : Nat := 118140960795 + 369279 * 2 ^ 59
def prefixEnd_369279 : Nat := 4983230072969 + 3 ^ 40 * 369279 * 2
def baseEnd_369279 : Nat := 126411748407843951942815

theorem tailTrace_369279 : CollatzResearch.WordTrace tailWord_369279 prefixEnd_369279 126411748407843951942815 := by
  unfold tailWord_369279
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468711629172725677222891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8979141086115150451481927 13468711629172725677222891)
  ·
    refine ⟨20203067443759088515834337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13468711629172725677222891 20203067443759088515834337)
    ·
      refine ⟨15152300582819316386875753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20203067443759088515834337 15152300582819316386875753)
      ·
        refine ⟨11364225437114487290156815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15152300582819316386875753 11364225437114487290156815)
        ·
          refine ⟨17046338155671730935235223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11364225437114487290156815 17046338155671730935235223)
          ·
            refine ⟨25569507233507596402852835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17046338155671730935235223 25569507233507596402852835)
            ·
              refine ⟨38354260850261394604279253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25569507233507596402852835 38354260850261394604279253)
              ·
                refine ⟨898927988678001436037795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38354260850261394604279253 898927988678001436037795)
                ·
                  refine ⟨1348391983017002154056693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 898927988678001436037795 1348391983017002154056693)
                  ·
                    refine ⟨126411748407843951942815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1348391983017002154056693 126411748407843951942815)
                    ·
                      rfl

theorem cell22_369279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_369279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369279 prefixEnd_369279 := by exact prefixLift 369279
  have htrace : WordTrace (prefixWord ++ tailWord_369279) baseStart_369279 baseEnd_369279 := by
    simpa [prefixWord, tailWord_369279, baseEnd_369279] using wordTrace_append hprefix tailTrace_369279
  have hstable : (prefixWord ++ tailWord_369279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369279).length < 2 ^ (prefixWord ++ tailWord_369279).sum := by decide
  have hdescent : baseEnd_369279 < baseStart_369279 := by decide
  rcases family_descends (prefixWord ++ tailWord_369279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369309 : List Nat := [1, 4, 2, 1, 1, 1, 12]
def baseStart_369309 : Nat := 118140960795 + 369309 * 2 ^ 59
def prefixEnd_369309 : Nat := 4983230072969 + 3 ^ 40 * 369309 * 2
def baseEnd_369309 : Nat := 4682296963738291618249

theorem tailTrace_369309 : CollatzResearch.WordTrace tailWord_369309 prefixEnd_369309 4682296963738291618249 := by
  unfold tailWord_369309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13469805819064040800814981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8979870546042693867209987 13469805819064040800814981)
  ·
    refine ⟨2525588591074507650152809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13469805819064040800814981 2525588591074507650152809)
    ·
      refine ⟨1894191443305880737614607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2525588591074507650152809 1894191443305880737614607)
      ·
        refine ⟨2841287164958821106421911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894191443305880737614607 2841287164958821106421911)
        ·
          refine ⟨4261930747438231659632867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841287164958821106421911 4261930747438231659632867)
          ·
            refine ⟨6392896121157347489449301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261930747438231659632867 6392896121157347489449301)
            ·
              refine ⟨4682296963738291618249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 6392896121157347489449301 4682296963738291618249)
              ·
                rfl

theorem cell22_369309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 12].length) (baseStart_369309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369309 prefixEnd_369309 := by exact prefixLift 369309
  have htrace : WordTrace (prefixWord ++ tailWord_369309) baseStart_369309 baseEnd_369309 := by
    simpa [prefixWord, tailWord_369309, baseEnd_369309] using wordTrace_append hprefix tailTrace_369309
  have hstable : (prefixWord ++ tailWord_369309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369309).length < 2 ^ (prefixWord ++ tailWord_369309).sum := by decide
  have hdescent : baseEnd_369309 < baseStart_369309 := by decide
  rcases family_descends (prefixWord ++ tailWord_369309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369334 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_369334 : Nat := 118140960795 + 369334 * 2 ^ 59
def prefixEnd_369334 : Nat := 4983230072969 + 3 ^ 40 * 369334 * 2
def baseEnd_369334 : Nat := 126430576031842141817647

theorem tailTrace_369334 : CollatzResearch.WordTrace tailWord_369334 prefixEnd_369334 126430576031842141817647 := by
  unfold tailWord_369334
  simp only [CollatzResearch.WordTrace]
  refine ⟨841919852748341879404691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8980478429315646713650037 841919852748341879404691)
  ·
    refine ⟨1262879779122512819107037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841919852748341879404691 1262879779122512819107037)
    ·
      refine ⟨473579917170942307165139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1262879779122512819107037 473579917170942307165139)
      ·
        refine ⟨710369875756413460747709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473579917170942307165139 710369875756413460747709)
        ·
          refine ⟨266388703408655047780391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 710369875756413460747709 266388703408655047780391)
          ·
            refine ⟨399583055112982571670587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266388703408655047780391 399583055112982571670587)
            ·
              refine ⟨599374582669473857505881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399583055112982571670587 599374582669473857505881)
              ·
                refine ⟨449530937002105393129411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599374582669473857505881 449530937002105393129411)
                ·
                  refine ⟨674296405503158089694117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449530937002105393129411 674296405503158089694117)
                  ·
                    refine ⟨126430576031842141817647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674296405503158089694117 126430576031842141817647)
                    ·
                      rfl

theorem cell22_369334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_369334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369334 prefixEnd_369334 := by exact prefixLift 369334
  have htrace : WordTrace (prefixWord ++ tailWord_369334) baseStart_369334 baseEnd_369334 := by
    simpa [prefixWord, tailWord_369334, baseEnd_369334] using wordTrace_append hprefix tailTrace_369334
  have hstable : (prefixWord ++ tailWord_369334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369334).length < 2 ^ (prefixWord ++ tailWord_369334).sum := by decide
  have hdescent : baseEnd_369334 < baseStart_369334 := by decide
  rcases family_descends (prefixWord ++ tailWord_369334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369375 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 1, 3]
def baseStart_369375 : Nat := 118140960795 + 369375 * 2 ^ 59
def prefixEnd_369375 : Nat := 4983230072969 + 3 ^ 40 * 369375 * 2
def baseEnd_369375 : Nat := 126444611169731701542521

theorem tailTrace_369375 : CollatzResearch.WordTrace tailWord_369375 prefixEnd_369375 126444611169731701542521 := by
  unfold tailWord_369375
  simp only [CollatzResearch.WordTrace]
  refine ⟨13472213036824934072717579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8981475357883289381811719 13472213036824934072717579)
  ·
    refine ⟨20208319555237401109076369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13472213036824934072717579 20208319555237401109076369)
    ·
      refine ⟨15156239666428050831807277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20208319555237401109076369 15156239666428050831807277)
      ·
        refine ⟨5683589874910519061927729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15156239666428050831807277 5683589874910519061927729)
        ·
          refine ⟨4262692406182889296445797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5683589874910519061927729 4262692406182889296445797)
          ·
            refine ⟨799254826159291743083587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4262692406182889296445797 799254826159291743083587)
            ·
              refine ⟨1198882239238937614625381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799254826159291743083587 1198882239238937614625381)
              ·
                refine ⟨224790419857300802742259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1198882239238937614625381 224790419857300802742259)
                ·
                  refine ⟨337185629785951204113389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224790419857300802742259 337185629785951204113389)
                  ·
                    refine ⟨126444611169731701542521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337185629785951204113389 126444611169731701542521)
                    ·
                      rfl

theorem cell22_369375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_369375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369375 prefixEnd_369375 := by exact prefixLift 369375
  have htrace : WordTrace (prefixWord ++ tailWord_369375) baseStart_369375 baseEnd_369375 := by
    simpa [prefixWord, tailWord_369375, baseEnd_369375] using wordTrace_append hprefix tailTrace_369375
  have hstable : (prefixWord ++ tailWord_369375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369375).length < 2 ^ (prefixWord ++ tailWord_369375).sum := by decide
  have hdescent : baseEnd_369375 < baseStart_369375 := by decide
  rcases family_descends (prefixWord ++ tailWord_369375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369418 : List Nat := [3, 1, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_369418 : Nat := 118140960795 + 369418 * 2 ^ 59
def prefixEnd_369418 : Nat := 4983230072969 + 3 ^ 40 * 369418 * 2
def baseEnd_369418 : Nat := 126459330948493922717389

theorem tailTrace_369418 : CollatzResearch.WordTrace tailWord_369418 prefixEnd_369418 126459330948493922717389 := by
  unfold tailWord_369418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368445343917288104133227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8982520917112768277688605 3368445343917288104133227)
  ·
    refine ⟨5052668015875932156199841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368445343917288104133227 5052668015875932156199841)
    ·
      refine ⟨3789501011906949117149881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5052668015875932156199841 3789501011906949117149881)
      ·
        refine ⟨2842125758930211837862411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789501011906949117149881 2842125758930211837862411)
        ·
          refine ⟨4263188638395317756793617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842125758930211837862411 4263188638395317756793617)
          ·
            refine ⟨3197391478796488317595213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263188638395317756793617 3197391478796488317595213)
            ·
              refine ⟨1199021804548683119098205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3197391478796488317595213 1199021804548683119098205)
              ·
                refine ⟨449633176705756169661827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199021804548683119098205 449633176705756169661827)
                ·
                  refine ⟨674449765058634254492741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449633176705756169661827 674449765058634254492741)
                  ·
                    refine ⟨126459330948493922717389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674449765058634254492741 126459330948493922717389)
                    ·
                      rfl

theorem cell22_369418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_369418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369418 prefixEnd_369418 := by exact prefixLift 369418
  have htrace : WordTrace (prefixWord ++ tailWord_369418) baseStart_369418 baseEnd_369418 := by
    simpa [prefixWord, tailWord_369418, baseEnd_369418] using wordTrace_append hprefix tailTrace_369418
  have hstable : (prefixWord ++ tailWord_369418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369418).length < 2 ^ (prefixWord ++ tailWord_369418).sum := by decide
  have hdescent : baseEnd_369418 < baseStart_369418 := by decide
  rcases family_descends (prefixWord ++ tailWord_369418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369544 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 1, 3]
def baseStart_369544 : Nat := 118140960795 + 369544 * 2 ^ 59
def prefixEnd_369544 : Nat := 4983230072969 + 3 ^ 40 * 369544 * 2
def baseEnd_369544 : Nat := 126502463323471594067003

theorem tailTrace_369544 : CollatzResearch.WordTrace tailWord_369544 prefixEnd_369544 126502463323471594067003 := by
  unfold tailWord_369544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739188486606337967809843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8985584648808450623746457 6739188486606337967809843)
  ·
    refine ⟨10108782729909506951714765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6739188486606337967809843 10108782729909506951714765)
    ·
      refine ⟨3790793523716065106893037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10108782729909506951714765 3790793523716065106893037)
      ·
        refine ⟨1421547571393524415084889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3790793523716065106893037 1421547571393524415084889)
        ·
          refine ⟨1066160678545143311313667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421547571393524415084889 1066160678545143311313667)
          ·
            refine ⟨1599241017817714966970501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066160678545143311313667 1599241017817714966970501)
            ·
              refine ⟨299857690840821556306969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1599241017817714966970501 299857690840821556306969)
              ·
                refine ⟨224893268130616167230227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299857690840821556306969 224893268130616167230227)
                ·
                  refine ⟨337339902195924250845341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224893268130616167230227 337339902195924250845341)
                  ·
                    refine ⟨126502463323471594067003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337339902195924250845341 126502463323471594067003)
                    ·
                      rfl

theorem cell22_369544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_369544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369544 prefixEnd_369544 := by exact prefixLift 369544
  have htrace : WordTrace (prefixWord ++ tailWord_369544) baseStart_369544 baseEnd_369544 := by
    simpa [prefixWord, tailWord_369544, baseEnd_369544] using wordTrace_append hprefix tailTrace_369544
  have hstable : (prefixWord ++ tailWord_369544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369544).length < 2 ^ (prefixWord ++ tailWord_369544).sum := by decide
  have hdescent : baseEnd_369544 < baseStart_369544 := by decide
  rcases family_descends (prefixWord ++ tailWord_369544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369570 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_369570 : Nat := 118140960795 + 369570 * 2 ^ 59
def prefixEnd_369570 : Nat := 4983230072969 + 3 ^ 40 * 369570 * 2
def baseEnd_369570 : Nat := 126511363654816192916923

theorem tailTrace_369570 : CollatzResearch.WordTrace tailWord_369570 prefixEnd_369570 126511363654816192916923 := by
  unfold tailWord_369570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369831317779620594016541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8986216847412321584044109 3369831317779620594016541)
  ·
    refine ⟨1263686744167357722756203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3369831317779620594016541 1263686744167357722756203)
    ·
      refine ⟨1895530116251036584134305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263686744167357722756203 1895530116251036584134305)
      ·
        refine ⟨1421647587188277438100729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895530116251036584134305 1421647587188277438100729)
        ·
          refine ⟨1066235690391208078575547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421647587188277438100729 1066235690391208078575547)
          ·
            refine ⟨1599353535586812117863321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066235690391208078575547 1599353535586812117863321)
            ·
              refine ⟨1199515151690109088397491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599353535586812117863321 1199515151690109088397491)
              ·
                refine ⟨1799272727535163632596237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199515151690109088397491 1799272727535163632596237)
                ·
                  refine ⟨674727272825686362223589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1799272727535163632596237 674727272825686362223589)
                  ·
                    refine ⟨126511363654816192916923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674727272825686362223589 126511363654816192916923)
                    ·
                      rfl

theorem cell22_369570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_369570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369570 prefixEnd_369570 := by exact prefixLift 369570
  have htrace : WordTrace (prefixWord ++ tailWord_369570) baseStart_369570 baseEnd_369570 := by
    simpa [prefixWord, tailWord_369570, baseEnd_369570] using wordTrace_append hprefix tailTrace_369570
  have hstable : (prefixWord ++ tailWord_369570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369570).length < 2 ^ (prefixWord ++ tailWord_369570).sum := by decide
  have hdescent : baseEnd_369570 < baseStart_369570 := by decide
  rcases family_descends (prefixWord ++ tailWord_369570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369600 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_369600 : Nat := 118140960795 + 369600 * 2 ^ 59
def prefixEnd_369600 : Nat := 4983230072969 + 3 ^ 40 * 369600 * 2
def baseEnd_369600 : Nat := 126521633267906114666831

theorem tailTrace_369600 : CollatzResearch.WordTrace tailWord_369600 prefixEnd_369600 126521633267906114666831 := by
  unfold tailWord_369600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740209730504898749829127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8986946307339864999772169 6740209730504898749829127)
  ·
    refine ⟨10110314595757348124743691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6740209730504898749829127 10110314595757348124743691)
    ·
      refine ⟨15165471893636022187115537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10110314595757348124743691 15165471893636022187115537)
      ·
        refine ⟨11374103920227016640336653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15165471893636022187115537 11374103920227016640336653)
        ·
          refine ⟨4265288970085131240126245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11374103920227016640336653 4265288970085131240126245)
          ·
            refine ⟨799741681890962107523671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4265288970085131240126245 799741681890962107523671)
            ·
              refine ⟨1199612522836443161285507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799741681890962107523671 1199612522836443161285507)
              ·
                refine ⟨1799418784254664741928261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199612522836443161285507 1799418784254664741928261)
                ·
                  refine ⟨337391022047749639111549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799418784254664741928261 337391022047749639111549)
                  ·
                    refine ⟨126521633267906114666831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337391022047749639111549 126521633267906114666831)
                    ·
                      rfl

theorem cell22_369600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_369600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369600 prefixEnd_369600 := by exact prefixLift 369600
  have htrace : WordTrace (prefixWord ++ tailWord_369600) baseStart_369600 baseEnd_369600 := by
    simpa [prefixWord, tailWord_369600, baseEnd_369600] using wordTrace_append hprefix tailTrace_369600
  have hstable : (prefixWord ++ tailWord_369600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369600).length < 2 ^ (prefixWord ++ tailWord_369600).sum := by decide
  have hdescent : baseEnd_369600 < baseStart_369600 := by decide
  rcases family_descends (prefixWord ++ tailWord_369600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369617 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_369617 : Nat := 118140960795 + 369617 * 2 ^ 59
def prefixEnd_369617 : Nat := 4983230072969 + 3 ^ 40 * 369617 * 2
def baseEnd_369617 : Nat := 126527452715323736991779

theorem tailTrace_369617 : CollatzResearch.WordTrace tailWord_369617 prefixEnd_369617 126527452715323736991779 := by
  unfold tailWord_369617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481039501948209403027105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8987359667965472935351403 13481039501948209403027105)
  ·
    refine ⟨10110779626461157052270329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13481039501948209403027105 10110779626461157052270329)
    ·
      refine ⟨7583084719845867789202747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10110779626461157052270329 7583084719845867789202747)
      ·
        refine ⟨11374627079768801683804121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583084719845867789202747 11374627079768801683804121)
        ·
          refine ⟨8530970309826601262853091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11374627079768801683804121 8530970309826601262853091)
          ·
            refine ⟨12796455464739901894279637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530970309826601262853091 12796455464739901894279637)
            ·
              refine ⟨299916924954841450647179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12796455464739901894279637 299916924954841450647179)
              ·
                refine ⟨449875387432262175970769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299916924954841450647179 449875387432262175970769)
                ·
                  refine ⟨337406540574196631978077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449875387432262175970769 337406540574196631978077)
                  ·
                    refine ⟨126527452715323736991779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337406540574196631978077 126527452715323736991779)
                    ·
                      rfl

theorem cell22_369617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_369617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369617 prefixEnd_369617 := by exact prefixLift 369617
  have htrace : WordTrace (prefixWord ++ tailWord_369617) baseStart_369617 baseEnd_369617 := by
    simpa [prefixWord, tailWord_369617, baseEnd_369617] using wordTrace_append hprefix tailTrace_369617
  have hstable : (prefixWord ++ tailWord_369617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369617).length < 2 ^ (prefixWord ++ tailWord_369617).sum := by decide
  have hdescent : baseEnd_369617 < baseStart_369617 := by decide
  rcases family_descends (prefixWord ++ tailWord_369617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369673 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_369673 : Nat := 118140960795 + 369673 * 2 ^ 59
def prefixEnd_369673 : Nat := 4983230072969 + 3 ^ 40 * 369673 * 2
def baseEnd_369673 : Nat := 126546622659758257591607

theorem tailTrace_369673 : CollatzResearch.WordTrace tailWord_369673 prefixEnd_369673 126546622659758257591607 := by
  unfold tailWord_369673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13483081989745330967065673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8988721326496887311377115 13483081989745330967065673)
  ·
    refine ⟨10112311492308998225299255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13483081989745330967065673 10112311492308998225299255)
    ·
      refine ⟨15168467238463497337948883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10112311492308998225299255 15168467238463497337948883)
      ·
        refine ⟨22752700857695246006923325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15168467238463497337948883 22752700857695246006923325)
        ·
          refine ⟨8532262821635717252596247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22752700857695246006923325 8532262821635717252596247)
          ·
            refine ⟨12798394232453575878894371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8532262821635717252596247 12798394232453575878894371)
            ·
              refine ⟨19197591348680363818341557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798394232453575878894371 19197591348680363818341557)
              ·
                refine ⟨1799774188938784107969521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19197591348680363818341557 1799774188938784107969521)
                ·
                  refine ⟨1349830641704088080977141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1799774188938784107969521 1349830641704088080977141)
                  ·
                    refine ⟨126546622659758257591607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1349830641704088080977141 126546622659758257591607)
                    ·
                      rfl

theorem cell22_369673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_369673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369673 prefixEnd_369673 := by exact prefixLift 369673
  have htrace : WordTrace (prefixWord ++ tailWord_369673) baseStart_369673 baseEnd_369673 := by
    simpa [prefixWord, tailWord_369673, baseEnd_369673] using wordTrace_append hprefix tailTrace_369673
  have hstable : (prefixWord ++ tailWord_369673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369673).length < 2 ^ (prefixWord ++ tailWord_369673).sum := by decide
  have hdescent : baseEnd_369673 < baseStart_369673 := by decide
  rcases family_descends (prefixWord ++ tailWord_369673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369675 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 5]
def baseStart_369675 : Nat := 118140960795 + 369675 * 2 ^ 59
def prefixEnd_369675 : Nat := 4983230072969 + 3 ^ 40 * 369675 * 2
def baseEnd_369675 : Nat := 42182435766876973013867

theorem tailTrace_369675 : CollatzResearch.WordTrace tailWord_369675 prefixEnd_369675 42182435766876973013867 := by
  unfold tailWord_369675
  simp only [CollatzResearch.WordTrace]
  refine ⟨13483154935738085308638479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8988769957158723539092319 13483154935738085308638479)
  ·
    refine ⟨20224732403607127962957719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13483154935738085308638479 20224732403607127962957719)
    ·
      refine ⟨30337098605410691944436579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20224732403607127962957719 30337098605410691944436579)
      ·
        refine ⟨45505647908116037916654869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30337098605410691944436579 45505647908116037916654869)
        ·
          refine ⟨2133077245692939277343197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45505647908116037916654869 2133077245692939277343197)
          ·
            refine ⟨799903967134852229003699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2133077245692939277343197 799903967134852229003699)
            ·
              refine ⟨1199855950702278343505549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799903967134852229003699 1199855950702278343505549)
              ·
                refine ⟨449945981513354378814581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199855950702278343505549 449945981513354378814581)
                ·
                  refine ⟨42182435766876973013867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 449945981513354378814581 42182435766876973013867)
                  ·
                    rfl

theorem cell22_369675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 5].length) (baseStart_369675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369675 prefixEnd_369675 := by exact prefixLift 369675
  have htrace : WordTrace (prefixWord ++ tailWord_369675) baseStart_369675 baseEnd_369675 := by
    simpa [prefixWord, tailWord_369675, baseEnd_369675] using wordTrace_append hprefix tailTrace_369675
  have hstable : (prefixWord ++ tailWord_369675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369675).length < 2 ^ (prefixWord ++ tailWord_369675).sum := by decide
  have hdescent : baseEnd_369675 < baseStart_369675 := by decide
  rcases family_descends (prefixWord ++ tailWord_369675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369735 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_369735 : Nat := 118140960795 + 369735 * 2 ^ 59
def prefixEnd_369735 : Nat := 4983230072969 + 3 ^ 40 * 369735 * 2
def baseEnd_369735 : Nat := 126567846526810762541417

theorem tailTrace_369735 : CollatzResearch.WordTrace tailWord_369735 prefixEnd_369735 126567846526810762541417 := by
  unfold tailWord_369735
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485343315520715555822659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8990228877013810370548439 13485343315520715555822659)
  ·
    refine ⟨20228014973281073333733989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13485343315520715555822659 20228014973281073333733989)
    ·
      refine ⟨3792752807490201250075123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20228014973281073333733989 3792752807490201250075123)
      ·
        refine ⟨5689129211235301875112685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792752807490201250075123 5689129211235301875112685)
        ·
          refine ⟨2133423454213238203167257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5689129211235301875112685 2133423454213238203167257)
          ·
            refine ⟨1600067590659928652375443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2133423454213238203167257 1600067590659928652375443)
            ·
              refine ⟨2400101385989892978563165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600067590659928652375443 2400101385989892978563165)
              ·
                refine ⟨900038019746209866961187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2400101385989892978563165 900038019746209866961187)
                ·
                  refine ⟨1350057029619314800441781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900038019746209866961187 1350057029619314800441781)
                  ·
                    refine ⟨126567846526810762541417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1350057029619314800441781 126567846526810762541417)
                    ·
                      rfl

theorem cell22_369735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_369735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369735 prefixEnd_369735 := by exact prefixLift 369735
  have htrace : WordTrace (prefixWord ++ tailWord_369735) baseStart_369735 baseEnd_369735 := by
    simpa [prefixWord, tailWord_369735, baseEnd_369735] using wordTrace_append hprefix tailTrace_369735
  have hstable : (prefixWord ++ tailWord_369735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369735).length < 2 ^ (prefixWord ++ tailWord_369735).sum := by decide
  have hdescent : baseEnd_369735 < baseStart_369735 := by decide
  rcases family_descends (prefixWord ++ tailWord_369735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369769 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 2, 3]
def baseStart_369769 : Nat := 118140960795 + 369769 * 2 ^ 59
def prefixEnd_369769 : Nat := 4983230072969 + 3 ^ 40 * 369769 * 2
def baseEnd_369769 : Nat := 126579485421646007191313

theorem tailTrace_369769 : CollatzResearch.WordTrace tailWord_369769 prefixEnd_369769 126579485421646007191313 := by
  unfold tailWord_369769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486583397397539362560361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8991055598265026241706907 13486583397397539362560361)
  ·
    refine ⟨10114937548048154521920271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13486583397397539362560361 10114937548048154521920271)
    ·
      refine ⟨15172406322072231782880407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114937548048154521920271 15172406322072231782880407)
      ·
        refine ⟨22758609483108347674320611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15172406322072231782880407 22758609483108347674320611)
        ·
          refine ⟨34137914224662521511480917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22758609483108347674320611 34137914224662521511480917)
          ·
            refine ⟨400053682320263923962667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 34137914224662521511480917 400053682320263923962667)
            ·
              refine ⟨600080523480395885944001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400053682320263923962667 600080523480395885944001)
              ·
                refine ⟨450060392610296914458001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600080523480395885944001 450060392610296914458001)
                ·
                  refine ⟨337545294457722685843501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450060392610296914458001 337545294457722685843501)
                  ·
                    refine ⟨126579485421646007191313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337545294457722685843501 126579485421646007191313)
                    ·
                      rfl

theorem cell22_369769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_369769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369769 prefixEnd_369769 := by exact prefixLift 369769
  have htrace : WordTrace (prefixWord ++ tailWord_369769) baseStart_369769 baseEnd_369769 := by
    simpa [prefixWord, tailWord_369769, baseEnd_369769] using wordTrace_append hprefix tailTrace_369769
  have hstable : (prefixWord ++ tailWord_369769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369769).length < 2 ^ (prefixWord ++ tailWord_369769).sum := by decide
  have hdescent : baseEnd_369769 < baseStart_369769 := by decide
  rcases family_descends (prefixWord ++ tailWord_369769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369831 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 3, 3]
def baseStart_369831 : Nat := 118140960795 + 369831 * 2 ^ 59
def prefixEnd_369831 : Nat := 4983230072969 + 3 ^ 40 * 369831 * 2
def baseEnd_369831 : Nat := 126600709288698512141123

theorem tailTrace_369831 : CollatzResearch.WordTrace tailWord_369831 prefixEnd_369831 126600709288698512141123 := by
  unfold tailWord_369831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488844723172923951317347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8992563148781949300878231 13488844723172923951317347)
  ·
    refine ⟨20233267084759385926976021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13488844723172923951317347 20233267084759385926976021)
    ·
      refine ⟨948434394598096215327001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20233267084759385926976021 948434394598096215327001)
      ·
        refine ⟨711325795948572161495251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948434394598096215327001 711325795948572161495251)
        ·
          refine ⟨1066988693922858242242877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711325795948572161495251 1066988693922858242242877)
          ·
            refine ⟨400120760221071840841079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1066988693922858242242877 400120760221071840841079)
            ·
              refine ⟨600181140331607761261619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400120760221071840841079 600181140331607761261619)
              ·
                refine ⟨900271710497411641892429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600181140331607761261619 900271710497411641892429)
                ·
                  refine ⟨337601891436529365709661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900271710497411641892429 337601891436529365709661)
                  ·
                    refine ⟨126600709288698512141123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337601891436529365709661 126600709288698512141123)
                    ·
                      rfl

theorem cell22_369831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_369831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369831 prefixEnd_369831 := by exact prefixLift 369831
  have htrace : WordTrace (prefixWord ++ tailWord_369831) baseStart_369831 baseEnd_369831 := by
    simpa [prefixWord, tailWord_369831, baseEnd_369831] using wordTrace_append hprefix tailTrace_369831
  have hstable : (prefixWord ++ tailWord_369831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369831).length < 2 ^ (prefixWord ++ tailWord_369831).sum := by decide
  have hdescent : baseEnd_369831 < baseStart_369831 := by decide
  rcases family_descends (prefixWord ++ tailWord_369831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369840 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_369840 : Nat := 118140960795 + 369840 * 2 ^ 59
def prefixEnd_369840 : Nat := 4983230072969 + 3 ^ 40 * 369840 * 2
def baseEnd_369840 : Nat := 126603790172625488666095

theorem tailTrace_369840 : CollatzResearch.WordTrace tailWord_369840 prefixEnd_369840 126603790172625488666095 := by
  unfold tailWord_369840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744586490070159244197487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8992781986760212325596649 6744586490070159244197487)
  ·
    refine ⟨10116879735105238866296231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744586490070159244197487 10116879735105238866296231)
    ·
      refine ⟨15175319602657858299444347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116879735105238866296231 15175319602657858299444347)
      ·
        refine ⟨22762979403986787449166521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15175319602657858299444347 22762979403986787449166521)
        ·
          refine ⟨17072234552990090586874891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22762979403986787449166521 17072234552990090586874891)
          ·
            refine ⟨25608351829485135880312337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17072234552990090586874891 25608351829485135880312337)
            ·
              refine ⟨19206263872113851910234253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25608351829485135880312337 19206263872113851910234253)
              ·
                refine ⟨7202348952042694466337845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19206263872113851910234253 7202348952042694466337845)
                ·
                  refine ⟨675220214254002606219173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7202348952042694466337845 675220214254002606219173)
                  ·
                    refine ⟨126603790172625488666095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675220214254002606219173 126603790172625488666095)
                    ·
                      rfl

theorem cell22_369840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_369840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369840 prefixEnd_369840 := by exact prefixLift 369840
  have htrace : WordTrace (prefixWord ++ tailWord_369840) baseStart_369840 baseEnd_369840 := by
    simpa [prefixWord, tailWord_369840, baseEnd_369840] using wordTrace_append hprefix tailTrace_369840
  have hstable : (prefixWord ++ tailWord_369840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369840).length < 2 ^ (prefixWord ++ tailWord_369840).sum := by decide
  have hdescent : baseEnd_369840 < baseStart_369840 := by decide
  rcases family_descends (prefixWord ++ tailWord_369840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369855 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 6]
def baseStart_369855 : Nat := 118140960795 + 369855 * 2 ^ 59
def prefixEnd_369855 : Nat := 4983230072969 + 3 ^ 40 * 369855 * 2
def baseEnd_369855 : Nat := 42202974993056816513683

theorem tailTrace_369855 : CollatzResearch.WordTrace tailWord_369855 prefixEnd_369855 42202974993056816513683 := by
  unfold tailWord_369855
  simp only [CollatzResearch.WordTrace]
  refine ⟨13489720075085976050191019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8993146716723984033460679 13489720075085976050191019)
  ·
    refine ⟨20234580112628964075286529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13489720075085976050191019 20234580112628964075286529)
    ·
      refine ⟨15175935084471723056464897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20234580112628964075286529 15175935084471723056464897)
      ·
        refine ⟨11381951313353792292348673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15175935084471723056464897 11381951313353792292348673)
        ·
          refine ⟨8536463485015344219261505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11381951313353792292348673 8536463485015344219261505)
          ·
            refine ⟨6402347613761508164446129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536463485015344219261505 6402347613761508164446129)
            ·
              refine ⟨4801760710321131123334597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402347613761508164446129 4801760710321131123334597)
              ·
                refine ⟨900330133185212085625237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4801760710321131123334597 900330133185212085625237)
                ·
                  refine ⟨42202974993056816513683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 900330133185212085625237 42202974993056816513683)
                  ·
                    rfl

theorem cell22_369855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_369855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369855 prefixEnd_369855 := by exact prefixLift 369855
  have htrace : WordTrace (prefixWord ++ tailWord_369855) baseStart_369855 baseEnd_369855 := by
    simpa [prefixWord, tailWord_369855, baseEnd_369855] using wordTrace_append hprefix tailTrace_369855
  have hstable : (prefixWord ++ tailWord_369855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369855).length < 2 ^ (prefixWord ++ tailWord_369855).sum := by decide
  have hdescent : baseEnd_369855 < baseStart_369855 := by decide
  rcases family_descends (prefixWord ++ tailWord_369855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369887 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 4, 3]
def baseStart_369887 : Nat := 118140960795 + 369887 * 2 ^ 59
def prefixEnd_369887 : Nat := 4983230072969 + 3 ^ 40 * 369887 * 2
def baseEnd_369887 : Nat := 126619879233133032740951

theorem tailTrace_369887 : CollatzResearch.WordTrace tailWord_369887 prefixEnd_369887 126619879233133032740951 := by
  unfold tailWord_369887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13490887210970045515355915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8993924807313363676903943 13490887210970045515355915)
  ·
    refine ⟨20236330816455068273033873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13490887210970045515355915 20236330816455068273033873)
    ·
      refine ⟨15177248112341301204775405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20236330816455068273033873 15177248112341301204775405)
      ·
        refine ⟨5691468042127987951790777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15177248112341301204775405 5691468042127987951790777)
        ·
          refine ⟨4268601031595990963843083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691468042127987951790777 4268601031595990963843083)
          ·
            refine ⟨6402901547393986445764625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268601031595990963843083 6402901547393986445764625)
            ·
              refine ⟨4802176160545489834323469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6402901547393986445764625 4802176160545489834323469)
              ·
                refine ⟨1800816060204558687871301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4802176160545489834323469 1800816060204558687871301)
                ·
                  refine ⟨337653011288354753975869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800816060204558687871301 337653011288354753975869)
                  ·
                    refine ⟨126619879233133032740951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337653011288354753975869 126619879233133032740951)
                    ·
                      rfl

theorem cell22_369887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_369887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369887 prefixEnd_369887 := by exact prefixLift 369887
  have htrace : WordTrace (prefixWord ++ tailWord_369887) baseStart_369887 baseEnd_369887 := by
    simpa [prefixWord, tailWord_369887, baseEnd_369887] using wordTrace_append hprefix tailTrace_369887
  have hstable : (prefixWord ++ tailWord_369887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369887).length < 2 ^ (prefixWord ++ tailWord_369887).sum := by decide
  have hdescent : baseEnd_369887 < baseStart_369887 := by decide
  rcases family_descends (prefixWord ++ tailWord_369887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369889 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 4]
def baseStart_369889 : Nat := 118140960795 + 369889 * 2 ^ 59
def prefixEnd_369889 : Nat := 4983230072969 + 3 ^ 40 * 369889 * 2
def baseEnd_369889 : Nat := 42206854624668564730315

theorem tailTrace_369889 : CollatzResearch.WordTrace tailWord_369889 prefixEnd_369889 42206854624668564730315 := by
  unfold tailWord_369889
  simp only [CollatzResearch.WordTrace]
  refine ⟨13490960156962799856928721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8993973437975199904619147 13490960156962799856928721)
  ·
    refine ⟨10118220117722099892696541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13490960156962799856928721 10118220117722099892696541)
    ·
      refine ⟨3794332544145787459761203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10118220117722099892696541 3794332544145787459761203)
      ·
        refine ⟨5691498816218681189641805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794332544145787459761203 5691498816218681189641805)
        ·
          refine ⟨2134312056082005446115677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5691498816218681189641805 2134312056082005446115677)
          ·
            refine ⟨800367021030752042293379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2134312056082005446115677 800367021030752042293379)
            ·
              refine ⟨1200550531546128063440069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800367021030752042293379 1200550531546128063440069)
              ·
                refine ⟨225103224664899011895013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1200550531546128063440069 225103224664899011895013)
                ·
                  refine ⟨42206854624668564730315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225103224664899011895013 42206854624668564730315)
                  ·
                    rfl

theorem cell22_369889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 4].length) (baseStart_369889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369889 prefixEnd_369889 := by exact prefixLift 369889
  have htrace : WordTrace (prefixWord ++ tailWord_369889) baseStart_369889 baseEnd_369889 := by
    simpa [prefixWord, tailWord_369889, baseEnd_369889] using wordTrace_append hprefix tailTrace_369889
  have hstable : (prefixWord ++ tailWord_369889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369889).length < 2 ^ (prefixWord ++ tailWord_369889).sum := by decide
  have hdescent : baseEnd_369889 < baseStart_369889 := by decide
  rcases family_descends (prefixWord ++ tailWord_369889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369902 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_369902 : Nat := 118140960795 + 369902 * 2 ^ 59
def prefixEnd_369902 : Nat := 4983230072969 + 3 ^ 40 * 369902 * 2
def baseEnd_369902 : Nat := 126625014039677993615905

theorem tailTrace_369902 : CollatzResearch.WordTrace tailWord_369902 prefixEnd_369902 126625014039677993615905 := by
  unfold tailWord_369902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686429288239462884643995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8994289537277135384767973 1686429288239462884643995)
  ·
    refine ⟨2529643932359194326965993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686429288239462884643995 2529643932359194326965993)
    ·
      refine ⟨1897232949269395745224495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529643932359194326965993 1897232949269395745224495)
      ·
        refine ⟨2845849423904093617836743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897232949269395745224495 2845849423904093617836743)
        ·
          refine ⟨4268774135856140426755115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845849423904093617836743 4268774135856140426755115)
          ·
            refine ⟨6403161203784210640132673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268774135856140426755115 6403161203784210640132673)
            ·
              refine ⟨4802370902838157980099505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6403161203784210640132673 4802370902838157980099505)
              ·
                refine ⟨3601778177128618485074629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4802370902838157980099505 3601778177128618485074629)
                ·
                  refine ⟨675333408211615965951493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3601778177128618485074629 675333408211615965951493)
                  ·
                    refine ⟨126625014039677993615905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675333408211615965951493 126625014039677993615905)
                    ·
                      rfl

theorem cell22_369902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_369902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369902 prefixEnd_369902 := by exact prefixLift 369902
  have htrace : WordTrace (prefixWord ++ tailWord_369902) baseStart_369902 baseEnd_369902 := by
    simpa [prefixWord, tailWord_369902, baseEnd_369902] using wordTrace_append hprefix tailTrace_369902
  have hstable : (prefixWord ++ tailWord_369902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369902).length < 2 ^ (prefixWord ++ tailWord_369902).sum := by decide
  have hdescent : baseEnd_369902 < baseStart_369902 := by decide
  rcases family_descends (prefixWord ++ tailWord_369902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369919 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 2, 4]
def baseStart_369919 : Nat := 118140960795 + 369919 * 2 ^ 59
def prefixEnd_369919 : Nat := 4983230072969 + 3 ^ 40 * 369919 * 2
def baseEnd_369919 : Nat := 126630833487095615940853

theorem tailTrace_369919 : CollatzResearch.WordTrace tailWord_369919 prefixEnd_369919 126630833487095615940853 := by
  unfold tailWord_369919
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492054346854114980520811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8994702897902743320347207 13492054346854114980520811)
  ·
    refine ⟨20238081520281172470781217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492054346854114980520811 20238081520281172470781217)
    ·
      refine ⟨15178561140210879353085913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20238081520281172470781217 15178561140210879353085913)
      ·
        refine ⟨11383920855158159514814435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15178561140210879353085913 11383920855158159514814435)
        ·
          refine ⟨17075881282737239272221653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11383920855158159514814435 17075881282737239272221653)
          ·
            refine ⟨400215967564154045442695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17075881282737239272221653 400215967564154045442695)
            ·
              refine ⟨600323951346231068164043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400215967564154045442695 600323951346231068164043)
              ·
                refine ⟨900485927019346602246065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600323951346231068164043 900485927019346602246065)
                ·
                  refine ⟨675364445264509951684549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900485927019346602246065 675364445264509951684549)
                  ·
                    refine ⟨126630833487095615940853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675364445264509951684549 126630833487095615940853)
                    ·
                      rfl

theorem cell22_369919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_369919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369919 prefixEnd_369919 := by exact prefixLift 369919
  have htrace : WordTrace (prefixWord ++ tailWord_369919) baseStart_369919 baseEnd_369919 := by
    simpa [prefixWord, tailWord_369919, baseEnd_369919] using wordTrace_append hprefix tailTrace_369919
  have hstable : (prefixWord ++ tailWord_369919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369919).length < 2 ^ (prefixWord ++ tailWord_369919).sum := by decide
  have hdescent : baseEnd_369919 < baseStart_369919 := by decide
  rcases family_descends (prefixWord ++ tailWord_369919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369938 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_369938 : Nat := 118140960795 + 369938 * 2 ^ 59
def prefixEnd_369938 : Nat := 4983230072969 + 3 ^ 40 * 369938 * 2
def baseEnd_369938 : Nat := 126637337575385899715795

theorem tailTrace_369938 : CollatzResearch.WordTrace tailWord_369938 prefixEnd_369938 126637337575385899715795 := by
  unfold tailWord_369938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373186833446320306365617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8995164889190187483641645 3373186833446320306365617)
  ·
    refine ⟨2529890125084740229774213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3373186833446320306365617 2529890125084740229774213)
    ·
      refine ⟨474354398453388793082665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2529890125084740229774213 474354398453388793082665)
      ·
        refine ⟨355765798840041594811999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474354398453388793082665 355765798840041594811999)
        ·
          refine ⟨533648698260062392217999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355765798840041594811999 533648698260062392217999)
          ·
            refine ⟨800473047390093588326999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533648698260062392217999 800473047390093588326999)
            ·
              refine ⟨1200709571085140382490499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800473047390093588326999 1200709571085140382490499)
              ·
                refine ⟨1801064356627710573735749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200709571085140382490499 1801064356627710573735749)
                ·
                  refine ⟨337699566867695732575453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1801064356627710573735749 337699566867695732575453)
                  ·
                    refine ⟨126637337575385899715795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337699566867695732575453 126637337575385899715795)
                    ·
                      rfl

theorem cell22_369938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_369938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369938 prefixEnd_369938 := by exact prefixLift 369938
  have htrace : WordTrace (prefixWord ++ tailWord_369938) baseStart_369938 baseEnd_369938 := by
    simpa [prefixWord, tailWord_369938, baseEnd_369938] using wordTrace_append hprefix tailTrace_369938
  have hstable : (prefixWord ++ tailWord_369938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369938).length < 2 ^ (prefixWord ++ tailWord_369938).sum := by decide
  have hdescent : baseEnd_369938 < baseStart_369938 := by decide
  rcases family_descends (prefixWord ++ tailWord_369938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369983 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 1, 3]
def baseStart_369983 : Nat := 118140960795 + 369983 * 2 ^ 59
def prefixEnd_369983 : Nat := 4983230072969 + 3 ^ 40 * 369983 * 2
def baseEnd_369983 : Nat := 126652741995020782340657

theorem tailTrace_369983 : CollatzResearch.WordTrace tailWord_369983 prefixEnd_369983 126652741995020782340657 := by
  unfold tailWord_369983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494388618622253910850603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8996259079081502607233735 13494388618622253910850603)
  ·
    refine ⟨20241582927933380866275905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13494388618622253910850603 20241582927933380866275905)
    ·
      refine ⟨15181187195950035649706929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20241582927933380866275905 15181187195950035649706929)
      ·
        refine ⟨11385890396962526737280197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15181187195950035649706929 11385890396962526737280197)
        ·
          refine ⟨2134854449430473763240037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11385890396962526737280197 2134854449430473763240037)
          ·
            refine ⟨400285209268213830607507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2134854449430473763240037 400285209268213830607507)
            ·
              refine ⟨600427813902320745911261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400285209268213830607507 600427813902320745911261)
              ·
                refine ⟨225160430213370279716723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600427813902320745911261 225160430213370279716723)
                ·
                  refine ⟨337740645320055419575085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225160430213370279716723 337740645320055419575085)
                  ·
                    refine ⟨126652741995020782340657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337740645320055419575085 126652741995020782340657)
                    ·
                      rfl

theorem cell22_369983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_369983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369983 prefixEnd_369983 := by exact prefixLift 369983
  have htrace : WordTrace (prefixWord ++ tailWord_369983) baseStart_369983 baseEnd_369983 := by
    simpa [prefixWord, tailWord_369983, baseEnd_369983] using wordTrace_append hprefix tailTrace_369983
  have hstable : (prefixWord ++ tailWord_369983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369983).length < 2 ^ (prefixWord ++ tailWord_369983).sum := by decide
  have hdescent : baseEnd_369983 < baseStart_369983 := by decide
  rcases family_descends (prefixWord ++ tailWord_369983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369992 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_369992 : Nat := 118140960795 + 369992 * 2 ^ 59
def prefixEnd_369992 : Nat := 4983230072969 + 3 ^ 40 * 369992 * 2
def baseEnd_369992 : Nat := 126655822878947758865629

theorem tailTrace_369992 : CollatzResearch.WordTrace tailWord_369992 prefixEnd_369992 126655822878947758865629 := by
  unfold tailWord_369992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747358437794824223964115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8996477917059765631952153 6747358437794824223964115)
  ·
    refine ⟨10121037656692236335946173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6747358437794824223964115 10121037656692236335946173)
    ·
      refine ⟨3795389121259588625979815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10121037656692236335946173 3795389121259588625979815)
      ·
        refine ⟨5693083681889382938969723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795389121259588625979815 5693083681889382938969723)
        ·
          refine ⟨8539625522834074408454585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693083681889382938969723 8539625522834074408454585)
          ·
            refine ⟨6404719142125555806340939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8539625522834074408454585 6404719142125555806340939)
            ·
              refine ⟨9607078713188333709511409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404719142125555806340939 9607078713188333709511409)
              ·
                refine ⟨7205309034891250282133557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9607078713188333709511409 7205309034891250282133557)
                ·
                  refine ⟨675497722021054713950021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7205309034891250282133557 675497722021054713950021)
                  ·
                    refine ⟨126655822878947758865629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675497722021054713950021 126655822878947758865629)
                    ·
                      rfl

theorem cell22_369992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_369992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_369992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_369992 prefixEnd_369992 := by exact prefixLift 369992
  have htrace : WordTrace (prefixWord ++ tailWord_369992) baseStart_369992 baseEnd_369992 := by
    simpa [prefixWord, tailWord_369992, baseEnd_369992] using wordTrace_append hprefix tailTrace_369992
  have hstable : (prefixWord ++ tailWord_369992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369992).length < 2 ^ (prefixWord ++ tailWord_369992).sum := by decide
  have hdescent : baseEnd_369992 < baseStart_369992 := by decide
  rcases family_descends (prefixWord ++ tailWord_369992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370006 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_370006 : Nat := 118140960795 + 370006 * 2 ^ 59
def prefixEnd_370006 : Nat := 4983230072969 + 3 ^ 40 * 370006 * 2
def baseEnd_370006 : Nat := 126660615365056389015587

theorem tailTrace_370006 : CollatzResearch.WordTrace tailWord_370006 prefixEnd_370006 126660615365056389015587 := by
  unfold tailWord_370006
  simp only [CollatzResearch.WordTrace]
  refine ⟨843451718596183052433617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8996818331692619225958581 843451718596183052433617)
  ·
    refine ⟨632588788947137289325213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 843451718596183052433617 632588788947137289325213)
    ·
      refine ⟨237220795855176483496955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 632588788947137289325213 237220795855176483496955)
      ·
        refine ⟨355831193782764725245433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237220795855176483496955 355831193782764725245433)
        ·
          refine ⟨266873395337073543934075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355831193782764725245433 266873395337073543934075)
          ·
            refine ⟨400310093005610315901113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266873395337073543934075 400310093005610315901113)
            ·
              refine ⟨300232569754207736925835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400310093005610315901113 300232569754207736925835)
              ·
                refine ⟨450348854631311605388753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300232569754207736925835 450348854631311605388753)
                ·
                  refine ⟨337761640973483704041565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450348854631311605388753 337761640973483704041565)
                  ·
                    refine ⟨126660615365056389015587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337761640973483704041565 126660615365056389015587)
                    ·
                      rfl

theorem cell22_370006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_370006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370006 prefixEnd_370006 := by exact prefixLift 370006
  have htrace : WordTrace (prefixWord ++ tailWord_370006) baseStart_370006 baseEnd_370006 := by
    simpa [prefixWord, tailWord_370006, baseEnd_370006] using wordTrace_append hprefix tailTrace_370006
  have hstable : (prefixWord ++ tailWord_370006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370006).length < 2 ^ (prefixWord ++ tailWord_370006).sum := by decide
  have hdescent : baseEnd_370006 < baseStart_370006 := by decide
  rcases family_descends (prefixWord ++ tailWord_370006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370026 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_370026 : Nat := 118140960795 + 370026 * 2 ^ 59
def prefixEnd_370026 : Nat := 4983230072969 + 3 ^ 40 * 370026 * 2
def baseEnd_370026 : Nat := 126667461773783003515525

theorem tailTrace_370026 : CollatzResearch.WordTrace tailWord_370026 prefixEnd_370026 126667461773783003515525 := by
  unfold tailWord_370026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373989239366618063666483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8997304638310981503110621 3373989239366618063666483)
  ·
    refine ⟨5060983859049927095499725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3373989239366618063666483 5060983859049927095499725)
    ·
      refine ⟨1897868947143722660812397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5060983859049927095499725 1897868947143722660812397)
      ·
        refine ⟨711700855178895997804649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1897868947143722660812397 711700855178895997804649)
        ·
          refine ⟨533775641384171998353487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711700855178895997804649 533775641384171998353487)
          ·
            refine ⟨800663462076257997530231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533775641384171998353487 800663462076257997530231)
            ·
              refine ⟨1200995193114386996295347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800663462076257997530231 1200995193114386996295347)
              ·
                refine ⟨1801492789671580494443021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200995193114386996295347 1801492789671580494443021)
                ·
                  refine ⟨675559796126842685416133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1801492789671580494443021 675559796126842685416133)
                  ·
                    refine ⟨126667461773783003515525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675559796126842685416133 126667461773783003515525)
                    ·
                      rfl

theorem cell22_370026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_370026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370026 prefixEnd_370026 := by exact prefixLift 370026
  have htrace : WordTrace (prefixWord ++ tailWord_370026) baseStart_370026 baseEnd_370026 := by
    simpa [prefixWord, tailWord_370026, baseEnd_370026] using wordTrace_append hprefix tailTrace_370026
  have hstable : (prefixWord ++ tailWord_370026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370026).length < 2 ^ (prefixWord ++ tailWord_370026).sum := by decide
  have hdescent : baseEnd_370026 < baseStart_370026 := by decide
  rcases family_descends (prefixWord ++ tailWord_370026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370052 : List Nat := [2, 3, 2, 1, 1, 13]
def baseStart_370052 : Nat := 118140960795 + 370052 * 2 ^ 59
def prefixEnd_370052 : Nat := 4983230072969 + 3 ^ 40 * 370052 * 2
def baseEnd_370052 : Nat := 1563905705001575337845

theorem tailTrace_370052 : CollatzResearch.WordTrace tailWord_370052 prefixEnd_370052 1563905705001575337845 := by
  unfold tailWord_370052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748452627686139347556205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8997936836914852463408273 6748452627686139347556205)
  ·
    refine ⟨2530669735382302255333577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6748452627686139347556205 2530669735382302255333577)
    ·
      refine ⟨1898002301536726691500183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2530669735382302255333577 1898002301536726691500183)
      ·
        refine ⟨2847003452305090037250275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898002301536726691500183 2847003452305090037250275)
        ·
          refine ⟨4270505178457635055875413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847003452305090037250275 4270505178457635055875413)
          ·
            refine ⟨1563905705001575337845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 4270505178457635055875413 1563905705001575337845)
            ·
              rfl

theorem cell22_370052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 13].length) (baseStart_370052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370052 prefixEnd_370052 := by exact prefixLift 370052
  have htrace : WordTrace (prefixWord ++ tailWord_370052) baseStart_370052 baseEnd_370052 := by
    simpa [prefixWord, tailWord_370052, baseEnd_370052] using wordTrace_append hprefix tailTrace_370052
  have hstable : (prefixWord ++ tailWord_370052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370052).length < 2 ^ (prefixWord ++ tailWord_370052).sum := by decide
  have hdescent : baseEnd_370052 < baseStart_370052 := by decide
  rcases family_descends (prefixWord ++ tailWord_370052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370056 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_370056 : Nat := 118140960795 + 370056 * 2 ^ 59
def prefixEnd_370056 : Nat := 4983230072969 + 3 ^ 40 * 370056 * 2
def baseEnd_370056 : Nat := 126677731386872925265433

theorem tailTrace_370056 : CollatzResearch.WordTrace tailWord_370056 prefixEnd_370056 126677731386872925265433 := by
  unfold tailWord_370056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748525573678893689129011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8998034098238524918838681 6748525573678893689129011)
  ·
    refine ⟨10122788360518340533693517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6748525573678893689129011 10122788360518340533693517)
    ·
      refine ⟨3796045635194377700135069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10122788360518340533693517 3796045635194377700135069)
      ·
        refine ⟨1423517113197891637550651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3796045635194377700135069 1423517113197891637550651)
        ·
          refine ⟨2135275669796837456325977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423517113197891637550651 2135275669796837456325977)
          ·
            refine ⟨1601456752347628092244483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135275669796837456325977 1601456752347628092244483)
            ·
              refine ⟨2402185128521442138366725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601456752347628092244483 2402185128521442138366725)
              ·
                refine ⟨450409711597770400943761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2402185128521442138366725 450409711597770400943761)
                ·
                  refine ⟨337807283698327800707821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450409711597770400943761 337807283698327800707821)
                  ·
                    refine ⟨126677731386872925265433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337807283698327800707821 126677731386872925265433)
                    ·
                      rfl

theorem cell22_370056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_370056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370056 prefixEnd_370056 := by exact prefixLift 370056
  have htrace : WordTrace (prefixWord ++ tailWord_370056) baseStart_370056 baseEnd_370056 := by
    simpa [prefixWord, tailWord_370056, baseEnd_370056] using wordTrace_append hprefix tailTrace_370056
  have hstable : (prefixWord ++ tailWord_370056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370056).length < 2 ^ (prefixWord ++ tailWord_370056).sum := by decide
  have hdescent : baseEnd_370056 < baseStart_370056 := by decide
  rcases family_descends (prefixWord ++ tailWord_370056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370161 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_370161 : Nat := 118140960795 + 370161 * 2 ^ 59
def prefixEnd_370161 : Nat := 4983230072969 + 3 ^ 40 * 370161 * 2
def baseEnd_370161 : Nat := 126713675032687651390111

theorem tailTrace_370161 : CollatzResearch.WordTrace tailWord_370161 prefixEnd_370161 126713675032687651390111 := by
  unfold tailWord_370161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500880811977390310830337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9000587207984926873886891 13500880811977390310830337)
  ·
    refine ⟨10125660608983042733122753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13500880811977390310830337 10125660608983042733122753)
    ·
      refine ⟨7594245456737282049842065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10125660608983042733122753 7594245456737282049842065)
      ·
        refine ⟨5695684092552961537381549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7594245456737282049842065 5695684092552961537381549)
        ·
          refine ⟨2135881534707360576518081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5695684092552961537381549 2135881534707360576518081)
          ·
            refine ⟨1601911151030520432388561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135881534707360576518081 1601911151030520432388561)
            ·
              refine ⟨1201433363272890324291421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601911151030520432388561 1201433363272890324291421)
              ·
                refine ⟨450537511227333871609283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201433363272890324291421 450537511227333871609283)
                ·
                  refine ⟨675806266841000807413925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450537511227333871609283 675806266841000807413925)
                  ·
                    refine ⟨126713675032687651390111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675806266841000807413925 126713675032687651390111)
                    ·
                      rfl

theorem cell22_370161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_370161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370161 prefixEnd_370161 := by exact prefixLift 370161
  have htrace : WordTrace (prefixWord ++ tailWord_370161) baseStart_370161 baseEnd_370161 := by
    simpa [prefixWord, tailWord_370161, baseEnd_370161] using wordTrace_append hprefix tailTrace_370161
  have hstable : (prefixWord ++ tailWord_370161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370161).length < 2 ^ (prefixWord ++ tailWord_370161).sum := by decide
  have hdescent : baseEnd_370161 < baseStart_370161 := by decide
  rcases family_descends (prefixWord ++ tailWord_370161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370182 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_370182 : Nat := 118140960795 + 370182 * 2 ^ 59
def prefixEnd_370182 : Nat := 4983230072969 + 3 ^ 40 * 370182 * 2
def baseEnd_370182 : Nat := 42240287920616865538349

theorem tailTrace_370182 : CollatzResearch.WordTrace tailWord_370182 prefixEnd_370182 42240287920616865538349 := by
  unfold tailWord_370182
  simp only [CollatzResearch.WordTrace]
  refine ⟨421926460778165965542025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9001097829934207264896533 421926460778165965542025)
  ·
    refine ⟨316444845583624474156519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 421926460778165965542025 316444845583624474156519)
    ·
      refine ⟨474667268375436711234779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316444845583624474156519 474667268375436711234779)
      ·
        refine ⟨712000902563155066852169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474667268375436711234779 712000902563155066852169)
        ·
          refine ⟨534000676922366300139127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712000902563155066852169 534000676922366300139127)
          ·
            refine ⟨801001015383549450208691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534000676922366300139127 801001015383549450208691)
            ·
              refine ⟨1201501523075324175313037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801001015383549450208691 1201501523075324175313037)
              ·
                refine ⟨450563071153246565742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201501523075324175313037 450563071153246565742389)
                ·
                  refine ⟨42240287920616865538349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450563071153246565742389 42240287920616865538349)
                  ·
                    rfl

theorem cell22_370182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_370182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370182 prefixEnd_370182 := by exact prefixLift 370182
  have htrace : WordTrace (prefixWord ++ tailWord_370182) baseStart_370182 baseEnd_370182 := by
    simpa [prefixWord, tailWord_370182, baseEnd_370182] using wordTrace_append hprefix tailTrace_370182
  have hstable : (prefixWord ++ tailWord_370182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370182).length < 2 ^ (prefixWord ++ tailWord_370182).sum := by decide
  have hdescent : baseEnd_370182 < baseStart_370182 := by decide
  rcases family_descends (prefixWord ++ tailWord_370182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370204 : List Nat := [2, 2, 3, 1, 2, 1, 1, 10]
def baseStart_370204 : Nat := 118140960795 + 370204 * 2 ^ 59
def prefixEnd_370204 : Nat := 4983230072969 + 3 ^ 40 * 370204 * 2
def baseEnd_370204 : Nat := 14080932756827763618331

theorem tailTrace_370204 : CollatzResearch.WordTrace tailWord_370204 prefixEnd_370204 14080932756827763618331 := by
  unfold tailWord_370204
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751224575410804327322833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9001632767214405769763777 6751224575410804327322833)
  ·
    refine ⟨5063418431558103245492125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6751224575410804327322833 5063418431558103245492125)
    ·
      refine ⟨1898781911834288717059547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5063418431558103245492125 1898781911834288717059547)
      ·
        refine ⟨2848172867751433075589321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898781911834288717059547 2848172867751433075589321)
        ·
          refine ⟨2136129650813574806691991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848172867751433075589321 2136129650813574806691991)
          ·
            refine ⟨3204194476220362210037987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136129650813574806691991 3204194476220362210037987)
            ·
              refine ⟨4806291714330543315056981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204194476220362210037987 4806291714330543315056981)
              ·
                refine ⟨14080932756827763618331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4806291714330543315056981 14080932756827763618331)
                ·
                  rfl

theorem cell22_370204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_370204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370204 prefixEnd_370204 := by exact prefixLift 370204
  have htrace : WordTrace (prefixWord ++ tailWord_370204) baseStart_370204 baseEnd_370204 := by
    simpa [prefixWord, tailWord_370204, baseEnd_370204] using wordTrace_append hprefix tailTrace_370204
  have hstable : (prefixWord ++ tailWord_370204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370204).length < 2 ^ (prefixWord ++ tailWord_370204).sum := by decide
  have hdescent : baseEnd_370204 < baseStart_370204 := by decide
  rcases family_descends (prefixWord ++ tailWord_370204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370221 : List Nat := [1, 5, 4, 12]
def baseStart_370221 : Nat := 118140960795 + 370221 * 2 ^ 59
def prefixEnd_370221 : Nat := 4983230072969 + 3 ^ 40 * 370221 * 2
def baseEnd_370221 : Nat := 173846658791313436063

theorem tailTrace_370221 : CollatzResearch.WordTrace tailWord_370221 prefixEnd_370221 173846658791313436063 := by
  unfold tailWord_370221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503069191760020558014517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9002046127840013705343011 13503069191760020558014517)
  ·
    refine ⟨1265912736727501927313861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13503069191760020558014517 1265912736727501927313861)
    ·
      refine ⟨237358638136406611371349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1265912736727501927313861 237358638136406611371349)
      ·
        refine ⟨173846658791313436063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 237358638136406611371349 173846658791313436063)
        ·
          rfl

theorem cell22_370221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 12].length) (baseStart_370221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370221 prefixEnd_370221 := by exact prefixLift 370221
  have htrace : WordTrace (prefixWord ++ tailWord_370221) baseStart_370221 baseEnd_370221 := by
    simpa [prefixWord, tailWord_370221, baseEnd_370221] using wordTrace_append hprefix tailTrace_370221
  have hstable : (prefixWord ++ tailWord_370221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370221).length < 2 ^ (prefixWord ++ tailWord_370221).sum := by decide
  have hdescent : baseEnd_370221 < baseStart_370221 := by decide
  rcases family_descends (prefixWord ++ tailWord_370221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370234 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_370234 : Nat := 118140960795 + 370234 * 2 ^ 59
def prefixEnd_370234 : Nat := 4983230072969 + 3 ^ 40 * 370234 * 2
def baseEnd_370234 : Nat := 126738664424539794314887

theorem tailTrace_370234 : CollatzResearch.WordTrace tailWord_370234 prefixEnd_370234 126738664424539794314887 := by
  unfold tailWord_370234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375885835178230944559439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9002362227141949185491837 3375885835178230944559439)
  ·
    refine ⟨5063828752767346416839159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375885835178230944559439 5063828752767346416839159)
    ·
      refine ⟨7595743129151019625258739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063828752767346416839159 7595743129151019625258739)
      ·
        refine ⟨11393614693726529437888109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595743129151019625258739 11393614693726529437888109)
        ·
          refine ⟨4272605510147448539208041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11393614693726529437888109 4272605510147448539208041)
          ·
            refine ⟨3204454132610586404406031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272605510147448539208041 3204454132610586404406031)
            ·
              refine ⟨4806681198915879606609047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204454132610586404406031 4806681198915879606609047)
              ·
                refine ⟨7210021798373819409913571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806681198915879606609047 7210021798373819409913571)
                ·
                  refine ⟨10815032697560729114870357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210021798373819409913571 10815032697560729114870357)
                  ·
                    refine ⟨126738664424539794314887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10815032697560729114870357 126738664424539794314887)
                    ·
                      rfl

theorem cell22_370234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_370234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370234 prefixEnd_370234 := by exact prefixLift 370234
  have htrace : WordTrace (prefixWord ++ tailWord_370234) baseStart_370234 baseEnd_370234 := by
    simpa [prefixWord, tailWord_370234, baseEnd_370234] using wordTrace_append hprefix tailTrace_370234
  have hstable : (prefixWord ++ tailWord_370234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370234).length < 2 ^ (prefixWord ++ tailWord_370234).sum := by decide
  have hdescent : baseEnd_370234 < baseStart_370234 := by decide
  rcases family_descends (prefixWord ++ tailWord_370234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370264 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_370264 : Nat := 118140960795 + 370264 * 2 ^ 59
def prefixEnd_370264 : Nat := 4983230072969 + 3 ^ 40 * 370264 * 2
def baseEnd_370264 : Nat := 126748934037629716064795

theorem tailTrace_370264 : CollatzResearch.WordTrace tailWord_370264 prefixEnd_370264 126748934037629716064795 := by
  unfold tailWord_370264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752318765302119450914923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9003091687069492601219897 6752318765302119450914923)
  ·
    refine ⟨10128478147953179176372385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752318765302119450914923 10128478147953179176372385)
    ·
      refine ⟨7596358610964884382279289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10128478147953179176372385 7596358610964884382279289)
      ·
        refine ⟨5697268958223663286709467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7596358610964884382279289 5697268958223663286709467)
        ·
          refine ⟨8545903437335494930064201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697268958223663286709467 8545903437335494930064201)
          ·
            refine ⟨6409427578001621197548151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8545903437335494930064201 6409427578001621197548151)
            ·
              refine ⟨9614141367002431796322227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409427578001621197548151 9614141367002431796322227)
              ·
                refine ⟨14421212050503647694483341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614141367002431796322227 14421212050503647694483341)
                ·
                  refine ⟨5407954518938867885431253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14421212050503647694483341 5407954518938867885431253)
                  ·
                    refine ⟨126748934037629716064795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5407954518938867885431253 126748934037629716064795)
                    ·
                      rfl

theorem cell22_370264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_370264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370264 prefixEnd_370264 := by exact prefixLift 370264
  have htrace : WordTrace (prefixWord ++ tailWord_370264) baseStart_370264 baseEnd_370264 := by
    simpa [prefixWord, tailWord_370264, baseEnd_370264] using wordTrace_append hprefix tailTrace_370264
  have hstable : (prefixWord ++ tailWord_370264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370264).length < 2 ^ (prefixWord ++ tailWord_370264).sum := by decide
  have hdescent : baseEnd_370264 < baseStart_370264 := by decide
  rcases family_descends (prefixWord ++ tailWord_370264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370311 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 6]
def baseStart_370311 : Nat := 118140960795 + 370311 * 2 ^ 59
def prefixEnd_370311 : Nat := 4983230072969 + 3 ^ 40 * 370311 * 2
def baseEnd_370311 : Nat := 42255007699379086713217

theorem tailTrace_370311 : CollatzResearch.WordTrace tailWord_370311 prefixEnd_370311 42255007699379086713217 := by
  unfold tailWord_370311
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506351761433965928790787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9004234507622643952527191 13506351761433965928790787)
  ·
    refine ⟨20259527642150948893186181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13506351761433965928790787 20259527642150948893186181)
    ·
      refine ⟨3798661432903302917472409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20259527642150948893186181 3798661432903302917472409)
      ·
        refine ⟨2848996074677477188104307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3798661432903302917472409 2848996074677477188104307)
        ·
          refine ⟨4273494112016215782156461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848996074677477188104307 4273494112016215782156461)
          ·
            refine ⟨1602560292006080918308673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4273494112016215782156461 1602560292006080918308673)
            ·
              refine ⟨1201920219004560688731505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602560292006080918308673 1201920219004560688731505)
              ·
                refine ⟨901440164253420516548629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201920219004560688731505 901440164253420516548629)
                ·
                  refine ⟨42255007699379086713217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 901440164253420516548629 42255007699379086713217)
                  ·
                    rfl

theorem cell22_370311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_370311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370311 prefixEnd_370311 := by exact prefixLift 370311
  have htrace : WordTrace (prefixWord ++ tailWord_370311) baseStart_370311 baseEnd_370311 := by
    simpa [prefixWord, tailWord_370311, baseEnd_370311] using wordTrace_append hprefix tailTrace_370311
  have hstable : (prefixWord ++ tailWord_370311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370311).length < 2 ^ (prefixWord ++ tailWord_370311).sum := by decide
  have hdescent : baseEnd_370311 < baseStart_370311 := by decide
  rcases family_descends (prefixWord ++ tailWord_370311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370341 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_370341 : Nat := 118140960795 + 370341 * 2 ^ 59
def prefixEnd_370341 : Nat := 4983230072969 + 3 ^ 40 * 370341 * 2
def baseEnd_370341 : Nat := 126775292711227181889559

theorem tailTrace_370341 : CollatzResearch.WordTrace tailWord_370341 prefixEnd_370341 126775292711227181889559 := by
  unfold tailWord_370341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13507445951325281052382877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9004963967550187368255251 13507445951325281052382877)
  ·
    refine ⟨5065292231746980394643579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13507445951325281052382877 5065292231746980394643579)
    ·
      refine ⟨7597938347620470591965369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065292231746980394643579 7597938347620470591965369)
      ·
        refine ⟨5698453760715352943974027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7597938347620470591965369 5698453760715352943974027)
        ·
          refine ⟨8547680641073029415961041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5698453760715352943974027 8547680641073029415961041)
          ·
            refine ⟨6410760480804772061970781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8547680641073029415961041 6410760480804772061970781)
            ·
              refine ⟨2404035180301789523239043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6410760480804772061970781 2404035180301789523239043)
              ·
                refine ⟨3606052770452684284858565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404035180301789523239043 3606052770452684284858565)
                ·
                  refine ⟨676134894459878303410981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3606052770452684284858565 676134894459878303410981)
                  ·
                    refine ⟨126775292711227181889559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676134894459878303410981 126775292711227181889559)
                    ·
                      rfl

theorem cell22_370341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_370341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370341 prefixEnd_370341 := by exact prefixLift 370341
  have htrace : WordTrace (prefixWord ++ tailWord_370341) baseStart_370341 baseEnd_370341 := by
    simpa [prefixWord, tailWord_370341, baseEnd_370341] using wordTrace_append hprefix tailTrace_370341
  have hstable : (prefixWord ++ tailWord_370341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370341).length < 2 ^ (prefixWord ++ tailWord_370341).sum := by decide
  have hdescent : baseEnd_370341 < baseStart_370341 := by decide
  rcases family_descends (prefixWord ++ tailWord_370341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370390 : List Nat := [5, 2, 1, 3, 1, 10]
def baseStart_370390 : Nat := 118140960795 + 370390 * 2 ^ 59
def prefixEnd_370390 : Nat := 4983230072969 + 3 ^ 40 * 370390 * 2
def baseEnd_370390 : Nat := 1565334153242066511289

theorem tailTrace_370390 : CollatzResearch.WordTrace tailWord_370390 prefixEnd_370390 1565334153242066511289 := by
  unfold tailWord_370390
  simp only [CollatzResearch.WordTrace]
  refine ⟨844327070509235151307289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9006155418765174947277749 844327070509235151307289)
  ·
    refine ⟨633245302881926363480467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 844327070509235151307289 633245302881926363480467)
    ·
      refine ⟨949867954322889545220701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633245302881926363480467 949867954322889545220701)
      ·
        refine ⟨356200482871083579457763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 949867954322889545220701 356200482871083579457763)
        ·
          refine ⟨534300724306625369186645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356200482871083579457763 534300724306625369186645)
          ·
            refine ⟨1565334153242066511289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 534300724306625369186645 1565334153242066511289)
            ·
              rfl

theorem cell22_370390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 10].length) (baseStart_370390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370390 prefixEnd_370390 := by exact prefixLift 370390
  have htrace : WordTrace (prefixWord ++ tailWord_370390) baseStart_370390 baseEnd_370390 := by
    simpa [prefixWord, tailWord_370390, baseEnd_370390] using wordTrace_append hprefix tailTrace_370390
  have hstable : (prefixWord ++ tailWord_370390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370390).length < 2 ^ (prefixWord ++ tailWord_370390).sum := by decide
  have hdescent : baseEnd_370390 < baseStart_370390 := by decide
  rcases family_descends (prefixWord ++ tailWord_370390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370396 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_370396 : Nat := 118140960795 + 370396 * 2 ^ 59
def prefixEnd_370396 : Nat := 4983230072969 + 3 ^ 40 * 370396 * 2
def baseEnd_370396 : Nat := 42264706778408457254797

theorem tailTrace_370396 : CollatzResearch.WordTrace tailWord_370396 prefixEnd_370396 42264706778408457254797 := by
  unfold tailWord_370396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754725983063012722817521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9006301310750683630423361 6754725983063012722817521)
  ·
    refine ⟨5066044487297259542113141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6754725983063012722817521 5066044487297259542113141)
    ·
      refine ⟨474941670684118082073107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5066044487297259542113141 474941670684118082073107)
      ·
        refine ⟨712412506026177123109661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474941670684118082073107 712412506026177123109661)
        ·
          refine ⟨267154689759816421166123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 712412506026177123109661 267154689759816421166123)
          ·
            refine ⟨400732034639724631749185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267154689759816421166123 400732034639724631749185)
            ·
              refine ⟨300549025979793473811889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400732034639724631749185 300549025979793473811889)
              ·
                refine ⟨225411769484845105358917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300549025979793473811889 225411769484845105358917)
                ·
                  refine ⟨42264706778408457254797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225411769484845105358917 42264706778408457254797)
                  ·
                    rfl

theorem cell22_370396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_370396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370396 prefixEnd_370396 := by exact prefixLift 370396
  have htrace : WordTrace (prefixWord ++ tailWord_370396) baseStart_370396 baseEnd_370396 := by
    simpa [prefixWord, tailWord_370396, baseEnd_370396] using wordTrace_append hprefix tailTrace_370396
  have hstable : (prefixWord ++ tailWord_370396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370396).length < 2 ^ (prefixWord ++ tailWord_370396).sum := by decide
  have hdescent : baseEnd_370396 < baseStart_370396 := by decide
  rcases family_descends (prefixWord ++ tailWord_370396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370407 : List Nat := [1, 1, 5, 4, 2, 1, 1, 7]
def baseStart_370407 : Nat := 118140960795 + 370407 * 2 ^ 59
def prefixEnd_370407 : Nat := 4983230072969 + 3 ^ 40 * 370407 * 2
def baseEnd_370407 : Nat := 14088653984447223304373

theorem tailTrace_370407 : CollatzResearch.WordTrace tailWord_370407 prefixEnd_370407 14088653984447223304373 := by
  unfold tailWord_370407
  simp only [CollatzResearch.WordTrace]
  refine ⟨13509853169086174324285475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9006568779390782882856983 13509853169086174324285475)
  ·
    refine ⟨20264779753629261486428213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13509853169086174324285475 20264779753629261486428213)
    ·
      refine ⟨1899823101902743264352645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20264779753629261486428213 1899823101902743264352645)
      ·
        refine ⟨356216831606764362066121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1899823101902743264352645 356216831606764362066121)
        ·
          refine ⟨267162623705073271549591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356216831606764362066121 267162623705073271549591)
          ·
            refine ⟨400743935557609907324387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267162623705073271549591 400743935557609907324387)
            ·
              refine ⟨601115903336414860986581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400743935557609907324387 601115903336414860986581)
              ·
                refine ⟨14088653984447223304373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 601115903336414860986581 14088653984447223304373)
                ·
                  rfl

theorem cell22_370407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 7].length) (baseStart_370407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370407 prefixEnd_370407 := by exact prefixLift 370407
  have htrace : WordTrace (prefixWord ++ tailWord_370407) baseStart_370407 baseEnd_370407 := by
    simpa [prefixWord, tailWord_370407, baseEnd_370407] using wordTrace_append hprefix tailTrace_370407
  have hstable : (prefixWord ++ tailWord_370407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370407).length < 2 ^ (prefixWord ++ tailWord_370407).sum := by decide
  have hdescent : baseEnd_370407 < baseStart_370407 := by decide
  rcases family_descends (prefixWord ++ tailWord_370407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370418 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_370418 : Nat := 118140960795 + 370418 * 2 ^ 59
def prefixEnd_370418 : Nat := 4983230072969 + 3 ^ 40 * 370418 * 2
def baseEnd_370418 : Nat := 42267217128274882571441

theorem tailTrace_370418 : CollatzResearch.WordTrace tailWord_370418 prefixEnd_370418 42267217128274882571441 := by
  unfold tailWord_370418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377563593011580800733977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9006836248030882135290605 3377563593011580800733977)
  ·
    refine ⟨2533172694758685600550483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377563593011580800733977 2533172694758685600550483)
    ·
      refine ⟨3799759042138028400825725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2533172694758685600550483 3799759042138028400825725)
      ·
        refine ⟨1424909640801760650309647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3799759042138028400825725 1424909640801760650309647)
        ·
          refine ⟨2137364461202640975464471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424909640801760650309647 2137364461202640975464471)
          ·
            refine ⟨3206046691803961463196707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137364461202640975464471 3206046691803961463196707)
            ·
              refine ⟨4809070037705942194795061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206046691803961463196707 4809070037705942194795061)
              ·
                refine ⟨450850316034932080762037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4809070037705942194795061 450850316034932080762037)
                ·
                  refine ⟨42267217128274882571441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450850316034932080762037 42267217128274882571441)
                  ·
                    rfl

theorem cell22_370418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_370418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370418 prefixEnd_370418 := by exact prefixLift 370418
  have htrace : WordTrace (prefixWord ++ tailWord_370418) baseStart_370418 baseEnd_370418 := by
    simpa [prefixWord, tailWord_370418, baseEnd_370418] using wordTrace_append hprefix tailTrace_370418
  have hstable : (prefixWord ++ tailWord_370418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370418).length < 2 ^ (prefixWord ++ tailWord_370418).sum := by decide
  have hdescent : baseEnd_370418 < baseStart_370418 := by decide
  rcases family_descends (prefixWord ++ tailWord_370418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370439 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 1, 3]
def baseStart_370439 : Nat := 118140960795 + 370439 * 2 ^ 59
def prefixEnd_370439 : Nat := 4983230072969 + 3 ^ 40 * 370439 * 2
def baseEnd_370439 : Nat := 126808840113987592939259

theorem tailTrace_370439 : CollatzResearch.WordTrace tailWord_370439 prefixEnd_370439 126808840113987592939259 := by
  unfold tailWord_370439
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511020304970243789450371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9007346869980162526300247 13511020304970243789450371)
  ·
    refine ⟨20266530457455365684175557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511020304970243789450371 20266530457455365684175557)
    ·
      refine ⟨3799974460772881065782917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20266530457455365684175557 3799974460772881065782917)
      ·
        refine ⟨712495211394915199834297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3799974460772881065782917 712495211394915199834297)
        ·
          refine ⟨534371408546186399875723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712495211394915199834297 534371408546186399875723)
          ·
            refine ⟨801557112819279599813585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534371408546186399875723 801557112819279599813585)
            ·
              refine ⟨601167834614459699860189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801557112819279599813585 601167834614459699860189)
              ·
                refine ⟨225437937980422387447571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601167834614459699860189 225437937980422387447571)
                ·
                  refine ⟨338156906970633581171357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225437937980422387447571 338156906970633581171357)
                  ·
                    refine ⟨126808840113987592939259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338156906970633581171357 126808840113987592939259)
                    ·
                      rfl

theorem cell22_370439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_370439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370439 prefixEnd_370439 := by exact prefixLift 370439
  have htrace : WordTrace (prefixWord ++ tailWord_370439) baseStart_370439 baseEnd_370439 := by
    simpa [prefixWord, tailWord_370439, baseEnd_370439] using wordTrace_append hprefix tailTrace_370439
  have hstable : (prefixWord ++ tailWord_370439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370439).length < 2 ^ (prefixWord ++ tailWord_370439).sum := by decide
  have hdescent : baseEnd_370439 < baseStart_370439 := by decide
  rcases family_descends (prefixWord ++ tailWord_370439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370445 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_370445 : Nat := 118140960795 + 370445 * 2 ^ 59
def prefixEnd_370445 : Nat := 4983230072969 + 3 ^ 40 * 370445 * 2
def baseEnd_370445 : Nat := 126810894036605577289241

theorem tailTrace_370445 : CollatzResearch.WordTrace tailWord_370445 prefixEnd_370445 126810894036605577289241 := by
  unfold tailWord_370445
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511239142948506814168789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9007492761965671209445859 13511239142948506814168789)
  ·
    refine ⟨316669667412855628457081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13511239142948506814168789 316669667412855628457081)
    ·
      refine ⟨237502250559641721342811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316669667412855628457081 237502250559641721342811)
      ·
        refine ⟨356253375839462582014217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237502250559641721342811 356253375839462582014217)
        ·
          refine ⟨267190031879596936510663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356253375839462582014217 267190031879596936510663)
          ·
            refine ⟨400785047819395404765995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267190031879596936510663 400785047819395404765995)
            ·
              refine ⟨601177571729093107148993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400785047819395404765995 601177571729093107148993)
              ·
                refine ⟨450883178796819830361745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601177571729093107148993 450883178796819830361745)
                ·
                  refine ⟨338162384097614872771309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450883178796819830361745 338162384097614872771309)
                  ·
                    refine ⟨126810894036605577289241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338162384097614872771309 126810894036605577289241)
                    ·
                      rfl

theorem cell22_370445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_370445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370445 prefixEnd_370445 := by exact prefixLift 370445
  have htrace : WordTrace (prefixWord ++ tailWord_370445) baseStart_370445 baseEnd_370445 := by
    simpa [prefixWord, tailWord_370445, baseEnd_370445] using wordTrace_append hprefix tailTrace_370445
  have hstable : (prefixWord ++ tailWord_370445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370445).length < 2 ^ (prefixWord ++ tailWord_370445).sum := by decide
  have hdescent : baseEnd_370445 < baseStart_370445 := by decide
  rcases family_descends (prefixWord ++ tailWord_370445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370450 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_370450 : Nat := 118140960795 + 370450 * 2 ^ 59
def prefixEnd_370450 : Nat := 4983230072969 + 3 ^ 40 * 370450 * 2
def baseEnd_370450 : Nat := 126812605638787230914225

theorem tailTrace_370450 : CollatzResearch.WordTrace tailWord_370450 prefixEnd_370450 126812605638787230914225 := by
  unfold tailWord_370450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377855376982598167025201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9007614338620261778733869 3377855376982598167025201)
  ·
    refine ⟨2533391532736948625268901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377855376982598167025201 2533391532736948625268901)
    ·
      refine ⟨475010912388177867237919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2533391532736948625268901 475010912388177867237919)
      ·
        refine ⟨712516368582266800856879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475010912388177867237919 712516368582266800856879)
        ·
          refine ⟨1068774552873400201285319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712516368582266800856879 1068774552873400201285319)
          ·
            refine ⟨1603161829310100301927979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068774552873400201285319 1603161829310100301927979)
            ·
              refine ⟨2404742743965150452891969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603161829310100301927979 2404742743965150452891969)
              ·
                refine ⟨1803557057973862839668977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404742743965150452891969 1803557057973862839668977)
                ·
                  refine ⟨1352667793480397129751733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803557057973862839668977 1352667793480397129751733)
                  ·
                    refine ⟨126812605638787230914225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1352667793480397129751733 126812605638787230914225)
                    ·
                      rfl

theorem cell22_370450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_370450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370450 prefixEnd_370450 := by exact prefixLift 370450
  have htrace : WordTrace (prefixWord ++ tailWord_370450) baseStart_370450 baseEnd_370450 := by
    simpa [prefixWord, tailWord_370450, baseEnd_370450] using wordTrace_append hprefix tailTrace_370450
  have hstable : (prefixWord ++ tailWord_370450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370450).length < 2 ^ (prefixWord ++ tailWord_370450).sum := by decide
  have hdescent : baseEnd_370450 < baseStart_370450 := by decide
  rcases family_descends (prefixWord ++ tailWord_370450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370463 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 6]
def baseStart_370463 : Nat := 118140960795 + 370463 * 2 ^ 59
def prefixEnd_370463 : Nat := 4983230072969 + 3 ^ 40 * 370463 * 2
def baseEnd_370463 : Nat := 42272351934819843446395

theorem tailTrace_370463 : CollatzResearch.WordTrace tailWord_370463 prefixEnd_370463 42272351934819843446395 := by
  unfold tailWord_370463
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511895656883295888324043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9007930437922197258882695 13511895656883295888324043)
  ·
    refine ⟨20267843485324943832486065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511895656883295888324043 20267843485324943832486065)
    ·
      refine ⟨15200882613993707874364549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20267843485324943832486065 15200882613993707874364549)
      ·
        refine ⟨2850165490123820226443353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15200882613993707874364549 2850165490123820226443353)
        ·
          refine ⟨2137624117592865169832515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2850165490123820226443353 2137624117592865169832515)
          ·
            refine ⟨3206436176389297754748773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137624117592865169832515 3206436176389297754748773)
            ·
              refine ⟨601206783072993329015395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3206436176389297754748773 601206783072993329015395)
              ·
                refine ⟨901810174609489993523093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601206783072993329015395 901810174609489993523093)
                ·
                  refine ⟨42272351934819843446395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 901810174609489993523093 42272351934819843446395)
                  ·
                    rfl

theorem cell22_370463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 6].length) (baseStart_370463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370463 prefixEnd_370463 := by exact prefixLift 370463
  have htrace : WordTrace (prefixWord ++ tailWord_370463) baseStart_370463 baseEnd_370463 := by
    simpa [prefixWord, tailWord_370463, baseEnd_370463] using wordTrace_append hprefix tailTrace_370463
  have hstable : (prefixWord ++ tailWord_370463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370463).length < 2 ^ (prefixWord ++ tailWord_370463).sum := by decide
  have hdescent : baseEnd_370463 < baseStart_370463 := by decide
  rcases family_descends (prefixWord ++ tailWord_370463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370557 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_370557 : Nat := 118140960795 + 370557 * 2 ^ 59
def prefixEnd_370557 : Nat := 4983230072969 + 3 ^ 40 * 370557 * 2
def baseEnd_370557 : Nat := 126849233925474618488897

theorem tailTrace_370557 : CollatzResearch.WordTrace tailWord_370557 prefixEnd_370557 126849233925474618488897 := by
  unfold tailWord_370557
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515324118542749942245925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9010216079028499961497283 13515324118542749942245925)
  ·
    refine ⟨2534123272226765614171111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13515324118542749942245925 2534123272226765614171111)
    ·
      refine ⟨3801184908340148421256667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534123272226765614171111 3801184908340148421256667)
      ·
        refine ⟨5701777362510222631885001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801184908340148421256667 5701777362510222631885001)
        ·
          refine ⟨4276333021882666973913751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5701777362510222631885001 4276333021882666973913751)
          ·
            refine ⟨6414499532824000460870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276333021882666973913751 6414499532824000460870627)
            ·
              refine ⟨9621749299236000691305941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6414499532824000460870627 9621749299236000691305941)
              ·
                refine ⟨225509749200843766202483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9621749299236000691305941 225509749200843766202483)
                ·
                  refine ⟨338264623801265649303725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225509749200843766202483 338264623801265649303725)
                  ·
                    refine ⟨126849233925474618488897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338264623801265649303725 126849233925474618488897)
                    ·
                      rfl

theorem cell22_370557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_370557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370557 prefixEnd_370557 := by exact prefixLift 370557
  have htrace : WordTrace (prefixWord ++ tailWord_370557) baseStart_370557 baseEnd_370557 := by
    simpa [prefixWord, tailWord_370557, baseEnd_370557] using wordTrace_append hprefix tailTrace_370557
  have hstable : (prefixWord ++ tailWord_370557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370557).length < 2 ^ (prefixWord ++ tailWord_370557).sum := by decide
  have hdescent : baseEnd_370557 < baseStart_370557 := by decide
  rcases family_descends (prefixWord ++ tailWord_370557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370632 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_370632 : Nat := 118140960795 + 370632 * 2 ^ 59
def prefixEnd_370632 : Nat := 4983230072969 + 3 ^ 40 * 370632 * 2
def baseEnd_370632 : Nat := 42291635986066474287889

theorem tailTrace_370632 : CollatzResearch.WordTrace tailWord_370632 prefixEnd_370632 42291635986066474287889 := by
  unfold tailWord_370632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759029796635518875613075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9012039728847358500817433 6759029796635518875613075)
  ·
    refine ⟨10138544694953278313419613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6759029796635518875613075 10138544694953278313419613)
    ·
      refine ⟨3801954260607479367532355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10138544694953278313419613 3801954260607479367532355)
      ·
        refine ⟨5702931390911219051298533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801954260607479367532355 5702931390911219051298533)
        ·
          refine ⟨1069299635795853572118475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5702931390911219051298533 1069299635795853572118475)
          ·
            refine ⟨1603949453693780358177713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069299635795853572118475 1603949453693780358177713)
            ·
              refine ⟨1202962090270335268633285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603949453693780358177713 1202962090270335268633285)
              ·
                refine ⟨225555391925687862868741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1202962090270335268633285 225555391925687862868741)
                ·
                  refine ⟨42291635986066474287889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225555391925687862868741 42291635986066474287889)
                  ·
                    rfl

theorem cell22_370632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_370632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370632 prefixEnd_370632 := by exact prefixLift 370632
  have htrace : WordTrace (prefixWord ++ tailWord_370632) baseStart_370632 baseEnd_370632 := by
    simpa [prefixWord, tailWord_370632, baseEnd_370632] using wordTrace_append hprefix tailTrace_370632
  have hstable : (prefixWord ++ tailWord_370632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370632).length < 2 ^ (prefixWord ++ tailWord_370632).sum := by decide
  have hdescent : baseEnd_370632 < baseStart_370632 := by decide
  rcases family_descends (prefixWord ++ tailWord_370632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370645 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_370645 : Nat := 118140960795 + 370645 * 2 ^ 59
def prefixEnd_370645 : Nat := 4983230072969 + 3 ^ 40 * 370645 * 2
def baseEnd_370645 : Nat := 126879358123871722288627

theorem tailTrace_370645 : CollatzResearch.WordTrace tailWord_370645 prefixEnd_370645 126879358123871722288627 := by
  unfold tailWord_370645
  simp only [CollatzResearch.WordTrace]
  refine ⟨13518533742223940971449389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9012355828149293980966259 13518533742223940971449389)
  ·
    refine ⟨5069450153333977864293521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13518533742223940971449389 5069450153333977864293521)
    ·
      refine ⟨3802087615000483398220141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069450153333977864293521 3802087615000483398220141)
      ·
        refine ⟨1425782855625181274332553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3802087615000483398220141 1425782855625181274332553)
        ·
          refine ⟨1069337141718885955749415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425782855625181274332553 1069337141718885955749415)
          ·
            refine ⟨1604005712578328933624123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069337141718885955749415 1604005712578328933624123)
            ·
              refine ⟨2406008568867493400436185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604005712578328933624123 2406008568867493400436185)
              ·
                refine ⟨1804506426650620050327139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406008568867493400436185 1804506426650620050327139)
                ·
                  refine ⟨2706759639975930075490709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804506426650620050327139 2706759639975930075490709)
                  ·
                    refine ⟨126879358123871722288627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2706759639975930075490709 126879358123871722288627)
                    ·
                      rfl

theorem cell22_370645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_370645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370645 prefixEnd_370645 := by exact prefixLift 370645
  have htrace : WordTrace (prefixWord ++ tailWord_370645) baseStart_370645 baseEnd_370645 := by
    simpa [prefixWord, tailWord_370645, baseEnd_370645] using wordTrace_append hprefix tailTrace_370645
  have hstable : (prefixWord ++ tailWord_370645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370645).length < 2 ^ (prefixWord ++ tailWord_370645).sum := by decide
  have hdescent : baseEnd_370645 < baseStart_370645 := by decide
  rcases family_descends (prefixWord ++ tailWord_370645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370675 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 5, 3]
def baseStart_370675 : Nat := 118140960795 + 370675 * 2 ^ 59
def prefixEnd_370675 : Nat := 4983230072969 + 3 ^ 40 * 370675 * 2
def baseEnd_370675 : Nat := 126889627736961644038535

theorem tailTrace_370675 : CollatzResearch.WordTrace tailWord_370675 prefixEnd_370675 126889627736961644038535 := by
  unfold tailWord_370675
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519627932115256095041479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9013085288076837396694319 13519627932115256095041479)
  ·
    refine ⟨20279441898172884142562219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13519627932115256095041479 20279441898172884142562219)
    ·
      refine ⟨30419162847259326213843329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20279441898172884142562219 30419162847259326213843329)
      ·
        refine ⟨22814372135444494660382497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30419162847259326213843329 22814372135444494660382497)
        ·
          refine ⟨17110779101583370995286873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22814372135444494660382497 17110779101583370995286873)
          ·
            refine ⟨12833084326187528246465155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17110779101583370995286873 12833084326187528246465155)
            ·
              refine ⟨19249626489281292369697733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12833084326187528246465155 19249626489281292369697733)
              ·
                refine ⟨3609304966740242319318325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19249626489281292369697733 3609304966740242319318325)
                ·
                  refine ⟨338372340631897717436093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3609304966740242319318325 338372340631897717436093)
                  ·
                    refine ⟨126889627736961644038535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338372340631897717436093 126889627736961644038535)
                    ·
                      rfl

theorem cell22_370675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 3].length) (baseStart_370675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370675 prefixEnd_370675 := by exact prefixLift 370675
  have htrace : WordTrace (prefixWord ++ tailWord_370675) baseStart_370675 baseEnd_370675 := by
    simpa [prefixWord, tailWord_370675, baseEnd_370675] using wordTrace_append hprefix tailTrace_370675
  have hstable : (prefixWord ++ tailWord_370675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370675).length < 2 ^ (prefixWord ++ tailWord_370675).sum := by decide
  have hdescent : baseEnd_370675 < baseStart_370675 := by decide
  rcases family_descends (prefixWord ++ tailWord_370675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370698 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_370698 : Nat := 118140960795 + 370698 * 2 ^ 59
def prefixEnd_370698 : Nat := 4983230072969 + 3 ^ 40 * 370698 * 2
def baseEnd_370698 : Nat := 126897501106997250713465

theorem tailTrace_370698 : CollatzResearch.WordTrace tailWord_370698 prefixEnd_370698 126897501106997250713465 := by
  unfold tailWord_370698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380116702757982755782187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9013644540687954015419165 3380116702757982755782187)
  ·
    refine ⟨5070175054136974133673281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380116702757982755782187 5070175054136974133673281)
    ·
      refine ⟨3802631290602730600254961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5070175054136974133673281 3802631290602730600254961)
      ·
        refine ⟨2851973467952047950191221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802631290602730600254961 2851973467952047950191221)
        ·
          refine ⟨267372512620504495330427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2851973467952047950191221 267372512620504495330427)
          ·
            refine ⟨401058768930756742995641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267372512620504495330427 401058768930756742995641)
            ·
              refine ⟨300794076698067557246731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401058768930756742995641 300794076698067557246731)
              ·
                refine ⟨451191115047101335870097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300794076698067557246731 451191115047101335870097)
                ·
                  refine ⟨338393336285326001902573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451191115047101335870097 338393336285326001902573)
                  ·
                    refine ⟨126897501106997250713465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338393336285326001902573 126897501106997250713465)
                    ·
                      rfl

theorem cell22_370698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_370698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370698 prefixEnd_370698 := by exact prefixLift 370698
  have htrace : WordTrace (prefixWord ++ tailWord_370698) baseStart_370698 baseEnd_370698 := by
    simpa [prefixWord, tailWord_370698, baseEnd_370698] using wordTrace_append hprefix tailTrace_370698
  have hstable : (prefixWord ++ tailWord_370698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370698).length < 2 ^ (prefixWord ++ tailWord_370698).sum := by decide
  have hdescent : baseEnd_370698 < baseStart_370698 := by decide
  rcases family_descends (prefixWord ++ tailWord_370698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370784 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_370784 : Nat := 118140960795 + 370784 * 2 ^ 59
def prefixEnd_370784 : Nat := 4983230072969 + 3 ^ 40 * 370784 * 2
def baseEnd_370784 : Nat := 42308980221507231021067

theorem tailTrace_370784 : CollatzResearch.WordTrace tailWord_370784 prefixEnd_370784 42308980221507231021067 := by
  unfold tailWord_370784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761801744360183855379703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9015735659146911807172937 6761801744360183855379703)
  ·
    refine ⟨10142702616540275783069555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6761801744360183855379703 10142702616540275783069555)
    ·
      refine ⟨15214053924810413674604333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142702616540275783069555 15214053924810413674604333)
      ·
        refine ⟨5705270221803905127976625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15214053924810413674604333 5705270221803905127976625)
        ·
          refine ⟨4278952666352928845982469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5705270221803905127976625 4278952666352928845982469)
          ·
            refine ⟨802303624941174158621713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4278952666352928845982469 802303624941174158621713)
            ·
              refine ⟨601727718705880618966285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802303624941174158621713 601727718705880618966285)
              ·
                refine ⟨225647894514705232112357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601727718705880618966285 225647894514705232112357)
                ·
                  refine ⟨42308980221507231021067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225647894514705232112357 42308980221507231021067)
                  ·
                    rfl

theorem cell22_370784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_370784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370784 prefixEnd_370784 := by exact prefixLift 370784
  have htrace : WordTrace (prefixWord ++ tailWord_370784) baseStart_370784 baseEnd_370784 := by
    simpa [prefixWord, tailWord_370784, baseEnd_370784] using wordTrace_append hprefix tailTrace_370784
  have hstable : (prefixWord ++ tailWord_370784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370784).length < 2 ^ (prefixWord ++ tailWord_370784).sum := by decide
  have hdescent : baseEnd_370784 < baseStart_370784 := by decide
  rcases family_descends (prefixWord ++ tailWord_370784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370786 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_370786 : Nat := 118140960795 + 370786 * 2 ^ 59
def prefixEnd_370786 : Nat := 4983230072969 + 3 ^ 40 * 370786 * 2
def baseEnd_370786 : Nat := 126927625305394354513195

theorem tailTrace_370786 : CollatzResearch.WordTrace tailWord_370786 prefixEnd_370786 126927625305394354513195 := by
  unfold tailWord_370786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380919108678280513083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9015784289808748034888141 3380919108678280513083053)
  ·
    refine ⟨1267844665754355192406145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3380919108678280513083053 1267844665754355192406145)
    ·
      refine ⟨950883499315766394304609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1267844665754355192406145 950883499315766394304609)
      ·
        refine ⟨713162624486824795728457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950883499315766394304609 713162624486824795728457)
        ·
          refine ⟨534871968365118596796343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713162624486824795728457 534871968365118596796343)
          ·
            refine ⟨802307952547677895194515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534871968365118596796343 802307952547677895194515)
            ·
              refine ⟨1203461928821516842791773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802307952547677895194515 1203461928821516842791773)
              ·
                refine ⟨451298223308068816046915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203461928821516842791773 451298223308068816046915)
                ·
                  refine ⟨676947334962103224070373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451298223308068816046915 676947334962103224070373)
                  ·
                    refine ⟨126927625305394354513195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676947334962103224070373 126927625305394354513195)
                    ·
                      rfl

theorem cell22_370786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_370786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370786 prefixEnd_370786 := by exact prefixLift 370786
  have htrace : WordTrace (prefixWord ++ tailWord_370786) baseStart_370786 baseEnd_370786 := by
    simpa [prefixWord, tailWord_370786, baseEnd_370786] using wordTrace_append hprefix tailTrace_370786
  have hstable : (prefixWord ++ tailWord_370786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370786).length < 2 ^ (prefixWord ++ tailWord_370786).sum := by decide
  have hdescent : baseEnd_370786 < baseStart_370786 := by decide
  rcases family_descends (prefixWord ++ tailWord_370786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370797 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_370797 : Nat := 118140960795 + 370797 * 2 ^ 59
def prefixEnd_370797 : Nat := 4983230072969 + 3 ^ 40 * 370797 * 2
def baseEnd_370797 : Nat := 126931390830193992488161

theorem tailTrace_370797 : CollatzResearch.WordTrace tailWord_370797 prefixEnd_370797 126931390830193992488161 := by
  unfold tailWord_370797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524077637673270930982645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9016051758448847287321763 13524077637673270930982645)
  ·
    refine ⟨1267882278531869149779623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13524077637673270930982645 1267882278531869149779623)
    ·
      refine ⟨1901823417797803724669435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267882278531869149779623 1901823417797803724669435)
      ·
        refine ⟨2852735126696705587004153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901823417797803724669435 2852735126696705587004153)
        ·
          refine ⟨2139551345022529190253115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852735126696705587004153 2139551345022529190253115)
          ·
            refine ⟨3209327017533793785379673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139551345022529190253115 3209327017533793785379673)
            ·
              refine ⟨2406995263150345339034755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209327017533793785379673 2406995263150345339034755)
              ·
                refine ⟨3610492894725518008552133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406995263150345339034755 3610492894725518008552133)
                ·
                  refine ⟨676967417761034626603525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3610492894725518008552133 676967417761034626603525)
                  ·
                    refine ⟨126931390830193992488161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676967417761034626603525 126931390830193992488161)
                    ·
                      rfl

theorem cell22_370797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_370797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370797 prefixEnd_370797 := by exact prefixLift 370797
  have htrace : WordTrace (prefixWord ++ tailWord_370797) baseStart_370797 baseEnd_370797 := by
    simpa [prefixWord, tailWord_370797, baseEnd_370797] using wordTrace_append hprefix tailTrace_370797
  have hstable : (prefixWord ++ tailWord_370797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370797).length < 2 ^ (prefixWord ++ tailWord_370797).sum := by decide
  have hdescent : baseEnd_370797 < baseStart_370797 := by decide
  rcases family_descends (prefixWord ++ tailWord_370797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370799 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 2, 3]
def baseStart_370799 : Nat := 118140960795 + 370799 * 2 ^ 59
def prefixEnd_370799 : Nat := 4983230072969 + 3 ^ 40 * 370799 * 2
def baseEnd_370799 : Nat := 126932075471066653938155

theorem tailTrace_370799 : CollatzResearch.WordTrace tailWord_370799 prefixEnd_370799 126932075471066653938155 := by
  unfold tailWord_370799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524150583666025272555451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9016100389110683515036967 13524150583666025272555451)
  ·
    refine ⟨20286225875499037908833177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13524150583666025272555451 20286225875499037908833177)
    ·
      refine ⟨15214669406624278431624883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20286225875499037908833177 15214669406624278431624883)
      ·
        refine ⟨22822004109936417647437325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15214669406624278431624883 22822004109936417647437325)
        ·
          refine ⟨8558251541226156617788997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22822004109936417647437325 8558251541226156617788997)
          ·
            refine ⟨1604672163979904365835437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8558251541226156617788997 1604672163979904365835437)
            ·
              refine ⟨601752061492464137188289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1604672163979904365835437 601752061492464137188289)
              ·
                refine ⟨451314046119348102891217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601752061492464137188289 451314046119348102891217)
                ·
                  refine ⟨338485534589511077168413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451314046119348102891217 338485534589511077168413)
                  ·
                    refine ⟨126932075471066653938155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338485534589511077168413 126932075471066653938155)
                    ·
                      rfl

theorem cell22_370799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_370799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370799 prefixEnd_370799 := by exact prefixLift 370799
  have htrace : WordTrace (prefixWord ++ tailWord_370799) baseStart_370799 baseEnd_370799 := by
    simpa [prefixWord, tailWord_370799, baseEnd_370799] using wordTrace_append hprefix tailTrace_370799
  have hstable : (prefixWord ++ tailWord_370799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370799).length < 2 ^ (prefixWord ++ tailWord_370799).sum := by decide
  have hdescent : baseEnd_370799 < baseStart_370799 := by decide
  rcases family_descends (prefixWord ++ tailWord_370799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370846 : List Nat := [4, 3, 1, 1, 4, 1, 8]
def baseStart_370846 : Nat := 118140960795 + 370846 * 2 ^ 59
def prefixEnd_370846 : Nat := 4983230072969 + 3 ^ 40 * 370846 * 2
def baseEnd_370846 : Nat := 4701783871539785111593

theorem tailTrace_370846 : CollatzResearch.WordTrace tailWord_370846 prefixEnd_370846 4701783871539785111593 := by
  unfold tailWord_370846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690733101811969037439549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9017243209663834866344261 1690733101811969037439549)
  ·
    refine ⟨634024913179488389039831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1690733101811969037439549 634024913179488389039831)
    ·
      refine ⟨951037369769232583559747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634024913179488389039831 951037369769232583559747)
      ·
        refine ⟨1426556054653848875339621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951037369769232583559747 1426556054653848875339621)
        ·
          refine ⟨267479260247596664126179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1426556054653848875339621 267479260247596664126179)
          ·
            refine ⟨401218890371394996189269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267479260247596664126179 401218890371394996189269)
            ·
              refine ⟨4701783871539785111593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 401218890371394996189269 4701783871539785111593)
              ·
                rfl

theorem cell22_370846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 8].length) (baseStart_370846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370846 prefixEnd_370846 := by exact prefixLift 370846
  have htrace : WordTrace (prefixWord ++ tailWord_370846) baseStart_370846 baseEnd_370846 := by
    simpa [prefixWord, tailWord_370846, baseEnd_370846] using wordTrace_append hprefix tailTrace_370846
  have hstable : (prefixWord ++ tailWord_370846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370846).length < 2 ^ (prefixWord ++ tailWord_370846).sum := by decide
  have hdescent : baseEnd_370846 < baseStart_370846 := by decide
  rcases family_descends (prefixWord ++ tailWord_370846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370861 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_370861 : Nat := 118140960795 + 370861 * 2 ^ 59
def prefixEnd_370861 : Nat := 4983230072969 + 3 ^ 40 * 370861 * 2
def baseEnd_370861 : Nat := 126953299338119158887965

theorem tailTrace_370861 : CollatzResearch.WordTrace tailWord_370861 prefixEnd_370861 126953299338119158887965 := by
  unfold tailWord_370861
  simp only [CollatzResearch.WordTrace]
  refine ⟨13526411909441409861312437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9017607939627606574208291 13526411909441409861312437)
  ·
    refine ⟨1268101116510132174498041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13526411909441409861312437 1268101116510132174498041)
    ·
      refine ⟨951075837382599130873531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1268101116510132174498041 951075837382599130873531)
      ·
        refine ⟨1426613756073898696310297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951075837382599130873531 1426613756073898696310297)
        ·
          refine ⟨1069960317055424022232723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426613756073898696310297 1069960317055424022232723)
          ·
            refine ⟨1604940475583136033349085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069960317055424022232723 1604940475583136033349085)
            ·
              refine ⟨601852678343676012505907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1604940475583136033349085 601852678343676012505907)
              ·
                refine ⟨902779017515514018758861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601852678343676012505907 902779017515514018758861)
                ·
                  refine ⟨338542131568317757034573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902779017515514018758861 338542131568317757034573)
                  ·
                    refine ⟨126953299338119158887965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338542131568317757034573 126953299338119158887965)
                    ·
                      rfl

theorem cell22_370861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_370861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370861 prefixEnd_370861 := by exact prefixLift 370861
  have htrace : WordTrace (prefixWord ++ tailWord_370861) baseStart_370861 baseEnd_370861 := by
    simpa [prefixWord, tailWord_370861, baseEnd_370861] using wordTrace_append hprefix tailTrace_370861
  have hstable : (prefixWord ++ tailWord_370861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370861).length < 2 ^ (prefixWord ++ tailWord_370861).sum := by decide
  have hdescent : baseEnd_370861 < baseStart_370861 := by decide
  rcases family_descends (prefixWord ++ tailWord_370861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370874 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_370874 : Nat := 118140960795 + 370874 * 2 ^ 59
def prefixEnd_370874 : Nat := 4983230072969 + 3 ^ 40 * 370874 * 2
def baseEnd_370874 : Nat := 42319249834597152770975

theorem tailTrace_370874 : CollatzResearch.WordTrace tailWord_370874 prefixEnd_370874 42319249834597152770975 := by
  unfold tailWord_370874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381721514598578270383919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9017924038929542054357117 3381721514598578270383919)
  ·
    refine ⟨5072582271897867405575879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381721514598578270383919 5072582271897867405575879)
    ·
      refine ⟨7608873407846801108363819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072582271897867405575879 7608873407846801108363819)
      ·
        refine ⟨11413310111770201662545729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7608873407846801108363819 11413310111770201662545729)
        ·
          refine ⟨8559982583827651246909297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11413310111770201662545729 8559982583827651246909297)
          ·
            refine ⟨6419986937870738435181973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8559982583827651246909297 6419986937870738435181973)
            ·
              refine ⟨300936887712690864149155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6419986937870738435181973 300936887712690864149155)
              ·
                refine ⟨451405331569036296223733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300936887712690864149155 451405331569036296223733)
                ·
                  refine ⟨42319249834597152770975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 451405331569036296223733 42319249834597152770975)
                  ·
                    rfl

theorem cell22_370874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_370874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370874 prefixEnd_370874 := by exact prefixLift 370874
  have htrace : WordTrace (prefixWord ++ tailWord_370874) baseStart_370874 baseEnd_370874 := by
    simpa [prefixWord, tailWord_370874, baseEnd_370874] using wordTrace_append hprefix tailTrace_370874
  have hstable : (prefixWord ++ tailWord_370874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370874).length < 2 ^ (prefixWord ++ tailWord_370874).sum := by decide
  have hdescent : baseEnd_370874 < baseStart_370874 := by decide
  rcases family_descends (prefixWord ++ tailWord_370874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370908 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_370908 : Nat := 118140960795 + 370908 * 2 ^ 59
def prefixEnd_370908 : Nat := 4983230072969 + 3 ^ 40 * 370908 * 2
def baseEnd_370908 : Nat := 42323129466208900987607

theorem tailTrace_370908 : CollatzResearch.WordTrace tailWord_370908 prefixEnd_370908 42323129466208900987607 := by
  unfold tailWord_370908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764063070135568444136689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9018750760180757925515585 6764063070135568444136689)
  ·
    refine ⟨5073047302601676333102517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6764063070135568444136689 5073047302601676333102517)
    ·
      refine ⟨475598184618907156228361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5073047302601676333102517 475598184618907156228361)
      ·
        refine ⟨356698638464180367171271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475598184618907156228361 356698638464180367171271)
        ·
          refine ⟨535047957696270550756907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356698638464180367171271 535047957696270550756907)
          ·
            refine ⟨802571936544405826135361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535047957696270550756907 802571936544405826135361)
            ·
              refine ⟨601928952408304369601521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802571936544405826135361 601928952408304369601521)
              ·
                refine ⟨451446714306228277201141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601928952408304369601521 451446714306228277201141)
                ·
                  refine ⟨42323129466208900987607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 451446714306228277201141 42323129466208900987607)
                  ·
                    rfl

theorem cell22_370908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_370908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370908 prefixEnd_370908 := by exact prefixLift 370908
  have htrace : WordTrace (prefixWord ++ tailWord_370908) baseStart_370908 baseEnd_370908 := by
    simpa [prefixWord, tailWord_370908, baseEnd_370908] using wordTrace_append hprefix tailTrace_370908
  have hstable : (prefixWord ++ tailWord_370908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370908).length < 2 ^ (prefixWord ++ tailWord_370908).sum := by decide
  have hdescent : baseEnd_370908 < baseStart_370908 := by decide
  rcases family_descends (prefixWord ++ tailWord_370908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370934 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_370934 : Nat := 118140960795 + 370934 * 2 ^ 59
def prefixEnd_370934 : Nat := 4983230072969 + 3 ^ 40 * 370934 * 2
def baseEnd_370934 : Nat := 126978288729971301812741

theorem tailTrace_370934 : CollatzResearch.WordTrace tailWord_370934 prefixEnd_370934 126978288729971301812741 := by
  unfold tailWord_370934
  simp only [CollatzResearch.WordTrace]
  refine ⟨845567152386058958044991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9019382958784628885813237 845567152386058958044991)
  ·
    refine ⟨1268350728579088437067487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 845567152386058958044991 1268350728579088437067487)
    ·
      refine ⟨1902526092868632655601231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1268350728579088437067487 1902526092868632655601231)
      ·
        refine ⟨2853789139302948983401847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902526092868632655601231 2853789139302948983401847)
        ·
          refine ⟨4280683708954423475102771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853789139302948983401847 4280683708954423475102771)
          ·
            refine ⟨6421025563431635212654157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280683708954423475102771 6421025563431635212654157)
            ·
              refine ⟨2407884586286863204745309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6421025563431635212654157 2407884586286863204745309)
              ·
                refine ⟨902956719857573701779491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2407884586286863204745309 902956719857573701779491)
                ·
                  refine ⟨1354435079786360552669237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902956719857573701779491 1354435079786360552669237)
                  ·
                    refine ⟨126978288729971301812741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1354435079786360552669237 126978288729971301812741)
                    ·
                      rfl

theorem cell22_370934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_370934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370934 prefixEnd_370934 := by exact prefixLift 370934
  have htrace : WordTrace (prefixWord ++ tailWord_370934) baseStart_370934 baseEnd_370934 := by
    simpa [prefixWord, tailWord_370934, baseEnd_370934] using wordTrace_append hprefix tailTrace_370934
  have hstable : (prefixWord ++ tailWord_370934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370934).length < 2 ^ (prefixWord ++ tailWord_370934).sum := by decide
  have hdescent : baseEnd_370934 < baseStart_370934 := by decide
  rcases family_descends (prefixWord ++ tailWord_370934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370977 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_370977 : Nat := 118140960795 + 370977 * 2 ^ 59
def prefixEnd_370977 : Nat := 4983230072969 + 3 ^ 40 * 370977 * 2
def baseEnd_370977 : Nat := 126993008508733522987609

theorem tailTrace_370977 : CollatzResearch.WordTrace tailWord_370977 prefixEnd_370977 126993008508733522987609 := by
  unfold tailWord_370977
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530642777021161672535185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9020428518014107781690123 13530642777021161672535185)
  ·
    refine ⟨10147982082765871254401389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13530642777021161672535185 10147982082765871254401389)
    ·
      refine ⟨3805493281037201720400521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10147982082765871254401389 3805493281037201720400521)
      ·
        refine ⟨2854119960777901290300391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3805493281037201720400521 2854119960777901290300391)
        ·
          refine ⟨4281179941166851935450587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854119960777901290300391 4281179941166851935450587)
          ·
            refine ⟨6421769911750277903175881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281179941166851935450587 6421769911750277903175881)
            ·
              refine ⟨4816327433812708427381911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6421769911750277903175881 4816327433812708427381911)
              ·
                refine ⟨7224491150719062641072867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816327433812708427381911 7224491150719062641072867)
                ·
                  refine ⟨10836736726078593961609301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7224491150719062641072867 10836736726078593961609301)
                  ·
                    refine ⟨126993008508733522987609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10836736726078593961609301 126993008508733522987609)
                    ·
                      rfl

theorem cell22_370977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_370977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_370977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_370977 prefixEnd_370977 := by exact prefixLift 370977
  have htrace : WordTrace (prefixWord ++ tailWord_370977) baseStart_370977 baseEnd_370977 := by
    simpa [prefixWord, tailWord_370977, baseEnd_370977] using wordTrace_append hprefix tailTrace_370977
  have hstable : (prefixWord ++ tailWord_370977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370977).length < 2 ^ (prefixWord ++ tailWord_370977).sum := by decide
  have hdescent : baseEnd_370977 < baseStart_370977 := by decide
  rcases family_descends (prefixWord ++ tailWord_370977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371056 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_371056 : Nat := 118140960795 + 371056 * 2 ^ 59
def prefixEnd_371056 : Nat := 4983230072969 + 3 ^ 40 * 371056 * 2
def baseEnd_371056 : Nat := 127020051823203650262367

theorem tailTrace_371056 : CollatzResearch.WordTrace tailWord_371056 prefixEnd_371056 127020051823203650262367 := by
  unfold tailWord_371056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766762071867479082330511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9022349429156638776440681 6766762071867479082330511)
  ·
    refine ⟨10150143107801218623495767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6766762071867479082330511 10150143107801218623495767)
    ·
      refine ⟨15225214661701827935243651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150143107801218623495767 15225214661701827935243651)
      ·
        refine ⟨22837821992552741902865477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225214661701827935243651 22837821992552741902865477)
        ·
          refine ⟨4282091623603639106787277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22837821992552741902865477 4282091623603639106787277)
          ·
            refine ⟨1605784358851364665045229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4282091623603639106787277 1605784358851364665045229)
            ·
              refine ⟨602169134569261749391961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605784358851364665045229 602169134569261749391961)
              ·
                refine ⟨451626850926946312043971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602169134569261749391961 451626850926946312043971)
                ·
                  refine ⟨677440276390419468065957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451626850926946312043971 677440276390419468065957)
                  ·
                    refine ⟨127020051823203650262367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 677440276390419468065957 127020051823203650262367)
                    ·
                      rfl

theorem cell22_371056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_371056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371056 prefixEnd_371056 := by exact prefixLift 371056
  have htrace : WordTrace (prefixWord ++ tailWord_371056) baseStart_371056 baseEnd_371056 := by
    simpa [prefixWord, tailWord_371056, baseEnd_371056] using wordTrace_append hprefix tailTrace_371056
  have hstable : (prefixWord ++ tailWord_371056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371056).length < 2 ^ (prefixWord ++ tailWord_371056).sum := by decide
  have hdescent : baseEnd_371056 < baseStart_371056 := by decide
  rcases family_descends (prefixWord ++ tailWord_371056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371069 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_371069 : Nat := 118140960795 + 371069 * 2 ^ 59
def prefixEnd_371069 : Nat := 4983230072969 + 3 ^ 40 * 371069 * 2
def baseEnd_371069 : Nat := 127024501988875949687327

theorem tailTrace_371069 : CollatzResearch.WordTrace tailWord_371069 prefixEnd_371069 127024501988875949687327 := by
  unfold tailWord_371069
  simp only [CollatzResearch.WordTrace]
  refine ⟨13533998292687861384884261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9022665528458574256589507 13533998292687861384884261)
  ·
    refine ⟨2537624679878974009665799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13533998292687861384884261 2537624679878974009665799)
    ·
      refine ⟨3806437019818461014498699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537624679878974009665799 3806437019818461014498699)
      ·
        refine ⟨5709655529727691521748049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806437019818461014498699 5709655529727691521748049)
        ·
          refine ⟨4282241647295768641311037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5709655529727691521748049 4282241647295768641311037)
          ·
            refine ⟨1605840617735913240491639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4282241647295768641311037 1605840617735913240491639)
            ·
              refine ⟨2408760926603869860737459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605840617735913240491639 2408760926603869860737459)
              ·
                refine ⟨3613141389905804791106189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408760926603869860737459 3613141389905804791106189)
                ·
                  refine ⟨1354928021214676796664821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3613141389905804791106189 1354928021214676796664821)
                  ·
                    refine ⟨127024501988875949687327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1354928021214676796664821 127024501988875949687327)
                    ·
                      rfl

theorem cell22_371069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_371069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371069 prefixEnd_371069 := by exact prefixLift 371069
  have htrace : WordTrace (prefixWord ++ tailWord_371069) baseStart_371069 baseEnd_371069 := by
    simpa [prefixWord, tailWord_371069, baseEnd_371069] using wordTrace_append hprefix tailTrace_371069
  have hstable : (prefixWord ++ tailWord_371069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371069).length < 2 ^ (prefixWord ++ tailWord_371069).sum := by decide
  have hdescent : baseEnd_371069 < baseStart_371069 := by decide
  rcases family_descends (prefixWord ++ tailWord_371069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371124 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_371124 : Nat := 118140960795 + 371124 * 2 ^ 59
def prefixEnd_371124 : Nat := 4983230072969 + 3 ^ 40 * 371124 * 2
def baseEnd_371124 : Nat := 127043329612874139562159

theorem tailTrace_371124 : CollatzResearch.WordTrace tailWord_371124 prefixEnd_371124 127043329612874139562159 := by
  unfold tailWord_371124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768002153744302889068213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9024002871659070518757617 6768002153744302889068213)
  ·
    refine ⟨634500201913528395850145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6768002153744302889068213 634500201913528395850145)
    ·
      refine ⟨475875151435146296887609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 634500201913528395850145 475875151435146296887609)
      ·
        refine ⟨356906363576359722665707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475875151435146296887609 356906363576359722665707)
        ·
          refine ⟨535359545364539583998561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356906363576359722665707 535359545364539583998561)
          ·
            refine ⟨401519659023404687998921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535359545364539583998561 401519659023404687998921)
            ·
              refine ⟨301139744267553515999191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401519659023404687998921 301139744267553515999191)
              ·
                refine ⟨451709616401330273998787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301139744267553515999191 451709616401330273998787)
                ·
                  refine ⟨677564424601995410998181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451709616401330273998787 677564424601995410998181)
                  ·
                    refine ⟨127043329612874139562159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 677564424601995410998181 127043329612874139562159)
                    ·
                      rfl

theorem cell22_371124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_371124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371124 prefixEnd_371124 := by exact prefixLift 371124
  have htrace : WordTrace (prefixWord ++ tailWord_371124) baseStart_371124 baseEnd_371124 := by
    simpa [prefixWord, tailWord_371124, baseEnd_371124] using wordTrace_append hprefix tailTrace_371124
  have hstable : (prefixWord ++ tailWord_371124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371124).length < 2 ^ (prefixWord ++ tailWord_371124).sum := by decide
  have hdescent : baseEnd_371124 < baseStart_371124 := by decide
  rcases family_descends (prefixWord ++ tailWord_371124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371137 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 4, 3]
def baseStart_371137 : Nat := 118140960795 + 371137 * 2 ^ 59
def prefixEnd_371137 : Nat := 4983230072969 + 3 ^ 40 * 371137 * 2
def baseEnd_371137 : Nat := 127047779778546438987119

theorem tailTrace_371137 : CollatzResearch.WordTrace tailWord_371137 prefixEnd_371137 127047779778546438987119 := by
  unfold tailWord_371137
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536478456441508998359665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9024318970961005998906443 13536478456441508998359665)
  ·
    refine ⟨10152358842331131748769749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13536478456441508998359665 10152358842331131748769749)
    ·
      refine ⟨237945910367135900361791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10152358842331131748769749 237945910367135900361791)
      ·
        refine ⟨356918865550703850542687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237945910367135900361791 356918865550703850542687)
        ·
          refine ⟨535378298326055775814031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356918865550703850542687 535378298326055775814031)
          ·
            refine ⟨803067447489083663721047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535378298326055775814031 803067447489083663721047)
            ·
              refine ⟨1204601171233625495581571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803067447489083663721047 1204601171233625495581571)
              ·
                refine ⟨1806901756850438243372357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204601171233625495581571 1806901756850438243372357)
                ·
                  refine ⟨338794079409457170632317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806901756850438243372357 338794079409457170632317)
                  ·
                    refine ⟨127047779778546438987119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338794079409457170632317 127047779778546438987119)
                    ·
                      rfl

theorem cell22_371137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_371137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371137 prefixEnd_371137 := by exact prefixLift 371137
  have htrace : WordTrace (prefixWord ++ tailWord_371137) baseStart_371137 baseEnd_371137 := by
    simpa [prefixWord, tailWord_371137, baseEnd_371137] using wordTrace_append hprefix tailTrace_371137
  have hstable : (prefixWord ++ tailWord_371137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371137).length < 2 ^ (prefixWord ++ tailWord_371137).sum := by decide
  have hdescent : baseEnd_371137 < baseStart_371137 := by decide
  rcases family_descends (prefixWord ++ tailWord_371137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371182 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_371182 : Nat := 118140960795 + 371182 * 2 ^ 59
def prefixEnd_371182 : Nat := 4983230072969 + 3 ^ 40 * 371182 * 2
def baseEnd_371182 : Nat := 127063184198181321611981

theorem tailTrace_371182 : CollatzResearch.WordTrace tailWord_371182 prefixEnd_371182 127063184198181321611981 := by
  unfold tailWord_371182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692264967659810210468475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9025413160852321122498533 1692264967659810210468475)
  ·
    refine ⟨2538397451489715315702713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692264967659810210468475 2538397451489715315702713)
    ·
      refine ⟨1903798088617286486777035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2538397451489715315702713 1903798088617286486777035)
      ·
        refine ⟨2855697132925929730165553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903798088617286486777035 2855697132925929730165553)
        ·
          refine ⟨2141772849694447297624165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855697132925929730165553 2141772849694447297624165)
          ·
            refine ⟨401582409317708868304531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2141772849694447297624165 401582409317708868304531)
            ·
              refine ⟨602373613976563302456797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401582409317708868304531 602373613976563302456797)
              ·
                refine ⟨225890105241211238421299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602373613976563302456797 225890105241211238421299)
                ·
                  refine ⟨338835157861816857631949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225890105241211238421299 338835157861816857631949)
                  ·
                    refine ⟨127063184198181321611981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338835157861816857631949 127063184198181321611981)
                    ·
                      rfl

theorem cell22_371182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_371182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371182 prefixEnd_371182 := by exact prefixLift 371182
  have htrace : WordTrace (prefixWord ++ tailWord_371182) baseStart_371182 baseEnd_371182 := by
    simpa [prefixWord, tailWord_371182, baseEnd_371182] using wordTrace_append hprefix tailTrace_371182
  have hstable : (prefixWord ++ tailWord_371182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371182).length < 2 ^ (prefixWord ++ tailWord_371182).sum := by decide
  have hdescent : baseEnd_371182 < baseStart_371182 := by decide
  rcases family_descends (prefixWord ++ tailWord_371182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371221 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_371221 : Nat := 118140960795 + 371221 * 2 ^ 59
def prefixEnd_371221 : Nat := 4983230072969 + 3 ^ 40 * 371221 * 2
def baseEnd_371221 : Nat := 127076534695198219886861

theorem tailTrace_371221 : CollatzResearch.WordTrace tailWord_371221 prefixEnd_371221 127076534695198219886861 := by
  unfold tailWord_371221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539542188137191344417517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026361458758127562945011 13539542188137191344417517)
  ·
    refine ⟨5077328320551446754156569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13539542188137191344417517 5077328320551446754156569)
    ·
      refine ⟨3807996240413585065617427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5077328320551446754156569 3807996240413585065617427)
      ·
        refine ⟨5711994360620377598426141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807996240413585065617427 5711994360620377598426141)
        ·
          refine ⟨2141997885232641599409803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5711994360620377598426141 2141997885232641599409803)
          ·
            refine ⟨3212996827848962399114705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141997885232641599409803 3212996827848962399114705)
            ·
              refine ⟨2409747620886721799336029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212996827848962399114705 2409747620886721799336029)
              ·
                refine ⟨903655357832520674751011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2409747620886721799336029 903655357832520674751011)
                ·
                  refine ⟨1355483036748781012126517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903655357832520674751011 1355483036748781012126517)
                  ·
                    refine ⟨127076534695198219886861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1355483036748781012126517 127076534695198219886861)
                    ·
                      rfl

theorem cell22_371221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_371221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371221 prefixEnd_371221 := by exact prefixLift 371221
  have htrace : WordTrace (prefixWord ++ tailWord_371221) baseStart_371221 baseEnd_371221 := by
    simpa [prefixWord, tailWord_371221, baseEnd_371221] using wordTrace_append hprefix tailTrace_371221
  have hstable : (prefixWord ++ tailWord_371221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371221).length < 2 ^ (prefixWord ++ tailWord_371221).sum := by decide
  have hdescent : baseEnd_371221 < baseStart_371221 := by decide
  rcases family_descends (prefixWord ++ tailWord_371221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371311 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_371311 : Nat := 118140960795 + 371311 * 2 ^ 59
def prefixEnd_371311 : Nat := 4983230072969 + 3 ^ 40 * 371311 * 2
def baseEnd_371311 : Nat := 127107343534467985136585

theorem tailTrace_371311 : CollatzResearch.WordTrace tailWord_371311 prefixEnd_371311 127107343534467985136585 := by
  unfold tailWord_371311
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542824757811136715193787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9028549838540757810129191 13542824757811136715193787)
  ·
    refine ⟨20314237136716705072790681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13542824757811136715193787 20314237136716705072790681)
    ·
      refine ⟨15235677852537528804593011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20314237136716705072790681 15235677852537528804593011)
      ·
        refine ⟨22853516778806293206889517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15235677852537528804593011 22853516778806293206889517)
        ·
          refine ⟨8570068792052359952583569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22853516778806293206889517 8570068792052359952583569)
          ·
            refine ⟨6427551594039269964437677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8570068792052359952583569 6427551594039269964437677)
            ·
              refine ⟨2410331847764726236664129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6427551594039269964437677 2410331847764726236664129)
              ·
                refine ⟨1807748885823544677498097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410331847764726236664129 1807748885823544677498097)
                ·
                  refine ⟨1355811664367658508123573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807748885823544677498097 1355811664367658508123573)
                  ·
                    refine ⟨127107343534467985136585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1355811664367658508123573 127107343534467985136585)
                    ·
                      rfl

theorem cell22_371311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_371311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371311 prefixEnd_371311 := by exact prefixLift 371311
  have htrace : WordTrace (prefixWord ++ tailWord_371311) baseStart_371311 baseEnd_371311 := by
    simpa [prefixWord, tailWord_371311, baseEnd_371311] using wordTrace_append hprefix tailTrace_371311
  have hstable : (prefixWord ++ tailWord_371311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371311).length < 2 ^ (prefixWord ++ tailWord_371311).sum := by decide
  have hdescent : baseEnd_371311 < baseStart_371311 := by decide
  rcases family_descends (prefixWord ++ tailWord_371311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371317 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 3, 3]
def baseStart_371317 : Nat := 118140960795 + 371317 * 2 ^ 59
def prefixEnd_371317 : Nat := 4983230072969 + 3 ^ 40 * 371317 * 2
def baseEnd_371317 : Nat := 127109397457085969486567

theorem tailTrace_371317 : CollatzResearch.WordTrace tailWord_371317 prefixEnd_371317 127109397457085969486567 := by
  unfold tailWord_371317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543043595789399739912205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9028695730526266493274803 13543043595789399739912205)
  ·
    refine ⟨5078641348421024902467077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13543043595789399739912205 5078641348421024902467077)
    ·
      refine ⟨952245252828942169212577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5078641348421024902467077 952245252828942169212577)
      ·
        refine ⟨714183939621706626909433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 952245252828942169212577 714183939621706626909433)
        ·
          refine ⟨535637954716279970182075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714183939621706626909433 535637954716279970182075)
          ·
            refine ⟨803456932074419955273113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535637954716279970182075 803456932074419955273113)
            ·
              refine ⟨602592699055814966454835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803456932074419955273113 602592699055814966454835)
              ·
                refine ⟨903889048583722449682253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602592699055814966454835 903889048583722449682253)
                ·
                  refine ⟨338958393218895918630845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903889048583722449682253 338958393218895918630845)
                  ·
                    refine ⟨127109397457085969486567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338958393218895918630845 127109397457085969486567)
                    ·
                      rfl

theorem cell22_371317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_371317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371317 prefixEnd_371317 := by exact prefixLift 371317
  have htrace : WordTrace (prefixWord ++ tailWord_371317) baseStart_371317 baseEnd_371317 := by
    simpa [prefixWord, tailWord_371317, baseEnd_371317] using wordTrace_append hprefix tailTrace_371317
  have hstable : (prefixWord ++ tailWord_371317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371317).length < 2 ^ (prefixWord ++ tailWord_371317).sum := by decide
  have hdescent : baseEnd_371317 < baseStart_371317 := by decide
  rcases family_descends (prefixWord ++ tailWord_371317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371388 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_371388 : Nat := 118140960795 + 371388 * 2 ^ 59
def prefixEnd_371388 : Nat := 4983230072969 + 3 ^ 40 * 371388 * 2
def baseEnd_371388 : Nat := 127133702208065450961349

theorem tailTrace_371388 : CollatzResearch.WordTrace tailWord_371388 prefixEnd_371388 127133702208065450961349 := by
  unfold tailWord_371388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772816589266089432873409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9030422119021452577164545 6772816589266089432873409)
  ·
    refine ⟨5079612441949567074655057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6772816589266089432873409 5079612441949567074655057)
    ·
      refine ⟨3809709331462175305991293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5079612441949567074655057 3809709331462175305991293)
      ·
        refine ⟨1428640999298315739746735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3809709331462175305991293 1428640999298315739746735)
        ·
          refine ⟨2142961498947473609620103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428640999298315739746735 2142961498947473609620103)
          ·
            refine ⟨3214442248421210414430155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142961498947473609620103 3214442248421210414430155)
            ·
              refine ⟨4821663372631815621645233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214442248421210414430155 4821663372631815621645233)
              ·
                refine ⟨3616247529473861716233925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821663372631815621645233 3616247529473861716233925)
                ·
                  refine ⟨678046411776349071793861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3616247529473861716233925 678046411776349071793861)
                  ·
                    refine ⟨127133702208065450961349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678046411776349071793861 127133702208065450961349)
                    ·
                      rfl

theorem cell22_371388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_371388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371388 prefixEnd_371388 := by exact prefixLift 371388
  have htrace : WordTrace (prefixWord ++ tailWord_371388) baseStart_371388 baseEnd_371388 := by
    simpa [prefixWord, tailWord_371388, baseEnd_371388] using wordTrace_append hprefix tailTrace_371388
  have hstable : (prefixWord ++ tailWord_371388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371388).length < 2 ^ (prefixWord ++ tailWord_371388).sum := by decide
  have hdescent : baseEnd_371388 < baseStart_371388 := by decide
  rcases family_descends (prefixWord ++ tailWord_371388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371448 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_371448 : Nat := 118140960795 + 371448 * 2 ^ 59
def prefixEnd_371448 : Nat := 4983230072969 + 3 ^ 40 * 371448 * 2
def baseEnd_371448 : Nat := 42384747144748431487055

theorem tailTrace_371448 : CollatzResearch.WordTrace tailWord_371448 prefixEnd_371448 42384747144748431487055 := by
  unfold tailWord_371448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773910779157404556465499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9031881038876539408620665 6773910779157404556465499)
  ·
    refine ⟨10160866168736106834698249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773910779157404556465499 10160866168736106834698249)
    ·
      refine ⟨7620649626552080126023687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10160866168736106834698249 7620649626552080126023687)
      ·
        refine ⟨11430974439828120189035531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7620649626552080126023687 11430974439828120189035531)
        ·
          refine ⟨17146461659742180283553297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11430974439828120189035531 17146461659742180283553297)
          ·
            refine ⟨12859846244806635212664973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17146461659742180283553297 12859846244806635212664973)
            ·
              refine ⟨4822442341802488204749365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12859846244806635212664973 4822442341802488204749365)
              ·
                refine ⟨452103969543983269195253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4822442341802488204749365 452103969543983269195253)
                ·
                  refine ⟨42384747144748431487055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452103969543983269195253 42384747144748431487055)
                  ·
                    rfl

theorem cell22_371448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_371448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371448 prefixEnd_371448 := by exact prefixLift 371448
  have htrace : WordTrace (prefixWord ++ tailWord_371448) baseStart_371448 baseEnd_371448 := by
    simpa [prefixWord, tailWord_371448, baseEnd_371448] using wordTrace_append hprefix tailTrace_371448
  have hstable : (prefixWord ++ tailWord_371448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371448).length < 2 ^ (prefixWord ++ tailWord_371448).sum := by decide
  have hdescent : baseEnd_371448 < baseStart_371448 := by decide
  rcases family_descends (prefixWord ++ tailWord_371448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371523 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_371523 : Nat := 118140960795 + 371523 * 2 ^ 59
def prefixEnd_371523 : Nat := 4983230072969 + 3 ^ 40 * 371523 * 2
def baseEnd_371523 : Nat := 127179915466970098835935

theorem tailTrace_371523 : CollatzResearch.WordTrace tailWord_371523 prefixEnd_371523 127179915466970098835935 := by
  unfold tailWord_371523
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550557033043096921911223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9033704688695397947940815 13550557033043096921911223)
  ·
    refine ⟨20325835549564645382866835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13550557033043096921911223 20325835549564645382866835)
    ·
      refine ⟨30488753324346968074300253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20325835549564645382866835 30488753324346968074300253)
      ·
        refine ⟨11433282496630113027862595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30488753324346968074300253 11433282496630113027862595)
        ·
          refine ⟨17149923744945169541793893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11433282496630113027862595 17149923744945169541793893)
          ·
            refine ⟨3215610702177219289086355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17149923744945169541793893 3215610702177219289086355)
            ·
              refine ⟨4823416053265828933629533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215610702177219289086355 4823416053265828933629533)
              ·
                refine ⟨1808781019974685850111075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4823416053265828933629533 1808781019974685850111075)
                ·
                  refine ⟨2713171529962028775166613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808781019974685850111075 2713171529962028775166613)
                  ·
                    refine ⟨127179915466970098835935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2713171529962028775166613 127179915466970098835935)
                    ·
                      rfl

theorem cell22_371523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_371523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371523 prefixEnd_371523 := by exact prefixLift 371523
  have htrace : WordTrace (prefixWord ++ tailWord_371523) baseStart_371523 baseEnd_371523 := by
    simpa [prefixWord, tailWord_371523, baseEnd_371523] using wordTrace_append hprefix tailTrace_371523
  have hstable : (prefixWord ++ tailWord_371523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371523).length < 2 ^ (prefixWord ++ tailWord_371523).sum := by decide
  have hdescent : baseEnd_371523 < baseStart_371523 := by decide
  rcases family_descends (prefixWord ++ tailWord_371523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371553 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_371553 : Nat := 118140960795 + 371553 * 2 ^ 59
def prefixEnd_371553 : Nat := 4983230072969 + 3 ^ 40 * 371553 * 2
def baseEnd_371553 : Nat := 127190185080060020585843

theorem tailTrace_371553 : CollatzResearch.WordTrace tailWord_371553 prefixEnd_371553 127190185080060020585843 := by
  unfold tailWord_371553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551651222934412045503313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9034434148622941363668875 13551651222934412045503313)
  ·
    refine ⟨10163738417200809034127485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13551651222934412045503313 10163738417200809034127485)
    ·
      refine ⟨3811401906450303387797807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10163738417200809034127485 3811401906450303387797807)
      ·
        refine ⟨5717102859675455081696711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811401906450303387797807 5717102859675455081696711)
        ·
          refine ⟨8575654289513182622545067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717102859675455081696711 8575654289513182622545067)
          ·
            refine ⟨12863481434269773933817601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575654289513182622545067 12863481434269773933817601)
            ·
              refine ⟨9647611075702330450363201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12863481434269773933817601 9647611075702330450363201)
              ·
                refine ⟨7235708306776747837772401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9647611075702330450363201 7235708306776747837772401)
                ·
                  refine ⟨5426781230082560878329301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235708306776747837772401 5426781230082560878329301)
                  ·
                    refine ⟨127190185080060020585843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5426781230082560878329301 127190185080060020585843)
                    ·
                      rfl

theorem cell22_371553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_371553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371553 prefixEnd_371553 := by exact prefixLift 371553
  have htrace : WordTrace (prefixWord ++ tailWord_371553) baseStart_371553 baseEnd_371553 := by
    simpa [prefixWord, tailWord_371553, baseEnd_371553] using wordTrace_append hprefix tailTrace_371553
  have hstable : (prefixWord ++ tailWord_371553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371553).length < 2 ^ (prefixWord ++ tailWord_371553).sum := by decide
  have hdescent : baseEnd_371553 < baseStart_371553 := by decide
  rcases family_descends (prefixWord ++ tailWord_371553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371555 : List Nat := [1, 1, 1, 5, 3, 2, 2, 7]
def baseStart_371555 : Nat := 118140960795 + 371555 * 2 ^ 59
def prefixEnd_371555 : Nat := 4983230072969 + 3 ^ 40 * 371555 * 2
def baseEnd_371555 : Nat := 14132318857881409115093

theorem tailTrace_371555 : CollatzResearch.WordTrace tailWord_371555 prefixEnd_371555 14132318857881409115093 := by
  unfold tailWord_371555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551724168927166387076119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9034482779284777591384079 13551724168927166387076119)
  ·
    refine ⟨20327586253390749580614179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13551724168927166387076119 20327586253390749580614179)
    ·
      refine ⟨30491379380086124370921269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20327586253390749580614179 30491379380086124370921269)
      ·
        refine ⟨2858566816883074159773869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30491379380086124370921269 2858566816883074159773869)
        ·
          refine ⟨1071962556331152809915201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2858566816883074159773869 1071962556331152809915201)
          ·
            refine ⟨803971917248364607436401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071962556331152809915201 803971917248364607436401)
            ·
              refine ⟨602978937936273455577301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803971917248364607436401 602978937936273455577301)
              ·
                refine ⟨14132318857881409115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 602978937936273455577301 14132318857881409115093)
                ·
                  rfl

theorem cell22_371555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 7].length) (baseStart_371555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371555 prefixEnd_371555 := by exact prefixLift 371555
  have htrace : WordTrace (prefixWord ++ tailWord_371555) baseStart_371555 baseEnd_371555 := by
    simpa [prefixWord, tailWord_371555, baseEnd_371555] using wordTrace_append hprefix tailTrace_371555
  have hstable : (prefixWord ++ tailWord_371555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371555).length < 2 ^ (prefixWord ++ tailWord_371555).sum := by decide
  have hdescent : baseEnd_371555 < baseStart_371555 := by decide
  rcases family_descends (prefixWord ++ tailWord_371555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371559 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 2, 3]
def baseStart_371559 : Nat := 118140960795 + 371559 * 2 ^ 59
def prefixEnd_371559 : Nat := 4983230072969 + 3 ^ 40 * 371559 * 2
def baseEnd_371559 : Nat := 127192239002678004935825

theorem tailTrace_371559 : CollatzResearch.WordTrace tailWord_371559 prefixEnd_371559 127192239002678004935825 := by
  unfold tailWord_371559
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551870060912675070221731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9034580040608450046814487 13551870060912675070221731)
  ·
    refine ⟨20327805091369012605332597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13551870060912675070221731 20327805091369012605332597)
    ·
      refine ⟨1905731727315844931749931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20327805091369012605332597 1905731727315844931749931)
      ·
        refine ⟨2858597590973767397624897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905731727315844931749931 2858597590973767397624897)
        ·
          refine ⟨2143948193230325548218673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858597590973767397624897 2143948193230325548218673)
          ·
            refine ⟨1607961144922744161164005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143948193230325548218673 1607961144922744161164005)
            ·
              refine ⟨301492714673014530218251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1607961144922744161164005 301492714673014530218251)
              ·
                refine ⟨452239072009521795327377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301492714673014530218251 452239072009521795327377)
                ·
                  refine ⟨339179304007141346495533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452239072009521795327377 339179304007141346495533)
                  ·
                    refine ⟨127192239002678004935825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339179304007141346495533 127192239002678004935825)
                    ·
                      rfl

theorem cell22_371559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_371559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371559 prefixEnd_371559 := by exact prefixLift 371559
  have htrace : WordTrace (prefixWord ++ tailWord_371559) baseStart_371559 baseEnd_371559 := by
    simpa [prefixWord, tailWord_371559, baseEnd_371559] using wordTrace_append hprefix tailTrace_371559
  have hstable : (prefixWord ++ tailWord_371559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371559).length < 2 ^ (prefixWord ++ tailWord_371559).sum := by decide
  have hdescent : baseEnd_371559 < baseStart_371559 := by decide
  rcases family_descends (prefixWord ++ tailWord_371559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371574 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_371574 : Nat := 118140960795 + 371574 * 2 ^ 59
def prefixEnd_371574 : Nat := 4983230072969 + 3 ^ 40 * 371574 * 2
def baseEnd_371574 : Nat := 127197373809222965810779

theorem tailTrace_371574 : CollatzResearch.WordTrace tailWord_371574 prefixEnd_371574 127197373809222965810779 := by
  unfold tailWord_371574
  simp only [CollatzResearch.WordTrace]
  refine ⟨847026072241145789501111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9034944770572221754678517 847026072241145789501111)
  ·
    refine ⟨1270539108361718684251667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847026072241145789501111 1270539108361718684251667)
    ·
      refine ⟨1905808662542578026377501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270539108361718684251667 1905808662542578026377501)
      ·
        refine ⟨714678248453466759891563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1905808662542578026377501 714678248453466759891563)
        ·
          refine ⟨1072017372680200139837345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714678248453466759891563 1072017372680200139837345)
          ·
            refine ⟨804013029510150104878009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072017372680200139837345 804013029510150104878009)
            ·
              refine ⟨603009772132612578658507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804013029510150104878009 603009772132612578658507)
              ·
                refine ⟨904514658198918867987761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603009772132612578658507 904514658198918867987761)
                ·
                  refine ⟨678385993649189150990821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904514658198918867987761 678385993649189150990821)
                  ·
                    refine ⟨127197373809222965810779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678385993649189150990821 127197373809222965810779)
                    ·
                      rfl

theorem cell22_371574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_371574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371574 prefixEnd_371574 := by exact prefixLift 371574
  have htrace : WordTrace (prefixWord ++ tailWord_371574) baseStart_371574 baseEnd_371574 := by
    simpa [prefixWord, tailWord_371574, baseEnd_371574] using wordTrace_append hprefix tailTrace_371574
  have hstable : (prefixWord ++ tailWord_371574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371574).length < 2 ^ (prefixWord ++ tailWord_371574).sum := by decide
  have hdescent : baseEnd_371574 < baseStart_371574 := by decide
  rcases family_descends (prefixWord ++ tailWord_371574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371583 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 9]
def baseStart_371583 : Nat := 118140960795 + 371583 * 2 ^ 59
def prefixEnd_371583 : Nat := 4983230072969 + 3 ^ 40 * 371583 * 2
def baseEnd_371583 : Nat := 42400151564383314111917

theorem tailTrace_371583 : CollatzResearch.WordTrace tailWord_371583 prefixEnd_371583 42400151564383314111917 := by
  unfold tailWord_371583
  simp only [CollatzResearch.WordTrace]
  refine ⟨13552745412825727169095403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9035163608550484779396935 13552745412825727169095403)
  ·
    refine ⟨20329118119238590753643105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13552745412825727169095403 20329118119238590753643105)
    ·
      refine ⟨15246838589428943065232329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20329118119238590753643105 15246838589428943065232329)
      ·
        refine ⟨11435128942071707298924247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15246838589428943065232329 11435128942071707298924247)
        ·
          refine ⟨17152693413107560948386371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11435128942071707298924247 17152693413107560948386371)
          ·
            refine ⟨25729040119661341422579557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17152693413107560948386371 25729040119661341422579557)
            ·
              refine ⟨4824195022436501516733667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25729040119661341422579557 4824195022436501516733667)
              ·
                refine ⟨7236292533654752275100501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824195022436501516733667 7236292533654752275100501)
                ·
                  refine ⟨42400151564383314111917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7236292533654752275100501 42400151564383314111917)
                  ·
                    rfl

theorem cell22_371583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_371583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371583 prefixEnd_371583 := by exact prefixLift 371583
  have htrace : WordTrace (prefixWord ++ tailWord_371583) baseStart_371583 baseEnd_371583 := by
    simpa [prefixWord, tailWord_371583, baseEnd_371583] using wordTrace_append hprefix tailTrace_371583
  have hstable : (prefixWord ++ tailWord_371583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371583).length < 2 ^ (prefixWord ++ tailWord_371583).sum := by decide
  have hdescent : baseEnd_371583 < baseStart_371583 := by decide
  rcases family_descends (prefixWord ++ tailWord_371583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371606 : List Nat := [5, 3, 1, 1, 1, 3, 1, 7]
def baseStart_371606 : Nat := 118140960795 + 371606 * 2 ^ 59
def prefixEnd_371606 : Nat := 4983230072969 + 3 ^ 40 * 371606 * 2
def baseEnd_371606 : Nat := 14134258673687283223409

theorem tailTrace_371606 : CollatzResearch.WordTrace tailWord_371606 prefixEnd_371606 14134258673687283223409 := by
  unfold tailWord_371606
  simp only [CollatzResearch.WordTrace]
  refine ⟨847099018233900131073917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9035722861161601398121781 847099018233900131073917)
  ·
    refine ⟨317662131837712549152719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 847099018233900131073917 317662131837712549152719)
    ·
      refine ⟨476493197756568823729079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317662131837712549152719 476493197756568823729079)
      ·
        refine ⟨714739796634853235593619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476493197756568823729079 714739796634853235593619)
        ·
          refine ⟨1072109694952279853390429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714739796634853235593619 1072109694952279853390429)
          ·
            refine ⟨402041135607104945021411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1072109694952279853390429 402041135607104945021411)
            ·
              refine ⟨603061703410657417532117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402041135607104945021411 603061703410657417532117)
              ·
                refine ⟨14134258673687283223409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 603061703410657417532117 14134258673687283223409)
                ·
                  rfl

theorem cell22_371606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_371606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371606 prefixEnd_371606 := by exact prefixLift 371606
  have htrace : WordTrace (prefixWord ++ tailWord_371606) baseStart_371606 baseEnd_371606 := by
    simpa [prefixWord, tailWord_371606, baseEnd_371606] using wordTrace_append hprefix tailTrace_371606
  have hstable : (prefixWord ++ tailWord_371606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371606).length < 2 ^ (prefixWord ++ tailWord_371606).sum := by decide
  have hdescent : baseEnd_371606 < baseStart_371606 := by decide
  rcases family_descends (prefixWord ++ tailWord_371606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371615 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_371615 : Nat := 118140960795 + 371615 * 2 ^ 59
def prefixEnd_371615 : Nat := 4983230072969 + 3 ^ 40 * 371615 * 2
def baseEnd_371615 : Nat := 127211408947112525535653

theorem tailTrace_371615 : CollatzResearch.WordTrace tailWord_371615 prefixEnd_371615 127211408947112525535653 := by
  unfold tailWord_371615
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553912548709796634260299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9035941699139864422840199 13553912548709796634260299)
  ·
    refine ⟨20330868823064694951390449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13553912548709796634260299 20330868823064694951390449)
    ·
      refine ⟨15248151617298521213542837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20330868823064694951390449 15248151617298521213542837)
      ·
        refine ⟨1429514214121736363769641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15248151617298521213542837 1429514214121736363769641)
        ·
          refine ⟨1072135660591302272827231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1429514214121736363769641 1072135660591302272827231)
          ·
            refine ⟨1608203490886953409240847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072135660591302272827231 1608203490886953409240847)
            ·
              refine ⟨2412305236330430113861271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608203490886953409240847 2412305236330430113861271)
              ·
                refine ⟨3618457854495645170791907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412305236330430113861271 3618457854495645170791907)
                ·
                  refine ⟨5427686781743467756187861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618457854495645170791907 5427686781743467756187861)
                  ·
                    refine ⟨127211408947112525535653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5427686781743467756187861 127211408947112525535653)
                    ·
                      rfl

theorem cell22_371615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_371615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371615 prefixEnd_371615 := by exact prefixLift 371615
  have htrace : WordTrace (prefixWord ++ tailWord_371615) baseStart_371615 baseEnd_371615 := by
    simpa [prefixWord, tailWord_371615, baseEnd_371615] using wordTrace_append hprefix tailTrace_371615
  have hstable : (prefixWord ++ tailWord_371615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371615).length < 2 ^ (prefixWord ++ tailWord_371615).sum := by decide
  have hdescent : baseEnd_371615 < baseStart_371615 := by decide
  rcases family_descends (prefixWord ++ tailWord_371615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371617 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 5]
def baseStart_371617 : Nat := 118140960795 + 371617 * 2 ^ 59
def prefixEnd_371617 : Nat := 4983230072969 + 3 ^ 40 * 371617 * 2
def baseEnd_371617 : Nat := 42404031195995062328549

theorem tailTrace_371617 : CollatzResearch.WordTrace tailWord_371617 prefixEnd_371617 42404031195995062328549 := by
  unfold tailWord_371617
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553985494702550975833105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9035990329801700650555403 13553985494702550975833105)
  ·
    refine ⟨10165489121026913231874829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13553985494702550975833105 10165489121026913231874829)
    ·
      refine ⟨3812058420385092461953061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10165489121026913231874829 3812058420385092461953061)
      ·
        refine ⟨714760953822204836616199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3812058420385092461953061 714760953822204836616199)
        ·
          refine ⟨1072141430733307254924299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714760953822204836616199 1072141430733307254924299)
          ·
            refine ⟨1608212146099960882386449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072141430733307254924299 1608212146099960882386449)
            ·
              refine ⟨1206159109574970661789837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608212146099960882386449 1206159109574970661789837)
              ·
                refine ⟨452309666090613998171189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1206159109574970661789837 452309666090613998171189)
                ·
                  refine ⟨42404031195995062328549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452309666090613998171189 42404031195995062328549)
                  ·
                    rfl

theorem cell22_371617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_371617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371617 prefixEnd_371617 := by exact prefixLift 371617
  have htrace : WordTrace (prefixWord ++ tailWord_371617) baseStart_371617 baseEnd_371617 := by
    simpa [prefixWord, tailWord_371617, baseEnd_371617] using wordTrace_append hprefix tailTrace_371617
  have hstable : (prefixWord ++ tailWord_371617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371617).length < 2 ^ (prefixWord ++ tailWord_371617).sum := by decide
  have hdescent : baseEnd_371617 < baseStart_371617 := by decide
  rcases family_descends (prefixWord ++ tailWord_371617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371662 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_371662 : Nat := 118140960795 + 371662 * 2 ^ 59
def prefixEnd_371662 : Nat := 4983230072969 + 3 ^ 40 * 371662 * 2
def baseEnd_371662 : Nat := 42409166002540023203503

theorem tailTrace_371662 : CollatzResearch.WordTrace tailWord_371662 prefixEnd_371662 42409166002540023203503 := by
  unfold tailWord_371662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694453347442440457652655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9037084519693015774147493 1694453347442440457652655)
  ·
    refine ⟨2541680021163660686478983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694453347442440457652655 2541680021163660686478983)
    ·
      refine ⟨3812520031745491029718475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2541680021163660686478983 3812520031745491029718475)
      ·
        refine ⟨5718780047618236544577713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812520031745491029718475 5718780047618236544577713)
        ·
          refine ⟨4289085035713677408433285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718780047618236544577713 4289085035713677408433285)
          ·
            refine ⟨804203444196314514081241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4289085035713677408433285 804203444196314514081241)
            ·
              refine ⟨603152583147235885560931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804203444196314514081241 603152583147235885560931)
              ·
                refine ⟨904728874720853828341397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603152583147235885560931 904728874720853828341397)
                ·
                  refine ⟨42409166002540023203503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 904728874720853828341397 42409166002540023203503)
                  ·
                    rfl

theorem cell22_371662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_371662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371662 prefixEnd_371662 := by exact prefixLift 371662
  have htrace : WordTrace (prefixWord ++ tailWord_371662) baseStart_371662 baseEnd_371662 := by
    simpa [prefixWord, tailWord_371662, baseEnd_371662] using wordTrace_append hprefix tailTrace_371662
  have hstable : (prefixWord ++ tailWord_371662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371662).length < 2 ^ (prefixWord ++ tailWord_371662).sum := by decide
  have hdescent : baseEnd_371662 < baseStart_371662 := by decide
  rcases family_descends (prefixWord ++ tailWord_371662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371769 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 5]
def baseStart_371769 : Nat := 118140960795 + 371769 * 2 ^ 59
def prefixEnd_371769 : Nat := 4983230072969 + 3 ^ 40 * 371769 * 2
def baseEnd_371769 : Nat := 42421375431435819061727

theorem tailTrace_371769 : CollatzResearch.WordTrace tailWord_371769 prefixEnd_371769 42421375431435819061727 := by
  unfold tailWord_371769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559529390151880935366361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9039686260101253956910907 13559529390151880935366361)
  ·
    refine ⟨10169647042613910701524771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13559529390151880935366361 10169647042613910701524771)
    ·
      refine ⟨15254470563920866052287157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169647042613910701524771 15254470563920866052287157)
      ·
        refine ⟨1430106615367581192401921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15254470563920866052287157 1430106615367581192401921)
        ·
          refine ⟨1072579961525685894301441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430106615367581192401921 1072579961525685894301441)
          ·
            refine ⟨804434971144264420726081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072579961525685894301441 804434971144264420726081)
            ·
              refine ⟨603326228358198315544561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804434971144264420726081 603326228358198315544561)
              ·
                refine ⟨452494671268648736658421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603326228358198315544561 452494671268648736658421)
                ·
                  refine ⟨42421375431435819061727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452494671268648736658421 42421375431435819061727)
                  ·
                    rfl

theorem cell22_371769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_371769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371769 prefixEnd_371769 := by exact prefixLift 371769
  have htrace : WordTrace (prefixWord ++ tailWord_371769) baseStart_371769 baseEnd_371769 := by
    simpa [prefixWord, tailWord_371769, baseEnd_371769] using wordTrace_append hprefix tailTrace_371769
  have hstable : (prefixWord ++ tailWord_371769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371769).length < 2 ^ (prefixWord ++ tailWord_371769).sum := by decide
  have hdescent : baseEnd_371769 < baseStart_371769 := by decide
  rcases family_descends (prefixWord ++ tailWord_371769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371773 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_371773 : Nat := 118140960795 + 371773 * 2 ^ 59
def prefixEnd_371773 : Nat := 4983230072969 + 3 ^ 40 * 371773 * 2
def baseEnd_371773 : Nat := 127265495576052780085169

theorem tailTrace_371773 : CollatzResearch.WordTrace tailWord_371773 prefixEnd_371773 127265495576052780085169 := by
  unfold tailWord_371773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559675282137389618511973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9039783521424926412341315 13559675282137389618511973)
  ·
    refine ⟨2542439115400760553470995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13559675282137389618511973 2542439115400760553470995)
    ·
      refine ⟨3813658673101140830206493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542439115400760553470995 3813658673101140830206493)
      ·
        refine ⟨1430122002412927811327435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3813658673101140830206493 1430122002412927811327435)
        ·
          refine ⟨2145183003619391716991153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430122002412927811327435 2145183003619391716991153)
          ·
            refine ⟨1608887252714543787743365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145183003619391716991153 1608887252714543787743365)
            ·
              refine ⟨301666359883976960201881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1608887252714543787743365 301666359883976960201881)
              ·
                refine ⟨226249769912982720151411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301666359883976960201881 226249769912982720151411)
                ·
                  refine ⟨339374654869474080227117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226249769912982720151411 339374654869474080227117)
                  ·
                    refine ⟨127265495576052780085169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339374654869474080227117 127265495576052780085169)
                    ·
                      rfl

theorem cell22_371773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_371773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371773 prefixEnd_371773 := by exact prefixLift 371773
  have htrace : WordTrace (prefixWord ++ tailWord_371773) baseStart_371773 baseEnd_371773 := by
    simpa [prefixWord, tailWord_371773, baseEnd_371773] using wordTrace_append hprefix tailTrace_371773
  have hstable : (prefixWord ++ tailWord_371773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371773).length < 2 ^ (prefixWord ++ tailWord_371773).sum := by decide
  have hdescent : baseEnd_371773 < baseStart_371773 := by decide
  rcases family_descends (prefixWord ++ tailWord_371773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371797 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 6]
def baseStart_371797 : Nat := 118140960795 + 371797 * 2 ^ 59
def prefixEnd_371797 : Nat := 4983230072969 + 3 ^ 40 * 371797 * 2
def baseEnd_371797 : Nat := 42424570422174905828365

theorem tailTrace_371797 : CollatzResearch.WordTrace tailWord_371797 prefixEnd_371797 42424570422174905828365 := by
  unfold tailWord_371797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560550634050441717385645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9040367089366961144923763 13560550634050441717385645)
  ·
    refine ⟨5085206487768915644019617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13560550634050441717385645 5085206487768915644019617)
    ·
      refine ⟨3813904865826686733014713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5085206487768915644019617 3813904865826686733014713)
      ·
        refine ⟨2860428649370015049761035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813904865826686733014713 2860428649370015049761035)
        ·
          refine ⟨4290642974055022574641553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860428649370015049761035 4290642974055022574641553)
          ·
            refine ⟨3217982230541266930981165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290642974055022574641553 3217982230541266930981165)
            ·
              refine ⟨1206743336452975099117937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3217982230541266930981165 1206743336452975099117937)
              ·
                refine ⟨905057502339731324338453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206743336452975099117937 905057502339731324338453)
                ·
                  refine ⟨42424570422174905828365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 905057502339731324338453 42424570422174905828365)
                  ·
                    rfl

theorem cell22_371797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_371797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371797 prefixEnd_371797 := by exact prefixLift 371797
  have htrace : WordTrace (prefixWord ++ tailWord_371797) baseStart_371797 baseEnd_371797 := by
    simpa [prefixWord, tailWord_371797, baseEnd_371797] using wordTrace_append hprefix tailTrace_371797
  have hstable : (prefixWord ++ tailWord_371797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371797).length < 2 ^ (prefixWord ++ tailWord_371797).sum := by decide
  have hdescent : baseEnd_371797 < baseStart_371797 := by decide
  rcases family_descends (prefixWord ++ tailWord_371797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371887 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 7]
def baseStart_371887 : Nat := 118140960795 + 371887 * 2 ^ 59
def prefixEnd_371887 : Nat := 4983230072969 + 3 ^ 40 * 371887 * 2
def baseEnd_371887 : Nat := 42434840035264827578273

theorem tailTrace_371887 : CollatzResearch.WordTrace tailWord_371887 prefixEnd_371887 42434840035264827578273 := by
  unfold tailWord_371887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13563833203724387088161915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9042555469149591392107943 13563833203724387088161915)
  ·
    refine ⟨20345749805586580632242873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13563833203724387088161915 20345749805586580632242873)
    ·
      refine ⟨15259312354189935474182155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20345749805586580632242873 15259312354189935474182155)
      ·
        refine ⟨22888968531284903211273233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15259312354189935474182155 22888968531284903211273233)
        ·
          refine ⟨17166726398463677408454925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22888968531284903211273233 17166726398463677408454925)
          ·
            refine ⟨6437522399423879028170597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17166726398463677408454925 6437522399423879028170597)
            ·
              refine ⟨1207035449891977317781987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6437522399423879028170597 1207035449891977317781987)
              ·
                refine ⟨1810553174837965976672981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207035449891977317781987 1810553174837965976672981)
                ·
                  refine ⟨42434840035264827578273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1810553174837965976672981 42434840035264827578273)
                  ·
                    rfl

theorem cell22_371887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_371887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371887 prefixEnd_371887 := by exact prefixLift 371887
  have htrace : WordTrace (prefixWord ++ tailWord_371887) baseStart_371887 baseEnd_371887 := by
    simpa [prefixWord, tailWord_371887, baseEnd_371887] using wordTrace_append hprefix tailTrace_371887
  have hstable : (prefixWord ++ tailWord_371887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371887).length < 2 ^ (prefixWord ++ tailWord_371887).sum := by decide
  have hdescent : baseEnd_371887 < baseStart_371887 := by decide
  rcases family_descends (prefixWord ++ tailWord_371887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371891 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 1, 3]
def baseStart_371891 : Nat := 118140960795 + 371891 * 2 ^ 59
def prefixEnd_371891 : Nat := 4983230072969 + 3 ^ 40 * 371891 * 2
def baseEnd_371891 : Nat := 127305889387539805634807

theorem tailTrace_371891 : CollatzResearch.WordTrace tailWord_371891 prefixEnd_371891 127305889387539805634807 := by
  unfold tailWord_371891
  simp only [CollatzResearch.WordTrace]
  refine ⟨13563979095709895771307527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9042652730473263847538351 13563979095709895771307527)
  ·
    refine ⟨20345968643564843656961291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13563979095709895771307527 20345968643564843656961291)
    ·
      refine ⟨30518952965347265485441937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20345968643564843656961291 30518952965347265485441937)
      ·
        refine ⟨22889214724010449114081453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30518952965347265485441937 22889214724010449114081453)
        ·
          refine ⟨8583455521503918417780545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22889214724010449114081453 8583455521503918417780545)
          ·
            refine ⟨6437591641127938813335409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8583455521503918417780545 6437591641127938813335409)
            ·
              refine ⟨4828193730845954110001557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437591641127938813335409 4828193730845954110001557)
              ·
                refine ⟨226321581133404098906323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4828193730845954110001557 226321581133404098906323)
                ·
                  refine ⟨339482371700106148359485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226321581133404098906323 339482371700106148359485)
                  ·
                    refine ⟨127305889387539805634807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339482371700106148359485 127305889387539805634807)
                    ·
                      rfl

theorem cell22_371891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 3].length) (baseStart_371891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371891 prefixEnd_371891 := by exact prefixLift 371891
  have htrace : WordTrace (prefixWord ++ tailWord_371891) baseStart_371891 baseEnd_371891 := by
    simpa [prefixWord, tailWord_371891, baseEnd_371891] using wordTrace_append hprefix tailTrace_371891
  have hstable : (prefixWord ++ tailWord_371891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371891).length < 2 ^ (prefixWord ++ tailWord_371891).sum := by decide
  have hdescent : baseEnd_371891 < baseStart_371891 := by decide
  rcases family_descends (prefixWord ++ tailWord_371891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371966 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_371966 : Nat := 118140960795 + 371966 * 2 ^ 59
def prefixEnd_371966 : Nat := 4983230072969 + 3 ^ 40 * 371966 * 2
def baseEnd_371966 : Nat := 42443854473421536669859

theorem tailTrace_371966 : CollatzResearch.WordTrace tailWord_371966 prefixEnd_371966 42443854473421536669859 := by
  unfold tailWord_371966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695839321304772947535969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9044476380292122386858501 1695839321304772947535969)
  ·
    refine ⟨1271879490978579710651977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1695839321304772947535969 1271879490978579710651977)
    ·
      refine ⟨953909618233934782988983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1271879490978579710651977 953909618233934782988983)
      ·
        refine ⟨1430864427350902174483475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953909618233934782988983 1430864427350902174483475)
        ·
          refine ⟨2146296641026353261725213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430864427350902174483475 2146296641026353261725213)
          ·
            refine ⟨804861240384882473146955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2146296641026353261725213 804861240384882473146955)
            ·
              refine ⟨1207291860577323709720433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804861240384882473146955 1207291860577323709720433)
              ·
                refine ⟨905468895432992782290325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207291860577323709720433 905468895432992782290325)
                ·
                  refine ⟨42443854473421536669859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 905468895432992782290325 42443854473421536669859)
                  ·
                    rfl

theorem cell22_371966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_371966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371966 prefixEnd_371966 := by exact prefixLift 371966
  have htrace : WordTrace (prefixWord ++ tailWord_371966) baseStart_371966 baseEnd_371966 := by
    simpa [prefixWord, tailWord_371966, baseEnd_371966] using wordTrace_append hprefix tailTrace_371966
  have hstable : (prefixWord ++ tailWord_371966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371966).length < 2 ^ (prefixWord ++ tailWord_371966).sum := by decide
  have hdescent : baseEnd_371966 < baseStart_371966 := by decide
  rcases family_descends (prefixWord ++ tailWord_371966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371979 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_371979 : Nat := 118140960795 + 371979 * 2 ^ 59
def prefixEnd_371979 : Nat := 4983230072969 + 3 ^ 40 * 371979 * 2
def baseEnd_371979 : Nat := 127336013585936909434537

theorem tailTrace_371979 : CollatzResearch.WordTrace tailWord_371979 prefixEnd_371979 127336013585936909434537 := by
  unfold tailWord_371979
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567188719391086800510991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9044792479594057867007327 13567188719391086800510991)
  ·
    refine ⟨20350783079086630200766487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13567188719391086800510991 20350783079086630200766487)
    ·
      refine ⟨30526174618629945301149731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20350783079086630200766487 30526174618629945301149731)
      ·
        refine ⟨45789261927944917951724597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30526174618629945301149731 45789261927944917951724597)
        ·
          refine ⟨4292743305744836057974181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45789261927944917951724597 4292743305744836057974181)
          ·
            refine ⟨804889369827156760870159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4292743305744836057974181 804889369827156760870159)
            ·
              refine ⟨1207334054740735141305239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804889369827156760870159 1207334054740735141305239)
              ·
                refine ⟨1811001082111102711957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207334054740735141305239 1811001082111102711957859)
                ·
                  refine ⟨2716501623166654067936789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811001082111102711957859 2716501623166654067936789)
                  ·
                    refine ⟨127336013585936909434537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2716501623166654067936789 127336013585936909434537)
                    ·
                      rfl

theorem cell22_371979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_371979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371979 prefixEnd_371979 := by exact prefixLift 371979
  have htrace : WordTrace (prefixWord ++ tailWord_371979) baseStart_371979 baseEnd_371979 := by
    simpa [prefixWord, tailWord_371979, baseEnd_371979] using wordTrace_append hprefix tailTrace_371979
  have hstable : (prefixWord ++ tailWord_371979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371979).length < 2 ^ (prefixWord ++ tailWord_371979).sum := by decide
  have hdescent : baseEnd_371979 < baseStart_371979 := by decide
  rcases family_descends (prefixWord ++ tailWord_371979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371994 : List Nat := [3, 1, 1, 3, 3, 2, 9]
def baseStart_371994 : Nat := 118140960795 + 371994 * 2 ^ 59
def prefixEnd_371994 : Nat := 4983230072969 + 3 ^ 40 * 371994 * 2
def baseEnd_371994 : Nat := 4716338829351180381833

theorem tailTrace_371994 : CollatzResearch.WordTrace tailWord_371994 prefixEnd_371994 4716338829351180381833 := by
  unfold tailWord_371994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391933953584186090576759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9045157209557829574871357 3391933953584186090576759)
  ·
    refine ⟨5087900930376279135865139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391933953584186090576759 5087900930376279135865139)
    ·
      refine ⟨7631851395564418703797709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087900930376279135865139 7631851395564418703797709)
      ·
        refine ⟨2861944273336657013924141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7631851395564418703797709 2861944273336657013924141)
        ·
          refine ⟨1073229102501246380221553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2861944273336657013924141 1073229102501246380221553)
          ·
            refine ⟨804921826875934785166165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073229102501246380221553 804921826875934785166165)
            ·
              refine ⟨4716338829351180381833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 804921826875934785166165 4716338829351180381833)
              ·
                rfl

theorem cell22_371994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 9].length) (baseStart_371994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_371994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_371994 prefixEnd_371994 := by exact prefixLift 371994
  have htrace : WordTrace (prefixWord ++ tailWord_371994) baseStart_371994 baseEnd_371994 := by
    simpa [prefixWord, tailWord_371994, baseEnd_371994] using wordTrace_append hprefix tailTrace_371994
  have hstable : (prefixWord ++ tailWord_371994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371994).length < 2 ^ (prefixWord ++ tailWord_371994).sum := by decide
  have hdescent : baseEnd_371994 < baseStart_371994 := by decide
  rcases family_descends (prefixWord ++ tailWord_371994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372026 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_372026 : Nat := 118140960795 + 372026 * 2 ^ 59
def prefixEnd_372026 : Nat := 4983230072969 + 3 ^ 40 * 372026 * 2
def baseEnd_372026 : Nat := 127352102646444453509393

theorem tailTrace_372026 : CollatzResearch.WordTrace tailWord_372026 prefixEnd_372026 127352102646444453509393 := by
  unfold tailWord_372026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392225737555203456867983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9045935300147209218314621 3392225737555203456867983)
  ·
    refine ⟨5088338606332805185301975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392225737555203456867983 5088338606332805185301975)
    ·
      refine ⟨7632507909499207777952963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5088338606332805185301975 7632507909499207777952963)
      ·
        refine ⟨11448761864248811666929445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7632507909499207777952963 11448761864248811666929445)
        ·
          refine ⟨2146642849546652187549271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11448761864248811666929445 2146642849546652187549271)
          ·
            refine ⟨3219964274319978281323907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146642849546652187549271 3219964274319978281323907)
            ·
              refine ⟨4829946411479967421985861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219964274319978281323907 4829946411479967421985861)
              ·
                refine ⟨905614952152493891622349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4829946411479967421985861 905614952152493891622349)
                ·
                  refine ⟨339605607057185209358381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905614952152493891622349 339605607057185209358381)
                  ·
                    refine ⟨127352102646444453509393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339605607057185209358381 127352102646444453509393)
                    ·
                      rfl

theorem cell22_372026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_372026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372026 prefixEnd_372026 := by exact prefixLift 372026
  have htrace : WordTrace (prefixWord ++ tailWord_372026) baseStart_372026 baseEnd_372026 := by
    simpa [prefixWord, tailWord_372026, baseEnd_372026] using wordTrace_append hprefix tailTrace_372026
  have hstable : (prefixWord ++ tailWord_372026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372026).length < 2 ^ (prefixWord ++ tailWord_372026).sum := by decide
  have hdescent : baseEnd_372026 < baseStart_372026 := by decide
  rcases family_descends (prefixWord ++ tailWord_372026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372039 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 7]
def baseStart_372039 : Nat := 118140960795 + 372039 * 2 ^ 59
def prefixEnd_372039 : Nat := 4983230072969 + 3 ^ 40 * 372039 * 2
def baseEnd_372039 : Nat := 42452184270705584311451

theorem tailTrace_372039 : CollatzResearch.WordTrace tailWord_372039 prefixEnd_372039 42452184270705584311451 := by
  unfold tailWord_372039
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569377099173717047695171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9046251399449144698463447 13569377099173717047695171)
  ·
    refine ⟨20354065648760575571542757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13569377099173717047695171 20354065648760575571542757)
    ·
      refine ⟨3816387309142607919664267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20354065648760575571542757 3816387309142607919664267)
      ·
        refine ⟨5724580963713911879496401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3816387309142607919664267 5724580963713911879496401)
        ·
          refine ⟨4293435722785433909622301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5724580963713911879496401 4293435722785433909622301)
          ·
            refine ⟨1610038396044537716108363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4293435722785433909622301 1610038396044537716108363)
            ·
              refine ⟨2415057594066806574162545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610038396044537716108363 2415057594066806574162545)
              ·
                refine ⟨1811293195550104930621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415057594066806574162545 1811293195550104930621909)
                ·
                  refine ⟨42452184270705584311451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1811293195550104930621909 42452184270705584311451)
                  ·
                    rfl

theorem cell22_372039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_372039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372039 prefixEnd_372039 := by exact prefixLift 372039
  have htrace : WordTrace (prefixWord ++ tailWord_372039) baseStart_372039 baseEnd_372039 := by
    simpa [prefixWord, tailWord_372039, baseEnd_372039] using wordTrace_append hprefix tailTrace_372039
  have hstable : (prefixWord ++ tailWord_372039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372039).length < 2 ^ (prefixWord ++ tailWord_372039).sum := by decide
  have hdescent : baseEnd_372039 < baseStart_372039 := by decide
  rcases family_descends (prefixWord ++ tailWord_372039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372045 : List Nat := [1, 6, 1, 3, 2, 1, 8]
def baseStart_372045 : Nat := 118140960795 + 372045 * 2 ^ 59
def prefixEnd_372045 : Nat := 4983230072969 + 3 ^ 40 * 372045 * 2
def baseEnd_372045 : Nat := 4716985434619805084605

theorem tailTrace_372045 : CollatzResearch.WordTrace tailWord_372045 prefixEnd_372045 4716985434619805084605 := by
  unfold tailWord_372045
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569595937151980072413589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9046397291434653381609059 13569595937151980072413589)
  ·
    refine ⟨636074809553999065894387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13569595937151980072413589 636074809553999065894387)
    ·
      refine ⟨954112214330998598841581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636074809553999065894387 954112214330998598841581)
      ·
        refine ⟨357792080374124474565593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 954112214330998598841581 357792080374124474565593)
        ·
          refine ⟨268344060280593355924195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357792080374124474565593 268344060280593355924195)
          ·
            refine ⟨402516090420890033886293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268344060280593355924195 402516090420890033886293)
            ·
              refine ⟨4716985434619805084605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 402516090420890033886293 4716985434619805084605)
              ·
                rfl

theorem cell22_372045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 8].length) (baseStart_372045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372045 prefixEnd_372045 := by exact prefixLift 372045
  have htrace : WordTrace (prefixWord ++ tailWord_372045) baseStart_372045 baseEnd_372045 := by
    simpa [prefixWord, tailWord_372045, baseEnd_372045] using wordTrace_append hprefix tailTrace_372045
  have hstable : (prefixWord ++ tailWord_372045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372045).length < 2 ^ (prefixWord ++ tailWord_372045).sum := by decide
  have hdescent : baseEnd_372045 < baseStart_372045 := by decide
  rcases family_descends (prefixWord ++ tailWord_372045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372144 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_372144 : Nat := 118140960795 + 372144 * 2 ^ 59
def prefixEnd_372144 : Nat := 4983230072969 + 3 ^ 40 * 372144 * 2
def baseEnd_372144 : Nat := 127392496457931479059031

theorem tailTrace_372144 : CollatzResearch.WordTrace tailWord_372144 prefixEnd_372144 127392496457931479059031 := by
  unfold tailWord_372144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786603381896659990133743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9048804509195546653511657 6786603381896659990133743)
  ·
    refine ⟨10179905072844989985200615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786603381896659990133743 10179905072844989985200615)
    ·
      refine ⟨15269857609267484977800923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10179905072844989985200615 15269857609267484977800923)
      ·
        refine ⟨22904786413901227466701385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15269857609267484977800923 22904786413901227466701385)
        ·
          refine ⟨17178589810425920600026039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22904786413901227466701385 17178589810425920600026039)
          ·
            refine ⟨25767884715638880900039059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17178589810425920600026039 25767884715638880900039059)
            ·
              refine ⟨38651827073458321350058589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25767884715638880900039059 38651827073458321350058589)
              ·
                refine ⟨14494435152546870506271971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38651827073458321350058589 14494435152546870506271971)
                ·
                  refine ⟨21741652728820305759407957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14494435152546870506271971 21741652728820305759407957)
                  ·
                    refine ⟨127392496457931479059031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21741652728820305759407957 127392496457931479059031)
                    ·
                      rfl

theorem cell22_372144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_372144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372144 prefixEnd_372144 := by exact prefixLift 372144
  have htrace : WordTrace (prefixWord ++ tailWord_372144) baseStart_372144 baseEnd_372144 := by
    simpa [prefixWord, tailWord_372144, baseEnd_372144] using wordTrace_append hprefix tailTrace_372144
  have hstable : (prefixWord ++ tailWord_372144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372144).length < 2 ^ (prefixWord ++ tailWord_372144).sum := by decide
  have hdescent : baseEnd_372144 < baseStart_372144 := by decide
  rcases family_descends (prefixWord ++ tailWord_372144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372281 : List Nat := [1, 2, 1, 5, 1, 12]
def baseStart_372281 : Nat := 118140960795 + 372281 * 2 ^ 59
def prefixEnd_372281 : Nat := 4983230072969 + 3 ^ 40 * 372281 * 2
def baseEnd_372281 : Nat := 1573325856268009733131

theorem tailTrace_372281 : CollatzResearch.WordTrace tailWord_372281 prefixEnd_372281 1573325856268009733131 := by
  unfold tailWord_372281
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578203564296992378004697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052135709531328252003131 13578203564296992378004697)
  ·
    refine ⟨10183652673222744283503523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13578203564296992378004697 10183652673222744283503523)
    ·
      refine ⟨15275479009834116425255285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10183652673222744283503523 15275479009834116425255285)
      ·
        refine ⟨1432076157171948414867683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15275479009834116425255285 1432076157171948414867683)
        ·
          refine ⟨2148114235757922622301525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432076157171948414867683 2148114235757922622301525)
          ·
            refine ⟨1573325856268009733131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2148114235757922622301525 1573325856268009733131)
            ·
              rfl

theorem cell22_372281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 12].length) (baseStart_372281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372281 prefixEnd_372281 := by exact prefixLift 372281
  have htrace : WordTrace (prefixWord ++ tailWord_372281) baseStart_372281 baseEnd_372281 := by
    simpa [prefixWord, tailWord_372281, baseEnd_372281] using wordTrace_append hprefix tailTrace_372281
  have hstable : (prefixWord ++ tailWord_372281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372281).length < 2 ^ (prefixWord ++ tailWord_372281).sum := by decide
  have hdescent : baseEnd_372281 < baseStart_372281 := by decide
  rcases family_descends (prefixWord ++ tailWord_372281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372287 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 4]
def baseStart_372287 : Nat := 118140960795 + 372287 * 2 ^ 59
def prefixEnd_372287 : Nat := 4983230072969 + 3 ^ 40 * 372287 * 2
def baseEnd_372287 : Nat := 42480482760108924244531

theorem tailTrace_372287 : CollatzResearch.WordTrace tailWord_372287 prefixEnd_372287 42480482760108924244531 := by
  unfold tailWord_372287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13578422402275255402723115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9052281601516836935148743 13578422402275255402723115)
  ·
    refine ⟨20367633603412883104084673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13578422402275255402723115 20367633603412883104084673)
    ·
      refine ⟨15275725202559662328063505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20367633603412883104084673 15275725202559662328063505)
      ·
        refine ⟨11456793901919746746047629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15275725202559662328063505 11456793901919746746047629)
        ·
          refine ⟨4296297713219905029767861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11456793901919746746047629 4296297713219905029767861)
          ·
            refine ⟨402777910614366096540737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4296297713219905029767861 402777910614366096540737)
            ·
              refine ⟨302083432960774572405553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402777910614366096540737 302083432960774572405553)
              ·
                refine ⟨226562574720580929304165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302083432960774572405553 226562574720580929304165)
                ·
                  refine ⟨42480482760108924244531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226562574720580929304165 42480482760108924244531)
                  ·
                    rfl

theorem cell22_372287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 4].length) (baseStart_372287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372287 prefixEnd_372287 := by exact prefixLift 372287
  have htrace : WordTrace (prefixWord ++ tailWord_372287) baseStart_372287 baseEnd_372287 := by
    simpa [prefixWord, tailWord_372287, baseEnd_372287] using wordTrace_append hprefix tailTrace_372287
  have hstable : (prefixWord ++ tailWord_372287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372287).length < 2 ^ (prefixWord ++ tailWord_372287).sum := by decide
  have hdescent : baseEnd_372287 < baseStart_372287 := by decide
  rcases family_descends (prefixWord ++ tailWord_372287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372296 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_372296 : Nat := 118140960795 + 372296 * 2 ^ 59
def prefixEnd_372296 : Nat := 4983230072969 + 3 ^ 40 * 372296 * 2
def baseEnd_372296 : Nat := 127444529164253749258565

theorem tailTrace_372296 : CollatzResearch.WordTrace tailWord_372296 prefixEnd_372296 127444529164253749258565 := by
  unfold tailWord_372296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789375329621324969900371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9052500439495099959867161 6789375329621324969900371)
  ·
    refine ⟨10184062994431987454850557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6789375329621324969900371 10184062994431987454850557)
    ·
      refine ⟨3819023622911995295568959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10184062994431987454850557 3819023622911995295568959)
      ·
        refine ⟨5728535434367992943353439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819023622911995295568959 5728535434367992943353439)
        ·
          refine ⟨8592803151551989415030159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728535434367992943353439 8592803151551989415030159)
          ·
            refine ⟨12889204727327984122545239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592803151551989415030159 12889204727327984122545239)
            ·
              refine ⟨19333807090991976183817859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12889204727327984122545239 19333807090991976183817859)
              ·
                refine ⟨29000710636487964275726789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19333807090991976183817859 29000710636487964275726789)
                ·
                  refine ⟨5437633244341493301698773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29000710636487964275726789 5437633244341493301698773)
                  ·
                    refine ⟨127444529164253749258565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5437633244341493301698773 127444529164253749258565)
                    ·
                      rfl

theorem cell22_372296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_372296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372296 prefixEnd_372296 := by exact prefixLift 372296
  have htrace : WordTrace (prefixWord ++ tailWord_372296) baseStart_372296 baseEnd_372296 := by
    simpa [prefixWord, tailWord_372296, baseEnd_372296] using wordTrace_append hprefix tailTrace_372296
  have hstable : (prefixWord ++ tailWord_372296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372296).length < 2 ^ (prefixWord ++ tailWord_372296).sum := by decide
  have hdescent : baseEnd_372296 < baseStart_372296 := by decide
  rcases family_descends (prefixWord ++ tailWord_372296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372317 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_372317 : Nat := 118140960795 + 372317 * 2 ^ 59
def prefixEnd_372317 : Nat := 4983230072969 + 3 ^ 40 * 372317 * 2
def baseEnd_372317 : Nat := 127451717893416694483501

theorem tailTrace_372317 : CollatzResearch.WordTrace tailWord_372317 prefixEnd_372317 127451717893416694483501 := by
  unfold tailWord_372317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13579516592166570526315205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9053011061444380350876803 13579516592166570526315205)
  ·
    refine ⟨2546159361031231973684101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13579516592166570526315205 2546159361031231973684101)
    ·
      refine ⟨477404880193355995065769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2546159361031231973684101 477404880193355995065769)
      ·
        refine ⟨358053660145016996299327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477404880193355995065769 358053660145016996299327)
        ·
          refine ⟨537080490217525494448991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358053660145016996299327 537080490217525494448991)
          ·
            refine ⟨805620735326288241673487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537080490217525494448991 805620735326288241673487)
            ·
              refine ⟨1208431102989432362510231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805620735326288241673487 1208431102989432362510231)
              ·
                refine ⟨1812646654484148543765347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208431102989432362510231 1812646654484148543765347)
                ·
                  refine ⟨2718969981726222815648021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812646654484148543765347 2718969981726222815648021)
                  ·
                    refine ⟨127451717893416694483501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2718969981726222815648021 127451717893416694483501)
                    ·
                      rfl

theorem cell22_372317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_372317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372317 prefixEnd_372317 := by exact prefixLift 372317
  have htrace : WordTrace (prefixWord ++ tailWord_372317) baseStart_372317 baseEnd_372317 := by
    simpa [prefixWord, tailWord_372317, baseEnd_372317] using wordTrace_append hprefix tailTrace_372317
  have hstable : (prefixWord ++ tailWord_372317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372317).length < 2 ^ (prefixWord ++ tailWord_372317).sum := by decide
  have hdescent : baseEnd_372317 < baseStart_372317 := by decide
  rcases family_descends (prefixWord ++ tailWord_372317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372373 : List Nat := [1, 3, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_372373 : Nat := 118140960795 + 372373 * 2 ^ 59
def prefixEnd_372373 : Nat := 4983230072969 + 3 ^ 40 * 372373 * 2
def baseEnd_372373 : Nat := 127470887837851215083329

theorem tailTrace_372373 : CollatzResearch.WordTrace tailWord_372373 prefixEnd_372373 127470887837851215083329 := by
  unfold tailWord_372373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13581559079963692090353773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9054372719975794726902515 13581559079963692090353773)
  ·
    refine ⟨5093084654986384533882665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13581559079963692090353773 5093084654986384533882665)
    ·
      refine ⟨3819813491239788400411999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5093084654986384533882665 3819813491239788400411999)
      ·
        refine ⟨5729720236859682600617999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819813491239788400411999 5729720236859682600617999)
        ·
          refine ⟨8594580355289523900926999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729720236859682600617999 8594580355289523900926999)
          ·
            refine ⟨12891870532934285851390499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594580355289523900926999 12891870532934285851390499)
            ·
              refine ⟨19337805799401428777085749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12891870532934285851390499 19337805799401428777085749)
              ·
                refine ⟨1812919293693883947851789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19337805799401428777085749 1812919293693883947851789)
                ·
                  refine ⟨679844735135206480444421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1812919293693883947851789 679844735135206480444421)
                  ·
                    refine ⟨127470887837851215083329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 679844735135206480444421 127470887837851215083329)
                    ·
                      rfl

theorem cell22_372373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_372373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372373 prefixEnd_372373 := by exact prefixLift 372373
  have htrace : WordTrace (prefixWord ++ tailWord_372373) baseStart_372373 baseEnd_372373 := by
    simpa [prefixWord, tailWord_372373, baseEnd_372373] using wordTrace_append hprefix tailTrace_372373
  have hstable : (prefixWord ++ tailWord_372373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372373).length < 2 ^ (prefixWord ++ tailWord_372373).sum := by decide
  have hdescent : baseEnd_372373 < baseStart_372373 := by decide
  rcases family_descends (prefixWord ++ tailWord_372373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372398 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_372398 : Nat := 118140960795 + 372398 * 2 ^ 59
def prefixEnd_372398 : Nat := 4983230072969 + 3 ^ 40 * 372398 * 2
def baseEnd_372398 : Nat := 127479445848759483208253

theorem tailTrace_372398 : CollatzResearch.WordTrace tailWord_372398 prefixEnd_372398 127479445848759483208253 := by
  unfold tailWord_372398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1697808863109140170001731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9054980603248747573342565 1697808863109140170001731)
  ·
    refine ⟨2546713294663710255002597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1697808863109140170001731 2546713294663710255002597)
    ·
      refine ⟨477508742749445672812987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2546713294663710255002597 477508742749445672812987)
      ·
        refine ⟨716263114124168509219481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477508742749445672812987 716263114124168509219481)
        ·
          refine ⟨537197335593126381914611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716263114124168509219481 537197335593126381914611)
          ·
            refine ⟨805796003389689572871917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537197335593126381914611 805796003389689572871917)
            ·
              refine ⟨302173501271133589826969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805796003389689572871917 302173501271133589826969)
              ·
                refine ⟨226630125953350192370227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302173501271133589826969 226630125953350192370227)
                ·
                  refine ⟨339945188930025288555341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226630125953350192370227 339945188930025288555341)
                  ·
                    refine ⟨127479445848759483208253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339945188930025288555341 127479445848759483208253)
                    ·
                      rfl

theorem cell22_372398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_372398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372398 prefixEnd_372398 := by exact prefixLift 372398
  have htrace : WordTrace (prefixWord ++ tailWord_372398) baseStart_372398 baseEnd_372398 := by
    simpa [prefixWord, tailWord_372398, baseEnd_372398] using wordTrace_append hprefix tailTrace_372398
  have hstable : (prefixWord ++ tailWord_372398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372398).length < 2 ^ (prefixWord ++ tailWord_372398).sum := by decide
  have hdescent : baseEnd_372398 < baseStart_372398 := by decide
  rcases family_descends (prefixWord ++ tailWord_372398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372420 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_372420 : Nat := 118140960795 + 372420 * 2 ^ 59
def prefixEnd_372420 : Nat := 4983230072969 + 3 ^ 40 * 372420 * 2
def baseEnd_372420 : Nat := 127486976898358759158185

theorem tailTrace_372420 : CollatzResearch.WordTrace tailWord_372420 prefixEnd_372420 127486976898358759158185 := by
  unfold tailWord_372420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791636655396709558657357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9055515540528946078209809 6791636655396709558657357)
  ·
    refine ⟨2546863745773766084496509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6791636655396709558657357 2546863745773766084496509)
    ·
      refine ⟨955073904665162281686191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2546863745773766084496509 955073904665162281686191)
      ·
        refine ⟨1432610856997743422529287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955073904665162281686191 1432610856997743422529287)
        ·
          refine ⟨2148916285496615133793931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432610856997743422529287 2148916285496615133793931)
          ·
            refine ⟨3223374428244922700690897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148916285496615133793931 3223374428244922700690897)
            ·
              refine ⟨2417530821183692025518173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223374428244922700690897 2417530821183692025518173)
              ·
                refine ⟨906574057943884509569315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2417530821183692025518173 906574057943884509569315)
                ·
                  refine ⟨1359861086915826764353973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906574057943884509569315 1359861086915826764353973)
                  ·
                    refine ⟨127486976898358759158185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1359861086915826764353973 127486976898358759158185)
                    ·
                      rfl

theorem cell22_372420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_372420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372420 prefixEnd_372420 := by exact prefixLift 372420
  have htrace : WordTrace (prefixWord ++ tailWord_372420) baseStart_372420 baseEnd_372420 := by
    simpa [prefixWord, tailWord_372420, baseEnd_372420] using wordTrace_append hprefix tailTrace_372420
  have hstable : (prefixWord ++ tailWord_372420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372420).length < 2 ^ (prefixWord ++ tailWord_372420).sum := by decide
  have hdescent : baseEnd_372420 < baseStart_372420 := by decide
  rcases family_descends (prefixWord ++ tailWord_372420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372433 : List Nat := [1, 2, 2, 1, 2, 4, 2, 8]
def baseStart_372433 : Nat := 118140960795 + 372433 * 2 ^ 59
def prefixEnd_372433 : Nat := 4983230072969 + 3 ^ 40 * 372433 * 2
def baseEnd_372433 : Nat := 14165714118225673175905

theorem tailTrace_372433 : CollatzResearch.WordTrace tailWord_372433 prefixEnd_372433 14165714118225673175905 := by
  unfold tailWord_372433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583747459746322337537953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9055831639830881558358635 13583747459746322337537953)
  ·
    refine ⟨10187810594809741753153465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13583747459746322337537953 10187810594809741753153465)
    ·
      refine ⟨7640857946107306314865099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10187810594809741753153465 7640857946107306314865099)
      ·
        refine ⟨11461286919160959472297649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640857946107306314865099 11461286919160959472297649)
        ·
          refine ⟨8595965189370719604223237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11461286919160959472297649 8595965189370719604223237)
          ·
            refine ⟨1611743473007009925791857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8595965189370719604223237 1611743473007009925791857)
            ·
              refine ⟨1208807604755257444343893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611743473007009925791857 1208807604755257444343893)
              ·
                refine ⟨14165714118225673175905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1208807604755257444343893 14165714118225673175905)
                ·
                  rfl

theorem cell22_372433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 8].length) (baseStart_372433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372433 prefixEnd_372433 := by exact prefixLift 372433
  have htrace : WordTrace (prefixWord ++ tailWord_372433) baseStart_372433 baseEnd_372433 := by
    simpa [prefixWord, tailWord_372433, baseEnd_372433] using wordTrace_append hprefix tailTrace_372433
  have hstable : (prefixWord ++ tailWord_372433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372433).length < 2 ^ (prefixWord ++ tailWord_372433).sum := by decide
  have hdescent : baseEnd_372433 < baseStart_372433 := by decide
  rcases family_descends (prefixWord ++ tailWord_372433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372463 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_372463 : Nat := 118140960795 + 372463 * 2 ^ 59
def prefixEnd_372463 : Nat := 4983230072969 + 3 ^ 40 * 372463 * 2
def baseEnd_372463 : Nat := 127501696677120980333053

theorem tailTrace_372463 : CollatzResearch.WordTrace tailWord_372463 prefixEnd_372463 127501696677120980333053 := by
  unfold tailWord_372463
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584841649637637461130043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9056561099758424974086695 13584841649637637461130043)
  ·
    refine ⟨20377262474456456191695065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584841649637637461130043 20377262474456456191695065)
    ·
      refine ⟨15282946855842342143771299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20377262474456456191695065 15282946855842342143771299)
      ·
        refine ⟨22924420283763513215656949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15282946855842342143771299 22924420283763513215656949)
        ·
          refine ⟨2149164401602829363967839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22924420283763513215656949 2149164401602829363967839)
          ·
            refine ⟨3223746602404244045951759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149164401602829363967839 3223746602404244045951759)
            ·
              refine ⟨4835619903606366068927639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3223746602404244045951759 4835619903606366068927639)
              ·
                refine ⟨7253429855409549103391459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835619903606366068927639 7253429855409549103391459)
                ·
                  refine ⟨10880144783114323655087189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253429855409549103391459 10880144783114323655087189)
                  ·
                    refine ⟨127501696677120980333053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10880144783114323655087189 127501696677120980333053)
                    ·
                      rfl

theorem cell22_372463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_372463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372463 prefixEnd_372463 := by exact prefixLift 372463
  have htrace : WordTrace (prefixWord ++ tailWord_372463) baseStart_372463 baseEnd_372463 := by
    simpa [prefixWord, tailWord_372463, baseEnd_372463] using wordTrace_append hprefix tailTrace_372463
  have hstable : (prefixWord ++ tailWord_372463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372463).length < 2 ^ (prefixWord ++ tailWord_372463).sum := by decide
  have hdescent : baseEnd_372463 < baseStart_372463 := by decide
  rcases family_descends (prefixWord ++ tailWord_372463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372540 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_372540 : Nat := 118140960795 + 372540 * 2 ^ 59
def prefixEnd_372540 : Nat := 4983230072969 + 3 ^ 40 * 372540 * 2
def baseEnd_372540 : Nat := 42509351783572815385939

theorem tailTrace_372540 : CollatzResearch.WordTrace tailWord_372540 prefixEnd_372540 42509351783572815385939 := by
  unfold tailWord_372540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793825035179339805841537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9058433380239119741122049 6793825035179339805841537)
  ·
    refine ⟨5095368776384504854381153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6793825035179339805841537 5095368776384504854381153)
    ·
      refine ⟨3821526582288378640785865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5095368776384504854381153 3821526582288378640785865)
      ·
        refine ⟨2866144936716283980589399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3821526582288378640785865 2866144936716283980589399)
        ·
          refine ⟨4299217405074425970884099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866144936716283980589399 4299217405074425970884099)
          ·
            refine ⟨6448826107611638956326149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299217405074425970884099 6448826107611638956326149)
            ·
              refine ⟨1209154895177182304311153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6448826107611638956326149 1209154895177182304311153)
              ·
                refine ⟨906866171382886728233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209154895177182304311153 906866171382886728233365)
                ·
                  refine ⟨42509351783572815385939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 906866171382886728233365 42509351783572815385939)
                  ·
                    rfl

theorem cell22_372540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_372540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372540 prefixEnd_372540 := by exact prefixLift 372540
  have htrace : WordTrace (prefixWord ++ tailWord_372540) baseStart_372540 baseEnd_372540 := by
    simpa [prefixWord, tailWord_372540, baseEnd_372540] using wordTrace_append hprefix tailTrace_372540
  have hstable : (prefixWord ++ tailWord_372540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372540).length < 2 ^ (prefixWord ++ tailWord_372540).sum := by decide
  have hdescent : baseEnd_372540 < baseStart_372540 := by decide
  rcases family_descends (prefixWord ++ tailWord_372540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372550 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_372550 : Nat := 118140960795 + 372550 * 2 ^ 59
def prefixEnd_372550 : Nat := 4983230072969 + 3 ^ 40 * 372550 * 2
def baseEnd_372550 : Nat := 127531478555081753407787

theorem tailTrace_372550 : CollatzResearch.WordTrace tailWord_372550 prefixEnd_372550 127531478555081753407787 := by
  unfold tailWord_372550
  simp only [CollatzResearch.WordTrace]
  refine ⟨424625462510076603735847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9058676533548300879698069 424625462510076603735847)
  ·
    refine ⟨636938193765114905603771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424625462510076603735847 636938193765114905603771)
    ·
      refine ⟨955407290647672358405657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636938193765114905603771 955407290647672358405657)
      ·
        refine ⟨716555467985754268804243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955407290647672358405657 716555467985754268804243)
        ·
          refine ⟨1074833201978631403206365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716555467985754268804243 1074833201978631403206365)
          ·
            refine ⟨403062450741986776202387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1074833201978631403206365 403062450741986776202387)
            ·
              refine ⟨604593676112980164303581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403062450741986776202387 604593676112980164303581)
              ·
                refine ⟨226722628542367561613843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 604593676112980164303581 226722628542367561613843)
                ·
                  refine ⟨340083942813551342420765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226722628542367561613843 340083942813551342420765)
                  ·
                    refine ⟨127531478555081753407787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340083942813551342420765 127531478555081753407787)
                    ·
                      rfl

theorem cell22_372550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_372550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372550 prefixEnd_372550 := by exact prefixLift 372550
  have htrace : WordTrace (prefixWord ++ tailWord_372550) baseStart_372550 baseEnd_372550 := by
    simpa [prefixWord, tailWord_372550, baseEnd_372550] using wordTrace_append hprefix tailTrace_372550
  have hstable : (prefixWord ++ tailWord_372550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372550).length < 2 ^ (prefixWord ++ tailWord_372550).sum := by decide
  have hdescent : baseEnd_372550 < baseStart_372550 := by decide
  rcases family_descends (prefixWord ++ tailWord_372550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372711 : List Nat := [1, 1, 5, 2, 3, 1, 2, 2, 1, 4]
def baseStart_372711 : Nat := 118140960795 + 372711 * 2 ^ 59
def prefixEnd_372711 : Nat := 4983230072969 + 3 ^ 40 * 372711 * 2
def baseEnd_372711 : Nat := 127586592145331000132293

theorem tailTrace_372711 : CollatzResearch.WordTrace tailWord_372711 prefixEnd_372711 127586592145331000132293 := by
  unfold tailWord_372711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593886952739175816157987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9062591301826117210771991 13593886952739175816157987)
  ·
    refine ⟨20390830429108763724236981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13593886952739175816157987 20390830429108763724236981)
    ·
      refine ⟨1911640352728946599147217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20390830429108763724236981 1911640352728946599147217)
      ·
        refine ⟨1433730264546709949360413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1911640352728946599147217 1433730264546709949360413)
        ·
          refine ⟨537648849205016231010155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1433730264546709949360413 537648849205016231010155)
          ·
            refine ⟨806473273807524346515233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537648849205016231010155 806473273807524346515233)
            ·
              refine ⟨604854955355643259886425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806473273807524346515233 604854955355643259886425)
              ·
                refine ⟨453641216516732444914819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604854955355643259886425 453641216516732444914819)
                ·
                  refine ⟨680461824775098667372229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453641216516732444914819 680461824775098667372229)
                  ·
                    refine ⟨127586592145331000132293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 680461824775098667372229 127586592145331000132293)
                    ·
                      rfl

theorem cell22_372711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_372711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372711 prefixEnd_372711 := by exact prefixLift 372711
  have htrace : WordTrace (prefixWord ++ tailWord_372711) baseStart_372711 baseEnd_372711 := by
    simpa [prefixWord, tailWord_372711, baseEnd_372711] using wordTrace_append hprefix tailTrace_372711
  have hstable : (prefixWord ++ tailWord_372711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372711).length < 2 ^ (prefixWord ++ tailWord_372711).sum := by decide
  have hdescent : baseEnd_372711 < baseStart_372711 := by decide
  rcases family_descends (prefixWord ++ tailWord_372711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372814 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_372814 : Nat := 118140960795 + 372814 * 2 ^ 59
def prefixEnd_372814 : Nat := 4983230072969 + 3 ^ 40 * 372814 * 2
def baseEnd_372814 : Nat := 127621851150273064806977

theorem tailTrace_372814 : CollatzResearch.WordTrace tailWord_372814 prefixEnd_372814 127621851150273064806977 := by
  unfold tailWord_372814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699705458920753050894687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9065095780910682938104997 1699705458920753050894687)
  ·
    refine ⟨2549558188381129576342031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1699705458920753050894687 2549558188381129576342031)
    ·
      refine ⟨3824337282571694364513047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2549558188381129576342031 3824337282571694364513047)
      ·
        refine ⟨5736505923857541546769571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824337282571694364513047 5736505923857541546769571)
        ·
          refine ⟨8604758885786312320154357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736505923857541546769571 8604758885786312320154357)
          ·
            refine ⟨806696145542466780014471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8604758885786312320154357 806696145542466780014471)
            ·
              refine ⟨1210044218313700170021707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806696145542466780014471 1210044218313700170021707)
              ·
                refine ⟨1815066327470550255032561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210044218313700170021707 1815066327470550255032561)
                ·
                  refine ⟨1361299745602912691274421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1815066327470550255032561 1361299745602912691274421)
                  ·
                    refine ⟨127621851150273064806977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1361299745602912691274421 127621851150273064806977)
                    ·
                      rfl

theorem cell22_372814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_372814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372814 prefixEnd_372814 := by exact prefixLift 372814
  have htrace : WordTrace (prefixWord ++ tailWord_372814) baseStart_372814 baseEnd_372814 := by
    simpa [prefixWord, tailWord_372814, baseEnd_372814] using wordTrace_append hprefix tailTrace_372814
  have hstable : (prefixWord ++ tailWord_372814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372814).length < 2 ^ (prefixWord ++ tailWord_372814).sum := by decide
  have hdescent : baseEnd_372814 < baseStart_372814 := by decide
  rcases family_descends (prefixWord ++ tailWord_372814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372846 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_372846 : Nat := 118140960795 + 372846 * 2 ^ 59
def prefixEnd_372846 : Nat := 4983230072969 + 3 ^ 40 * 372846 * 2
def baseEnd_372846 : Nat := 127632805404235648006879

theorem tailTrace_372846 : CollatzResearch.WordTrace tailWord_372846 prefixEnd_372846 127632805404235648006879 := by
  unfold tailWord_372846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699851350906261734040299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9065873871500062581548261 1699851350906261734040299)
  ·
    refine ⟨2549777026359392601060449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1699851350906261734040299 2549777026359392601060449)
    ·
      refine ⟨1912332769769544450795337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2549777026359392601060449 1912332769769544450795337)
      ·
        refine ⟨1434249577327158338096503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912332769769544450795337 1434249577327158338096503)
        ·
          refine ⟨2151374365990737507144755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434249577327158338096503 2151374365990737507144755)
          ·
            refine ⟨3227061548986106260717133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151374365990737507144755 3227061548986106260717133)
            ·
              refine ⟨1210148080869789847768925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3227061548986106260717133 1210148080869789847768925)
              ·
                refine ⟨453805530326171192913347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1210148080869789847768925 453805530326171192913347)
                ·
                  refine ⟨680708295489256789370021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453805530326171192913347 680708295489256789370021)
                  ·
                    refine ⟨127632805404235648006879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 680708295489256789370021 127632805404235648006879)
                    ·
                      rfl

theorem cell22_372846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_372846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372846 prefixEnd_372846 := by exact prefixLift 372846
  have htrace : WordTrace (prefixWord ++ tailWord_372846) baseStart_372846 baseEnd_372846 := by
    simpa [prefixWord, tailWord_372846, baseEnd_372846] using wordTrace_append hprefix tailTrace_372846
  have hstable : (prefixWord ++ tailWord_372846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372846).length < 2 ^ (prefixWord ++ tailWord_372846).sum := by decide
  have hdescent : baseEnd_372846 < baseStart_372846 := by decide
  rcases family_descends (prefixWord ++ tailWord_372846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372861 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 4]
def baseStart_372861 : Nat := 118140960795 + 372861 * 2 ^ 59
def prefixEnd_372861 : Nat := 4983230072969 + 3 ^ 40 * 372861 * 2
def baseEnd_372861 : Nat := 42545980070260202960611

theorem tailTrace_372861 : CollatzResearch.WordTrace tailWord_372861 prefixEnd_372861 42545980070260202960611 := by
  unfold tailWord_372861
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599357902195751434118437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9066238601463834289412291 13599357902195751434118437)
  ·
    refine ⟨2549879606661703393897207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13599357902195751434118437 2549879606661703393897207)
    ·
      refine ⟨3824819409992555090845811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2549879606661703393897207 3824819409992555090845811)
      ·
        refine ⟨5737229114988832636268717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824819409992555090845811 5737229114988832636268717)
        ·
          refine ⟨2151460918120812238600769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5737229114988832636268717 2151460918120812238600769)
          ·
            refine ⟨1613595688590609178950577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151460918120812238600769 1613595688590609178950577)
            ·
              refine ⟨1210196766442956884212933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613595688590609178950577 1210196766442956884212933)
              ·
                refine ⟨226911893708054415789925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1210196766442956884212933 226911893708054415789925)
                ·
                  refine ⟨42545980070260202960611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226911893708054415789925 42545980070260202960611)
                  ·
                    rfl

theorem cell22_372861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_372861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372861 prefixEnd_372861 := by exact prefixLift 372861
  have htrace : WordTrace (prefixWord ++ tailWord_372861) baseStart_372861 baseEnd_372861 := by
    simpa [prefixWord, tailWord_372861, baseEnd_372861] using wordTrace_append hprefix tailTrace_372861
  have hstable : (prefixWord ++ tailWord_372861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372861).length < 2 ^ (prefixWord ++ tailWord_372861).sum := by decide
  have hdescent : baseEnd_372861 < baseStart_372861 := by decide
  rcases family_descends (prefixWord ++ tailWord_372861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372874 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_372874 : Nat := 118140960795 + 372874 * 2 ^ 59
def prefixEnd_372874 : Nat := 4983230072969 + 3 ^ 40 * 372874 * 2
def baseEnd_372874 : Nat := 127642390376452908306793

theorem tailTrace_372874 : CollatzResearch.WordTrace tailWord_372874 prefixEnd_372874 127642390376452908306793 := by
  unfold tailWord_372874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3399958012787163663585419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9066554700765769769561117 3399958012787163663585419)
  ·
    refine ⟨5099937019180745495378129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3399958012787163663585419 5099937019180745495378129)
    ·
      refine ⟨3824952764385559121533597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5099937019180745495378129 3824952764385559121533597)
      ·
        refine ⟨1434357286644584670575099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3824952764385559121533597 1434357286644584670575099)
        ·
          refine ⟨2151535929966877005862649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434357286644584670575099 2151535929966877005862649)
          ·
            refine ⟨1613651947475157754396987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151535929966877005862649 1613651947475157754396987)
            ·
              refine ⟨2420477921212736631595481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613651947475157754396987 2420477921212736631595481)
              ·
                refine ⟨1815358440909552473696611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420477921212736631595481 1815358440909552473696611)
                ·
                  refine ⟨2723037661364328710544917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815358440909552473696611 2723037661364328710544917)
                  ·
                    refine ⟨127642390376452908306793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2723037661364328710544917 127642390376452908306793)
                    ·
                      rfl

theorem cell22_372874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_372874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372874 prefixEnd_372874 := by exact prefixLift 372874
  have htrace : WordTrace (prefixWord ++ tailWord_372874) baseStart_372874 baseEnd_372874 := by
    simpa [prefixWord, tailWord_372874, baseEnd_372874] using wordTrace_append hprefix tailTrace_372874
  have hstable : (prefixWord ++ tailWord_372874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372874).length < 2 ^ (prefixWord ++ tailWord_372874).sum := by decide
  have hdescent : baseEnd_372874 < baseStart_372874 := by decide
  rcases family_descends (prefixWord ++ tailWord_372874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372979 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 6]
def baseStart_372979 : Nat := 118140960795 + 372979 * 2 ^ 59
def prefixEnd_372979 : Nat := 4983230072969 + 3 ^ 40 * 372979 * 2
def baseEnd_372979 : Nat := 42559444674089211477157

theorem tailTrace_372979 : CollatzResearch.WordTrace tailWord_372979 prefixEnd_372979 42559444674089211477157 := by
  unfold tailWord_372979
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603661715768257586913991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069107810512171724609327 13603661715768257586913991)
  ·
    refine ⟨20405492573652386380370987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603661715768257586913991 20405492573652386380370987)
    ·
      refine ⟨30608238860478579570556481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20405492573652386380370987 30608238860478579570556481)
      ·
        refine ⟨22956179145358934677917361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30608238860478579570556481 22956179145358934677917361)
        ·
          refine ⟨17217134359019201008438021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22956179145358934677917361 17217134359019201008438021)
          ·
            refine ⟨3228212692316100189082129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17217134359019201008438021 3228212692316100189082129)
            ·
              refine ⟨2421159519237075141811597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228212692316100189082129 2421159519237075141811597)
              ·
                refine ⟨907934819713903178179349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2421159519237075141811597 907934819713903178179349)
                ·
                  refine ⟨42559444674089211477157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 907934819713903178179349 42559444674089211477157)
                  ·
                    rfl

theorem cell22_372979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_372979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_372979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_372979 prefixEnd_372979 := by exact prefixLift 372979
  have htrace : WordTrace (prefixWord ++ tailWord_372979) baseStart_372979 baseEnd_372979 := by
    simpa [prefixWord, tailWord_372979, baseEnd_372979] using wordTrace_append hprefix tailTrace_372979
  have hstable : (prefixWord ++ tailWord_372979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372979).length < 2 ^ (prefixWord ++ tailWord_372979).sum := by decide
  have hdescent : baseEnd_372979 < baseStart_372979 := by decide
  rcases family_descends (prefixWord ++ tailWord_372979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373015 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 1, 4]
def baseStart_373015 : Nat := 118140960795 + 373015 * 2 ^ 59
def prefixEnd_373015 : Nat := 4983230072969 + 3 ^ 40 * 373015 * 2
def baseEnd_373015 : Nat := 127690657557975540531361

theorem tailTrace_373015 : CollatzResearch.WordTrace tailWord_373015 prefixEnd_373015 127690657557975540531361 := by
  unfold tailWord_373015
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604974743637835735224499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9069983162425223823482999 13604974743637835735224499)
  ·
    refine ⟨20407462115456753602836749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13604974743637835735224499 20407462115456753602836749)
    ·
      refine ⟨7652798293296282601063781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20407462115456753602836749 7652798293296282601063781)
      ·
        refine ⟨1434899679993052987699459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7652798293296282601063781 1434899679993052987699459)
        ·
          refine ⟨2152349519989579481549189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434899679993052987699459 2152349519989579481549189)
          ·
            refine ⟨403565534998046152790473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2152349519989579481549189 403565534998046152790473)
            ·
              refine ⟨302674151248534614592855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403565534998046152790473 302674151248534614592855)
              ·
                refine ⟨454011226872801921889283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302674151248534614592855 454011226872801921889283)
                ·
                  refine ⟨681016840309202882833925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454011226872801921889283 681016840309202882833925)
                  ·
                    refine ⟨127690657557975540531361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681016840309202882833925 127690657557975540531361)
                    ·
                      rfl

theorem cell22_373015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_373015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373015 prefixEnd_373015 := by exact prefixLift 373015
  have htrace : WordTrace (prefixWord ++ tailWord_373015) baseStart_373015 baseEnd_373015 := by
    simpa [prefixWord, tailWord_373015, baseEnd_373015] using wordTrace_append hprefix tailTrace_373015
  have hstable : (prefixWord ++ tailWord_373015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373015).length < 2 ^ (prefixWord ++ tailWord_373015).sum := by decide
  have hdescent : baseEnd_373015 < baseStart_373015 := by decide
  rcases family_descends (prefixWord ++ tailWord_373015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373028 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_373028 : Nat := 118140960795 + 373028 * 2 ^ 59
def prefixEnd_373028 : Nat := 4983230072969 + 3 ^ 40 * 373028 * 2
def baseEnd_373028 : Nat := 127695107723647839956321

theorem tailTrace_373028 : CollatzResearch.WordTrace tailWord_373028 prefixEnd_373028 127695107723647839956321 := by
  unfold tailWord_373028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802724446295369477723869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9070299261727159303631825 6802724446295369477723869)
  ·
    refine ⟨2551021667360763554146451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6802724446295369477723869 2551021667360763554146451)
    ·
      refine ⟨3826532501041145331219677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551021667360763554146451 3826532501041145331219677)
      ·
        refine ⟨1434949687890429499207379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3826532501041145331219677 1434949687890429499207379)
        ·
          refine ⟨2152424531835644248811069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434949687890429499207379 2152424531835644248811069)
          ·
            refine ⟨807159199438366593304151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2152424531835644248811069 807159199438366593304151)
            ·
              refine ⟨1210738799157549889956227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807159199438366593304151 1210738799157549889956227)
              ·
                refine ⟨1816108198736324834934341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210738799157549889956227 1816108198736324834934341)
                ·
                  refine ⟨340520287263060906550189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816108198736324834934341 340520287263060906550189)
                  ·
                    refine ⟨127695107723647839956321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340520287263060906550189 127695107723647839956321)
                    ·
                      rfl

theorem cell22_373028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_373028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373028 prefixEnd_373028 := by exact prefixLift 373028
  have htrace : WordTrace (prefixWord ++ tailWord_373028) baseStart_373028 baseEnd_373028 := by
    simpa [prefixWord, tailWord_373028, baseEnd_373028] using wordTrace_append hprefix tailTrace_373028
  have hstable : (prefixWord ++ tailWord_373028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373028).length < 2 ^ (prefixWord ++ tailWord_373028).sum := by decide
  have hdescent : baseEnd_373028 < baseStart_373028 := by decide
  rcases family_descends (prefixWord ++ tailWord_373028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373045 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 2, 3]
def baseStart_373045 : Nat := 118140960795 + 373045 * 2 ^ 59
def prefixEnd_373045 : Nat := 4983230072969 + 3 ^ 40 * 373045 * 2
def baseEnd_373045 : Nat := 127700927171065462281269

theorem tailTrace_373045 : CollatzResearch.WordTrace tailWord_373045 prefixEnd_373045 127700927171065462281269 := by
  unfold tailWord_373045
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606068933529150858816589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9070712622352767239211059 13606068933529150858816589)
  ·
    refine ⟨5102275850073431572056221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13606068933529150858816589 5102275850073431572056221)
    ·
      refine ⟨1913353443777536839521083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5102275850073431572056221 1913353443777536839521083)
      ·
        refine ⟨2870030165666305259281625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913353443777536839521083 2870030165666305259281625)
        ·
          refine ⟨2152522624249728944461219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2870030165666305259281625 2152522624249728944461219)
          ·
            refine ⟨3228783936374593416691829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152522624249728944461219 3228783936374593416691829)
            ·
              refine ⟨302698494035118132814859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3228783936374593416691829 302698494035118132814859)
              ·
                refine ⟨454047741052677199222289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302698494035118132814859 454047741052677199222289)
                ·
                  refine ⟨340535805789507899416717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454047741052677199222289 340535805789507899416717)
                  ·
                    refine ⟨127700927171065462281269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340535805789507899416717 127700927171065462281269)
                    ·
                      rfl

theorem cell22_373045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_373045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373045 prefixEnd_373045 := by exact prefixLift 373045
  have htrace : WordTrace (prefixWord ++ tailWord_373045) baseStart_373045 baseEnd_373045 := by
    simpa [prefixWord, tailWord_373045, baseEnd_373045] using wordTrace_append hprefix tailTrace_373045
  have hstable : (prefixWord ++ tailWord_373045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373045).length < 2 ^ (prefixWord ++ tailWord_373045).sum := by decide
  have hdescent : baseEnd_373045 < baseStart_373045 := by decide
  rcases family_descends (prefixWord ++ tailWord_373045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373056 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_373056 : Nat := 118140960795 + 373056 * 2 ^ 59
def prefixEnd_373056 : Nat := 4983230072969 + 3 ^ 40 * 373056 * 2
def baseEnd_373056 : Nat := 127704692695865100256235

theorem tailTrace_373056 : CollatzResearch.WordTrace tailWord_373056 prefixEnd_373056 127704692695865100256235 := by
  unfold tailWord_373056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803235068244649868733511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9070980090992866491644681 6803235068244649868733511)
  ·
    refine ⟨10204852602366974803100267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6803235068244649868733511 10204852602366974803100267)
    ·
      refine ⟨15307278903550462204650401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10204852602366974803100267 15307278903550462204650401)
      ·
        refine ⟨11480459177662846653487801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15307278903550462204650401 11480459177662846653487801)
        ·
          refine ⟨8610344383247134990115851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11480459177662846653487801 8610344383247134990115851)
          ·
            refine ⟨12915516574870702485173777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610344383247134990115851 12915516574870702485173777)
            ·
              refine ⟨9686637431153026863880333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12915516574870702485173777 9686637431153026863880333)
              ·
                refine ⟨3632489036682385073955125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9686637431153026863880333 3632489036682385073955125)
                ·
                  refine ⟨340545847188973600683293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3632489036682385073955125 340545847188973600683293)
                  ·
                    refine ⟨127704692695865100256235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340545847188973600683293 127704692695865100256235)
                    ·
                      rfl

theorem cell22_373056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_373056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373056 prefixEnd_373056 := by exact prefixLift 373056
  have htrace : WordTrace (prefixWord ++ tailWord_373056) baseStart_373056 baseEnd_373056 := by
    simpa [prefixWord, tailWord_373056, baseEnd_373056] using wordTrace_append hprefix tailTrace_373056
  have hstable : (prefixWord ++ tailWord_373056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373056).length < 2 ^ (prefixWord ++ tailWord_373056).sum := by decide
  have hdescent : baseEnd_373056 < baseStart_373056 := by decide
  rcases family_descends (prefixWord ++ tailWord_373056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373090 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_373090 : Nat := 118140960795 + 373090 * 2 ^ 59
def prefixEnd_373090 : Nat := 4983230072969 + 3 ^ 40 * 373090 * 2
def baseEnd_373090 : Nat := 127716331590700344906131

theorem tailTrace_373090 : CollatzResearch.WordTrace tailWord_373090 prefixEnd_373090 127716331590700344906131 := by
  unfold tailWord_373090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401927554591530886051181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9071806812244082362803149 3401927554591530886051181)
  ·
    refine ⟨1275722832971824082269193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3401927554591530886051181 1275722832971824082269193)
    ·
      refine ⟨956792124728868061701895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1275722832971824082269193 956792124728868061701895)
      ·
        refine ⟨1435188187093302092552843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956792124728868061701895 1435188187093302092552843)
        ·
          refine ⟨2152782280639953138829265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435188187093302092552843 2152782280639953138829265)
          ·
            refine ⟨1614586710479964854121949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152782280639953138829265 1614586710479964854121949)
            ·
              refine ⟨605470016429986820295731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614586710479964854121949 605470016429986820295731)
              ·
                refine ⟨908205024644980230443597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605470016429986820295731 908205024644980230443597)
                ·
                  refine ⟨340576884241867586416349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908205024644980230443597 340576884241867586416349)
                  ·
                    refine ⟨127716331590700344906131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340576884241867586416349 127716331590700344906131)
                    ·
                      rfl

theorem cell22_373090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_373090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373090 prefixEnd_373090 := by exact prefixLift 373090
  have htrace : WordTrace (prefixWord ++ tailWord_373090) baseStart_373090 baseEnd_373090 := by
    simpa [prefixWord, tailWord_373090, baseEnd_373090] using wordTrace_append hprefix tailTrace_373090
  have hstable : (prefixWord ++ tailWord_373090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373090).length < 2 ^ (prefixWord ++ tailWord_373090).sum := by decide
  have hdescent : baseEnd_373090 < baseStart_373090 := by decide
  rcases family_descends (prefixWord ++ tailWord_373090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373101 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_373101 : Nat := 118140960795 + 373101 * 2 ^ 59
def prefixEnd_373101 : Nat := 4983230072969 + 3 ^ 40 * 373101 * 2
def baseEnd_373101 : Nat := 127720097115499982881097

theorem tailTrace_373101 : CollatzResearch.WordTrace tailWord_373101 prefixEnd_373101 127720097115499982881097 := by
  unfold tailWord_373101
  simp only [CollatzResearch.WordTrace]
  refine ⟨13608111421326272422855157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9072074280884181615236771 13608111421326272422855157)
  ·
    refine ⟨1275760445749338039642671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13608111421326272422855157 1275760445749338039642671)
    ·
      refine ⟨1913640668624007059464007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275760445749338039642671 1913640668624007059464007)
      ·
        refine ⟨2870461002936010589196011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913640668624007059464007 2870461002936010589196011)
        ·
          refine ⟨4305691504404015883794017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870461002936010589196011 4305691504404015883794017)
          ·
            refine ⟨3229268628303011912845513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4305691504404015883794017 3229268628303011912845513)
            ·
              refine ⟨2421951471227258934634135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229268628303011912845513 2421951471227258934634135)
              ·
                refine ⟨3632927206840888401951203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421951471227258934634135 3632927206840888401951203)
                ·
                  refine ⟨5449390810261332602926805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632927206840888401951203 5449390810261332602926805)
                  ·
                    refine ⟨127720097115499982881097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5449390810261332602926805 127720097115499982881097)
                    ·
                      rfl

theorem cell22_373101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_373101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373101 prefixEnd_373101 := by exact prefixLift 373101
  have htrace : WordTrace (prefixWord ++ tailWord_373101) baseStart_373101 baseEnd_373101 := by
    simpa [prefixWord, tailWord_373101, baseEnd_373101] using wordTrace_append hprefix tailTrace_373101
  have hstable : (prefixWord ++ tailWord_373101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373101).length < 2 ^ (prefixWord ++ tailWord_373101).sum := by decide
  have hdescent : baseEnd_373101 < baseStart_373101 := by decide
  rcases family_descends (prefixWord ++ tailWord_373101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373150 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_373150 : Nat := 118140960795 + 373150 * 2 ^ 59
def prefixEnd_373150 : Nat := 4983230072969 + 3 ^ 40 * 373150 * 2
def baseEnd_373150 : Nat := 127736870816880188405947

theorem tailTrace_373150 : CollatzResearch.WordTrace tailWord_373150 prefixEnd_373150 127736870816880188405947 := by
  unfold tailWord_373150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701237324768594223923613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9073265732099169194259269 1701237324768594223923613)
  ·
    refine ⟨637963996788222833971355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1701237324768594223923613 637963996788222833971355)
    ·
      refine ⟨956945995182334250957033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637963996788222833971355 956945995182334250957033)
      ·
        refine ⟨717709496386750688217775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 956945995182334250957033 717709496386750688217775)
        ·
          refine ⟨1076564244580126032326663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717709496386750688217775 1076564244580126032326663)
          ·
            refine ⟨1614846366870189048489995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076564244580126032326663 1614846366870189048489995)
            ·
              refine ⟨2422269550305283572734993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614846366870189048489995 2422269550305283572734993)
              ·
                refine ⟨1816702162728962679551245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422269550305283572734993 1816702162728962679551245)
                ·
                  refine ⟨681263311023361004831717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1816702162728962679551245 681263311023361004831717)
                  ·
                    refine ⟨127736870816880188405947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681263311023361004831717 127736870816880188405947)
                    ·
                      rfl

theorem cell22_373150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_373150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373150 prefixEnd_373150 := by exact prefixLift 373150
  have htrace : WordTrace (prefixWord ++ tailWord_373150) baseStart_373150 baseEnd_373150 := by
    simpa [prefixWord, tailWord_373150, baseEnd_373150] using wordTrace_append hprefix tailTrace_373150
  have hstable : (prefixWord ++ tailWord_373150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373150).length < 2 ^ (prefixWord ++ tailWord_373150).sum := by decide
  have hdescent : baseEnd_373150 < baseStart_373150 := by decide
  rcases family_descends (prefixWord ++ tailWord_373150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373161 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_373161 : Nat := 118140960795 + 373161 * 2 ^ 59
def prefixEnd_373161 : Nat := 4983230072969 + 3 ^ 40 * 373161 * 2
def baseEnd_373161 : Nat := 127740636341679826380913

theorem tailTrace_373161 : CollatzResearch.WordTrace tailWord_373161 prefixEnd_373161 127740636341679826380913 := by
  unfold tailWord_373161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610299801108902670039337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9073533200739268446692891 13610299801108902670039337)
  ·
    refine ⟨10207724850831677002529503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13610299801108902670039337 10207724850831677002529503)
    ·
      refine ⟨15311587276247515503794255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207724850831677002529503 15311587276247515503794255)
      ·
        refine ⟨22967380914371273255691383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311587276247515503794255 22967380914371273255691383)
        ·
          refine ⟨34451071371556909883537075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22967380914371273255691383 34451071371556909883537075)
          ·
            refine ⟨51676607057335364825305613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34451071371556909883537075 51676607057335364825305613)
            ·
              refine ⟨19378727646500761809489605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51676607057335364825305613 19378727646500761809489605)
              ·
                refine ⟨3633511433718892839279301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19378727646500761809489605 3633511433718892839279301)
                ·
                  refine ⟨681283393822292407364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3633511433718892839279301 681283393822292407364869)
                  ·
                    refine ⟨127740636341679826380913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681283393822292407364869 127740636341679826380913)
                    ·
                      rfl

theorem cell22_373161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_373161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373161 prefixEnd_373161 := by exact prefixLift 373161
  have htrace : WordTrace (prefixWord ++ tailWord_373161) baseStart_373161 baseEnd_373161 := by
    simpa [prefixWord, tailWord_373161, baseEnd_373161] using wordTrace_append hprefix tailTrace_373161
  have hstable : (prefixWord ++ tailWord_373161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373161).length < 2 ^ (prefixWord ++ tailWord_373161).sum := by decide
  have hdescent : baseEnd_373161 < baseStart_373161 := by decide
  rcases family_descends (prefixWord ++ tailWord_373161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373165 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 6]
def baseStart_373165 : Nat := 118140960795 + 373165 * 2 ^ 59
def prefixEnd_373165 : Nat := 4983230072969 + 3 ^ 40 * 373165 * 2
def baseEnd_373165 : Nat := 42580668541141716426967

theorem tailTrace_373165 : CollatzResearch.WordTrace tailWord_373165 prefixEnd_373165 42580668541141716426967 := by
  unfold tailWord_373165
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610445693094411353184949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9073630462062940902123299 13610445693094411353184949)
  ·
    refine ⟨1275979283727601064361089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13610445693094411353184949 1275979283727601064361089)
    ·
      refine ⟨956984462795700798270817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1275979283727601064361089 956984462795700798270817)
      ·
        refine ⟨717738347096775598703113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 956984462795700798270817 717738347096775598703113)
        ·
          refine ⟨538303760322581699027335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717738347096775598703113 538303760322581699027335)
          ·
            refine ⟨807455640483872548541003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538303760322581699027335 807455640483872548541003)
            ·
              refine ⟨1211183460725808822811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807455640483872548541003 1211183460725808822811505)
              ·
                refine ⟨908387595544356617108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211183460725808822811505 908387595544356617108629)
                ·
                  refine ⟨42580668541141716426967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 908387595544356617108629 42580668541141716426967)
                  ·
                    rfl

theorem cell22_373165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_373165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373165 prefixEnd_373165 := by exact prefixLift 373165
  have htrace : WordTrace (prefixWord ++ tailWord_373165) baseStart_373165 baseEnd_373165 := by
    simpa [prefixWord, tailWord_373165, baseEnd_373165] using wordTrace_append hprefix tailTrace_373165
  have hstable : (prefixWord ++ tailWord_373165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373165).length < 2 ^ (prefixWord ++ tailWord_373165).sum := by decide
  have hdescent : baseEnd_373165 < baseStart_373165 := by decide
  rcases family_descends (prefixWord ++ tailWord_373165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373238 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_373238 : Nat := 118140960795 + 373238 * 2 ^ 59
def prefixEnd_373238 : Nat := 4983230072969 + 3 ^ 40 * 373238 * 2
def baseEnd_373238 : Nat := 42588998338425764068559

theorem tailTrace_373238 : CollatzResearch.WordTrace tailWord_373238 prefixEnd_373238 42588998338425764068559 := by
  unfold tailWord_373238
  simp only [CollatzResearch.WordTrace]
  refine ⟨850819263864371551287023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9075405481219963213728245 850819263864371551287023)
  ·
    refine ⟨1276228895796557326930535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 850819263864371551287023 1276228895796557326930535)
    ·
      refine ⟨1914343343694835990395803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276228895796557326930535 1914343343694835990395803)
      ·
        refine ⟨2871515015542253985593705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914343343694835990395803 2871515015542253985593705)
        ·
          refine ⟨2153636261656690489195279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2871515015542253985593705 2153636261656690489195279)
          ·
            refine ⟨3230454392485035733792919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153636261656690489195279 3230454392485035733792919)
            ·
              refine ⟨4845681588727553600689379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230454392485035733792919 4845681588727553600689379)
              ·
                refine ⟨7268522383091330401034069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845681588727553600689379 7268522383091330401034069)
                ·
                  refine ⟨42588998338425764068559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7268522383091330401034069 42588998338425764068559)
                  ·
                    rfl

theorem cell22_373238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_373238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373238 prefixEnd_373238 := by exact prefixLift 373238
  have htrace : WordTrace (prefixWord ++ tailWord_373238) baseStart_373238 baseEnd_373238 := by
    simpa [prefixWord, tailWord_373238, baseEnd_373238] using wordTrace_append hprefix tailTrace_373238
  have hstable : (prefixWord ++ tailWord_373238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373238).length < 2 ^ (prefixWord ++ tailWord_373238).sum := by decide
  have hdescent : baseEnd_373238 < baseStart_373238 := by decide
  rcases family_descends (prefixWord ++ tailWord_373238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373259 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 1, 3]
def baseStart_373259 : Nat := 118140960795 + 373259 * 2 ^ 59
def prefixEnd_373259 : Nat := 4983230072969 + 3 ^ 40 * 373259 * 2
def baseEnd_373259 : Nat := 127774183744440237430613

theorem tailTrace_373259 : CollatzResearch.WordTrace tailWord_373259 prefixEnd_373259 127774183744440237430613 := by
  unfold tailWord_373259
  simp only [CollatzResearch.WordTrace]
  refine ⟨13613874154753865407106831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9075916103169243604737887 13613874154753865407106831)
  ·
    refine ⟨20420811232130798110660247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13613874154753865407106831 20420811232130798110660247)
    ·
      refine ⟨30631216848196197165990371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20420811232130798110660247 30631216848196197165990371)
      ·
        refine ⟨45946825272294295748985557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30631216848196197165990371 45946825272294295748985557)
        ·
          refine ⟨1076878717319397556616849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45946825272294295748985557 1076878717319397556616849)
          ·
            refine ⟨807659037989548167462637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076878717319397556616849 807659037989548167462637)
            ·
              refine ⟨302872139246080562798489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807659037989548167462637 302872139246080562798489)
              ·
                refine ⟨227154104434560422098867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302872139246080562798489 227154104434560422098867)
                ·
                  refine ⟨340731156651840633148301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227154104434560422098867 340731156651840633148301)
                  ·
                    refine ⟨127774183744440237430613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340731156651840633148301 127774183744440237430613)
                    ·
                      rfl

theorem cell22_373259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 1, 3].length) (baseStart_373259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373259 prefixEnd_373259 := by exact prefixLift 373259
  have htrace : WordTrace (prefixWord ++ tailWord_373259) baseStart_373259 baseEnd_373259 := by
    simpa [prefixWord, tailWord_373259, baseEnd_373259] using wordTrace_append hprefix tailTrace_373259
  have hstable : (prefixWord ++ tailWord_373259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373259).length < 2 ^ (prefixWord ++ tailWord_373259).sum := by decide
  have hdescent : baseEnd_373259 < baseStart_373259 := by decide
  rcases family_descends (prefixWord ++ tailWord_373259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373272 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_373272 : Nat := 118140960795 + 373272 * 2 ^ 59
def prefixEnd_373272 : Nat := 4983230072969 + 3 ^ 40 * 373272 * 2
def baseEnd_373272 : Nat := 42592877970037512285191

theorem tailTrace_373272 : CollatzResearch.WordTrace tailWord_373272 prefixEnd_373272 42592877970037512285191 := by
  unfold tailWord_373272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6807174151853384313665035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9076232202471179084886713 6807174151853384313665035)
  ·
    refine ⟨10210761227780076470497553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6807174151853384313665035 10210761227780076470497553)
    ·
      refine ⟨7658070920835057352873165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10210761227780076470497553 7658070920835057352873165)
      ·
        refine ⟨2871776595313146507327437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7658070920835057352873165 2871776595313146507327437)
        ·
          refine ⟨1076916223242429940247789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2871776595313146507327437 1076916223242429940247789)
          ·
            refine ⟨403843583715911227592921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1076916223242429940247789 403843583715911227592921)
            ·
              refine ⟨302882687786933420694691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403843583715911227592921 302882687786933420694691)
              ·
                refine ⟨454324031680400131042037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302882687786933420694691 454324031680400131042037)
                ·
                  refine ⟨42592877970037512285191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 454324031680400131042037 42592877970037512285191)
                  ·
                    rfl

theorem cell22_373272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_373272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373272 prefixEnd_373272 := by exact prefixLift 373272
  have htrace : WordTrace (prefixWord ++ tailWord_373272) baseStart_373272 baseEnd_373272 := by
    simpa [prefixWord, tailWord_373272, baseEnd_373272] using wordTrace_append hprefix tailTrace_373272
  have hstable : (prefixWord ++ tailWord_373272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373272).length < 2 ^ (prefixWord ++ tailWord_373272).sum := by decide
  have hdescent : baseEnd_373272 < baseStart_373272 := by decide
  rcases family_descends (prefixWord ++ tailWord_373272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373285 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_373285 : Nat := 118140960795 + 373285 * 2 ^ 59
def prefixEnd_373285 : Nat := 4983230072969 + 3 ^ 40 * 373285 * 2
def baseEnd_373285 : Nat := 127783084075784836280533

theorem tailTrace_373285 : CollatzResearch.WordTrace tailWord_373285 prefixEnd_373285 127783084075784836280533 := by
  unfold tailWord_373285
  simp only [CollatzResearch.WordTrace]
  refine ⟨13614822452659671847553309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9076548301773114565035539 13614822452659671847553309)
  ·
    refine ⟨5105558419747376942832491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13614822452659671847553309 5105558419747376942832491)
    ·
      refine ⟨7658337629621065414248737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105558419747376942832491 7658337629621065414248737)
      ·
        refine ⟨5743753222215799060686553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7658337629621065414248737 5743753222215799060686553)
        ·
          refine ⟨4307814916661849295514915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743753222215799060686553 4307814916661849295514915)
          ·
            refine ⟨6461722374992773943272373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307814916661849295514915 6461722374992773943272373)
            ·
              refine ⟨605786472655572557181785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6461722374992773943272373 605786472655572557181785)
              ·
                refine ⟨454339854491679417886339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605786472655572557181785 454339854491679417886339)
                ·
                  refine ⟨681509781737519126829509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454339854491679417886339 681509781737519126829509)
                  ·
                    refine ⟨127783084075784836280533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681509781737519126829509 127783084075784836280533)
                    ·
                      rfl

theorem cell22_373285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_373285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373285 prefixEnd_373285 := by exact prefixLift 373285
  have htrace : WordTrace (prefixWord ++ tailWord_373285) baseStart_373285 baseEnd_373285 := by
    simpa [prefixWord, tailWord_373285, baseEnd_373285] using wordTrace_append hprefix tailTrace_373285
  have hstable : (prefixWord ++ tailWord_373285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373285).length < 2 ^ (prefixWord ++ tailWord_373285).sum := by decide
  have hdescent : baseEnd_373285 < baseStart_373285 := by decide
  rcases family_descends (prefixWord ++ tailWord_373285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373298 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_373298 : Nat := 118140960795 + 373298 * 2 ^ 59
def prefixEnd_373298 : Nat := 4983230072969 + 3 ^ 40 * 373298 * 2
def baseEnd_373298 : Nat := 127787534241457135705493

theorem tailTrace_373298 : CollatzResearch.WordTrace tailWord_373298 prefixEnd_373298 127787534241457135705493 := by
  unfold tailWord_373298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403824150403143766944137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9076864401075050045184365 3403824150403143766944137)
  ·
    refine ⟨2552868112802357825208103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3403824150403143766944137 2552868112802357825208103)
    ·
      refine ⟨3829302169203536737812155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552868112802357825208103 3829302169203536737812155)
      ·
        refine ⟨5743953253805305106718233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829302169203536737812155 5743953253805305106718233)
        ·
          refine ⟨4307964940353978830038675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743953253805305106718233 4307964940353978830038675)
          ·
            refine ⟨6461947410530968245058013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307964940353978830038675 6461947410530968245058013)
            ·
              refine ⟨2423230278949113091896755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6461947410530968245058013 2423230278949113091896755)
              ·
                refine ⟨3634845418423669637845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423230278949113091896755 3634845418423669637845133)
                ·
                  refine ⟨1363067031908876114191925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3634845418423669637845133 1363067031908876114191925)
                  ·
                    refine ⟨127787534241457135705493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1363067031908876114191925 127787534241457135705493)
                    ·
                      rfl

theorem cell22_373298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_373298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373298 prefixEnd_373298 := by exact prefixLift 373298
  have htrace : WordTrace (prefixWord ++ tailWord_373298) baseStart_373298 baseEnd_373298 := by
    simpa [prefixWord, tailWord_373298, baseEnd_373298] using wordTrace_append hprefix tailTrace_373298
  have hstable : (prefixWord ++ tailWord_373298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373298).length < 2 ^ (prefixWord ++ tailWord_373298).sum := by decide
  have hdescent : baseEnd_373298 < baseStart_373298 := by decide
  rcases family_descends (prefixWord ++ tailWord_373298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373310 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_373310 : Nat := 118140960795 + 373310 * 2 ^ 59
def prefixEnd_373310 : Nat := 4983230072969 + 3 ^ 40 * 373310 * 2
def baseEnd_373310 : Nat := 127791642086693104405457

theorem tailTrace_373310 : CollatzResearch.WordTrace tailWord_373310 prefixEnd_373310 127791642086693104405457 := by
  unfold tailWord_373310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701966784696137639651673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9077156185046067411475589 1701966784696137639651673)
  ·
    refine ⟨1276475088522103229738755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1701966784696137639651673 1276475088522103229738755)
    ·
      refine ⟨1914712632783154844608133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276475088522103229738755 1914712632783154844608133)
      ·
        refine ⟨359008618646841533364025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1914712632783154844608133 359008618646841533364025)
        ·
          refine ⟨269256463985131150023019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359008618646841533364025 269256463985131150023019)
          ·
            refine ⟨403884695977696725034529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269256463985131150023019 403884695977696725034529)
            ·
              refine ⟨302913521983272543775897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403884695977696725034529 302913521983272543775897)
              ·
                refine ⟨227185141487454407831923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302913521983272543775897 227185141487454407831923)
                ·
                  refine ⟨340777712231181611747885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227185141487454407831923 340777712231181611747885)
                  ·
                    refine ⟨127791642086693104405457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340777712231181611747885 127791642086693104405457)
                    ·
                      rfl

theorem cell22_373310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_373310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373310 prefixEnd_373310 := by exact prefixLift 373310
  have htrace : WordTrace (prefixWord ++ tailWord_373310) baseStart_373310 baseEnd_373310 := by
    simpa [prefixWord, tailWord_373310, baseEnd_373310] using wordTrace_append hprefix tailTrace_373310
  have hstable : (prefixWord ++ tailWord_373310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373310).length < 2 ^ (prefixWord ++ tailWord_373310).sum := by decide
  have hdescent : baseEnd_373310 < baseStart_373310 := by decide
  rcases family_descends (prefixWord ++ tailWord_373310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373317 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 4]
def baseStart_373317 : Nat := 118140960795 + 373317 * 2 ^ 59
def prefixEnd_373317 : Nat := 4983230072969 + 3 ^ 40 * 373317 * 2
def baseEnd_373317 : Nat := 42598012776582473160145

theorem tailTrace_373317 : CollatzResearch.WordTrace tailWord_373317 prefixEnd_373317 42598012776582473160145 := by
  unfold tailWord_373317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13615989588543741312718205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9077326392362494208478803 13615989588543741312718205)
  ·
    refine ⟨5105996095703902992269327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13615989588543741312718205 5105996095703902992269327)
    ·
      refine ⟨7658994143555854488403991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5105996095703902992269327 7658994143555854488403991)
      ·
        refine ⟨11488491215333781732605987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7658994143555854488403991 11488491215333781732605987)
        ·
          refine ⟨17232736823000672598908981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11488491215333781732605987 17232736823000672598908981)
          ·
            refine ⟨1615569077156313056147717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17232736823000672598908981 1615569077156313056147717)
            ·
              refine ⟨302919201966808698027697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1615569077156313056147717 302919201966808698027697)
              ·
                refine ⟨227189401475106523520773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302919201966808698027697 227189401475106523520773)
                ·
                  refine ⟨42598012776582473160145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227189401475106523520773 42598012776582473160145)
                  ·
                    rfl

theorem cell22_373317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_373317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373317 prefixEnd_373317 := by exact prefixLift 373317
  have htrace : WordTrace (prefixWord ++ tailWord_373317) baseStart_373317 baseEnd_373317 := by
    simpa [prefixWord, tailWord_373317, baseEnd_373317] using wordTrace_append hprefix tailTrace_373317
  have hstable : (prefixWord ++ tailWord_373317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373317).length < 2 ^ (prefixWord ++ tailWord_373317).sum := by decide
  have hdescent : baseEnd_373317 < baseStart_373317 := by decide
  rcases family_descends (prefixWord ++ tailWord_373317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373332 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_373332 : Nat := 118140960795 + 373332 * 2 ^ 59
def prefixEnd_373332 : Nat := 4983230072969 + 3 ^ 40 * 373332 * 2
def baseEnd_373332 : Nat := 127799173136292380355389

theorem tailTrace_373332 : CollatzResearch.WordTrace tailWord_373332 prefixEnd_373332 127799173136292380355389 := by
  unfold tailWord_373332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808268341744699437257125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9077691122326265916342833 6808268341744699437257125)
  ·
    refine ⟨1276550314077131144485711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6808268341744699437257125 1276550314077131144485711)
    ·
      refine ⟨1914825471115696716728567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276550314077131144485711 1914825471115696716728567)
      ·
        refine ⟨2872238206673545075092851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914825471115696716728567 2872238206673545075092851)
        ·
          refine ⟨4308357310010317612639277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872238206673545075092851 4308357310010317612639277)
          ·
            refine ⟨1615633991253869104739729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4308357310010317612639277 1615633991253869104739729)
            ·
              refine ⟨1211725493440401828554797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615633991253869104739729 1211725493440401828554797)
              ·
                refine ⟨454397060040150685708049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1211725493440401828554797 454397060040150685708049)
                ·
                  refine ⟨340797795030113014281037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454397060040150685708049 340797795030113014281037)
                  ·
                    refine ⟨127799173136292380355389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340797795030113014281037 127799173136292380355389)
                    ·
                      rfl

theorem cell22_373332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_373332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373332 prefixEnd_373332 := by exact prefixLift 373332
  have htrace : WordTrace (prefixWord ++ tailWord_373332) baseStart_373332 baseEnd_373332 := by
    simpa [prefixWord, tailWord_373332, baseEnd_373332] using wordTrace_append hprefix tailTrace_373332
  have hstable : (prefixWord ++ tailWord_373332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373332).length < 2 ^ (prefixWord ++ tailWord_373332).sum := by decide
  have hdescent : baseEnd_373332 < baseStart_373332 := by decide
  rcases family_descends (prefixWord ++ tailWord_373332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373345 : List Nat := [1, 2, 3, 1, 1, 5, 3, 6]
def baseStart_373345 : Nat := 118140960795 + 373345 * 2 ^ 59
def prefixEnd_373345 : Nat := 4983230072969 + 3 ^ 40 * 373345 * 2
def baseEnd_373345 : Nat := 14200402589107186642261

theorem tailTrace_373345 : CollatzResearch.WordTrace tailWord_373345 prefixEnd_373345 14200402589107186642261 := by
  unfold tailWord_373345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13617010832442302094737489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9078007221628201396491659 13617010832442302094737489)
  ·
    refine ⟨10212758124331726571053117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13617010832442302094737489 10212758124331726571053117)
    ·
      refine ⟨3829784296624397464144919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10212758124331726571053117 3829784296624397464144919)
      ·
        refine ⟨5744676444936596196217379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829784296624397464144919 5744676444936596196217379)
        ·
          refine ⟨8617014667404894294326069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744676444936596196217379 8617014667404894294326069)
          ·
            refine ⟨807845125069208840093069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8617014667404894294326069 807845125069208840093069)
            ·
              refine ⟨302941921900953315034901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807845125069208840093069 302941921900953315034901)
              ·
                refine ⟨14200402589107186642261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 302941921900953315034901 14200402589107186642261)
                ·
                  rfl

theorem cell22_373345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 6].length) (baseStart_373345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373345 prefixEnd_373345 := by exact prefixLift 373345
  have htrace : WordTrace (prefixWord ++ tailWord_373345) baseStart_373345 baseEnd_373345 := by
    simpa [prefixWord, tailWord_373345, baseEnd_373345] using wordTrace_append hprefix tailTrace_373345
  have hstable : (prefixWord ++ tailWord_373345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373345).length < 2 ^ (prefixWord ++ tailWord_373345).sum := by decide
  have hdescent : baseEnd_373345 < baseStart_373345 := by decide
  rcases family_descends (prefixWord ++ tailWord_373345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373366 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_373366 : Nat := 118140960795 + 373366 * 2 ^ 59
def prefixEnd_373366 : Nat := 4983230072969 + 3 ^ 40 * 373366 * 2
def baseEnd_373366 : Nat := 127810812031127625005285

theorem tailTrace_373366 : CollatzResearch.WordTrace tailWord_373366 prefixEnd_373366 127810812031127625005285 := by
  unfold tailWord_373366
  simp only [CollatzResearch.WordTrace]
  refine ⟨851111047835388917578247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9078517843577481787501301 851111047835388917578247)
  ·
    refine ⟨1276666571753083376367371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 851111047835388917578247 1276666571753083376367371)
    ·
      refine ⟨1914999857629625064551057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276666571753083376367371 1914999857629625064551057)
      ·
        refine ⟨1436249893222218798413293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1914999857629625064551057 1436249893222218798413293)
        ·
          refine ⟨538593709958332049404985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1436249893222218798413293 538593709958332049404985)
          ·
            refine ⟨403945282468749037053739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538593709958332049404985 403945282468749037053739)
            ·
              refine ⟨605917923703123555580609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403945282468749037053739 605917923703123555580609)
              ·
                refine ⟨454438442777342666685457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605917923703123555580609 454438442777342666685457)
                ·
                  refine ⟨340828832083007000014093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454438442777342666685457 340828832083007000014093)
                  ·
                    refine ⟨127810812031127625005285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340828832083007000014093 127810812031127625005285)
                    ·
                      rfl

theorem cell22_373366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_373366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373366 prefixEnd_373366 := by exact prefixLift 373366
  have htrace : WordTrace (prefixWord ++ tailWord_373366) baseStart_373366 baseEnd_373366 := by
    simpa [prefixWord, tailWord_373366, baseEnd_373366] using wordTrace_append hprefix tailTrace_373366
  have hstable : (prefixWord ++ tailWord_373366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373366).length < 2 ^ (prefixWord ++ tailWord_373366).sum := by decide
  have hdescent : baseEnd_373366 < baseStart_373366 := by decide
  rcases family_descends (prefixWord ++ tailWord_373366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373377 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_373377 : Nat := 118140960795 + 373377 * 2 ^ 59
def prefixEnd_373377 : Nat := 4983230072969 + 3 ^ 40 * 373377 * 2
def baseEnd_373377 : Nat := 127814577555927262980251

theorem tailTrace_373377 : CollatzResearch.WordTrace tailWord_373377 prefixEnd_373377 127814577555927262980251 := by
  unfold tailWord_373377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13618177968326371559902385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9078785312217581039934923 13618177968326371559902385)
  ·
    refine ⟨10213633476244778669926789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13618177968326371559902385 10213633476244778669926789)
    ·
      refine ⟨1915056276795896000611273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10213633476244778669926789 1915056276795896000611273)
      ·
        refine ⟨1436292207596922000458455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1915056276795896000611273 1436292207596922000458455)
        ·
          refine ⟨2154438311395383000687683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436292207596922000458455 2154438311395383000687683)
          ·
            refine ⟨3231657467093074501031525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154438311395383000687683 3231657467093074501031525)
            ·
              refine ⟨605935775079951468943411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3231657467093074501031525 605935775079951468943411)
              ·
                refine ⟨908903662619927203415117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605935775079951468943411 908903662619927203415117)
                ·
                  refine ⟨340838873482472701280669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908903662619927203415117 340838873482472701280669)
                  ·
                    refine ⟨127814577555927262980251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340838873482472701280669 127814577555927262980251)
                    ·
                      rfl

theorem cell22_373377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_373377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373377 prefixEnd_373377 := by exact prefixLift 373377
  have htrace : WordTrace (prefixWord ++ tailWord_373377) baseStart_373377 baseEnd_373377 := by
    simpa [prefixWord, tailWord_373377, baseEnd_373377] using wordTrace_append hprefix tailTrace_373377
  have hstable : (prefixWord ++ tailWord_373377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373377).length < 2 ^ (prefixWord ++ tailWord_373377).sum := by decide
  have hdescent : baseEnd_373377 < baseStart_373377 := by decide
  rcases family_descends (prefixWord ++ tailWord_373377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373388 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_373388 : Nat := 118140960795 + 373388 * 2 ^ 59
def prefixEnd_373388 : Nat := 4983230072969 + 3 ^ 40 * 373388 * 2
def baseEnd_373388 : Nat := 127818343080726900955217

theorem tailTrace_373388 : CollatzResearch.WordTrace tailWord_373388 prefixEnd_373388 127818343080726900955217 := by
  unfold tailWord_373388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6809289585643260219276409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9079052780857680292368545 6809289585643260219276409)
  ·
    refine ⟨5106967189232445164457307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6809289585643260219276409 5106967189232445164457307)
    ·
      refine ⟨7660450783848667746685961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106967189232445164457307 7660450783848667746685961)
      ·
        refine ⟨5745338087886500810014471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7660450783848667746685961 5745338087886500810014471)
        ·
          refine ⟨8618007131829751215021707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745338087886500810014471 8618007131829751215021707)
          ·
            refine ⟨12927010697744626822532561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618007131829751215021707 12927010697744626822532561)
            ·
              refine ⟨9695258023308470116899421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12927010697744626822532561 9695258023308470116899421)
              ·
                refine ⟨3635721758740676293837283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9695258023308470116899421 3635721758740676293837283)
                ·
                  refine ⟨5453582638111014440755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635721758740676293837283 5453582638111014440755925)
                  ·
                    refine ⟨127818343080726900955217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5453582638111014440755925 127818343080726900955217)
                    ·
                      rfl

theorem cell22_373388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_373388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373388 prefixEnd_373388 := by exact prefixLift 373388
  have htrace : WordTrace (prefixWord ++ tailWord_373388) baseStart_373388 baseEnd_373388 := by
    simpa [prefixWord, tailWord_373388, baseEnd_373388] using wordTrace_append hprefix tailTrace_373388
  have hstable : (prefixWord ++ tailWord_373388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373388).length < 2 ^ (prefixWord ++ tailWord_373388).sum := by decide
  have hdescent : baseEnd_373388 < baseStart_373388 := by decide
  rcases family_descends (prefixWord ++ tailWord_373388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373454 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_373454 : Nat := 118140960795 + 373454 * 2 ^ 59
def prefixEnd_373454 : Nat := 4983230072969 + 3 ^ 40 * 373454 * 2
def baseEnd_373454 : Nat := 127840936229524728805015

theorem tailTrace_373454 : CollatzResearch.WordTrace tailWord_373454 prefixEnd_373454 127840936229524728805015 := by
  unfold tailWord_373454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702623298630926713806927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9080657592698275806970277 1702623298630926713806927)
  ·
    refine ⟨2553934947946390070710391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1702623298630926713806927 2553934947946390070710391)
    ·
      refine ⟨3830902421919585106065587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2553934947946390070710391 3830902421919585106065587)
      ·
        refine ⟨5746353632879377659098381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830902421919585106065587 5746353632879377659098381)
        ·
          refine ⟨2154882612329766622161893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5746353632879377659098381 2154882612329766622161893)
          ·
            refine ⟨404040489811831241655355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2154882612329766622161893 404040489811831241655355)
            ·
              refine ⟨606060734717746862483033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404040489811831241655355 606060734717746862483033)
              ·
                refine ⟨454545551038310146862275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606060734717746862483033 454545551038310146862275)
                ·
                  refine ⟨681818326557465220293413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454545551038310146862275 681818326557465220293413)
                  ·
                    refine ⟨127840936229524728805015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681818326557465220293413 127840936229524728805015)
                    ·
                      rfl

theorem cell22_373454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_373454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373454 prefixEnd_373454 := by exact prefixLift 373454
  have htrace : WordTrace (prefixWord ++ tailWord_373454) baseStart_373454 baseEnd_373454 := by
    simpa [prefixWord, tailWord_373454, baseEnd_373454] using wordTrace_append hprefix tailTrace_373454
  have hstable : (prefixWord ++ tailWord_373454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373454).length < 2 ^ (prefixWord ++ tailWord_373454).sum := by decide
  have hdescent : baseEnd_373454 < baseStart_373454 := by decide
  rcases family_descends (prefixWord ++ tailWord_373454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373480 : List Nat := [2, 1, 4, 1, 4, 10]
def baseStart_373480 : Nat := 118140960795 + 373480 * 2 ^ 59
def prefixEnd_373480 : Nat := 4983230072969 + 3 ^ 40 * 373480 * 2
def baseEnd_373480 : Nat := 1578393043961349724135

theorem tailTrace_373480 : CollatzResearch.WordTrace tailWord_373480 prefixEnd_373480 1578393043961349724135 := by
  unfold tailWord_373480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810967343476610075450947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9081289791302146767267929 6810967343476610075450947)
  ·
    refine ⟨10216451015214915113176421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6810967343476610075450947 10216451015214915113176421)
    ·
      refine ⟨1915584565352796583720579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10216451015214915113176421 1915584565352796583720579)
      ·
        refine ⟨2873376848029194875580869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915584565352796583720579 2873376848029194875580869)
        ·
          refine ⟨538758159005474039171413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2873376848029194875580869 538758159005474039171413)
          ·
            refine ⟨1578393043961349724135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 538758159005474039171413 1578393043961349724135)
            ·
              rfl

theorem cell22_373480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 10].length) (baseStart_373480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373480 prefixEnd_373480 := by exact prefixLift 373480
  have htrace : WordTrace (prefixWord ++ tailWord_373480) baseStart_373480 baseEnd_373480 := by
    simpa [prefixWord, tailWord_373480, baseEnd_373480] using wordTrace_append hprefix tailTrace_373480
  have hstable : (prefixWord ++ tailWord_373480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373480).length < 2 ^ (prefixWord ++ tailWord_373480).sum := by decide
  have hdescent : baseEnd_373480 < baseStart_373480 := by decide
  rcases family_descends (prefixWord ++ tailWord_373480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373486 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_373486 : Nat := 118140960795 + 373486 * 2 ^ 59
def prefixEnd_373486 : Nat := 4983230072969 + 3 ^ 40 * 373486 * 2
def baseEnd_373486 : Nat := 42617296827829104001639

theorem tailTrace_373486 : CollatzResearch.WordTrace tailWord_373486 prefixEnd_373486 42617296827829104001639 := by
  unfold tailWord_373486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702769190616435396952539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9081435683287655450413541 1702769190616435396952539)
  ·
    refine ⟨2554153785924653095428809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1702769190616435396952539 2554153785924653095428809)
    ·
      refine ⟨1915615339443489821571607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2554153785924653095428809 1915615339443489821571607)
      ·
        refine ⟨2873423009165234732357411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915615339443489821571607 2873423009165234732357411)
        ·
          refine ⟨4310134513747852098536117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873423009165234732357411 4310134513747852098536117)
          ·
            refine ⟨404075110663861134237761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4310134513747852098536117 404075110663861134237761)
            ·
              refine ⟨303056332997895850678321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404075110663861134237761 303056332997895850678321)
              ·
                refine ⟨227292249748421888008741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303056332997895850678321 227292249748421888008741)
                ·
                  refine ⟨42617296827829104001639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227292249748421888008741 42617296827829104001639)
                  ·
                    rfl

theorem cell22_373486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_373486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373486 prefixEnd_373486 := by exact prefixLift 373486
  have htrace : WordTrace (prefixWord ++ tailWord_373486) baseStart_373486 baseEnd_373486 := by
    simpa [prefixWord, tailWord_373486, baseEnd_373486] using wordTrace_append hprefix tailTrace_373486
  have hstable : (prefixWord ++ tailWord_373486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373486).length < 2 ^ (prefixWord ++ tailWord_373486).sum := by decide
  have hdescent : baseEnd_373486 < baseStart_373486 := by decide
  rcases family_descends (prefixWord ++ tailWord_373486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373512 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_373512 : Nat := 118140960795 + 373512 * 2 ^ 59
def prefixEnd_373512 : Nat := 4983230072969 + 3 ^ 40 * 373512 * 2
def baseEnd_373512 : Nat := 127860790814831910854837

theorem tailTrace_373512 : CollatzResearch.WordTrace tailWord_373512 prefixEnd_373512 127860790814831910854837 := by
  unfold tailWord_373512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811550911418644808033395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9082067881891526410711193 6811550911418644808033395)
  ·
    refine ⟨10217326367127967212050093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6811550911418644808033395 10217326367127967212050093)
    ·
      refine ⟨3831497387672987704518785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10217326367127967212050093 3831497387672987704518785)
      ·
        refine ⟨2873623040754740778389089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3831497387672987704518785 2873623040754740778389089)
        ·
          refine ⟨2155217280566055583791817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873623040754740778389089 2155217280566055583791817)
          ·
            refine ⟨1616412960424541687843863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2155217280566055583791817 1616412960424541687843863)
            ·
              refine ⟨2424619440636812531765795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616412960424541687843863 2424619440636812531765795)
              ·
                refine ⟨3636929160955218797648693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424619440636812531765795 3636929160955218797648693)
                ·
                  refine ⟨340962108839551762279565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3636929160955218797648693 340962108839551762279565)
                  ·
                    refine ⟨127860790814831910854837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340962108839551762279565 127860790814831910854837)
                    ·
                      rfl

theorem cell22_373512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_373512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373512 prefixEnd_373512 := by exact prefixLift 373512
  have htrace : WordTrace (prefixWord ++ tailWord_373512) baseStart_373512 baseEnd_373512 := by
    simpa [prefixWord, tailWord_373512, baseEnd_373512] using wordTrace_append hprefix tailTrace_373512
  have hstable : (prefixWord ++ tailWord_373512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373512).length < 2 ^ (prefixWord ++ tailWord_373512).sum := by decide
  have hdescent : baseEnd_373512 < baseStart_373512 := by decide
  rcases family_descends (prefixWord ++ tailWord_373512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373525 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 7]
def baseStart_373525 : Nat := 118140960795 + 373525 * 2 ^ 59
def prefixEnd_373525 : Nat := 4983230072969 + 3 ^ 40 * 373525 * 2
def baseEnd_373525 : Nat := 42621746993501403426599

theorem tailTrace_373525 : CollatzResearch.WordTrace tailWord_373525 prefixEnd_373525 42621746993501403426599 := by
  unfold tailWord_373525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623575971790192836290029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9082383981193461890860019 13623575971790192836290029)
  ·
    refine ⟨5108840989421322313608761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13623575971790192836290029 5108840989421322313608761)
    ·
      refine ⟨3831630742065991735206571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5108840989421322313608761 3831630742065991735206571)
      ·
        refine ⟨5747446113098987602809857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3831630742065991735206571 5747446113098987602809857)
        ·
          refine ⟨4310584584824240702107393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747446113098987602809857 4310584584824240702107393)
          ·
            refine ⟨3232938438618180526580545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310584584824240702107393 3232938438618180526580545)
            ·
              refine ⟨2424703828963635394935409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232938438618180526580545 2424703828963635394935409)
              ·
                refine ⟨1818527871722726546201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424703828963635394935409 1818527871722726546201557)
                ·
                  refine ⟨42621746993501403426599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1818527871722726546201557 42621746993501403426599)
                  ·
                    rfl

theorem cell22_373525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_373525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373525 prefixEnd_373525 := by exact prefixLift 373525
  have htrace : WordTrace (prefixWord ++ tailWord_373525) baseStart_373525 baseEnd_373525 := by
    simpa [prefixWord, tailWord_373525, baseEnd_373525] using wordTrace_append hprefix tailTrace_373525
  have hstable : (prefixWord ++ tailWord_373525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373525).length < 2 ^ (prefixWord ++ tailWord_373525).sum := by decide
  have hdescent : baseEnd_373525 < baseStart_373525 := by decide
  rcases family_descends (prefixWord ++ tailWord_373525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373557 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_373557 : Nat := 118140960795 + 373557 * 2 ^ 59
def prefixEnd_373557 : Nat := 4983230072969 + 3 ^ 40 * 373557 * 2
def baseEnd_373557 : Nat := 127876195234466793479699

theorem tailTrace_373557 : CollatzResearch.WordTrace tailWord_373557 prefixEnd_373557 127876195234466793479699 := by
  unfold tailWord_373557
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624743107674262301454925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9083162071782841534303283 13624743107674262301454925)
  ·
    refine ⟨5109278665377848363045597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13624743107674262301454925 5109278665377848363045597)
    ·
      refine ⟨1915979499516693136142099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5109278665377848363045597 1915979499516693136142099)
      ·
        refine ⟨2873969249275039704213149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915979499516693136142099 2873969249275039704213149)
        ·
          refine ⟨1077738468478139889079931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2873969249275039704213149 1077738468478139889079931)
          ·
            refine ⟨1616607702717209833619897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077738468478139889079931 1616607702717209833619897)
            ·
              refine ⟨1212455777037907375214923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616607702717209833619897 1212455777037907375214923)
              ·
                refine ⟨1818683665556861062822385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212455777037907375214923 1818683665556861062822385)
                ·
                  refine ⟨1364012749167645797116789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818683665556861062822385 1364012749167645797116789)
                  ·
                    refine ⟨127876195234466793479699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1364012749167645797116789 127876195234466793479699)
                    ·
                      rfl

theorem cell22_373557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_373557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373557 prefixEnd_373557 := by exact prefixLift 373557
  have htrace : WordTrace (prefixWord ++ tailWord_373557) baseStart_373557 baseEnd_373557 := by
    simpa [prefixWord, tailWord_373557, baseEnd_373557] using wordTrace_append hprefix tailTrace_373557
  have hstable : (prefixWord ++ tailWord_373557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373557).length < 2 ^ (prefixWord ++ tailWord_373557).sum := by decide
  have hdescent : baseEnd_373557 < baseStart_373557 := by decide
  rcases family_descends (prefixWord ++ tailWord_373557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373604 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_373604 : Nat := 118140960795 + 373604 * 2 ^ 59
def prefixEnd_373604 : Nat := 4983230072969 + 3 ^ 40 * 373604 * 2
def baseEnd_373604 : Nat := 42630761431658112518185

theorem tailTrace_373604 : CollatzResearch.WordTrace tailWord_373604 prefixEnd_373604 42630761431658112518185 := by
  unfold tailWord_373604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813228669251994664207933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9084304892335992885610577 6813228669251994664207933)
  ·
    refine ⟨2554960750969497999077975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6813228669251994664207933 2554960750969497999077975)
    ·
      refine ⟨3832441126454246998616963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2554960750969497999077975 3832441126454246998616963)
      ·
        refine ⟨5748661689681370497925445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832441126454246998616963 5748661689681370497925445)
        ·
          refine ⟨1077874066815256968361021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5748661689681370497925445 1077874066815256968361021)
          ·
            refine ⟨404202775055721363135383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1077874066815256968361021 404202775055721363135383)
            ·
              refine ⟨606304162583582044703075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404202775055721363135383 606304162583582044703075)
              ·
                refine ⟨909456243875373067054613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606304162583582044703075 909456243875373067054613)
                ·
                  refine ⟨42630761431658112518185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 909456243875373067054613 42630761431658112518185)
                  ·
                    rfl

theorem cell22_373604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_373604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373604 prefixEnd_373604 := by exact prefixLift 373604
  have htrace : WordTrace (prefixWord ++ tailWord_373604) baseStart_373604 baseEnd_373604 := by
    simpa [prefixWord, tailWord_373604, baseEnd_373604] using wordTrace_append hprefix tailTrace_373604
  have hstable : (prefixWord ++ tailWord_373604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373604).length < 2 ^ (prefixWord ++ tailWord_373604).sum := by decide
  have hdescent : baseEnd_373604 < baseStart_373604 := by decide
  rcases family_descends (prefixWord ++ tailWord_373604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373681 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 3, 3]
def baseStart_373681 : Nat := 118140960795 + 373681 * 2 ^ 59
def prefixEnd_373681 : Nat := 4983230072969 + 3 ^ 40 * 373681 * 2
def baseEnd_373681 : Nat := 127918642968571803379319

theorem tailTrace_373681 : CollatzResearch.WordTrace tailWord_373681 prefixEnd_373681 127918642968571803379319 := by
  unfold tailWord_373681
  simp only [CollatzResearch.WordTrace]
  refine ⟨13629265759225031478968897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9086177172816687652645931 13629265759225031478968897)
  ·
    refine ⟨10221949319418773609226673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13629265759225031478968897 10221949319418773609226673)
    ·
      refine ⟨7666461989564080206920005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10221949319418773609226673 7666461989564080206920005)
      ·
        refine ⟨1437461623043265038797501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7666461989564080206920005 1437461623043265038797501)
        ·
          refine ⟨539048108641224389549063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1437461623043265038797501 539048108641224389549063)
          ·
            refine ⟨808572162961836584323595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539048108641224389549063 808572162961836584323595)
            ·
              refine ⟨1212858244442754876485393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808572162961836584323595 1212858244442754876485393)
              ·
                refine ⟨909643683332066157364045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212858244442754876485393 909643683332066157364045)
                ·
                  refine ⟨341116381249524809011517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909643683332066157364045 341116381249524809011517)
                  ·
                    refine ⟨127918642968571803379319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341116381249524809011517 127918642968571803379319)
                    ·
                      rfl

theorem cell22_373681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_373681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373681 prefixEnd_373681 := by exact prefixLift 373681
  have htrace : WordTrace (prefixWord ++ tailWord_373681) baseStart_373681 baseEnd_373681 := by
    simpa [prefixWord, tailWord_373681, baseEnd_373681] using wordTrace_append hprefix tailTrace_373681
  have hstable : (prefixWord ++ tailWord_373681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373681).length < 2 ^ (prefixWord ++ tailWord_373681).sum := by decide
  have hdescent : baseEnd_373681 < baseStart_373681 := by decide
  rcases family_descends (prefixWord ++ tailWord_373681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373749 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_373749 : Nat := 118140960795 + 373749 * 2 ^ 59
def prefixEnd_373749 : Nat := 4983230072969 + 3 ^ 40 * 373749 * 2
def baseEnd_373749 : Nat := 127941920758242292679111

theorem tailTrace_373749 : CollatzResearch.WordTrace tailWord_373749 prefixEnd_373749 127941920758242292679111 := by
  unfold tailWord_373749
  simp only [CollatzResearch.WordTrace]
  refine ⟨13631745922978679092444301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9087830615319119394962867 13631745922978679092444301)
  ·
    refine ⟨5111904721117004659666613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13631745922978679092444301 5111904721117004659666613)
    ·
      refine ⟨479241067604719186843745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5111904721117004659666613 479241067604719186843745)
      ·
        refine ⟨359430800703539390132809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479241067604719186843745 359430800703539390132809)
        ·
          refine ⟨269573100527654542599607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359430800703539390132809 269573100527654542599607)
          ·
            refine ⟨404359650791481813899411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269573100527654542599607 404359650791481813899411)
            ·
              refine ⟨606539476187222720849117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404359650791481813899411 606539476187222720849117)
              ·
                refine ⟨227452303570208520318419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 606539476187222720849117 227452303570208520318419)
                ·
                  refine ⟨341178455355312780477629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227452303570208520318419 341178455355312780477629)
                  ·
                    refine ⟨127941920758242292679111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341178455355312780477629 127941920758242292679111)
                    ·
                      rfl

theorem cell22_373749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_373749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373749 prefixEnd_373749 := by exact prefixLift 373749
  have htrace : WordTrace (prefixWord ++ tailWord_373749) baseStart_373749 baseEnd_373749 := by
    simpa [prefixWord, tailWord_373749, baseEnd_373749] using wordTrace_append hprefix tailTrace_373749
  have hstable : (prefixWord ++ tailWord_373749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373749).length < 2 ^ (prefixWord ++ tailWord_373749).sum := by decide
  have hdescent : baseEnd_373749 < baseStart_373749 := by decide
  rcases family_descends (prefixWord ++ tailWord_373749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373756 : List Nat := [2, 2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_373756 : Nat := 118140960795 + 373756 * 2 ^ 59
def prefixEnd_373756 : Nat := 4983230072969 + 3 ^ 40 * 373756 * 2
def baseEnd_373756 : Nat := 42648105667098869251363

theorem tailTrace_373756 : CollatzResearch.WordTrace tailWord_373756 prefixEnd_373756 42648105667098869251363 := by
  unfold tailWord_373756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816000616976659643974561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9088000822635546191966081 6816000616976659643974561)
  ·
    refine ⟨5112000462732494732980921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6816000616976659643974561 5112000462732494732980921)
    ·
      refine ⟨3834000347049371049735691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5112000462732494732980921 3834000347049371049735691)
      ·
        refine ⟨5751000520574056574603537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834000347049371049735691 5751000520574056574603537)
        ·
          refine ⟨4313250390430542430952653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5751000520574056574603537 4313250390430542430952653)
          ·
            refine ⟨1617468896411453411607245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4313250390430542430952653 1617468896411453411607245)
            ·
              refine ⟨606550836154295029352717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617468896411453411607245 606550836154295029352717)
              ·
                refine ⟨227456563557860636007269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 606550836154295029352717 227456563557860636007269)
                ·
                  refine ⟨42648105667098869251363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227456563557860636007269 42648105667098869251363)
                  ·
                    rfl

theorem cell22_373756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_373756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373756 prefixEnd_373756 := by exact prefixLift 373756
  have htrace : WordTrace (prefixWord ++ tailWord_373756) baseStart_373756 baseEnd_373756 := by
    simpa [prefixWord, tailWord_373756, baseEnd_373756] using wordTrace_append hprefix tailTrace_373756
  have hstable : (prefixWord ++ tailWord_373756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373756).length < 2 ^ (prefixWord ++ tailWord_373756).sum := by decide
  have hdescent : baseEnd_373756 < baseStart_373756 := by decide
  rcases family_descends (prefixWord ++ tailWord_373756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373784 : List Nat := [2, 1, 2, 3, 2, 3, 2, 7]
def baseStart_373784 : Nat := 118140960795 + 373784 * 2 ^ 59
def prefixEnd_373784 : Nat := 4983230072969 + 3 ^ 40 * 373784 * 2
def baseEnd_373784 : Nat := 14217100219279318672667

theorem tailTrace_373784 : CollatzResearch.WordTrace tailWord_373784 prefixEnd_373784 14217100219279318672667 := by
  unfold tailWord_373784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816511238925940034984203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9088681651901253379978937 6816511238925940034984203)
  ·
    refine ⟨10224766858388910052476305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6816511238925940034984203 10224766858388910052476305)
    ·
      refine ⟨7668575143791682539357229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10224766858388910052476305 7668575143791682539357229)
      ·
        refine ⟨2875715678921880952258961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7668575143791682539357229 2875715678921880952258961)
        ·
          refine ⟨2156786759191410714194221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2875715678921880952258961 2156786759191410714194221)
          ·
            refine ⟨808795034696779017822833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2156786759191410714194221 808795034696779017822833)
            ·
              refine ⟨606596276022584263367125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808795034696779017822833 606596276022584263367125)
              ·
                refine ⟨14217100219279318672667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 606596276022584263367125 14217100219279318672667)
                ·
                  rfl

theorem cell22_373784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_373784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373784 prefixEnd_373784 := by exact prefixLift 373784
  have htrace : WordTrace (prefixWord ++ tailWord_373784) baseStart_373784 baseEnd_373784 := by
    simpa [prefixWord, tailWord_373784, baseEnd_373784] using wordTrace_append hprefix tailTrace_373784
  have hstable : (prefixWord ++ tailWord_373784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373784).length < 2 ^ (prefixWord ++ tailWord_373784).sum := by decide
  have hdescent : baseEnd_373784 < baseStart_373784 := by decide
  rcases family_descends (prefixWord ++ tailWord_373784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373788 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_373788 : Nat := 118140960795 + 373788 * 2 ^ 59
def prefixEnd_373788 : Nat := 4983230072969 + 3 ^ 40 * 373788 * 2
def baseEnd_373788 : Nat := 127955271255259190953991

theorem tailTrace_373788 : CollatzResearch.WordTrace tailWord_373788 prefixEnd_373788 127955271255259190953991 := by
  unfold tailWord_373788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6816584184918694376557009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9088778913224925835409345 6816584184918694376557009)
  ·
    refine ⟨5112438138689020782417757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6816584184918694376557009 5112438138689020782417757)
    ·
      refine ⟨1917164302008382793406659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5112438138689020782417757 1917164302008382793406659)
      ·
        refine ⟨2875746453012574190109989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917164302008382793406659 2875746453012574190109989)
        ·
          refine ⟨539202459939857660645623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2875746453012574190109989 539202459939857660645623)
          ·
            refine ⟨808803689909786490968435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539202459939857660645623 808803689909786490968435)
            ·
              refine ⟨1213205534864679736452653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808803689909786490968435 1213205534864679736452653)
              ·
                refine ⟨454952075574254901169745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213205534864679736452653 454952075574254901169745)
                ·
                  refine ⟨341214056680691175877309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454952075574254901169745 341214056680691175877309)
                  ·
                    refine ⟨127955271255259190953991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341214056680691175877309 127955271255259190953991)
                    ·
                      rfl

theorem cell22_373788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_373788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373788 prefixEnd_373788 := by exact prefixLift 373788
  have htrace : WordTrace (prefixWord ++ tailWord_373788) baseStart_373788 baseEnd_373788 := by
    simpa [prefixWord, tailWord_373788, baseEnd_373788] using wordTrace_append hprefix tailTrace_373788
  have hstable : (prefixWord ++ tailWord_373788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373788).length < 2 ^ (prefixWord ++ tailWord_373788).sum := by decide
  have hdescent : baseEnd_373788 < baseStart_373788 := by decide
  rcases family_descends (prefixWord ++ tailWord_373788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373829 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 5]
def baseStart_373829 : Nat := 118140960795 + 373829 * 2 ^ 59
def prefixEnd_373829 : Nat := 4983230072969 + 3 ^ 40 * 373829 * 2
def baseEnd_373829 : Nat := 42656435464382916892955

theorem tailTrace_373829 : CollatzResearch.WordTrace tailWord_373829 prefixEnd_373829 42656435464382916892955 := by
  unfold tailWord_373829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13634663762688852755356541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9089775841792568503571027 13634663762688852755356541)
  ·
    refine ⟨5112998911008319783258703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13634663762688852755356541 5112998911008319783258703)
    ·
      refine ⟨7669498366512479674888055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5112998911008319783258703 7669498366512479674888055)
      ·
        refine ⟨11504247549768719512332083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669498366512479674888055 11504247549768719512332083)
        ·
          refine ⟨17256371324653079268498125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11504247549768719512332083 17256371324653079268498125)
          ·
            refine ⟨6471139246744904725686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17256371324653079268498125 6471139246744904725686797)
            ·
              refine ⟨2426677217529339272132549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6471139246744904725686797 2426677217529339272132549)
              ·
                refine ⟨455001978286751113524853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2426677217529339272132549 455001978286751113524853)
                ·
                  refine ⟨42656435464382916892955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 455001978286751113524853 42656435464382916892955)
                  ·
                    rfl

theorem cell22_373829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_373829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373829 prefixEnd_373829 := by exact prefixLift 373829
  have htrace : WordTrace (prefixWord ++ tailWord_373829) baseStart_373829 baseEnd_373829 := by
    simpa [prefixWord, tailWord_373829, baseEnd_373829] using wordTrace_append hprefix tailTrace_373829
  have hstable : (prefixWord ++ tailWord_373829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373829).length < 2 ^ (prefixWord ++ tailWord_373829).sum := by decide
  have hdescent : baseEnd_373829 < baseStart_373829 := by decide
  rcases family_descends (prefixWord ++ tailWord_373829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373844 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_373844 : Nat := 118140960795 + 373844 * 2 ^ 59
def prefixEnd_373844 : Nat := 4983230072969 + 3 ^ 40 * 373844 * 2
def baseEnd_373844 : Nat := 127974441199693711553819

theorem tailTrace_373844 : CollatzResearch.WordTrace tailWord_373844 prefixEnd_373844 127974441199693711553819 := by
  unfold tailWord_373844
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817605428817255158576293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9090140571756340211435057 6817605428817255158576293)
  ·
    refine ⟨1278301017903235342233055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6817605428817255158576293 1278301017903235342233055)
    ·
      refine ⟨1917451526854853013349583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278301017903235342233055 1917451526854853013349583)
      ·
        refine ⟨2876177290282279520024375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917451526854853013349583 2876177290282279520024375)
        ·
          refine ⟨4314265935423419280036563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876177290282279520024375 4314265935423419280036563)
          ·
            refine ⟨6471398903135128920054845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314265935423419280036563 6471398903135128920054845)
            ·
              refine ⟨2426774588675673345020567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6471398903135128920054845 2426774588675673345020567)
              ·
                refine ⟨3640161883013510017530851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426774588675673345020567 3640161883013510017530851)
                ·
                  refine ⟨5460242824520265026296277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640161883013510017530851 5460242824520265026296277)
                  ·
                    refine ⟨127974441199693711553819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5460242824520265026296277 127974441199693711553819)
                    ·
                      rfl

theorem cell22_373844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_373844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373844 prefixEnd_373844 := by exact prefixLift 373844
  have htrace : WordTrace (prefixWord ++ tailWord_373844) baseStart_373844 baseEnd_373844 := by
    simpa [prefixWord, tailWord_373844, baseEnd_373844] using wordTrace_append hprefix tailTrace_373844
  have hstable : (prefixWord ++ tailWord_373844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373844).length < 2 ^ (prefixWord ++ tailWord_373844).sum := by decide
  have hdescent : baseEnd_373844 < baseStart_373844 := by decide
  rcases family_descends (prefixWord ++ tailWord_373844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373874 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_373874 : Nat := 118140960795 + 373874 * 2 ^ 59
def prefixEnd_373874 : Nat := 4983230072969 + 3 ^ 40 * 373874 * 2
def baseEnd_373874 : Nat := 42661570270927877767909

theorem tailTrace_373874 : CollatzResearch.WordTrace tailWord_373874 prefixEnd_373874 42661570270927877767909 := by
  unfold tailWord_373874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3409076261881456360186169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9090870031683883627163117 3409076261881456360186169)
  ·
    refine ⟨2556807196411092270139627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3409076261881456360186169 2556807196411092270139627)
    ·
      refine ⟨3835210794616638405209441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2556807196411092270139627 3835210794616638405209441)
      ·
        refine ⟨2876408095962478803907081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3835210794616638405209441 2876408095962478803907081)
        ·
          refine ⟨2157306071971859102930311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876408095962478803907081 2157306071971859102930311)
          ·
            refine ⟨3235959107957788654395467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157306071971859102930311 3235959107957788654395467)
            ·
              refine ⟨4853938661936682981593201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235959107957788654395467 4853938661936682981593201)
              ·
                refine ⟨3640453996452512236194901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853938661936682981593201 3640453996452512236194901)
                ·
                  refine ⟨42661570270927877767909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3640453996452512236194901 42661570270927877767909)
                  ·
                    rfl

theorem cell22_373874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_373874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373874 prefixEnd_373874 := by exact prefixLift 373874
  have htrace : WordTrace (prefixWord ++ tailWord_373874) baseStart_373874 baseEnd_373874 := by
    simpa [prefixWord, tailWord_373874, baseEnd_373874] using wordTrace_append hprefix tailTrace_373874
  have hstable : (prefixWord ++ tailWord_373874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373874).length < 2 ^ (prefixWord ++ tailWord_373874).sum := by decide
  have hdescent : baseEnd_373874 < baseStart_373874 := by decide
  rcases family_descends (prefixWord ++ tailWord_373874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373891 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 4]
def baseStart_373891 : Nat := 118140960795 + 373891 * 2 ^ 59
def prefixEnd_373891 : Nat := 4983230072969 + 3 ^ 40 * 373891 * 2
def baseEnd_373891 : Nat := 42663510086733751876225

theorem tailTrace_373891 : CollatzResearch.WordTrace tailWord_373891 prefixEnd_373891 42663510086733751876225 := by
  unfold tailWord_373891
  simp only [CollatzResearch.WordTrace]
  refine ⟨13636925088464237344113527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9091283392309491562742351 13636925088464237344113527)
  ·
    refine ⟨20455387632696356016170291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13636925088464237344113527 20455387632696356016170291)
    ·
      refine ⟨30683081449044534024255437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20455387632696356016170291 30683081449044534024255437)
      ·
        refine ⟨11506155543391700259095789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30683081449044534024255437 11506155543391700259095789)
        ·
          refine ⟨4314808328771887597160921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11506155543391700259095789 4314808328771887597160921)
          ·
            refine ⟨3236106246578915697870691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314808328771887597160921 3236106246578915697870691)
            ·
              refine ⟨4854159369868373546806037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236106246578915697870691 4854159369868373546806037)
              ·
                refine ⟨227538720462580010006533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4854159369868373546806037 227538720462580010006533)
                ·
                  refine ⟨42663510086733751876225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227538720462580010006533 42663510086733751876225)
                  ·
                    rfl

theorem cell22_373891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 4].length) (baseStart_373891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373891 prefixEnd_373891 := by exact prefixLift 373891
  have htrace : WordTrace (prefixWord ++ tailWord_373891) baseStart_373891 baseEnd_373891 := by
    simpa [prefixWord, tailWord_373891, baseEnd_373891] using wordTrace_append hprefix tailTrace_373891
  have hstable : (prefixWord ++ tailWord_373891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373891).length < 2 ^ (prefixWord ++ tailWord_373891).sum := by decide
  have hdescent : baseEnd_373891 < baseStart_373891 := by decide
  rcases family_descends (prefixWord ++ tailWord_373891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373904 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_373904 : Nat := 118140960795 + 373904 * 2 ^ 59
def prefixEnd_373904 : Nat := 4983230072969 + 3 ^ 40 * 373904 * 2
def baseEnd_373904 : Nat := 127994980425873555053635

theorem tailTrace_373904 : CollatzResearch.WordTrace tailWord_373904 prefixEnd_373904 127994980425873555053635 := by
  unfold tailWord_373904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6818699618708570282168383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9091599491611427042891177 6818699618708570282168383)
  ·
    refine ⟨10228049428062855423252575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6818699618708570282168383 10228049428062855423252575)
    ·
      refine ⟨15342074142094283134878863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10228049428062855423252575 15342074142094283134878863)
      ·
        refine ⟨23013111213141424702318295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342074142094283134878863 23013111213141424702318295)
        ·
          refine ⟨34519666819712137053477443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23013111213141424702318295 34519666819712137053477443)
          ·
            refine ⟨51779500229568205580216165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34519666819712137053477443 51779500229568205580216165)
            ·
              refine ⟨9708656293044038546290531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51779500229568205580216165 9708656293044038546290531)
              ·
                refine ⟨14562984439566057819435797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9708656293044038546290531 14562984439566057819435797)
                ·
                  refine ⟨682639895604658960286053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14562984439566057819435797 682639895604658960286053)
                  ·
                    refine ⟨127994980425873555053635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682639895604658960286053 127994980425873555053635)
                    ·
                      rfl

theorem cell22_373904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_373904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373904 prefixEnd_373904 := by exact prefixLift 373904
  have htrace : WordTrace (prefixWord ++ tailWord_373904) baseStart_373904 baseEnd_373904 := by
    simpa [prefixWord, tailWord_373904, baseEnd_373904] using wordTrace_append hprefix tailTrace_373904
  have hstable : (prefixWord ++ tailWord_373904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373904).length < 2 ^ (prefixWord ++ tailWord_373904).sum := by decide
  have hdescent : baseEnd_373904 < baseStart_373904 := by decide
  rcases family_descends (prefixWord ++ tailWord_373904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373921 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_373921 : Nat := 118140960795 + 373921 * 2 ^ 59
def prefixEnd_373921 : Nat := 4983230072969 + 3 ^ 40 * 373921 * 2
def baseEnd_373921 : Nat := 128000799873291177378583

theorem tailTrace_373921 : CollatzResearch.WordTrace tailWord_373921 prefixEnd_373921 128000799873291177378583 := by
  unfold tailWord_373921
  simp only [CollatzResearch.WordTrace]
  refine ⟨13638019278355552467705617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9092012852237034978470411 13638019278355552467705617)
  ·
    refine ⟨10228514458766664350779213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13638019278355552467705617 10228514458766664350779213)
    ·
      refine ⟨3835692922037499131542205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10228514458766664350779213 3835692922037499131542205)
      ·
        refine ⟨1438384845764062174328327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3835692922037499131542205 1438384845764062174328327)
        ·
          refine ⟨2157577268646093261492491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438384845764062174328327 2157577268646093261492491)
          ·
            refine ⟨3236365902969139892238737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157577268646093261492491 3236365902969139892238737)
            ·
              refine ⟨2427274427226854919179053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236365902969139892238737 2427274427226854919179053)
              ·
                refine ⟨910227910210070594692145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427274427226854919179053 910227910210070594692145)
                ·
                  refine ⟨682670932657552946019109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 910227910210070594692145 682670932657552946019109)
                  ·
                    refine ⟨128000799873291177378583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682670932657552946019109 128000799873291177378583)
                    ·
                      rfl

theorem cell22_373921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_373921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373921 prefixEnd_373921 := by exact prefixLift 373921
  have htrace : WordTrace (prefixWord ++ tailWord_373921) baseStart_373921 baseEnd_373921 := by
    simpa [prefixWord, tailWord_373921, baseEnd_373921] using wordTrace_append hprefix tailTrace_373921
  have hstable : (prefixWord ++ tailWord_373921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373921).length < 2 ^ (prefixWord ++ tailWord_373921).sum := by decide
  have hdescent : baseEnd_373921 < baseStart_373921 := by decide
  rcases family_descends (prefixWord ++ tailWord_373921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373942 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_373942 : Nat := 118140960795 + 373942 * 2 ^ 59
def prefixEnd_373942 : Nat := 4983230072969 + 3 ^ 40 * 373942 * 2
def baseEnd_373942 : Nat := 42669329534151374201173

theorem tailTrace_373942 : CollatzResearch.WordTrace tailWord_373942 prefixEnd_373942 42669329534151374201173 := by
  unfold tailWord_373942
  simp only [CollatzResearch.WordTrace]
  refine ⟨852424075704967065888755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9092523474186315369480053 852424075704967065888755)
  ·
    refine ⟨1278636113557450598833133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 852424075704967065888755 1278636113557450598833133)
    ·
      refine ⟨479488542584043974562425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1278636113557450598833133 479488542584043974562425)
      ·
        refine ⟨359616406938032980921819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479488542584043974562425 359616406938032980921819)
        ·
          refine ⟨539424610407049471382729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359616406938032980921819 539424610407049471382729)
          ·
            refine ⟨404568457805287103537047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539424610407049471382729 404568457805287103537047)
            ·
              refine ⟨606852686707930655305571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404568457805287103537047 606852686707930655305571)
              ·
                refine ⟨910279030061895982958357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606852686707930655305571 910279030061895982958357)
                ·
                  refine ⟨42669329534151374201173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 910279030061895982958357 42669329534151374201173)
                  ·
                    rfl

theorem cell22_373942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_373942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373942 prefixEnd_373942 := by exact prefixLift 373942
  have htrace : WordTrace (prefixWord ++ tailWord_373942) baseStart_373942 baseEnd_373942 := by
    simpa [prefixWord, tailWord_373942, baseEnd_373942] using wordTrace_append hprefix tailTrace_373942
  have hstable : (prefixWord ++ tailWord_373942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373942).length < 2 ^ (prefixWord ++ tailWord_373942).sum := by decide
  have hdescent : baseEnd_373942 < baseStart_373942 := by decide
  rcases family_descends (prefixWord ++ tailWord_373942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_373953 : List Nat := [1, 2, 6, 1, 1, 2, 2, 7]
def baseStart_373953 : Nat := 118140960795 + 373953 * 2 ^ 59
def prefixEnd_373953 : Nat := 4983230072969 + 3 ^ 40 * 373953 * 2
def baseEnd_373953 : Nat := 14223528236361528953165

theorem tailTrace_373953 : CollatzResearch.WordTrace tailWord_373953 prefixEnd_373953 14223528236361528953165 := by
  unfold tailWord_373953
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639186414239621932870513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9092790942826414621913675 13639186414239621932870513)
  ·
    refine ⟨10229389810679716449652885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13639186414239621932870513 10229389810679716449652885)
    ·
      refine ⟨479502647375611708577479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10229389810679716449652885 479502647375611708577479)
      ·
        refine ⟨719253971063417562866219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479502647375611708577479 719253971063417562866219)
        ·
          refine ⟨1078880956595126344299329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719253971063417562866219 1078880956595126344299329)
          ·
            refine ⟨809160717446344758224497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078880956595126344299329 809160717446344758224497)
            ·
              refine ⟨606870538084758568668373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809160717446344758224497 606870538084758568668373)
              ·
                refine ⟨14223528236361528953165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 606870538084758568668373 14223528236361528953165)
                ·
                  rfl

theorem cell22_373953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 7].length) (baseStart_373953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_373953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_373953 prefixEnd_373953 := by exact prefixLift 373953
  have htrace : WordTrace (prefixWord ++ tailWord_373953) baseStart_373953 baseEnd_373953 := by
    simpa [prefixWord, tailWord_373953, baseEnd_373953] using wordTrace_append hprefix tailTrace_373953
  have hstable : (prefixWord ++ tailWord_373953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_373953).length < 2 ^ (prefixWord ++ tailWord_373953).sum := by decide
  have hdescent : baseEnd_373953 < baseStart_373953 := by decide
  rcases family_descends (prefixWord ++ tailWord_373953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374002 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_374002 : Nat := 118140960795 + 374002 * 2 ^ 59
def prefixEnd_374002 : Nat := 4983230072969 + 3 ^ 40 * 374002 * 2
def baseEnd_374002 : Nat := 128028527828633966103335

theorem tailTrace_374002 : CollatzResearch.WordTrace tailWord_374002 prefixEnd_374002 128028527828633966103335 := by
  unfold tailWord_374002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3410243397765525825351065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9093982394041402200936173 3410243397765525825351065)
  ·
    refine ⟨2557682548324144369013299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3410243397765525825351065 2557682548324144369013299)
    ·
      refine ⟨3836523822486216553519949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2557682548324144369013299 3836523822486216553519949)
      ·
        refine ⟨1438696433432331207569981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3836523822486216553519949 1438696433432331207569981)
        ·
          refine ⟨539511162537124202838743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1438696433432331207569981 539511162537124202838743)
          ·
            refine ⟨809266743805686304258115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539511162537124202838743 809266743805686304258115)
            ·
              refine ⟨1213900115708529456387173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809266743805686304258115 1213900115708529456387173)
              ·
                refine ⟨227606271695349273072595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1213900115708529456387173 227606271695349273072595)
                ·
                  refine ⟨341409407543023909608893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227606271695349273072595 341409407543023909608893)
                  ·
                    refine ⟨128028527828633966103335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341409407543023909608893 128028527828633966103335)
                    ·
                      rfl

theorem cell22_374002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_374002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374002 prefixEnd_374002 := by exact prefixLift 374002
  have htrace : WordTrace (prefixWord ++ tailWord_374002) baseStart_374002 baseEnd_374002 := by
    simpa [prefixWord, tailWord_374002, baseEnd_374002] using wordTrace_append hprefix tailTrace_374002
  have hstable : (prefixWord ++ tailWord_374002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374002).length < 2 ^ (prefixWord ++ tailWord_374002).sum := by decide
  have hdescent : baseEnd_374002 < baseStart_374002 := by decide
  rcases family_descends (prefixWord ++ tailWord_374002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374004 : List Nat := [2, 6, 1, 2, 2, 1, 1, 7]
def baseStart_374004 : Nat := 118140960795 + 374004 * 2 ^ 59
def prefixEnd_374004 : Nat := 4983230072969 + 3 ^ 40 * 374004 * 2
def baseEnd_374004 : Nat := 14225468052167403061481

theorem tailTrace_374004 : CollatzResearch.WordTrace tailWord_374004 prefixEnd_374004 14225468052167403061481 := by
  unfold tailWord_374004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820523268527428821488533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9094031024703238428651377 6820523268527428821488533)
  ·
    refine ⟨319712028212223226007275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6820523268527428821488533 319712028212223226007275)
    ·
      refine ⟨479568042318334839010913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319712028212223226007275 479568042318334839010913)
      ·
        refine ⟨359676031738751129258185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479568042318334839010913 359676031738751129258185)
        ·
          refine ⟨269757023804063346943639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359676031738751129258185 269757023804063346943639)
          ·
            refine ⟨404635535706095020415459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269757023804063346943639 404635535706095020415459)
            ·
              refine ⟨606953303559142530623189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404635535706095020415459 606953303559142530623189)
              ·
                refine ⟨14225468052167403061481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 606953303559142530623189 14225468052167403061481)
                ·
                  rfl

theorem cell22_374004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_374004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374004 prefixEnd_374004 := by exact prefixLift 374004
  have htrace : WordTrace (prefixWord ++ tailWord_374004) baseStart_374004 baseEnd_374004 := by
    simpa [prefixWord, tailWord_374004, baseEnd_374004] using wordTrace_append hprefix tailTrace_374004
  have hstable : (prefixWord ++ tailWord_374004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374004).length < 2 ^ (prefixWord ++ tailWord_374004).sum := by decide
  have hdescent : baseEnd_374004 < baseStart_374004 := by decide
  rcases family_descends (prefixWord ++ tailWord_374004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374045 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_374045 : Nat := 118140960795 + 374045 * 2 ^ 59
def prefixEnd_374045 : Nat := 4983230072969 + 3 ^ 40 * 374045 * 2
def baseEnd_374045 : Nat := 128043247607396187278203

theorem tailTrace_374045 : CollatzResearch.WordTrace tailWord_374045 prefixEnd_374045 128043247607396187278203 := by
  unfold tailWord_374045
  simp only [CollatzResearch.WordTrace]
  refine ⟨13642541929906321645219589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9095027953270881096813059 13642541929906321645219589)
  ·
    refine ⟨2557976611857435308478673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13642541929906321645219589 2557976611857435308478673)
    ·
      refine ⟨1918482458893076481359005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2557976611857435308478673 1918482458893076481359005)
      ·
        refine ⟨719430922084903680509627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1918482458893076481359005 719430922084903680509627)
        ·
          refine ⟨1079146383127355520764441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719430922084903680509627 1079146383127355520764441)
          ·
            refine ⟨809359787345516640573331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079146383127355520764441 809359787345516640573331)
            ·
              refine ⟨1214039681018274960859997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809359787345516640573331 1214039681018274960859997)
              ·
                refine ⟨455264880381853110322499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214039681018274960859997 455264880381853110322499)
                ·
                  refine ⟨682897320572779665483749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 455264880381853110322499 682897320572779665483749)
                  ·
                    refine ⟨128043247607396187278203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 682897320572779665483749 128043247607396187278203)
                    ·
                      rfl

theorem cell22_374045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_374045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374045 prefixEnd_374045 := by exact prefixLift 374045
  have htrace : WordTrace (prefixWord ++ tailWord_374045) baseStart_374045 baseEnd_374045 := by
    simpa [prefixWord, tailWord_374045, baseEnd_374045] using wordTrace_append hprefix tailTrace_374045
  have hstable : (prefixWord ++ tailWord_374045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374045).length < 2 ^ (prefixWord ++ tailWord_374045).sum := by decide
  have hdescent : baseEnd_374045 < baseStart_374045 := by decide
  rcases family_descends (prefixWord ++ tailWord_374045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374126 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_374126 : Nat := 118140960795 + 374126 * 2 ^ 59
def prefixEnd_374126 : Nat := 4983230072969 + 3 ^ 40 * 374126 * 2
def baseEnd_374126 : Nat := 128070975562738976002955

theorem tailTrace_374126 : CollatzResearch.WordTrace tailWord_374126 prefixEnd_374126 128070975562738976002955 := by
  unfold tailWord_374126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705687030326609059864779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9096997495075248319278821 1705687030326609059864779)
  ·
    refine ⟨2558530545489913589797169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705687030326609059864779 2558530545489913589797169)
    ·
      refine ⟨1918897909117435192347877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2558530545489913589797169 1918897909117435192347877)
      ·
        refine ⟨359793357959519098565227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1918897909117435192347877 359793357959519098565227)
        ·
          refine ⟨539690036939278647847841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 359793357959519098565227 539690036939278647847841)
          ·
            refine ⟨404767527704458985885881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539690036939278647847841 404767527704458985885881)
            ·
              refine ⟨303575645778344239414411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404767527704458985885881 303575645778344239414411)
              ·
                refine ⟨455363468667516359121617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303575645778344239414411 455363468667516359121617)
                ·
                  refine ⟨341522601500637269341213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455363468667516359121617 341522601500637269341213)
                  ·
                    refine ⟨128070975562738976002955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341522601500637269341213 128070975562738976002955)
                    ·
                      rfl

theorem cell22_374126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_374126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374126 prefixEnd_374126 := by exact prefixLift 374126
  have htrace : WordTrace (prefixWord ++ tailWord_374126) baseStart_374126 baseEnd_374126 := by
    simpa [prefixWord, tailWord_374126, baseEnd_374126] using wordTrace_append hprefix tailTrace_374126
  have hstable : (prefixWord ++ tailWord_374126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374126).length < 2 ^ (prefixWord ++ tailWord_374126).sum := by decide
  have hdescent : baseEnd_374126 < baseStart_374126 := by decide
  rcases family_descends (prefixWord ++ tailWord_374126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374161 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 8]
def baseStart_374161 : Nat := 118140960795 + 374161 * 2 ^ 59
def prefixEnd_374161 : Nat := 4983230072969 + 3 ^ 40 * 374161 * 2
def baseEnd_374161 : Nat := 42694318926003517125949

theorem tailTrace_374161 : CollatzResearch.WordTrace tailWord_374161 prefixEnd_374161 42694318926003517125949 := by
  unfold tailWord_374161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646772797486073456442337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9097848531657382304294891 13646772797486073456442337)
  ·
    refine ⟨10235079598114555092331753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13646772797486073456442337 10235079598114555092331753)
    ·
      refine ⟨7676309698585916319248815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10235079598114555092331753 7676309698585916319248815)
      ·
        refine ⟨11514464547878874478873223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7676309698585916319248815 11514464547878874478873223)
        ·
          refine ⟨17271696821818311718309835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11514464547878874478873223 17271696821818311718309835)
          ·
            refine ⟨25907545232727467577464753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17271696821818311718309835 25907545232727467577464753)
            ·
              refine ⟨19430658924545600683098565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25907545232727467577464753 19430658924545600683098565)
              ·
                refine ⟨3643248548352300128080981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19430658924545600683098565 3643248548352300128080981)
                ·
                  refine ⟨42694318926003517125949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3643248548352300128080981 42694318926003517125949)
                  ·
                    rfl

theorem cell22_374161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_374161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374161 prefixEnd_374161 := by exact prefixLift 374161
  have htrace : WordTrace (prefixWord ++ tailWord_374161) baseStart_374161 baseEnd_374161 := by
    simpa [prefixWord, tailWord_374161, baseEnd_374161] using wordTrace_append hprefix tailTrace_374161
  have hstable : (prefixWord ++ tailWord_374161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374161).length < 2 ^ (prefixWord ++ tailWord_374161).sum := by decide
  have hdescent : baseEnd_374161 < baseStart_374161 := by decide
  rcases family_descends (prefixWord ++ tailWord_374161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374212 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_374212 : Nat := 118140960795 + 374212 * 2 ^ 59
def prefixEnd_374212 : Nat := 4983230072969 + 3 ^ 40 * 374212 * 2
def baseEnd_374212 : Nat := 42700138373421139450897

theorem tailTrace_374212 : CollatzResearch.WordTrace tailWord_374212 prefixEnd_374212 42700138373421139450897 := by
  unfold tailWord_374212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6824316460150654583274445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9099088613534206111032593 6824316460150654583274445)
  ·
    refine ⟨2559118672556495468727917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6824316460150654583274445 2559118672556495468727917)
    ·
      refine ⟨959669502208685800772969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2559118672556495468727917 959669502208685800772969)
      ·
        refine ⟨719752126656514350579727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959669502208685800772969 719752126656514350579727)
        ·
          refine ⟨1079628189984771525869591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719752126656514350579727 1079628189984771525869591)
          ·
            refine ⟨1619442284977157288804387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079628189984771525869591 1619442284977157288804387)
            ·
              refine ⟨2429163427465735933206581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619442284977157288804387 2429163427465735933206581)
              ·
                refine ⟨227734071324912743738117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2429163427465735933206581 227734071324912743738117)
                ·
                  refine ⟨42700138373421139450897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 227734071324912743738117 42700138373421139450897)
                  ·
                    rfl

theorem cell22_374212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_374212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374212 prefixEnd_374212 := by exact prefixLift 374212
  have htrace : WordTrace (prefixWord ++ tailWord_374212) baseStart_374212 baseEnd_374212 := by
    simpa [prefixWord, tailWord_374212, baseEnd_374212] using wordTrace_append hprefix tailTrace_374212
  have hstable : (prefixWord ++ tailWord_374212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374212).length < 2 ^ (prefixWord ++ tailWord_374212).sum := by decide
  have hdescent : baseEnd_374212 < baseStart_374212 := by decide
  rcases family_descends (prefixWord ++ tailWord_374212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374255 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 3, 3]
def baseStart_374255 : Nat := 118140960795 + 374255 * 2 ^ 59
def prefixEnd_374255 : Nat := 4983230072969 + 3 ^ 40 * 374255 * 2
def baseEnd_374255 : Nat := 128115134899025639527559

theorem tailTrace_374255 : CollatzResearch.WordTrace tailWord_374255 prefixEnd_374255 128115134899025639527559 := by
  unfold tailWord_374255
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650201259145527510364219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9100134172763685006909479 13650201259145527510364219)
  ·
    refine ⟨20475301888718291265546329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13650201259145527510364219 20475301888718291265546329)
    ·
      refine ⟨15356476416538718449159747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20475301888718291265546329 15356476416538718449159747)
      ·
        refine ⟨23034714624808077673739621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15356476416538718449159747 23034714624808077673739621)
        ·
          refine ⟨4319008992151514563826179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23034714624808077673739621 4319008992151514563826179)
          ·
            refine ⟨6478513488227271845739269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319008992151514563826179 6478513488227271845739269)
            ·
              refine ⟨1214721279042613471076113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6478513488227271845739269 1214721279042613471076113)
              ·
                refine ⟨911040959281960103307085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214721279042613471076113 911040959281960103307085)
                ·
                  refine ⟨341640359730735038740157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911040959281960103307085 341640359730735038740157)
                  ·
                    refine ⟨128115134899025639527559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341640359730735038740157 128115134899025639527559)
                    ·
                      rfl

theorem cell22_374255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_374255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374255 prefixEnd_374255 := by exact prefixLift 374255
  have htrace : WordTrace (prefixWord ++ tailWord_374255) baseStart_374255 baseEnd_374255 := by
    simpa [prefixWord, tailWord_374255, baseEnd_374255] using wordTrace_append hprefix tailTrace_374255
  have hstable : (prefixWord ++ tailWord_374255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374255).length < 2 ^ (prefixWord ++ tailWord_374255).sum := by decide
  have hdescent : baseEnd_374255 < baseStart_374255 := by decide
  rcases family_descends (prefixWord ++ tailWord_374255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374268 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_374268 : Nat := 118140960795 + 374268 * 2 ^ 59
def prefixEnd_374268 : Nat := 4983230072969 + 3 ^ 40 * 374268 * 2
def baseEnd_374268 : Nat := 42706528354899312984173

theorem tailTrace_374268 : CollatzResearch.WordTrace tailWord_374268 prefixEnd_374268 42706528354899312984173 := by
  unfold tailWord_374268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825337704049215365293729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9100450272065620487058305 6825337704049215365293729)
  ·
    refine ⟨5119003278036911523970297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6825337704049215365293729 5119003278036911523970297)
    ·
      refine ⟨3839252458527683642977723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5119003278036911523970297 3839252458527683642977723)
      ·
        refine ⟨5758878687791525464466585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3839252458527683642977723 5758878687791525464466585)
        ·
          refine ⟨4319159015843644098349939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758878687791525464466585 4319159015843644098349939)
          ·
            refine ⟨6478738523765466147524909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319159015843644098349939 6478738523765466147524909)
            ·
              refine ⟨2429526946412049805321841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6478738523765466147524909 2429526946412049805321841)
              ·
                refine ⟨1822145209809037353991381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429526946412049805321841 1822145209809037353991381)
                ·
                  refine ⟨42706528354899312984173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1822145209809037353991381 42706528354899312984173)
                  ·
                    rfl

theorem cell22_374268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_374268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374268 prefixEnd_374268 := by exact prefixLift 374268
  have htrace : WordTrace (prefixWord ++ tailWord_374268) baseStart_374268 baseEnd_374268 := by
    simpa [prefixWord, tailWord_374268, baseEnd_374268] using wordTrace_append hprefix tailTrace_374268
  have hstable : (prefixWord ++ tailWord_374268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374268).length < 2 ^ (prefixWord ++ tailWord_374268).sum := by decide
  have hdescent : baseEnd_374268 < baseStart_374268 := by decide
  rcases family_descends (prefixWord ++ tailWord_374268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374289 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 1, 3]
def baseStart_374289 : Nat := 118140960795 + 374289 * 2 ^ 59
def prefixEnd_374289 : Nat := 4983230072969 + 3 ^ 40 * 374289 * 2
def baseEnd_374289 : Nat := 128126773793860884177455

theorem tailTrace_374289 : CollatzResearch.WordTrace tailWord_374289 prefixEnd_374289 128126773793860884177455 := by
  unfold tailWord_374289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13651441341022351317101921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9100960894014900878067947 13651441341022351317101921)
  ·
    refine ⟨10238581005766763487826441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13651441341022351317101921 10238581005766763487826441)
    ·
      refine ⟨7678935754325072615869831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10238581005766763487826441 7678935754325072615869831)
      ·
        refine ⟨11518403631487608923804747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7678935754325072615869831 11518403631487608923804747)
        ·
          refine ⟨17277605447231413385707121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11518403631487608923804747 17277605447231413385707121)
          ·
            refine ⟨12958204085423560039280341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17277605447231413385707121 12958204085423560039280341)
            ·
              refine ⟨303707908252114688420633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12958204085423560039280341 303707908252114688420633)
              ·
                refine ⟨227780931189086016315475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303707908252114688420633 227780931189086016315475)
                ·
                  refine ⟨341671396783629024473213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227780931189086016315475 341671396783629024473213)
                  ·
                    refine ⟨128126773793860884177455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341671396783629024473213 128126773793860884177455)
                    ·
                      rfl

theorem cell22_374289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_374289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374289 prefixEnd_374289 := by exact prefixLift 374289
  have htrace : WordTrace (prefixWord ++ tailWord_374289) baseStart_374289 baseEnd_374289 := by
    simpa [prefixWord, tailWord_374289, baseEnd_374289] using wordTrace_append hprefix tailTrace_374289
  have hstable : (prefixWord ++ tailWord_374289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374289).length < 2 ^ (prefixWord ++ tailWord_374289).sum := by decide
  have hdescent : baseEnd_374289 < baseStart_374289 := by decide
  rcases family_descends (prefixWord ++ tailWord_374289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374298 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_374298 : Nat := 118140960795 + 374298 * 2 ^ 59
def prefixEnd_374298 : Nat := 4983230072969 + 3 ^ 40 * 374298 * 2
def baseEnd_374298 : Nat := 128129854677787860702427

theorem tailTrace_374298 : CollatzResearch.WordTrace tailWord_374298 prefixEnd_374298 128129854677787860702427 := by
  unfold tailWord_374298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412942399497436463544887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9101179731993163902786365 3412942399497436463544887)
  ·
    refine ⟨5119413599246154695317331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3412942399497436463544887 5119413599246154695317331)
    ·
      refine ⟨7679120398869232042975997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5119413599246154695317331 7679120398869232042975997)
      ·
        refine ⟨2879670149575962016115999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7679120398869232042975997 2879670149575962016115999)
        ·
          refine ⟨4319505224363943024173999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879670149575962016115999 4319505224363943024173999)
          ·
            refine ⟨6479257836545914536260999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319505224363943024173999 6479257836545914536260999)
            ·
              refine ⟨9718886754818871804391499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6479257836545914536260999 9718886754818871804391499)
              ·
                refine ⟨14578330132228307706587249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9718886754818871804391499 14578330132228307706587249)
                ·
                  refine ⟨10933747599171230779940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14578330132228307706587249 10933747599171230779940437)
                  ·
                    refine ⟨128129854677787860702427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10933747599171230779940437 128129854677787860702427)
                    ·
                      rfl

theorem cell22_374298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_374298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374298 prefixEnd_374298 := by exact prefixLift 374298
  have htrace : WordTrace (prefixWord ++ tailWord_374298) baseStart_374298 baseEnd_374298 := by
    simpa [prefixWord, tailWord_374298, baseEnd_374298] using wordTrace_append hprefix tailTrace_374298
  have hstable : (prefixWord ++ tailWord_374298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374298).length < 2 ^ (prefixWord ++ tailWord_374298).sum := by decide
  have hdescent : baseEnd_374298 < baseStart_374298 := by decide
  rcases family_descends (prefixWord ++ tailWord_374298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374345 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 4, 3]
def baseStart_374345 : Nat := 118140960795 + 374345 * 2 ^ 59
def prefixEnd_374345 : Nat := 4983230072969 + 3 ^ 40 * 374345 * 2
def baseEnd_374345 : Nat := 128145943738295404777283

theorem tailTrace_374345 : CollatzResearch.WordTrace tailWord_374345 prefixEnd_374345 128145943738295404777283 := by
  unfold tailWord_374345
  simp only [CollatzResearch.WordTrace]
  refine ⟨13653483828819472881140489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9102322552546315254093659 13653483828819472881140489)
  ·
    refine ⟨10240112871614604660855367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13653483828819472881140489 10240112871614604660855367)
    ·
      refine ⟨15360169307421906991283051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10240112871614604660855367 15360169307421906991283051)
      ·
        refine ⟨23040253961132860486924577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15360169307421906991283051 23040253961132860486924577)
        ·
          refine ⟨17280190470849645365193433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23040253961132860486924577 17280190470849645365193433)
          ·
            refine ⟨12960142853137234023895075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17280190470849645365193433 12960142853137234023895075)
            ·
              refine ⟨19440214279705851035842613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12960142853137234023895075 19440214279705851035842613)
              ·
                refine ⟨1822520088722423534610245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19440214279705851035842613 1822520088722423534610245)
                ·
                  refine ⟨341722516635454412739421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1822520088722423534610245 341722516635454412739421)
                  ·
                    refine ⟨128145943738295404777283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341722516635454412739421 128145943738295404777283)
                    ·
                      rfl

theorem cell22_374345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_374345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374345 prefixEnd_374345 := by exact prefixLift 374345
  have htrace : WordTrace (prefixWord ++ tailWord_374345) baseStart_374345 baseEnd_374345 := by
    simpa [prefixWord, tailWord_374345, baseEnd_374345] using wordTrace_append hprefix tailTrace_374345
  have hstable : (prefixWord ++ tailWord_374345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374345).length < 2 ^ (prefixWord ++ tailWord_374345).sum := by decide
  have hdescent : baseEnd_374345 < baseStart_374345 := by decide
  rcases family_descends (prefixWord ++ tailWord_374345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374407 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 3, 3]
def baseStart_374407 : Nat := 118140960795 + 374407 * 2 ^ 59
def prefixEnd_374407 : Nat := 4983230072969 + 3 ^ 40 * 374407 * 2
def baseEnd_374407 : Nat := 128167167605347909727093

theorem tailTrace_374407 : CollatzResearch.WordTrace tailWord_374407 prefixEnd_374407 128167167605347909727093 := by
  unfold tailWord_374407
  simp only [CollatzResearch.WordTrace]
  refine ⟨13655745154594857469897475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9103830103063238313264983 13655745154594857469897475)
  ·
    refine ⟨20483617731892286204846213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13655745154594857469897475 20483617731892286204846213)
    ·
      refine ⟨3840678324729803663408665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20483617731892286204846213 3840678324729803663408665)
      ·
        refine ⟨2880508743547352747556499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3840678324729803663408665 2880508743547352747556499)
        ·
          refine ⟨4320763115321029121334749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880508743547352747556499 4320763115321029121334749)
          ·
            refine ⟨1620286168245385920500531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4320763115321029121334749 1620286168245385920500531)
            ·
              refine ⟨2430429252368078880750797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620286168245385920500531 2430429252368078880750797)
              ·
                refine ⟨911410969638029580281549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430429252368078880750797 911410969638029580281549)
                ·
                  refine ⟨341779113614261092605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 911410969638029580281549 341779113614261092605581)
                  ·
                    refine ⟨128167167605347909727093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341779113614261092605581 128167167605347909727093)
                    ·
                      rfl

theorem cell22_374407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_374407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374407 prefixEnd_374407 := by exact prefixLift 374407
  have htrace : WordTrace (prefixWord ++ tailWord_374407) baseStart_374407 baseEnd_374407 := by
    simpa [prefixWord, tailWord_374407, baseEnd_374407] using wordTrace_append hprefix tailTrace_374407
  have hstable : (prefixWord ++ tailWord_374407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374407).length < 2 ^ (prefixWord ++ tailWord_374407).sum := by decide
  have hdescent : baseEnd_374407 < baseStart_374407 := by decide
  rcases family_descends (prefixWord ++ tailWord_374407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374454 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_374454 : Nat := 118140960795 + 374454 * 2 ^ 59
def prefixEnd_374454 : Nat := 4983230072969 + 3 ^ 40 * 374454 * 2
def baseEnd_374454 : Nat := 42727752221951817933983

theorem tailTrace_374454 : CollatzResearch.WordTrace tailWord_374454 prefixEnd_374454 42727752221951817933983 := by
  unfold tailWord_374454
  simp only [CollatzResearch.WordTrace]
  refine ⟨853591211589036531053651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9104972923616389664572277 853591211589036531053651)
  ·
    refine ⟨1280386817383554796580477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853591211589036531053651 1280386817383554796580477)
    ·
      refine ⟨480145056518833048717679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1280386817383554796580477 480145056518833048717679)
      ·
        refine ⟨720217584778249573076519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480145056518833048717679 720217584778249573076519)
        ·
          refine ⟨1080326377167374359614779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720217584778249573076519 1080326377167374359614779)
          ·
            refine ⟨1620489565751061539422169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080326377167374359614779 1620489565751061539422169)
            ·
              refine ⟨1215367174313296154566627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1620489565751061539422169 1215367174313296154566627)
              ·
                refine ⟨1823050761469944231849941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215367174313296154566627 1823050761469944231849941)
                ·
                  refine ⟨42727752221951817933983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1823050761469944231849941 42727752221951817933983)
                  ·
                    rfl

theorem cell22_374454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_374454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374454 prefixEnd_374454 := by exact prefixLift 374454
  have htrace : WordTrace (prefixWord ++ tailWord_374454) baseStart_374454 baseEnd_374454 := by
    simpa [prefixWord, tailWord_374454, baseEnd_374454] using wordTrace_append hprefix tailTrace_374454
  have hstable : (prefixWord ++ tailWord_374454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374454).length < 2 ^ (prefixWord ++ tailWord_374454).sum := by decide
  have hdescent : baseEnd_374454 < baseStart_374454 := by decide
  rcases family_descends (prefixWord ++ tailWord_374454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374484 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_374484 : Nat := 118140960795 + 374484 * 2 ^ 59
def prefixEnd_374484 : Nat := 4983230072969 + 3 ^ 40 * 374484 * 2
def baseEnd_374484 : Nat := 128193526278945375551857

theorem tailTrace_374484 : CollatzResearch.WordTrace tailWord_374484 prefixEnd_374484 128193526278945375551857 := by
  unfold tailWord_374484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6829276787657949810225253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9105702383543933080300337 6829276787657949810225253)
  ·
    refine ⟨1280489397685865589417235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6829276787657949810225253 1280489397685865589417235)
    ·
      refine ⟨1920734096528798384125853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280489397685865589417235 1920734096528798384125853)
      ·
        refine ⟨720275286198299394047195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1920734096528798384125853 720275286198299394047195)
        ·
          refine ⟨1080412929297449091070793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720275286198299394047195 1080412929297449091070793)
          ·
            refine ⟨810309696973086818303095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080412929297449091070793 810309696973086818303095)
            ·
              refine ⟨1215464545459630227454643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810309696973086818303095 1215464545459630227454643)
              ·
                refine ⟨1823196818189445341181965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215464545459630227454643 1823196818189445341181965)
                ·
                  refine ⟨683698806821042002943237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1823196818189445341181965 683698806821042002943237)
                  ·
                    refine ⟨128193526278945375551857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683698806821042002943237 128193526278945375551857)
                    ·
                      rfl

theorem cell22_374484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_374484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374484 prefixEnd_374484 := by exact prefixLift 374484
  have htrace : WordTrace (prefixWord ++ tailWord_374484) baseStart_374484 baseEnd_374484 := by
    simpa [prefixWord, tailWord_374484, baseEnd_374484] using wordTrace_append hprefix tailTrace_374484
  have hstable : (prefixWord ++ tailWord_374484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374484).length < 2 ^ (prefixWord ++ tailWord_374484).sum := by decide
  have hdescent : baseEnd_374484 < baseStart_374484 := by decide
  rcases family_descends (prefixWord ++ tailWord_374484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374546 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_374546 : Nat := 118140960795 + 374546 * 2 ^ 59
def prefixEnd_374546 : Nat := 4983230072969 + 3 ^ 40 * 374546 * 2
def baseEnd_374546 : Nat := 128214750145997880501667

theorem tailTrace_374546 : CollatzResearch.WordTrace tailWord_374546 prefixEnd_374546 128214750145997880501667 := by
  unfold tailWord_374546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415203725272821052301873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9107209934060856139471661 3415203725272821052301873)
  ·
    refine ⟨2561402793954615789226405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3415203725272821052301873 2561402793954615789226405)
    ·
      refine ⟨480263023866490460479951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2561402793954615789226405 480263023866490460479951)
      ·
        refine ⟨720394535799735690719927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480263023866490460479951 720394535799735690719927)
        ·
          refine ⟨1080591803699603536079891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720394535799735690719927 1080591803699603536079891)
          ·
            refine ⟨1620887705549405304119837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080591803699603536079891 1620887705549405304119837)
            ·
              refine ⟨607832889581026989044939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1620887705549405304119837 607832889581026989044939)
              ·
                refine ⟨911749334371540483567409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607832889581026989044939 911749334371540483567409)
                ·
                  refine ⟨683812000778655362675557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 911749334371540483567409 683812000778655362675557)
                  ·
                    refine ⟨128214750145997880501667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 683812000778655362675557 128214750145997880501667)
                    ·
                      rfl

theorem cell22_374546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_374546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374546 prefixEnd_374546 := by exact prefixLift 374546
  have htrace : WordTrace (prefixWord ++ tailWord_374546) baseStart_374546 baseEnd_374546 := by
    simpa [prefixWord, tailWord_374546, baseEnd_374546] using wordTrace_append hprefix tailTrace_374546
  have hstable : (prefixWord ++ tailWord_374546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374546).length < 2 ^ (prefixWord ++ tailWord_374546).sum := by decide
  have hdescent : baseEnd_374546 < baseStart_374546 := by decide
  rcases family_descends (prefixWord ++ tailWord_374546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374555 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 9]
def baseStart_374555 : Nat := 118140960795 + 374555 * 2 ^ 59
def prefixEnd_374555 : Nat := 4983230072969 + 3 ^ 40 * 374555 * 2
def baseEnd_374555 : Nat := 42739277009974952342213

theorem tailTrace_374555 : CollatzResearch.WordTrace tailWord_374555 prefixEnd_374555 42739277009974952342213 := by
  unfold tailWord_374555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13661143158058678746285119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9107428772039119164190079 13661143158058678746285119)
  ·
    refine ⟨20491714737088018119427679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13661143158058678746285119 20491714737088018119427679)
    ·
      refine ⟨30737572105632027179141519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20491714737088018119427679 30737572105632027179141519)
      ·
        refine ⟨46106358158448040768712279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30737572105632027179141519 46106358158448040768712279)
        ·
          refine ⟨69159537237672061153068419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46106358158448040768712279 69159537237672061153068419)
          ·
            refine ⟨103739305856508091729602629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69159537237672061153068419 103739305856508091729602629)
            ·
              refine ⟨19451119848095267199300493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103739305856508091729602629 19451119848095267199300493)
              ·
                refine ⟨7294169943035725199737685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19451119848095267199300493 7294169943035725199737685)
                ·
                  refine ⟨42739277009974952342213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7294169943035725199737685 42739277009974952342213)
                  ·
                    rfl

theorem cell22_374555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_374555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374555 prefixEnd_374555 := by exact prefixLift 374555
  have htrace : WordTrace (prefixWord ++ tailWord_374555) baseStart_374555 baseEnd_374555 := by
    simpa [prefixWord, tailWord_374555, baseEnd_374555] using wordTrace_append hprefix tailTrace_374555
  have hstable : (prefixWord ++ tailWord_374555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374555).length < 2 ^ (prefixWord ++ tailWord_374555).sum := by decide
  have hdescent : baseEnd_374555 < baseStart_374555 := by decide
  rcases family_descends (prefixWord ++ tailWord_374555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374572 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_374572 : Nat := 118140960795 + 374572 * 2 ^ 59
def prefixEnd_374572 : Nat := 4983230072969 + 3 ^ 40 * 374572 * 2
def baseEnd_374572 : Nat := 42741216825780826450529

theorem tailTrace_374572 : CollatzResearch.WordTrace tailWord_374572 prefixEnd_374572 42741216825780826450529 := by
  unfold tailWord_374572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830881599498545324826985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9107842132664727099769313 6830881599498545324826985)
  ·
    refine ⟨5123161199623908993620239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6830881599498545324826985 5123161199623908993620239)
    ·
      refine ⟨7684741799435863490430359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5123161199623908993620239 7684741799435863490430359)
      ·
        refine ⟨11527112699153795235645539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7684741799435863490430359 11527112699153795235645539)
        ·
          refine ⟨17290669048730692853468309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11527112699153795235645539 17290669048730692853468309)
          ·
            refine ⟨810500111659251227506327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17290669048730692853468309 810500111659251227506327)
            ·
              refine ⟨1215750167488876841259491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810500111659251227506327 1215750167488876841259491)
              ·
                refine ⟨1823625251233315261889237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215750167488876841259491 1823625251233315261889237)
                ·
                  refine ⟨42741216825780826450529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1823625251233315261889237 42741216825780826450529)
                  ·
                    rfl

theorem cell22_374572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_374572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374572 prefixEnd_374572 := by exact prefixLift 374572
  have htrace : WordTrace (prefixWord ++ tailWord_374572) baseStart_374572 baseEnd_374572 := by
    simpa [prefixWord, tailWord_374572, baseEnd_374572] using wordTrace_append hprefix tailTrace_374572
  have hstable : (prefixWord ++ tailWord_374572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374572).length < 2 ^ (prefixWord ++ tailWord_374572).sum := by decide
  have hdescent : baseEnd_374572 < baseStart_374572 := by decide
  rcases family_descends (prefixWord ++ tailWord_374572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374666 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_374666 : Nat := 118140960795 + 374666 * 2 ^ 59
def prefixEnd_374666 : Nat := 4983230072969 + 3 ^ 40 * 374666 * 2
def baseEnd_374666 : Nat := 128255828598357567501299

theorem tailTrace_374666 : CollatzResearch.WordTrace tailWord_374666 prefixEnd_374666 128255828598357567501299 := by
  unfold tailWord_374666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416297915164136175893963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9110127773771029802383901 3416297915164136175893963)
  ·
    refine ⟨5124446872746204263840945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3416297915164136175893963 5124446872746204263840945)
    ·
      refine ⟨3843335154559653197880709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5124446872746204263840945 3843335154559653197880709)
      ·
        refine ⟨720625341479934974602633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3843335154559653197880709 720625341479934974602633)
        ·
          refine ⟨540469006109951230951975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 720625341479934974602633 540469006109951230951975)
          ·
            refine ⟨810703509164926846427963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540469006109951230951975 810703509164926846427963)
            ·
              refine ⟨1216055263747390269641945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810703509164926846427963 1216055263747390269641945)
              ·
                refine ⟨912041447810542702231459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1216055263747390269641945 912041447810542702231459)
                ·
                  refine ⟨1368062171715814053347189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 912041447810542702231459 1368062171715814053347189)
                  ·
                    refine ⟨128255828598357567501299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1368062171715814053347189 128255828598357567501299)
                    ·
                      rfl

theorem cell22_374666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_374666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374666 prefixEnd_374666 := by exact prefixLift 374666
  have htrace : WordTrace (prefixWord ++ tailWord_374666) baseStart_374666 baseEnd_374666 := by
    simpa [prefixWord, tailWord_374666, baseEnd_374666] using wordTrace_append hprefix tailTrace_374666
  have hstable : (prefixWord ++ tailWord_374666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374666).length < 2 ^ (prefixWord ++ tailWord_374666).sum := by decide
  have hdescent : baseEnd_374666 < baseStart_374666 := by decide
  rcases family_descends (prefixWord ++ tailWord_374666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374670 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_374670 : Nat := 118140960795 + 374670 * 2 ^ 59
def prefixEnd_374670 : Nat := 4983230072969 + 3 ^ 40 * 374670 * 2
def baseEnd_374670 : Nat := 128257197880102890401287

theorem tailTrace_374670 : CollatzResearch.WordTrace tailWord_374670 prefixEnd_374670 128257197880102890401287 := by
  unfold tailWord_374670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708167194080256673340183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9110225035094702257814309 1708167194080256673340183)
  ·
    refine ⟨2562250791120385010010275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708167194080256673340183 2562250791120385010010275)
    ·
      refine ⟨3843376186680577515015413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562250791120385010010275 3843376186680577515015413)
      ·
        refine ⟨360316517501304142032695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3843376186680577515015413 360316517501304142032695)
        ·
          refine ⟨540474776251956213049043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360316517501304142032695 540474776251956213049043)
          ·
            refine ⟨810712164377934319573565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540474776251956213049043 810712164377934319573565)
            ·
              refine ⟨304017061641725369840087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810712164377934319573565 304017061641725369840087)
              ·
                refine ⟨456025592462588054760131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304017061641725369840087 456025592462588054760131)
                ·
                  refine ⟨684038388693882082140197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456025592462588054760131 684038388693882082140197)
                  ·
                    refine ⟨128257197880102890401287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684038388693882082140197 128257197880102890401287)
                    ·
                      rfl

theorem cell22_374670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_374670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374670 prefixEnd_374670 := by exact prefixLift 374670
  have htrace : WordTrace (prefixWord ++ tailWord_374670) baseStart_374670 baseEnd_374670 := by
    simpa [prefixWord, tailWord_374670, baseEnd_374670] using wordTrace_append hprefix tailTrace_374670
  have hstable : (prefixWord ++ tailWord_374670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374670).length < 2 ^ (prefixWord ++ tailWord_374670).sum := by decide
  have hdescent : baseEnd_374670 < baseStart_374670 := by decide
  rcases family_descends (prefixWord ++ tailWord_374670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374728 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 1, 3]
def baseStart_374728 : Nat := 118140960795 + 374728 * 2 ^ 59
def prefixEnd_374728 : Nat := 4983230072969 + 3 ^ 40 * 374728 * 2
def baseEnd_374728 : Nat := 128277052465410072451109

theorem tailTrace_374728 : CollatzResearch.WordTrace tailWord_374728 prefixEnd_374728 128277052465410072451109 := by
  unfold tailWord_374728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6833726493215964646166419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9111635324287952861555225 6833726493215964646166419)
  ·
    refine ⟨10250589739823946969249629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6833726493215964646166419 10250589739823946969249629)
    ·
      refine ⟨3843971152433980113468611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10250589739823946969249629 3843971152433980113468611)
      ·
        refine ⟨5765956728650970170202917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843971152433980113468611 5765956728650970170202917)
        ·
          refine ⟨1081116886622056906913047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5765956728650970170202917 1081116886622056906913047)
          ·
            refine ⟨1621675329933085360369571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081116886622056906913047 1621675329933085360369571)
            ·
              refine ⟨2432512994899628040554357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621675329933085360369571 2432512994899628040554357)
              ·
                refine ⟨228048093271840128801971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2432512994899628040554357 228048093271840128801971)
                ·
                  refine ⟨342072139907760193202957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228048093271840128801971 342072139907760193202957)
                  ·
                    refine ⟨128277052465410072451109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342072139907760193202957 128277052465410072451109)
                    ·
                      rfl

theorem cell22_374728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_374728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374728 prefixEnd_374728 := by exact prefixLift 374728
  have htrace : WordTrace (prefixWord ++ tailWord_374728) baseStart_374728 baseEnd_374728 := by
    simpa [prefixWord, tailWord_374728, baseEnd_374728] using wordTrace_append hprefix tailTrace_374728
  have hstable : (prefixWord ++ tailWord_374728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374728).length < 2 ^ (prefixWord ++ tailWord_374728).sum := by decide
  have hdescent : baseEnd_374728 < baseStart_374728 := by decide
  rcases family_descends (prefixWord ++ tailWord_374728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374741 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 5]
def baseStart_374741 : Nat := 118140960795 + 374741 * 2 ^ 59
def prefixEnd_374741 : Nat := 4983230072969 + 3 ^ 40 * 374741 * 2
def baseEnd_374741 : Nat := 42760500877027457292023

theorem tailTrace_374741 : CollatzResearch.WordTrace tailWord_374741 prefixEnd_374741 42760500877027457292023 := by
  unfold tailWord_374741
  simp only [CollatzResearch.WordTrace]
  refine ⟨13667927135384832512556077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9111951423589888341704051 13667927135384832512556077)
  ·
    refine ⟨5125472675769312192208529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13667927135384832512556077 5125472675769312192208529)
    ·
      refine ⟨3844104506826984144156397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5125472675769312192208529 3844104506826984144156397)
      ·
        refine ⟨1441539190060119054058649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3844104506826984144156397 1441539190060119054058649)
        ·
          refine ⟨1081154392545089290543987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441539190060119054058649 1081154392545089290543987)
          ·
            refine ⟨1621731588817633935815981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081154392545089290543987 1621731588817633935815981)
            ·
              refine ⟨608149345806612725930993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621731588817633935815981 608149345806612725930993)
              ·
                refine ⟨456112009354959544448245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608149345806612725930993 456112009354959544448245)
                ·
                  refine ⟨42760500877027457292023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456112009354959544448245 42760500877027457292023)
                  ·
                    rfl

theorem cell22_374741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_374741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374741 prefixEnd_374741 := by exact prefixLift 374741
  have htrace : WordTrace (prefixWord ++ tailWord_374741) baseStart_374741 baseEnd_374741 := by
    simpa [prefixWord, tailWord_374741, baseEnd_374741] using wordTrace_append hprefix tailTrace_374741
  have hstable : (prefixWord ++ tailWord_374741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374741).length < 2 ^ (prefixWord ++ tailWord_374741).sum := by decide
  have hdescent : baseEnd_374741 < baseStart_374741 := by decide
  rcases family_descends (prefixWord ++ tailWord_374741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374818 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_374818 : Nat := 118140960795 + 374818 * 2 ^ 59
def prefixEnd_374818 : Nat := 4983230072969 + 3 ^ 40 * 374818 * 2
def baseEnd_374818 : Nat := 128307861304679837700833

theorem tailTrace_374818 : CollatzResearch.WordTrace tailWord_374818 prefixEnd_374818 128307861304679837700833 := by
  unfold tailWord_374818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417683889026468665777277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9113823704070583108739405 3417683889026468665777277)
  ·
    refine ⟨1281631458384925749666479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3417683889026468665777277 1281631458384925749666479)
    ·
      refine ⟨1922447187577388624499719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1281631458384925749666479 1922447187577388624499719)
      ·
        refine ⟨2883670781366082936749579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922447187577388624499719 2883670781366082936749579)
        ·
          refine ⟨4325506172049124405124369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883670781366082936749579 4325506172049124405124369)
          ·
            refine ⟨3244129629036843303843277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325506172049124405124369 3244129629036843303843277)
            ·
              refine ⟨1216548610888816238941229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3244129629036843303843277 1216548610888816238941229)
              ·
                refine ⟨456205729083306089602961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216548610888816238941229 456205729083306089602961)
                ·
                  refine ⟨342154296812479567202221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456205729083306089602961 342154296812479567202221)
                  ·
                    refine ⟨128307861304679837700833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342154296812479567202221 128307861304679837700833)
                    ·
                      rfl

theorem cell22_374818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_374818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374818 prefixEnd_374818 := by exact prefixLift 374818
  have htrace : WordTrace (prefixWord ++ tailWord_374818) baseStart_374818 baseEnd_374818 := by
    simpa [prefixWord, tailWord_374818, baseEnd_374818] using wordTrace_append hprefix tailTrace_374818
  have hstable : (prefixWord ++ tailWord_374818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374818).length < 2 ^ (prefixWord ++ tailWord_374818).sum := by decide
  have hdescent : baseEnd_374818 < baseStart_374818 := by decide
  rcases family_descends (prefixWord ++ tailWord_374818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374861 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_374861 : Nat := 118140960795 + 374861 * 2 ^ 59
def prefixEnd_374861 : Nat := 4983230072969 + 3 ^ 40 * 374861 * 2
def baseEnd_374861 : Nat := 128322581083442058875701

theorem tailTrace_374861 : CollatzResearch.WordTrace tailWord_374861 prefixEnd_374861 128322581083442058875701 := by
  unfold tailWord_374861
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672303894950093006924437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9114869263300062004616291 13672303894950093006924437)
  ·
    refine ⟨640889245075785609699583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13672303894950093006924437 640889245075785609699583)
    ·
      refine ⟨961333867613678414549375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640889245075785609699583 961333867613678414549375)
      ·
        refine ⟨1442000801420517621824063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961333867613678414549375 1442000801420517621824063)
        ·
          refine ⟨2163001202130776432736095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1442000801420517621824063 2163001202130776432736095)
          ·
            refine ⟨3244501803196164649104143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163001202130776432736095 3244501803196164649104143)
            ·
              refine ⟨4866752704794246973656215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244501803196164649104143 4866752704794246973656215)
              ·
                refine ⟨7300129057191370460484323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866752704794246973656215 7300129057191370460484323)
                ·
                  refine ⟨10950193585787055690726485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7300129057191370460484323 10950193585787055690726485)
                  ·
                    refine ⟨128322581083442058875701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10950193585787055690726485 128322581083442058875701)
                    ·
                      rfl

theorem cell22_374861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_374861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374861 prefixEnd_374861 := by exact prefixLift 374861
  have htrace : WordTrace (prefixWord ++ tailWord_374861) baseStart_374861 baseEnd_374861 := by
    simpa [prefixWord, tailWord_374861, baseEnd_374861] using wordTrace_append hprefix tailTrace_374861
  have hstable : (prefixWord ++ tailWord_374861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374861).length < 2 ^ (prefixWord ++ tailWord_374861).sum := by decide
  have hdescent : baseEnd_374861 < baseStart_374861 := by decide
  rcases family_descends (prefixWord ++ tailWord_374861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374863 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 1, 3]
def baseStart_374863 : Nat := 118140960795 + 374863 * 2 ^ 59
def prefixEnd_374863 : Nat := 4983230072969 + 3 ^ 40 * 374863 * 2
def baseEnd_374863 : Nat := 128323265724314720325695

theorem tailTrace_374863 : CollatzResearch.WordTrace tailWord_374863 prefixEnd_374863 128323265724314720325695 := by
  unfold tailWord_374863
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672376840942847348497243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9114917893961898232331495 13672376840942847348497243)
  ·
    refine ⟨20508565261414271022745865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13672376840942847348497243 20508565261414271022745865)
    ·
      refine ⟨15381423946060703267059399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20508565261414271022745865 15381423946060703267059399)
      ·
        refine ⟨23072135919091054900589099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15381423946060703267059399 23072135919091054900589099)
        ·
          refine ⟨34608203878636582350883649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23072135919091054900589099 34608203878636582350883649)
          ·
            refine ⟨25956152908977436763162737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34608203878636582350883649 25956152908977436763162737)
            ·
              refine ⟨19467114681733077572372053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25956152908977436763162737 19467114681733077572372053)
              ·
                refine ⟨228130250176559502801235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19467114681733077572372053 228130250176559502801235)
                ·
                  refine ⟨342195375264839254201853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228130250176559502801235 342195375264839254201853)
                  ·
                    refine ⟨128323265724314720325695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342195375264839254201853 128323265724314720325695)
                    ·
                      rfl

theorem cell22_374863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_374863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374863 prefixEnd_374863 := by exact prefixLift 374863
  have htrace : WordTrace (prefixWord ++ tailWord_374863) baseStart_374863 baseEnd_374863 := by
    simpa [prefixWord, tailWord_374863, baseEnd_374863] using wordTrace_append hprefix tailTrace_374863
  have hstable : (prefixWord ++ tailWord_374863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374863).length < 2 ^ (prefixWord ++ tailWord_374863).sum := by decide
  have hdescent : baseEnd_374863 < baseStart_374863 := by decide
  rcases family_descends (prefixWord ++ tailWord_374863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374904 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_374904 : Nat := 118140960795 + 374904 * 2 ^ 59
def prefixEnd_374904 : Nat := 4983230072969 + 3 ^ 40 * 374904 * 2
def baseEnd_374904 : Nat := 42779100287401426683523

theorem tailTrace_374904 : CollatzResearch.WordTrace tailWord_374904 prefixEnd_374904 42779100287401426683523 := by
  unfold tailWord_374904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836936116897155675369883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9115914822529540900493177 6836936116897155675369883)
  ·
    refine ⟨10255404175345733513054825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836936116897155675369883 10255404175345733513054825)
    ·
      refine ⟨7691553131509300134791119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10255404175345733513054825 7691553131509300134791119)
      ·
        refine ⟨11537329697263950202186679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691553131509300134791119 11537329697263950202186679)
        ·
          refine ⟨17305994545895925303280019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537329697263950202186679 17305994545895925303280019)
          ·
            refine ⟨25958991818843887954920029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17305994545895925303280019 25958991818843887954920029)
            ·
              refine ⟨9734621932066457983095011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25958991818843887954920029 9734621932066457983095011)
              ·
                refine ⟨14601932898099686974642517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9734621932066457983095011 14601932898099686974642517)
                ·
                  refine ⟨42779100287401426683523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14601932898099686974642517 42779100287401426683523)
                  ·
                    rfl

theorem cell22_374904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_374904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374904 prefixEnd_374904 := by exact prefixLift 374904
  have htrace : WordTrace (prefixWord ++ tailWord_374904) baseStart_374904 baseEnd_374904 := by
    simpa [prefixWord, tailWord_374904, baseEnd_374904] using wordTrace_append hprefix tailTrace_374904
  have hstable : (prefixWord ++ tailWord_374904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374904).length < 2 ^ (prefixWord ++ tailWord_374904).sum := by decide
  have hdescent : baseEnd_374904 < baseStart_374904 := by decide
  rcases family_descends (prefixWord ++ tailWord_374904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374921 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 6]
def baseStart_374921 : Nat := 118140960795 + 374921 * 2 ^ 59
def prefixEnd_374921 : Nat := 4983230072969 + 3 ^ 40 * 374921 * 2
def baseEnd_374921 : Nat := 42781040103207300791839

theorem tailTrace_374921 : CollatzResearch.WordTrace tailWord_374921 prefixEnd_374921 42781040103207300791839 := by
  unfold tailWord_374921
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674492274732723254108617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9116328183155148836072411 13674492274732723254108617)
  ·
    refine ⟨10255869206049542440581463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13674492274732723254108617 10255869206049542440581463)
    ·
      refine ⟨15383803809074313660872195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10255869206049542440581463 15383803809074313660872195)
      ·
        refine ⟨23075705713611470491308293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15383803809074313660872195 23075705713611470491308293)
        ·
          refine ⟨4326694821302150717120305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23075705713611470491308293 4326694821302150717120305)
          ·
            refine ⟨3245021115976613037840229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326694821302150717120305 3245021115976613037840229)
            ·
              refine ⟨608441459245614944595043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3245021115976613037840229 608441459245614944595043)
              ·
                refine ⟨912662188868422416892565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608441459245614944595043 912662188868422416892565)
                ·
                  refine ⟨42781040103207300791839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 912662188868422416892565 42781040103207300791839)
                  ·
                    rfl

theorem cell22_374921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_374921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374921 prefixEnd_374921 := by exact prefixLift 374921
  have htrace : WordTrace (prefixWord ++ tailWord_374921) baseStart_374921 baseEnd_374921 := by
    simpa [prefixWord, tailWord_374921, baseEnd_374921] using wordTrace_append hprefix tailTrace_374921
  have hstable : (prefixWord ++ tailWord_374921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374921).length < 2 ^ (prefixWord ++ tailWord_374921).sum := by decide
  have hdescent : baseEnd_374921 < baseStart_374921 := by decide
  rcases family_descends (prefixWord ++ tailWord_374921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_374972 : List Nat := [2, 2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_374972 : Nat := 118140960795 + 374972 * 2 ^ 59
def prefixEnd_374972 : Nat := 4983230072969 + 3 ^ 40 * 374972 * 2
def baseEnd_374972 : Nat := 42786859550624923116787

theorem tailTrace_374972 : CollatzResearch.WordTrace tailWord_374972 prefixEnd_374972 42786859550624923116787 := by
  unfold tailWord_374972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838176198773979482107585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9117568265031972642810113 6838176198773979482107585)
  ·
    refine ⟨5128632149080484611580689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6838176198773979482107585 5128632149080484611580689)
    ·
      refine ⟨3846474111810363458685517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5128632149080484611580689 3846474111810363458685517)
      ·
        refine ⟨1442427791928886297007069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3846474111810363458685517 1442427791928886297007069)
        ·
          refine ⟨540910421973332361377651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1442427791928886297007069 540910421973332361377651)
          ·
            refine ⟨811365632959998542066477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540910421973332361377651 811365632959998542066477)
            ·
              refine ⟨304262112359999453274929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 811365632959998542066477 304262112359999453274929)
              ·
                refine ⟨228196584269999589956197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304262112359999453274929 228196584269999589956197)
                ·
                  refine ⟨42786859550624923116787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228196584269999589956197 42786859550624923116787)
                  ·
                    rfl

theorem cell22_374972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_374972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_374972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_374972 prefixEnd_374972 := by exact prefixLift 374972
  have htrace : WordTrace (prefixWord ++ tailWord_374972) baseStart_374972 baseEnd_374972 := by
    simpa [prefixWord, tailWord_374972, baseEnd_374972] using wordTrace_append hprefix tailTrace_374972
  have hstable : (prefixWord ++ tailWord_374972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_374972).length < 2 ^ (prefixWord ++ tailWord_374972).sum := by decide
  have hdescent : baseEnd_374972 < baseStart_374972 := by decide
  rcases family_descends (prefixWord ++ tailWord_374972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375090 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_375090 : Nat := 118140960795 + 375090 * 2 ^ 59
def prefixEnd_375090 : Nat := 4983230072969 + 3 ^ 40 * 375090 * 2
def baseEnd_375090 : Nat := 42800324154453931633333

theorem tailTrace_375090 : CollatzResearch.WordTrace tailWord_375090 prefixEnd_375090 42800324154453931633333 := by
  unfold tailWord_375090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3420164052780116279252681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9120437474080310078007149 3420164052780116279252681)
  ·
    refine ⟨2565123039585087209439511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3420164052780116279252681 2565123039585087209439511)
    ·
      refine ⟨3847684559377630814159267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2565123039585087209439511 3847684559377630814159267)
      ·
        refine ⟨5771526839066446221238901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847684559377630814159267 5771526839066446221238901)
        ·
          refine ⟨541080641162479333241147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5771526839066446221238901 541080641162479333241147)
          ·
            refine ⟨811620961743718999861721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541080641162479333241147 811620961743718999861721)
            ·
              refine ⟨608715721307789249896291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811620961743718999861721 608715721307789249896291)
              ·
                refine ⟨913073581961683874844437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608715721307789249896291 913073581961683874844437)
                ·
                  refine ⟨42800324154453931633333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 913073581961683874844437 42800324154453931633333)
                  ·
                    rfl

theorem cell22_375090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_375090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375090 prefixEnd_375090 := by exact prefixLift 375090
  have htrace : WordTrace (prefixWord ++ tailWord_375090) baseStart_375090 baseEnd_375090 := by
    simpa [prefixWord, tailWord_375090, baseEnd_375090] using wordTrace_append hprefix tailTrace_375090
  have hstable : (prefixWord ++ tailWord_375090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375090).length < 2 ^ (prefixWord ++ tailWord_375090).sum := by decide
  have hdescent : baseEnd_375090 < baseStart_375090 := by decide
  rcases family_descends (prefixWord ++ tailWord_375090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375197 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 5]
def baseStart_375197 : Nat := 118140960795 + 375197 * 2 ^ 59
def prefixEnd_375197 : Nat := 4983230072969 + 3 ^ 40 * 375197 * 2
def baseEnd_375197 : Nat := 42812533583349727491557

theorem tailTrace_375197 : CollatzResearch.WordTrace tailWord_375197 prefixEnd_375197 42812533583349727491557 := by
  unfold tailWord_375197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684558821732822391155845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9123039214488548260770563 13684558821732822391155845)
  ·
    refine ⟨2565854779074904198341721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13684558821732822391155845 2565854779074904198341721)
    ·
      refine ⟨1924391084306178148756291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2565854779074904198341721 1924391084306178148756291)
      ·
        refine ⟨2886586626459267223134437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924391084306178148756291 2886586626459267223134437)
        ·
          refine ⟨541234992461112604337707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2886586626459267223134437 541234992461112604337707)
          ·
            refine ⟨811852488691668906506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541234992461112604337707 811852488691668906506561)
            ·
              refine ⟨608889366518751679879921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811852488691668906506561 608889366518751679879921)
              ·
                refine ⟨456667024889063759909941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608889366518751679879921 456667024889063759909941)
                ·
                  refine ⟨42812533583349727491557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456667024889063759909941 42812533583349727491557)
                  ·
                    rfl

theorem cell22_375197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_375197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375197 prefixEnd_375197 := by exact prefixLift 375197
  have htrace : WordTrace (prefixWord ++ tailWord_375197) baseStart_375197 baseEnd_375197 := by
    simpa [prefixWord, tailWord_375197, baseEnd_375197] using wordTrace_append hprefix tailTrace_375197
  have hstable : (prefixWord ++ tailWord_375197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375197).length < 2 ^ (prefixWord ++ tailWord_375197).sum := by decide
  have hdescent : baseEnd_375197 < baseStart_375197 := by decide
  rcases family_descends (prefixWord ++ tailWord_375197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375201 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 1, 3]
def baseStart_375201 : Nat := 118140960795 + 375201 * 2 ^ 59
def prefixEnd_375201 : Nat := 4983230072969 + 3 ^ 40 * 375201 * 2
def baseEnd_375201 : Nat := 128438970031794505374659

theorem tailTrace_375201 : CollatzResearch.WordTrace tailWord_375201 prefixEnd_375201 128438970031794505374659 := by
  unfold tailWord_375201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684704713718331074301457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9123136475812220716200971 13684704713718331074301457)
  ·
    refine ⟨10263528535288748305726093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13684704713718331074301457 10263528535288748305726093)
    ·
      refine ⟨3848823200733280614647285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10263528535288748305726093 3848823200733280614647285)
      ·
        refine ⟨360827175068745057623183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3848823200733280614647285 360827175068745057623183)
        ·
          refine ⟨541240762603117586434775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360827175068745057623183 541240762603117586434775)
          ·
            refine ⟨811861143904676379652163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541240762603117586434775 811861143904676379652163)
            ·
              refine ⟨1217791715857014569478245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811861143904676379652163 1217791715857014569478245)
              ·
                refine ⟨228335946723190231777171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1217791715857014569478245 228335946723190231777171)
                ·
                  refine ⟨342503920084785347665757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228335946723190231777171 342503920084785347665757)
                  ·
                    refine ⟨128438970031794505374659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342503920084785347665757 128438970031794505374659)
                    ·
                      rfl

theorem cell22_375201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_375201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375201 prefixEnd_375201 := by exact prefixLift 375201
  have htrace : WordTrace (prefixWord ++ tailWord_375201) baseStart_375201 baseEnd_375201 := by
    simpa [prefixWord, tailWord_375201, baseEnd_375201] using wordTrace_append hprefix tailTrace_375201
  have hstable : (prefixWord ++ tailWord_375201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375201).length < 2 ^ (prefixWord ++ tailWord_375201).sum := by decide
  have hdescent : baseEnd_375201 < baseStart_375201 := by decide
  rcases family_descends (prefixWord ++ tailWord_375201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375225 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 6]
def baseStart_375225 : Nat := 118140960795 + 375225 * 2 ^ 59
def prefixEnd_375225 : Nat := 4983230072969 + 3 ^ 40 * 375225 * 2
def baseEnd_375225 : Nat := 42815728574088814258195

theorem tailTrace_375225 : CollatzResearch.WordTrace tailWord_375225 prefixEnd_375225 42815728574088814258195 := by
  unfold tailWord_375225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13685580065631383173175129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9123720043754255448783419 13685580065631383173175129)
  ·
    refine ⟨10264185049223537379881347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13685580065631383173175129 10264185049223537379881347)
    ·
      refine ⟨15396277573835306069822021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264185049223537379881347 15396277573835306069822021)
      ·
        refine ⟨2886802045094119888091629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15396277573835306069822021 2886802045094119888091629)
        ·
          refine ⟨1082550766910294958034361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2886802045094119888091629 1082550766910294958034361)
          ·
            refine ⟨811913075182721218525771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082550766910294958034361 811913075182721218525771)
            ·
              refine ⟨1217869612774081827788657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811913075182721218525771 1217869612774081827788657)
              ·
                refine ⟨913402209580561370841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217869612774081827788657 913402209580561370841493)
                ·
                  refine ⟨42815728574088814258195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 913402209580561370841493 42815728574088814258195)
                  ·
                    rfl

theorem cell22_375225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_375225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375225 prefixEnd_375225 := by exact prefixLift 375225
  have htrace : WordTrace (prefixWord ++ tailWord_375225) baseStart_375225 baseEnd_375225 := by
    simpa [prefixWord, tailWord_375225, baseEnd_375225] using wordTrace_append hprefix tailTrace_375225
  have hstable : (prefixWord ++ tailWord_375225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375225).length < 2 ^ (prefixWord ++ tailWord_375225).sum := by decide
  have hdescent : baseEnd_375225 < baseStart_375225 := by decide
  rcases family_descends (prefixWord ++ tailWord_375225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375240 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_375240 : Nat := 118140960795 + 375240 * 2 ^ 59
def prefixEnd_375240 : Nat := 4983230072969 + 3 ^ 40 * 375240 * 2
def baseEnd_375240 : Nat := 128452320528811403649539

theorem tailTrace_375240 : CollatzResearch.WordTrace tailWord_375240 prefixEnd_375240 128452320528811403649539 := by
  unfold tailWord_375240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843063580288520367485587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9124084773718027156647449 6843063580288520367485587)
  ·
    refine ⟨10264595370432780551228381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6843063580288520367485587 10264595370432780551228381)
    ·
      refine ⟨3849223263912292706710643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10264595370432780551228381 3849223263912292706710643)
      ·
        refine ⟨5773834895868439060065965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849223263912292706710643 5773834895868439060065965)
        ·
          refine ⟨2165188085950664647524737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5773834895868439060065965 2165188085950664647524737)
          ·
            refine ⟨1623891064462998485643553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165188085950664647524737 1623891064462998485643553)
            ·
              refine ⟨1217918298347248864232665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623891064462998485643553 1217918298347248864232665)
              ·
                refine ⟨913438723760436648174499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217918298347248864232665 913438723760436648174499)
                ·
                  refine ⟨1370158085640654972261749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 913438723760436648174499 1370158085640654972261749)
                  ·
                    refine ⟨128452320528811403649539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1370158085640654972261749 128452320528811403649539)
                    ·
                      rfl

theorem cell22_375240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_375240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375240 prefixEnd_375240 := by exact prefixLift 375240
  have htrace : WordTrace (prefixWord ++ tailWord_375240) baseStart_375240 baseEnd_375240 := by
    simpa [prefixWord, tailWord_375240, baseEnd_375240] using wordTrace_append hprefix tailTrace_375240
  have hstable : (prefixWord ++ tailWord_375240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375240).length < 2 ^ (prefixWord ++ tailWord_375240).sum := by decide
  have hdescent : baseEnd_375240 < baseStart_375240 := by decide
  rcases family_descends (prefixWord ++ tailWord_375240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375242 : List Nat := [3, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_375242 : Nat := 118140960795 + 375242 * 2 ^ 59
def prefixEnd_375242 : Nat := 4983230072969 + 3 ^ 40 * 375242 * 2
def baseEnd_375242 : Nat := 42817668389894688366511

theorem tailTrace_375242 : CollatzResearch.WordTrace tailWord_375242 prefixEnd_375242 42817668389894688366511 := by
  unfold tailWord_375242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3421550026642448769135995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9124133404379863384362653 3421550026642448769135995)
  ·
    refine ⟨5132325039963673153703993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3421550026642448769135995 5132325039963673153703993)
    ·
      refine ⟨3849243779972754865277995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5132325039963673153703993 3849243779972754865277995)
      ·
        refine ⟨5773865669959132297916993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849243779972754865277995 5773865669959132297916993)
        ·
          refine ⟨4330399252469349223437745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773865669959132297916993 4330399252469349223437745)
          ·
            refine ⟨3247799439352011917578309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4330399252469349223437745 3247799439352011917578309)
            ·
              refine ⟨608962394878502234545933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3247799439352011917578309 608962394878502234545933)
              ·
                refine ⟨228360898079438337954725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608962394878502234545933 228360898079438337954725)
                ·
                  refine ⟨42817668389894688366511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228360898079438337954725 42817668389894688366511)
                  ·
                    rfl

theorem cell22_375242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_375242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375242 prefixEnd_375242 := by exact prefixLift 375242
  have htrace : WordTrace (prefixWord ++ tailWord_375242) baseStart_375242 baseEnd_375242 := by
    simpa [prefixWord, tailWord_375242, baseEnd_375242] using wordTrace_append hprefix tailTrace_375242
  have hstable : (prefixWord ++ tailWord_375242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375242).length < 2 ^ (prefixWord ++ tailWord_375242).sum := by decide
  have hdescent : baseEnd_375242 < baseStart_375242 := by decide
  rcases family_descends (prefixWord ++ tailWord_375242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375315 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 5]
def baseStart_375315 : Nat := 118140960795 + 375315 * 2 ^ 59
def prefixEnd_375315 : Nat := 4983230072969 + 3 ^ 40 * 375315 * 2
def baseEnd_375315 : Nat := 42825998187178736008103

theorem tailTrace_375315 : CollatzResearch.WordTrace tailWord_375315 prefixEnd_375315 42825998187178736008103 := by
  unfold tailWord_375315
  simp only [CollatzResearch.WordTrace]
  refine ⟨13688862635305328543951399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9125908423536885695967599 13688862635305328543951399)
  ·
    refine ⟨20533293952957992815927099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13688862635305328543951399 20533293952957992815927099)
    ·
      refine ⟨30799940929436989223890649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20533293952957992815927099 30799940929436989223890649)
      ·
        refine ⟨23099955697077741917917987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30799940929436989223890649 23099955697077741917917987)
        ·
          refine ⟨34649933545616612876876981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099955697077741917917987 34649933545616612876876981)
          ·
            refine ⟨3248431269901557457207217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34649933545616612876876981 3248431269901557457207217)
            ·
              refine ⟨2436323452426168092905413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248431269901557457207217 2436323452426168092905413)
              ·
                refine ⟨456810647329906517419765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2436323452426168092905413 456810647329906517419765)
                ·
                  refine ⟨42825998187178736008103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456810647329906517419765 42825998187178736008103)
                  ·
                    rfl

theorem cell22_375315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 5].length) (baseStart_375315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375315 prefixEnd_375315 := by exact prefixLift 375315
  have htrace : WordTrace (prefixWord ++ tailWord_375315) baseStart_375315 baseEnd_375315 := by
    simpa [prefixWord, tailWord_375315, baseEnd_375315] using wordTrace_append hprefix tailTrace_375315
  have hstable : (prefixWord ++ tailWord_375315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375315).length < 2 ^ (prefixWord ++ tailWord_375315).sum := by decide
  have hdescent : baseEnd_375315 < baseStart_375315 := by decide
  rcases family_descends (prefixWord ++ tailWord_375315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375330 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_375330 : Nat := 118140960795 + 375330 * 2 ^ 59
def prefixEnd_375330 : Nat := 4983230072969 + 3 ^ 40 * 375330 * 2
def baseEnd_375330 : Nat := 128483129368081168899263

theorem tailTrace_375330 : CollatzResearch.WordTrace tailWord_375330 prefixEnd_375330 128483129368081168899263 := by
  unfold tailWord_375330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3422352432562746526436861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9126273153500657403831629 3422352432562746526436861)
  ·
    refine ⟨1283382162211029947413823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3422352432562746526436861 1283382162211029947413823)
    ·
      refine ⟨1925073243316544921120735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283382162211029947413823 1925073243316544921120735)
      ·
        refine ⟨2887609864974817381681103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925073243316544921120735 2887609864974817381681103)
        ·
          refine ⟨4331414797462226072521655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887609864974817381681103 4331414797462226072521655)
          ·
            refine ⟨6497122196193339108782483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331414797462226072521655 6497122196193339108782483)
            ·
              refine ⟨9745683294290008663173725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497122196193339108782483 9745683294290008663173725)
              ·
                refine ⟨3654631235358753248690147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9745683294290008663173725 3654631235358753248690147)
                ·
                  refine ⟨5481946853038129873035221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654631235358753248690147 5481946853038129873035221)
                  ·
                    refine ⟨128483129368081168899263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5481946853038129873035221 128483129368081168899263)
                    ·
                      rfl

theorem cell22_375330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_375330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375330 prefixEnd_375330 := by exact prefixLift 375330
  have htrace : WordTrace (prefixWord ++ tailWord_375330) baseStart_375330 baseEnd_375330 := by
    simpa [prefixWord, tailWord_375330, baseEnd_375330] using wordTrace_append hprefix tailTrace_375330
  have hstable : (prefixWord ++ tailWord_375330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375330).length < 2 ^ (prefixWord ++ tailWord_375330).sum := by decide
  have hdescent : baseEnd_375330 < baseStart_375330 := by decide
  rcases family_descends (prefixWord ++ tailWord_375330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375366 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_375366 : Nat := 118140960795 + 375366 * 2 ^ 59
def prefixEnd_375366 : Nat := 4983230072969 + 3 ^ 40 * 375366 * 2
def baseEnd_375366 : Nat := 42831817634596358333051

theorem tailTrace_375366 : CollatzResearch.WordTrace tailWord_375366 prefixEnd_375366 42831817634596358333051 := by
  unfold tailWord_375366
  simp only [CollatzResearch.WordTrace]
  refine ⟨427835086191267632939311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9127148505413709502705301 427835086191267632939311)
  ·
    refine ⟨641752629286901449408967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427835086191267632939311 641752629286901449408967)
    ·
      refine ⟨962628943930352174113451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641752629286901449408967 962628943930352174113451)
      ·
        refine ⟨1443943415895528261170177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962628943930352174113451 1443943415895528261170177)
        ·
          refine ⟨1082957561921646195877633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1443943415895528261170177 1082957561921646195877633)
          ·
            refine ⟨812218171441234646908225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082957561921646195877633 812218171441234646908225)
            ·
              refine ⟨609163628580925985181169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812218171441234646908225 609163628580925985181169)
              ·
                refine ⟨456872721435694488885877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609163628580925985181169 456872721435694488885877)
                ·
                  refine ⟨42831817634596358333051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456872721435694488885877 42831817634596358333051)
                  ·
                    rfl

theorem cell22_375366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_375366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375366 prefixEnd_375366 := by exact prefixLift 375366
  have htrace : WordTrace (prefixWord ++ tailWord_375366) baseStart_375366 baseEnd_375366 := by
    simpa [prefixWord, tailWord_375366, baseEnd_375366] using wordTrace_append hprefix tailTrace_375366
  have hstable : (prefixWord ++ tailWord_375366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375366).length < 2 ^ (prefixWord ++ tailWord_375366).sum := by decide
  have hdescent : baseEnd_375366 < baseStart_375366 := by decide
  rcases family_descends (prefixWord ++ tailWord_375366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375407 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 2, 4]
def baseStart_375407 : Nat := 118140960795 + 375407 * 2 ^ 59
def prefixEnd_375407 : Nat := 4983230072969 + 3 ^ 40 * 375407 * 2
def baseEnd_375407 : Nat := 128509488041678634724027

theorem tailTrace_375407 : CollatzResearch.WordTrace tailWord_375407 prefixEnd_375407 128509488041678634724027 := by
  unfold tailWord_375407
  simp only [CollatzResearch.WordTrace]
  refine ⟨13692218150972028256300475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9128145433981352170866983 13692218150972028256300475)
  ·
    refine ⟨20538327226458042384450713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13692218150972028256300475 20538327226458042384450713)
    ·
      refine ⟨15403745419843531788338035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20538327226458042384450713 15403745419843531788338035)
      ·
        refine ⟨23105618129765297682507053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15403745419843531788338035 23105618129765297682507053)
        ·
          refine ⟨8664606798661986630940145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23105618129765297682507053 8664606798661986630940145)
          ·
            refine ⟨6498455098996489973205109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8664606798661986630940145 6498455098996489973205109)
            ·
              refine ⟨609230165530920934987979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6498455098996489973205109 609230165530920934987979)
              ·
                refine ⟨913845248296381402481969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609230165530920934987979 913845248296381402481969)
                ·
                  refine ⟨685383936222286051861477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 913845248296381402481969 685383936222286051861477)
                  ·
                    refine ⟨128509488041678634724027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685383936222286051861477 128509488041678634724027)
                    ·
                      rfl

theorem cell22_375407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_375407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375407 prefixEnd_375407 := by exact prefixLift 375407
  have htrace : WordTrace (prefixWord ++ tailWord_375407) baseStart_375407 baseEnd_375407 := by
    simpa [prefixWord, tailWord_375407, baseEnd_375407] using wordTrace_append hprefix tailTrace_375407
  have hstable : (prefixWord ++ tailWord_375407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375407).length < 2 ^ (prefixWord ++ tailWord_375407).sum := by decide
  have hdescent : baseEnd_375407 < baseStart_375407 := by decide
  rcases family_descends (prefixWord ++ tailWord_375407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375413 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_375413 : Nat := 118140960795 + 375413 * 2 ^ 59
def prefixEnd_375413 : Nat := 4983230072969 + 3 ^ 40 * 375413 * 2
def baseEnd_375413 : Nat := 128511541964296619074009

theorem tailTrace_375413 : CollatzResearch.WordTrace tailWord_375413 prefixEnd_375413 128511541964296619074009 := by
  unfold tailWord_375413
  simp only [CollatzResearch.WordTrace]
  refine ⟨13692436988950291281018893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9128291325966860854012595 13692436988950291281018893)
  ·
    refine ⟨5134663870856359230382085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13692436988950291281018893 5134663870856359230382085)
    ·
      refine ⟨962749475785567355696641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5134663870856359230382085 962749475785567355696641)
      ·
        refine ⟨722062106839175516772481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 962749475785567355696641 722062106839175516772481)
        ·
          refine ⟨541546580129381637579361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 722062106839175516772481 541546580129381637579361)
          ·
            refine ⟨406159935097036228184521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541546580129381637579361 406159935097036228184521)
            ·
              refine ⟨304619951322777171138391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406159935097036228184521 304619951322777171138391)
              ·
                refine ⟨456929926984165756707587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304619951322777171138391 456929926984165756707587)
                ·
                  refine ⟨685394890476248635061381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456929926984165756707587 685394890476248635061381)
                  ·
                    refine ⟨128511541964296619074009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685394890476248635061381 128511541964296619074009)
                    ·
                      rfl

theorem cell22_375413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_375413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375413 prefixEnd_375413 := by exact prefixLift 375413
  have htrace : WordTrace (prefixWord ++ tailWord_375413) baseStart_375413 baseEnd_375413 := by
    simpa [prefixWord, tailWord_375413, baseEnd_375413] using wordTrace_append hprefix tailTrace_375413
  have hstable : (prefixWord ++ tailWord_375413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375413).length < 2 ^ (prefixWord ++ tailWord_375413).sum := by decide
  have hdescent : baseEnd_375413 < baseStart_375413 := by decide
  rcases family_descends (prefixWord ++ tailWord_375413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375435 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_375435 : Nat := 118140960795 + 375435 * 2 ^ 59
def prefixEnd_375435 : Nat := 4983230072969 + 3 ^ 40 * 375435 * 2
def baseEnd_375435 : Nat := 128519073013895895023941

theorem tailTrace_375435 : CollatzResearch.WordTrace tailWord_375435 prefixEnd_375435 128519073013895895023941 := by
  unfold tailWord_375435
  simp only [CollatzResearch.WordTrace]
  refine ⟨13693239394870589038319759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9128826263247059358879839 13693239394870589038319759)
  ·
    refine ⟨20539859092305883557479639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13693239394870589038319759 20539859092305883557479639)
    ·
      refine ⟨30809788638458825336219459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20539859092305883557479639 30809788638458825336219459)
      ·
        refine ⟨46214682957688238004329189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30809788638458825336219459 46214682957688238004329189)
        ·
          refine ⟨8665253054566544625811723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46214682957688238004329189 8665253054566544625811723)
          ·
            refine ⟨12997879581849816938717585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665253054566544625811723 12997879581849816938717585)
            ·
              refine ⟨9748409686387362704038189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12997879581849816938717585 9748409686387362704038189)
              ·
                refine ⟨3655653632395261014014321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9748409686387362704038189 3655653632395261014014321)
                ·
                  refine ⟨2741740224296445760510741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655653632395261014014321 2741740224296445760510741)
                  ·
                    refine ⟨128519073013895895023941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2741740224296445760510741 128519073013895895023941)
                    ·
                      rfl

theorem cell22_375435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_375435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375435 prefixEnd_375435 := by exact prefixLift 375435
  have htrace : WordTrace (prefixWord ++ tailWord_375435) baseStart_375435 baseEnd_375435 := by
    simpa [prefixWord, tailWord_375435, baseEnd_375435] using wordTrace_append hprefix tailTrace_375435
  have hstable : (prefixWord ++ tailWord_375435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375435).length < 2 ^ (prefixWord ++ tailWord_375435).sum := by decide
  have hdescent : baseEnd_375435 < baseStart_375435 := by decide
  rcases family_descends (prefixWord ++ tailWord_375435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375456 : List Nat := [2, 1, 1, 4, 5, 1, 2, 6]
def baseStart_375456 : Nat := 118140960795 + 375456 * 2 ^ 59
def prefixEnd_375456 : Nat := 4983230072969 + 3 ^ 40 * 375456 * 2
def baseEnd_375456 : Nat := 14280695749228760027653

theorem tailTrace_375456 : CollatzResearch.WordTrace tailWord_375456 prefixEnd_375456 14280695749228760027653 := by
  unfold tailWord_375456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847002663897254812417111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9129336885196339749889481 6847002663897254812417111)
  ·
    refine ⟨10270503995845882218625667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6847002663897254812417111 10270503995845882218625667)
    ·
      refine ⟨15405755993768823327938501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10270503995845882218625667 15405755993768823327938501)
      ·
        refine ⟨2888579248831654373988469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15405755993768823327938501 2888579248831654373988469)
        ·
          refine ⟨270804304577967597561419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2888579248831654373988469 270804304577967597561419)
          ·
            refine ⟨406206456866951396342129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270804304577967597561419 406206456866951396342129)
            ·
              refine ⟨304654842650213547256597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406206456866951396342129 304654842650213547256597)
              ·
                refine ⟨14280695749228760027653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 304654842650213547256597 14280695749228760027653)
                ·
                  rfl

theorem cell22_375456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_375456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375456 prefixEnd_375456 := by exact prefixLift 375456
  have htrace : WordTrace (prefixWord ++ tailWord_375456) baseStart_375456 baseEnd_375456 := by
    simpa [prefixWord, tailWord_375456, baseEnd_375456] using wordTrace_append hprefix tailTrace_375456
  have hstable : (prefixWord ++ tailWord_375456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375456).length < 2 ^ (prefixWord ++ tailWord_375456).sum := by decide
  have hdescent : baseEnd_375456 < baseStart_375456 := by decide
  rcases family_descends (prefixWord ++ tailWord_375456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_375465 : Nat := 118140960795 + 375465 * 2 ^ 59
def prefixEnd_375465 : Nat := 4983230072969 + 3 ^ 40 * 375465 * 2
def baseEnd_375465 : Nat := 128529342626985816773849

theorem tailTrace_375465 : CollatzResearch.WordTrace tailWord_375465 prefixEnd_375465 128529342626985816773849 := by
  unfold tailWord_375465
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694333584761904161911849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9129555723174602774607899 13694333584761904161911849)
  ·
    refine ⟨10270750188571428121433887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13694333584761904161911849 10270750188571428121433887)
    ·
      refine ⟨15406125282857142182150831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10270750188571428121433887 15406125282857142182150831)
      ·
        refine ⟨23109187924285713273226247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15406125282857142182150831 23109187924285713273226247)
        ·
          refine ⟨34663781886428569909839371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23109187924285713273226247 34663781886428569909839371)
          ·
            refine ⟨51995672829642854864759057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34663781886428569909839371 51995672829642854864759057)
            ·
              refine ⟨38996754622232141148569293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51995672829642854864759057 38996754622232141148569293)
              ·
                refine ⟨14623782983337052930713485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38996754622232141148569293 14623782983337052930713485)
                ·
                  refine ⟨5483918618751394849017557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14623782983337052930713485 5483918618751394849017557)
                  ·
                    refine ⟨128529342626985816773849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5483918618751394849017557 128529342626985816773849)
                    ·
                      rfl

theorem cell22_375465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_375465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375465 prefixEnd_375465 := by exact prefixLift 375465
  have htrace : WordTrace (prefixWord ++ tailWord_375465) baseStart_375465 baseEnd_375465 := by
    simpa [prefixWord, tailWord_375465, baseEnd_375465] using wordTrace_append hprefix tailTrace_375465
  have hstable : (prefixWord ++ tailWord_375465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375465).length < 2 ^ (prefixWord ++ tailWord_375465).sum := by decide
  have hdescent : baseEnd_375465 < baseStart_375465 := by decide
  rcases family_descends (prefixWord ++ tailWord_375465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375471 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 1, 3]
def baseStart_375471 : Nat := 118140960795 + 375471 * 2 ^ 59
def prefixEnd_375471 : Nat := 4983230072969 + 3 ^ 40 * 375471 * 2
def baseEnd_375471 : Nat := 128531396549603801123831

theorem tailTrace_375471 : CollatzResearch.WordTrace tailWord_375471 prefixEnd_375471 128531396549603801123831 := by
  unfold tailWord_375471
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694552422740167186630267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9129701615160111457753511 13694552422740167186630267)
  ·
    refine ⟨20541828634110250779945401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13694552422740167186630267 20541828634110250779945401)
    ·
      refine ⟨15406371475582688084959051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20541828634110250779945401 15406371475582688084959051)
      ·
        refine ⟨23109557213374032127438577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15406371475582688084959051 23109557213374032127438577)
        ·
          refine ⟨17332167910030524095578933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23109557213374032127438577 17332167910030524095578933)
          ·
            refine ⟨1624890741565361633960525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17332167910030524095578933 1624890741565361633960525)
            ·
              refine ⟨609334028087010612735197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1624890741565361633960525 609334028087010612735197)
              ·
                refine ⟨228500260532628979775699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609334028087010612735197 228500260532628979775699)
                ·
                  refine ⟨342750390798943469663549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228500260532628979775699 342750390798943469663549)
                  ·
                    refine ⟨128531396549603801123831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342750390798943469663549 128531396549603801123831)
                    ·
                      rfl

theorem cell22_375471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_375471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375471 prefixEnd_375471 := by exact prefixLift 375471
  have htrace : WordTrace (prefixWord ++ tailWord_375471) baseStart_375471 baseEnd_375471 := by
    simpa [prefixWord, tailWord_375471, baseEnd_375471] using wordTrace_append hprefix tailTrace_375471
  have hstable : (prefixWord ++ tailWord_375471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375471).length < 2 ^ (prefixWord ++ tailWord_375471).sum := by decide
  have hdescent : baseEnd_375471 < baseStart_375471 := by decide
  rcases family_descends (prefixWord ++ tailWord_375471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375488 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 1, 3]
def baseStart_375488 : Nat := 118140960795 + 375488 * 2 ^ 59
def prefixEnd_375488 : Nat := 4983230072969 + 3 ^ 40 * 375488 * 2
def baseEnd_375488 : Nat := 128537215997021423448779

theorem tailTrace_375488 : CollatzResearch.WordTrace tailWord_375488 prefixEnd_375488 128537215997021423448779 := by
  unfold tailWord_375488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6847586231839289544999559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9130114975785719393332745 6847586231839289544999559)
  ·
    refine ⟨10271379347758934317499339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6847586231839289544999559 10271379347758934317499339)
    ·
      refine ⟨15407069021638401476249009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10271379347758934317499339 15407069021638401476249009)
      ·
        refine ⟨11555301766228801107186757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15407069021638401476249009 11555301766228801107186757)
        ·
          refine ⟨2166619081167900207597517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11555301766228801107186757 2166619081167900207597517)
          ·
            refine ⟨812482155437962577849069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2166619081167900207597517 812482155437962577849069)
            ·
              refine ⟨304680808289235966693401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 812482155437962577849069 304680808289235966693401)
              ·
                refine ⟨228510606216926975020051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304680808289235966693401 228510606216926975020051)
                ·
                  refine ⟨342765909325390462530077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228510606216926975020051 342765909325390462530077)
                  ·
                    refine ⟨128537215997021423448779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342765909325390462530077 128537215997021423448779)
                    ·
                      rfl

theorem cell22_375488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_375488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375488 prefixEnd_375488 := by exact prefixLift 375488
  have htrace : WordTrace (prefixWord ++ tailWord_375488) baseStart_375488 baseEnd_375488 := by
    simpa [prefixWord, tailWord_375488, baseEnd_375488] using wordTrace_append hprefix tailTrace_375488
  have hstable : (prefixWord ++ tailWord_375488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375488).length < 2 ^ (prefixWord ++ tailWord_375488).sum := by decide
  have hdescent : baseEnd_375488 < baseStart_375488 := by decide
  rcases family_descends (prefixWord ++ tailWord_375488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375494 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_375494 : Nat := 118140960795 + 375494 * 2 ^ 59
def prefixEnd_375494 : Nat := 4983230072969 + 3 ^ 40 * 375494 * 2
def baseEnd_375494 : Nat := 128539269919639407798761

theorem tailTrace_375494 : CollatzResearch.WordTrace tailWord_375494 prefixEnd_375494 128539269919639407798761 := by
  unfold tailWord_375494
  simp only [CollatzResearch.WordTrace]
  refine ⟨427980978176776316084923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9130260867771228076478357 427980978176776316084923)
  ·
    refine ⟨641971467265164474127385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427980978176776316084923 641971467265164474127385)
    ·
      refine ⟨481478600448873355595539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 641971467265164474127385 481478600448873355595539)
      ·
        refine ⟨722217900673310033393309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481478600448873355595539 722217900673310033393309)
        ·
          refine ⟨270831712752491262522491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722217900673310033393309 270831712752491262522491)
          ·
            refine ⟨406247569128736893783737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270831712752491262522491 406247569128736893783737)
            ·
              refine ⟨304685676846552670337803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406247569128736893783737 304685676846552670337803)
              ·
                refine ⟨457028515269829005506705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304685676846552670337803 457028515269829005506705)
                ·
                  refine ⟨342771386452371754130029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457028515269829005506705 342771386452371754130029)
                  ·
                    refine ⟨128539269919639407798761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342771386452371754130029 128539269919639407798761)
                    ·
                      rfl

theorem cell22_375494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_375494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375494 prefixEnd_375494 := by exact prefixLift 375494
  have htrace : WordTrace (prefixWord ++ tailWord_375494) baseStart_375494 baseEnd_375494 := by
    simpa [prefixWord, tailWord_375494, baseEnd_375494] using wordTrace_append hprefix tailTrace_375494
  have hstable : (prefixWord ++ tailWord_375494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375494).length < 2 ^ (prefixWord ++ tailWord_375494).sum := by decide
  have hdescent : baseEnd_375494 < baseStart_375494 := by decide
  rcases family_descends (prefixWord ++ tailWord_375494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375546 : List Nat := [3, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_375546 : Nat := 118140960795 + 375546 * 2 ^ 59
def prefixEnd_375546 : Nat := 4983230072969 + 3 ^ 40 * 375546 * 2
def baseEnd_375546 : Nat := 42852356860776201832867

theorem tailTrace_375546 : CollatzResearch.WordTrace tailWord_375546 prefixEnd_375546 42852356860776201832867 := by
  unfold tailWord_375546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3424321974367113748902623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9131525264978969997073661 3424321974367113748902623)
  ·
    refine ⟨5136482961550670623353935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3424321974367113748902623 5136482961550670623353935)
    ·
      refine ⟨7704724442326005935030903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5136482961550670623353935 7704724442326005935030903)
      ·
        refine ⟨11557086663489008902546355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7704724442326005935030903 11557086663489008902546355)
        ·
          refine ⟨17335629995233513353819533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557086663489008902546355 17335629995233513353819533)
          ·
            refine ⟨6500861248212567507682325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17335629995233513353819533 6500861248212567507682325)
            ·
              refine ⟨304727871009964101922609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6500861248212567507682325 304727871009964101922609)
              ·
                refine ⟨228545903257473076441957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304727871009964101922609 228545903257473076441957)
                ·
                  refine ⟨42852356860776201832867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228545903257473076441957 42852356860776201832867)
                  ·
                    rfl

theorem cell22_375546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_375546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375546 prefixEnd_375546 := by exact prefixLift 375546
  have htrace : WordTrace (prefixWord ++ tailWord_375546) baseStart_375546 baseEnd_375546 := by
    simpa [prefixWord, tailWord_375546, baseEnd_375546] using wordTrace_append hprefix tailTrace_375546
  have hstable : (prefixWord ++ tailWord_375546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375546).length < 2 ^ (prefixWord ++ tailWord_375546).sum := by decide
  have hdescent : baseEnd_375546 < baseStart_375546 := by decide
  rcases family_descends (prefixWord ++ tailWord_375546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375589 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_375589 : Nat := 118140960795 + 375589 * 2 ^ 59
def prefixEnd_375589 : Nat := 4983230072969 + 3 ^ 40 * 375589 * 2
def baseEnd_375589 : Nat := 128571790361090826673469

theorem tailTrace_375589 : CollatzResearch.WordTrace tailWord_375589 prefixEnd_375589 128571790361090826673469 := by
  unfold tailWord_375589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698856236312673339425821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9132570824208448892950547 13698856236312673339425821)
  ·
    refine ⟨5137071088617252502284683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13698856236312673339425821 5137071088617252502284683)
    ·
      refine ⟨7705606632925878753427025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5137071088617252502284683 7705606632925878753427025)
      ·
        refine ⟨5779204974694409065070269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7705606632925878753427025 5779204974694409065070269)
        ·
          refine ⟨2167201865510403399401351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5779204974694409065070269 2167201865510403399401351)
          ·
            refine ⟨3250802798265605099102027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167201865510403399401351 3250802798265605099102027)
            ·
              refine ⟨4876204197398407648653041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250802798265605099102027 4876204197398407648653041)
              ·
                refine ⟨3657153148048805736489781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876204197398407648653041 3657153148048805736489781)
                ·
                  refine ⟨342858107629575537795917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657153148048805736489781 342858107629575537795917)
                  ·
                    refine ⟨128571790361090826673469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342858107629575537795917 128571790361090826673469)
                    ·
                      rfl

theorem cell22_375589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_375589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375589 prefixEnd_375589 := by exact prefixLift 375589
  have htrace : WordTrace (prefixWord ++ tailWord_375589) baseStart_375589 baseEnd_375589 := by
    simpa [prefixWord, tailWord_375589, baseEnd_375589] using wordTrace_append hprefix tailTrace_375589
  have hstable : (prefixWord ++ tailWord_375589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375589).length < 2 ^ (prefixWord ++ tailWord_375589).sum := by decide
  have hdescent : baseEnd_375589 < baseStart_375589 := by decide
  rcases family_descends (prefixWord ++ tailWord_375589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375664 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_375664 : Nat := 118140960795 + 375664 * 2 ^ 59
def prefixEnd_375664 : Nat := 4983230072969 + 3 ^ 40 * 375664 * 2
def baseEnd_375664 : Nat := 42865821464605210349413

theorem tailTrace_375664 : CollatzResearch.WordTrace tailWord_375664 prefixEnd_375664 42865821464605210349413 := by
  unfold tailWord_375664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850795855520480574203023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9134394474027307432270697 6850795855520480574203023)
  ·
    refine ⟨10276193783280720861304535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6850795855520480574203023 10276193783280720861304535)
    ·
      refine ⟨15414290674921081291956803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10276193783280720861304535 15414290674921081291956803)
      ·
        refine ⟨23121436012381621937935205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15414290674921081291956803 23121436012381621937935205)
        ·
          refine ⟨4335269252321554113362851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23121436012381621937935205 4335269252321554113362851)
          ·
            refine ⟨6502903878482331170044277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335269252321554113362851 6502903878482331170044277)
            ·
              refine ⟨609647238607718547191651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6502903878482331170044277 609647238607718547191651)
              ·
                refine ⟨914470857911577820787477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609647238607718547191651 914470857911577820787477)
                ·
                  refine ⟨42865821464605210349413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 914470857911577820787477 42865821464605210349413)
                  ·
                    rfl

theorem cell22_375664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_375664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375664 prefixEnd_375664 := by exact prefixLift 375664
  have htrace : WordTrace (prefixWord ++ tailWord_375664) baseStart_375664 baseEnd_375664 := by
    simpa [prefixWord, tailWord_375664, baseEnd_375664] using wordTrace_append hprefix tailTrace_375664
  have hstable : (prefixWord ++ tailWord_375664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375664).length < 2 ^ (prefixWord ++ tailWord_375664).sum := by decide
  have hdescent : baseEnd_375664 < baseStart_375664 := by decide
  rcases family_descends (prefixWord ++ tailWord_375664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375670 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_375670 : Nat := 118140960795 + 375670 * 2 ^ 59
def prefixEnd_375670 : Nat := 4983230072969 + 3 ^ 40 * 375670 * 2
def baseEnd_375670 : Nat := 42866506105477871799407

theorem tailTrace_375670 : CollatzResearch.WordTrace tailWord_375670 prefixEnd_375670 42866506105477871799407 := by
  unfold tailWord_375670
  simp only [CollatzResearch.WordTrace]
  refine ⟨856363159313701510820279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9134540366012816115416309 856363159313701510820279)
  ·
    refine ⟨1284544738970552266230419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 856363159313701510820279 1284544738970552266230419)
    ·
      refine ⟨1926817108455828399345629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1284544738970552266230419 1926817108455828399345629)
      ·
        refine ⟨722556415670935649754611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1926817108455828399345629 722556415670935649754611)
        ·
          refine ⟨1083834623506403474631917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722556415670935649754611 1083834623506403474631917)
          ·
            refine ⟨406437983814901302986969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1083834623506403474631917 406437983814901302986969)
            ·
              refine ⟨304828487861175977240227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406437983814901302986969 304828487861175977240227)
              ·
                refine ⟨457242731791763965860341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304828487861175977240227 457242731791763965860341)
                ·
                  refine ⟨42866506105477871799407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457242731791763965860341 42866506105477871799407)
                  ·
                    rfl

theorem cell22_375670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_375670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375670 prefixEnd_375670 := by exact prefixLift 375670
  have htrace : WordTrace (prefixWord ++ tailWord_375670) baseStart_375670 baseEnd_375670 := by
    simpa [prefixWord, tailWord_375670, baseEnd_375670] using wordTrace_append hprefix tailTrace_375670
  have hstable : (prefixWord ++ tailWord_375670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375670).length < 2 ^ (prefixWord ++ tailWord_375670).sum := by decide
  have hdescent : baseEnd_375670 < baseStart_375670 := by decide
  rcases family_descends (prefixWord ++ tailWord_375670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375711 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_375711 : Nat := 118140960795 + 375711 * 2 ^ 59
def prefixEnd_375711 : Nat := 4983230072969 + 3 ^ 40 * 375711 * 2
def baseEnd_375711 : Nat := 128613553454323175123095

theorem tailTrace_375711 : CollatzResearch.WordTrace tailWord_375711 prefixEnd_375711 128613553454323175123095 := by
  unfold tailWord_375711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703305941870688175366987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9135537294580458783577991 13703305941870688175366987)
  ·
    refine ⟨20554958912806032263050481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13703305941870688175366987 20554958912806032263050481)
    ·
      refine ⟨15416219184604524197287861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20554958912806032263050481 15416219184604524197287861)
      ·
        refine ⟨1445270548556674143495737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15416219184604524197287861 1445270548556674143495737)
        ·
          refine ⟨1083952911417505607621803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1445270548556674143495737 1083952911417505607621803)
          ·
            refine ⟨1625929367126258411432705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083952911417505607621803 1625929367126258411432705)
            ·
              refine ⟨1219447025344693808574529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1625929367126258411432705 1219447025344693808574529)
              ·
                refine ⟨914585269008520356430897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1219447025344693808574529 914585269008520356430897)
                ·
                  refine ⟨685938951756390267323173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 914585269008520356430897 685938951756390267323173)
                  ·
                    refine ⟨128613553454323175123095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685938951756390267323173 128613553454323175123095)
                    ·
                      rfl

theorem cell22_375711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_375711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375711 prefixEnd_375711 := by exact prefixLift 375711
  have htrace : WordTrace (prefixWord ++ tailWord_375711) baseStart_375711 baseEnd_375711 := by
    simpa [prefixWord, tailWord_375711, baseEnd_375711] using wordTrace_append hprefix tailTrace_375711
  have hstable : (prefixWord ++ tailWord_375711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375711).length < 2 ^ (prefixWord ++ tailWord_375711).sum := by decide
  have hdescent : baseEnd_375711 < baseStart_375711 := by decide
  rcases family_descends (prefixWord ++ tailWord_375711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375713 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_375713 : Nat := 118140960795 + 375713 * 2 ^ 59
def prefixEnd_375713 : Nat := 4983230072969 + 3 ^ 40 * 375713 * 2
def baseEnd_375713 : Nat := 128614238095195836573089

theorem tailTrace_375713 : CollatzResearch.WordTrace tailWord_375713 prefixEnd_375713 128614238095195836573089 := by
  unfold tailWord_375713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13703378887863442516939793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9135585925242295011293195 13703378887863442516939793)
  ·
    refine ⟨10277534165897581887704845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13703378887863442516939793 10277534165897581887704845)
    ·
      refine ⟨3854075312211593207889317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10277534165897581887704845 3854075312211593207889317)
      ·
        refine ⟨722639121039673726479247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3854075312211593207889317 722639121039673726479247)
        ·
          refine ⟨1083958681559510589718871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722639121039673726479247 1083958681559510589718871)
          ·
            refine ⟨1625938022339265884578307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083958681559510589718871 1625938022339265884578307)
            ·
              refine ⟨2438907033508898826867461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625938022339265884578307 2438907033508898826867461)
              ·
                refine ⟨457295068782918530037649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2438907033508898826867461 457295068782918530037649)
                ·
                  refine ⟨342971301587188897528237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 457295068782918530037649 342971301587188897528237)
                  ·
                    refine ⟨128614238095195836573089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 342971301587188897528237 128614238095195836573089)
                    ·
                      rfl

theorem cell22_375713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_375713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375713 prefixEnd_375713 := by exact prefixLift 375713
  have htrace : WordTrace (prefixWord ++ tailWord_375713) baseStart_375713 baseEnd_375713 := by
    simpa [prefixWord, tailWord_375713, baseEnd_375713] using wordTrace_append hprefix tailTrace_375713
  have hstable : (prefixWord ++ tailWord_375713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375713).length < 2 ^ (prefixWord ++ tailWord_375713).sum := by decide
  have hdescent : baseEnd_375713 < baseStart_375713 := by decide
  rcases family_descends (prefixWord ++ tailWord_375713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375754 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_375754 : Nat := 118140960795 + 375754 * 2 ^ 59
def prefixEnd_375754 : Nat := 4983230072969 + 3 ^ 40 * 375754 * 2
def baseEnd_375754 : Nat := 42876091077695132099321

theorem tailTrace_375754 : CollatzResearch.WordTrace tailWord_375754 prefixEnd_375754 42876091077695132099321 := by
  unfold tailWord_375754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426218570178726629795579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9136582853809937679454877 3426218570178726629795579)
  ·
    refine ⟨5139327855268089944693369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426218570178726629795579 5139327855268089944693369)
    ·
      refine ⟨3854495891451067458520027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5139327855268089944693369 3854495891451067458520027)
      ·
        refine ⟨5781743837176601187780041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854495891451067458520027 5781743837176601187780041)
        ·
          refine ⟨4336307877882450890835031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5781743837176601187780041 4336307877882450890835031)
          ·
            refine ⟨6504461816823676336252547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4336307877882450890835031 6504461816823676336252547)
            ·
              refine ⟨9756692725235514504378821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6504461816823676336252547 9756692725235514504378821)
              ·
                refine ⟨1829379885981658969571029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9756692725235514504378821 1829379885981658969571029)
                ·
                  refine ⟨42876091077695132099321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1829379885981658969571029 42876091077695132099321)
                  ·
                    rfl

theorem cell22_375754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_375754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375754 prefixEnd_375754 := by exact prefixLift 375754
  have htrace : WordTrace (prefixWord ++ tailWord_375754) baseStart_375754 baseEnd_375754 := by
    simpa [prefixWord, tailWord_375754, baseEnd_375754] using wordTrace_append hprefix tailTrace_375754
  have hstable : (prefixWord ++ tailWord_375754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375754).length < 2 ^ (prefixWord ++ tailWord_375754).sum := by decide
  have hdescent : baseEnd_375754 < baseStart_375754 := by decide
  rcases family_descends (prefixWord ++ tailWord_375754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375786 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_375786 : Nat := 118140960795 + 375786 * 2 ^ 59
def prefixEnd_375786 : Nat := 4983230072969 + 3 ^ 40 * 375786 * 2
def baseEnd_375786 : Nat := 128639227487047979497865

theorem tailTrace_375786 : CollatzResearch.WordTrace tailWord_375786 prefixEnd_375786 128639227487047979497865 := by
  unfold tailWord_375786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426510354149743996086803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9137360944399317322898141 3426510354149743996086803)
  ·
    refine ⟨5139765531224615994130205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426510354149743996086803 5139765531224615994130205)
    ·
      refine ⟨1927412074209230997798827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5139765531224615994130205 1927412074209230997798827)
      ·
        refine ⟨2891118111313846496698241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1927412074209230997798827 2891118111313846496698241)
        ·
          refine ⟨2168338583485384872523681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2891118111313846496698241 2168338583485384872523681)
          ·
            refine ⟨1626253937614038654392761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2168338583485384872523681 1626253937614038654392761)
            ·
              refine ⟨1219690453210528990794571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626253937614038654392761 1219690453210528990794571)
              ·
                refine ⟨1829535679815793486191857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219690453210528990794571 1829535679815793486191857)
                ·
                  refine ⟨1372151759861845114643893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1829535679815793486191857 1372151759861845114643893)
                  ·
                    refine ⟨128639227487047979497865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1372151759861845114643893 128639227487047979497865)
                    ·
                      rfl

theorem cell22_375786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_375786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375786 prefixEnd_375786 := by exact prefixLift 375786
  have htrace : WordTrace (prefixWord ++ tailWord_375786) baseStart_375786 baseEnd_375786 := by
    simpa [prefixWord, tailWord_375786, baseEnd_375786] using wordTrace_append hprefix tailTrace_375786
  have hstable : (prefixWord ++ tailWord_375786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375786).length < 2 ^ (prefixWord ++ tailWord_375786).sum := by decide
  have hdescent : baseEnd_375786 < baseStart_375786 := by decide
  rcases family_descends (prefixWord ++ tailWord_375786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375818 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_375818 : Nat := 118140960795 + 375818 * 2 ^ 59
def prefixEnd_375818 : Nat := 4983230072969 + 3 ^ 40 * 375818 * 2
def baseEnd_375818 : Nat := 128650181741010562697767

theorem tailTrace_375818 : CollatzResearch.WordTrace tailWord_375818 prefixEnd_375818 128650181741010562697767 := by
  unfold tailWord_375818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426802138120761362378027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9138139034988696966341405 3426802138120761362378027)
  ·
    refine ⟨5140203207181142043567041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3426802138120761362378027 5140203207181142043567041)
    ·
      refine ⟨3855152405385856532675281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5140203207181142043567041 3855152405385856532675281)
      ·
        refine ⟨2891364304039392399506461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3855152405385856532675281 2891364304039392399506461)
        ·
          refine ⟨1084261614014772149814923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2891364304039392399506461 1084261614014772149814923)
          ·
            refine ⟨1626392421022158224722385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084261614014772149814923 1626392421022158224722385)
            ·
              refine ⟨1219794315766618668541789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1626392421022158224722385 1219794315766618668541789)
              ·
                refine ⟨457422868412482000703171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1219794315766618668541789 457422868412482000703171)
                ·
                  refine ⟨686134302618723001054757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457422868412482000703171 686134302618723001054757)
                  ·
                    refine ⟨128650181741010562697767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 686134302618723001054757 128650181741010562697767)
                    ·
                      rfl

theorem cell22_375818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_375818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375818 prefixEnd_375818 := by exact prefixLift 375818
  have htrace : WordTrace (prefixWord ++ tailWord_375818) baseStart_375818 baseEnd_375818 := by
    simpa [prefixWord, tailWord_375818, baseEnd_375818] using wordTrace_append hprefix tailTrace_375818
  have hstable : (prefixWord ++ tailWord_375818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375818).length < 2 ^ (prefixWord ++ tailWord_375818).sum := by decide
  have hdescent : baseEnd_375818 < baseStart_375818 := by decide
  rcases family_descends (prefixWord ++ tailWord_375818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
