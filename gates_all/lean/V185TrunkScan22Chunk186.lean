import V185TrunkScan22Chunk185

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1659073 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 5]
def baseStart_1659073 : Nat := 118140960795 + 1659073 * 2 ^ 59
def prefixEnd_1659073 : Nat := 4983230072969 + 3 ^ 40 * 1659073 * 2
def baseEnd_1659073 : Nat := 189311531088198356212793

theorem tailTrace_1659073 : CollatzResearch.WordTrace tailWord_1659073 prefixEnd_1659073 189311531088198356212793 := by
  unfold tailWord_1659073
  simp only [CollatzResearch.WordTrace]
  refine ⟨60511363518469342955093873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40340909012312895303395915 60511363518469342955093873)
  ·
    refine ⟨45383522638852007216320405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60511363518469342955093873 45383522638852007216320405)
    ·
      refine ⟨2127352623696187838265019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45383522638852007216320405 2127352623696187838265019)
      ·
        refine ⟨3191028935544281757397529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127352623696187838265019 3191028935544281757397529)
        ·
          refine ⟨2393271701658211318048147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3191028935544281757397529 2393271701658211318048147)
          ·
            refine ⟨3589907552487316977072221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393271701658211318048147 3589907552487316977072221)
            ·
              refine ⟨1346215332182743866402083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3589907552487316977072221 1346215332182743866402083)
              ·
                refine ⟨2019322998274115799603125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346215332182743866402083 2019322998274115799603125)
                ·
                  refine ⟨189311531088198356212793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2019322998274115799603125 189311531088198356212793)
                  ·
                    rfl

theorem cell22_1659073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_1659073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659073 prefixEnd_1659073 := by exact prefixLift 1659073
  have htrace : WordTrace (prefixWord ++ tailWord_1659073) baseStart_1659073 baseEnd_1659073 := by
    simpa [prefixWord, tailWord_1659073, baseEnd_1659073] using wordTrace_append hprefix tailTrace_1659073
  have hstable : (prefixWord ++ tailWord_1659073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659073).length < 2 ^ (prefixWord ++ tailWord_1659073).sum := by decide
  have hdescent : baseEnd_1659073 < baseStart_1659073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659086 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1659086 : Nat := 118140960795 + 1659086 * 2 ^ 59
def prefixEnd_1659086 : Nat := 4983230072969 + 3 ^ 40 * 1659086 * 2
def baseEnd_1659086 : Nat := 567939043430267368063339

theorem tailTrace_1659086 : CollatzResearch.WordTrace tailWord_1659086 prefixEnd_1659086 567939043430267368063339 := by
  unfold tailWord_1659086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563979708427780771914639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40341225111614830783544741 7563979708427780771914639)
  ·
    refine ⟨11345969562641671157871959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7563979708427780771914639 11345969562641671157871959)
    ·
      refine ⟨17018954343962506736807939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11345969562641671157871959 17018954343962506736807939)
      ·
        refine ⟨25528431515943760105211909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17018954343962506736807939 25528431515943760105211909)
        ·
          refine ⟨4786580909239455019727233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25528431515943760105211909 4786580909239455019727233)
          ·
            refine ⟨3589935681929591264795425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4786580909239455019727233 3589935681929591264795425)
            ·
              refine ⟨2692451761447193448596569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589935681929591264795425 2692451761447193448596569)
              ·
                refine ⟨2019338821085395086447427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692451761447193448596569 2019338821085395086447427)
                ·
                  refine ⟨3029008231628092629671141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019338821085395086447427 3029008231628092629671141)
                  ·
                    refine ⟨567939043430267368063339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029008231628092629671141 567939043430267368063339)
                    ·
                      rfl

theorem cell22_1659086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1659086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659086 prefixEnd_1659086 := by exact prefixLift 1659086
  have htrace : WordTrace (prefixWord ++ tailWord_1659086) baseStart_1659086 baseEnd_1659086 := by
    simpa [prefixWord, tailWord_1659086, baseEnd_1659086] using wordTrace_append hprefix tailTrace_1659086
  have hstable : (prefixWord ++ tailWord_1659086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659086).length < 2 ^ (prefixWord ++ tailWord_1659086).sum := by decide
  have hdescent : baseEnd_1659086 < baseStart_1659086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659097 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1659097 : Nat := 118140960795 + 1659097 * 2 ^ 59
def prefixEnd_1659097 : Nat := 4983230072969 + 3 ^ 40 * 1659097 * 2
def baseEnd_1659097 : Nat := 567942808955067006038305

theorem tailTrace_1659097 : CollatzResearch.WordTrace tailWord_1659097 prefixEnd_1659097 567942808955067006038305 := by
  unfold tailWord_1659097
  simp only [CollatzResearch.WordTrace]
  refine ⟨60512238870382395053967545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40341492580254930035978363 60512238870382395053967545)
  ·
    refine ⟨45384179152786796290475659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60512238870382395053967545 45384179152786796290475659)
    ·
      refine ⟨68076268729180194435713489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45384179152786796290475659 68076268729180194435713489)
      ·
        refine ⟨51057201546885145826785117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68076268729180194435713489 51057201546885145826785117)
        ·
          refine ⟨19146450580081929685044419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51057201546885145826785117 19146450580081929685044419)
          ·
            refine ⟨28719675870122894527566629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19146450580081929685044419 28719675870122894527566629)
            ·
              refine ⟨5384939225648042723918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28719675870122894527566629 5384939225648042723918743)
              ·
                refine ⟨8077408838472064085878115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384939225648042723918743 8077408838472064085878115)
                ·
                  refine ⟨12116113257708096128817173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8077408838472064085878115 12116113257708096128817173)
                  ·
                    refine ⟨567942808955067006038305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12116113257708096128817173 567942808955067006038305)
                    ·
                      rfl

theorem cell22_1659097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1659097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659097 prefixEnd_1659097 := by exact prefixLift 1659097
  have htrace : WordTrace (prefixWord ++ tailWord_1659097) baseStart_1659097 baseEnd_1659097 := by
    simpa [prefixWord, tailWord_1659097, baseEnd_1659097] using wordTrace_append hprefix tailTrace_1659097
  have hstable : (prefixWord ++ tailWord_1659097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659097).length < 2 ^ (prefixWord ++ tailWord_1659097).sum := by decide
  have hdescent : baseEnd_1659097 < baseStart_1659097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659112 : List Nat := [2, 1, 4, 1, 2, 2, 10]
def baseStart_1659112 : Nat := 118140960795 + 1659112 * 2 ^ 59
def prefixEnd_1659112 : Nat := 4983230072969 + 3 ^ 40 * 1659112 * 2
def baseEnd_1659112 : Nat := 21035109028207850626417

theorem tailTrace_1659112 : CollatzResearch.WordTrace tailWord_1659112 prefixEnd_1659112 21035109028207850626417 := by
  unfold tailWord_1659112
  simp only [CollatzResearch.WordTrace]
  refine ⟨30256392982664026307881795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40341857310218701743842393 30256392982664026307881795)
  ·
    refine ⟨45384589473996039461822693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30256392982664026307881795 45384589473996039461822693)
    ·
      refine ⟨8509610526374257399091755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45384589473996039461822693 8509610526374257399091755)
      ·
        refine ⟨12764415789561386098637633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509610526374257399091755 12764415789561386098637633)
        ·
          refine ⟨9573311842171039573978225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12764415789561386098637633 9573311842171039573978225)
          ·
            refine ⟨7179983881628279680483669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9573311842171039573978225 7179983881628279680483669)
            ·
              refine ⟨21035109028207850626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7179983881628279680483669 21035109028207850626417)
              ·
                rfl

theorem cell22_1659112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 10].length) (baseStart_1659112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659112 prefixEnd_1659112 := by exact prefixLift 1659112
  have htrace : WordTrace (prefixWord ++ tailWord_1659112) baseStart_1659112 baseEnd_1659112 := by
    simpa [prefixWord, tailWord_1659112, baseEnd_1659112] using wordTrace_append hprefix tailTrace_1659112
  have hstable : (prefixWord ++ tailWord_1659112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659112).length < 2 ^ (prefixWord ++ tailWord_1659112).sum := by decide
  have hdescent : baseEnd_1659112 < baseStart_1659112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659114 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1659114 : Nat := 118140960795 + 1659114 * 2 ^ 59
def prefixEnd_1659114 : Nat := 4983230072969 + 3 ^ 40 * 1659114 * 2
def baseEnd_1659114 : Nat := 567948628402484628363253

theorem tailTrace_1659114 : CollatzResearch.WordTrace tailWord_1659114 prefixEnd_1659114 567948628402484628363253 := by
  unfold tailWord_1659114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128214727830201739334099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40341905940880537971557597 15128214727830201739334099)
  ·
    refine ⟨22692322091745302609001149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15128214727830201739334099 22692322091745302609001149)
    ·
      refine ⟨8509620784404488478375431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22692322091745302609001149 8509620784404488478375431)
      ·
        refine ⟨12764431176606732717563147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509620784404488478375431 12764431176606732717563147)
        ·
          refine ⟨19146646764910099076344721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12764431176606732717563147 19146646764910099076344721)
          ·
            refine ⟨14359985073682574307258541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19146646764910099076344721 14359985073682574307258541)
            ·
              refine ⟨5384994402630965365221953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14359985073682574307258541 5384994402630965365221953)
              ·
                refine ⟨4038745801973224023916465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384994402630965365221953 4038745801973224023916465)
                ·
                  refine ⟨3029059351479918017937349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038745801973224023916465 3029059351479918017937349)
                  ·
                    refine ⟨567948628402484628363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029059351479918017937349 567948628402484628363253)
                    ·
                      rfl

theorem cell22_1659114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1659114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659114 prefixEnd_1659114 := by exact prefixLift 1659114
  have htrace : WordTrace (prefixWord ++ tailWord_1659114) baseStart_1659114 baseEnd_1659114 := by
    simpa [prefixWord, tailWord_1659114, baseEnd_1659114] using wordTrace_append hprefix tailTrace_1659114
  have hstable : (prefixWord ++ tailWord_1659114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659114).length < 2 ^ (prefixWord ++ tailWord_1659114).sum := by decide
  have hdescent : baseEnd_1659114 < baseStart_1659114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659157 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1659157 : Nat := 118140960795 + 1659157 * 2 ^ 59
def prefixEnd_1659157 : Nat := 4983230072969 + 3 ^ 40 * 1659157 * 2
def baseEnd_1659157 : Nat := 189321116060415616512707

theorem tailTrace_1659157 : CollatzResearch.WordTrace tailWord_1659157 prefixEnd_1659157 189321116060415616512707 := by
  unfold tailWord_1659157
  simp only [CollatzResearch.WordTrace]
  refine ⟨60514427250165025301151725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40342951500110016867434483 60514427250165025301151725)
  ·
    refine ⟨22692910218811884487931897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60514427250165025301151725 22692910218811884487931897)
    ·
      refine ⟨17019682664108913365948923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22692910218811884487931897 17019682664108913365948923)
      ·
        refine ⟨25529523996163370048923385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17019682664108913365948923 25529523996163370048923385)
        ·
          refine ⟨19147142997122527536692539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25529523996163370048923385 19147142997122527536692539)
          ·
            refine ⟨28720714495683791305038809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19147142997122527536692539 28720714495683791305038809)
            ·
              refine ⟨21540535871762843478779107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28720714495683791305038809 21540535871762843478779107)
              ·
                refine ⟨32310803807644265218168661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21540535871762843478779107 32310803807644265218168661)
                ·
                  refine ⟨189321116060415616512707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32310803807644265218168661 189321116060415616512707)
                  ·
                    rfl

theorem cell22_1659157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1659157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659157 prefixEnd_1659157 := by exact prefixLift 1659157
  have htrace : WordTrace (prefixWord ++ tailWord_1659157) baseStart_1659157 baseEnd_1659157 := by
    simpa [prefixWord, tailWord_1659157, baseEnd_1659157] using wordTrace_append hprefix tailTrace_1659157
  have hstable : (prefixWord ++ tailWord_1659157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659157).length < 2 ^ (prefixWord ++ tailWord_1659157).sum := by decide
  have hdescent : baseEnd_1659157 < baseStart_1659157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659189 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_1659189 : Nat := 118140960795 + 1659189 * 2 ^ 59
def prefixEnd_1659189 : Nat := 4983230072969 + 3 ^ 40 * 1659189 * 2
def baseEnd_1659189 : Nat := 567974302435209432738023

theorem tailTrace_1659189 : CollatzResearch.WordTrace tailWord_1659189 prefixEnd_1659189 567974302435209432738023 := by
  unfold tailWord_1659189
  simp only [CollatzResearch.WordTrace]
  refine ⟨60515594386049094766316621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40343729590699396510877747 60515594386049094766316621)
  ·
    refine ⟨22693347894768410537368733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60515594386049094766316621 22693347894768410537368733)
    ·
      refine ⟨8510005460538153951513275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22693347894768410537368733 8510005460538153951513275)
      ·
        refine ⟨12765008190807230927269913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8510005460538153951513275 12765008190807230927269913)
        ·
          refine ⟨9573756143105423195452435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12765008190807230927269913 9573756143105423195452435)
          ·
            refine ⟨14360634214658134793178653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573756143105423195452435 14360634214658134793178653)
            ·
              refine ⟨5385237830496800547441995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14360634214658134793178653 5385237830496800547441995)
              ·
                refine ⟨8077856745745200821162993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385237830496800547441995 8077856745745200821162993)
                ·
                  refine ⟨6058392559308900615872245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8077856745745200821162993 6058392559308900615872245)
                  ·
                    refine ⟨567974302435209432738023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6058392559308900615872245 567974302435209432738023)
                    ·
                      rfl

theorem cell22_1659189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_1659189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659189 prefixEnd_1659189 := by exact prefixLift 1659189
  have htrace : WordTrace (prefixWord ++ tailWord_1659189) baseStart_1659189 baseEnd_1659189 := by
    simpa [prefixWord, tailWord_1659189, baseEnd_1659189] using wordTrace_append hprefix tailTrace_1659189
  have hstable : (prefixWord ++ tailWord_1659189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659189).length < 2 ^ (prefixWord ++ tailWord_1659189).sum := by decide
  have hdescent : baseEnd_1659189 < baseStart_1659189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659236 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1659236 : Nat := 118140960795 + 1659236 * 2 ^ 59
def prefixEnd_1659236 : Nat := 4983230072969 + 3 ^ 40 * 1659236 * 2
def baseEnd_1659236 : Nat := 189330130498572325604293

theorem tailTrace_1659236 : CollatzResearch.WordTrace tailWord_1659236 prefixEnd_1659236 189330130498572325604293 := by
  unfold tailWord_1659236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30258654308439410896638781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40344872411252547862185041 30258654308439410896638781)
  ·
    refine ⟨11346995365664779086239543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30258654308439410896638781 11346995365664779086239543)
    ·
      refine ⟨17020493048497168629359315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11346995365664779086239543 17020493048497168629359315)
      ·
        refine ⟨25530739572745752944038973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17020493048497168629359315 25530739572745752944038973)
        ·
          refine ⟨9574027339779657354014615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25530739572745752944038973 9574027339779657354014615)
          ·
            refine ⟨14361041009669486031021923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574027339779657354014615 14361041009669486031021923)
            ·
              refine ⟨21541561514504229046532885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14361041009669486031021923 21541561514504229046532885)
              ·
                refine ⟨1009760695992385736556229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21541561514504229046532885 1009760695992385736556229)
                ·
                  refine ⟨189330130498572325604293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009760695992385736556229 189330130498572325604293)
                  ·
                    rfl

theorem cell22_1659236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1659236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659236 prefixEnd_1659236 := by exact prefixLift 1659236
  have htrace : WordTrace (prefixWord ++ tailWord_1659236) baseStart_1659236 baseEnd_1659236 := by
    simpa [prefixWord, tailWord_1659236, baseEnd_1659236] using wordTrace_append hprefix tailTrace_1659236
  have hstable : (prefixWord ++ tailWord_1659236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659236).length < 2 ^ (prefixWord ++ tailWord_1659236).sum := by decide
  have hdescent : baseEnd_1659236 < baseStart_1659236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659373 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1659373 : Nat := 118140960795 + 1659373 * 2 ^ 59
def prefixEnd_1659373 : Nat := 4983230072969 + 3 ^ 40 * 1659373 * 2
def baseEnd_1659373 : Nat := 568037289395494286137459

theorem tailTrace_1659373 : CollatzResearch.WordTrace tailWord_1659373 prefixEnd_1659373 568037289395494286137459 := by
  unfold tailWord_1659373
  simp only [CollatzResearch.WordTrace]
  refine ⟨60522305417382494191014773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40348203611588329460676515 60522305417382494191014773)
  ·
    refine ⟨5673966132879608830407635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60522305417382494191014773 5673966132879608830407635)
    ·
      refine ⟨8510949199319413245611453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5673966132879608830407635 8510949199319413245611453)
      ·
        refine ⟨3191605949744779967104295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8510949199319413245611453 3191605949744779967104295)
        ·
          refine ⟨4787408924617169950656443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191605949744779967104295 4787408924617169950656443)
          ·
            refine ⟨7181113386925754925984665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787408924617169950656443 7181113386925754925984665)
            ·
              refine ⟨5385835040194316194488499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7181113386925754925984665 5385835040194316194488499)
              ·
                refine ⟨8078752560291474291732749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385835040194316194488499 8078752560291474291732749)
                ·
                  refine ⟨3029532210109302859399781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8078752560291474291732749 3029532210109302859399781)
                  ·
                    refine ⟨568037289395494286137459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029532210109302859399781 568037289395494286137459)
                    ·
                      rfl

theorem cell22_1659373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1659373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659373 prefixEnd_1659373 := by exact prefixLift 1659373
  have htrace : WordTrace (prefixWord ++ tailWord_1659373) baseStart_1659373 baseEnd_1659373 := by
    simpa [prefixWord, tailWord_1659373, baseEnd_1659373] using wordTrace_append hprefix tailTrace_1659373
  have hstable : (prefixWord ++ tailWord_1659373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659373).length < 2 ^ (prefixWord ++ tailWord_1659373).sum := by decide
  have hdescent : baseEnd_1659373 < baseStart_1659373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659403 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 4, 3]
def baseStart_1659403 : Nat := 118140960795 + 1659403 * 2 ^ 59
def prefixEnd_1659403 : Nat := 4983230072969 + 3 ^ 40 * 1659403 * 2
def baseEnd_1659403 : Nat := 568047559008584207887367

theorem tailTrace_1659403 : CollatzResearch.WordTrace tailWord_1659403 prefixEnd_1659403 568047559008584207887367 := by
  unfold tailWord_1659403
  simp only [CollatzResearch.WordTrace]
  refine ⟨60523399607273809314606863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40348933071515872876404575 60523399607273809314606863)
  ·
    refine ⟨90785099410910713971910295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60523399607273809314606863 90785099410910713971910295)
    ·
      refine ⟨136177649116366070957865443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90785099410910713971910295 136177649116366070957865443)
      ·
        refine ⟨204266473674549106436798165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136177649116366070957865443 204266473674549106436798165)
        ·
          refine ⟨4787495476747244682112457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 204266473674549106436798165 4787495476747244682112457)
          ·
            refine ⟨3590621607560433511584343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787495476747244682112457 3590621607560433511584343)
            ·
              refine ⟨5385932411340650267376515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590621607560433511584343 5385932411340650267376515)
              ·
                refine ⟨8078898617010975401064773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385932411340650267376515 8078898617010975401064773)
                ·
                  refine ⟨1514793490689557887699645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8078898617010975401064773 1514793490689557887699645)
                  ·
                    refine ⟨568047559008584207887367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1514793490689557887699645 568047559008584207887367)
                    ·
                      rfl

theorem cell22_1659403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 3].length) (baseStart_1659403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659403 prefixEnd_1659403 := by exact prefixLift 1659403
  have htrace : WordTrace (prefixWord ++ tailWord_1659403) baseStart_1659403 baseEnd_1659403 := by
    simpa [prefixWord, tailWord_1659403, baseEnd_1659403] using wordTrace_append hprefix tailTrace_1659403
  have hstable : (prefixWord ++ tailWord_1659403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659403).length < 2 ^ (prefixWord ++ tailWord_1659403).sum := by decide
  have hdescent : baseEnd_1659403 < baseStart_1659403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659405 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1659405 : Nat := 118140960795 + 1659405 * 2 ^ 59
def prefixEnd_1659405 : Nat := 4983230072969 + 3 ^ 40 * 1659405 * 2
def baseEnd_1659405 : Nat := 189349414549818956445787

theorem tailTrace_1659405 : CollatzResearch.WordTrace tailWord_1659405 prefixEnd_1659405 189349414549818956445787 := by
  unfold tailWord_1659405
  simp only [CollatzResearch.WordTrace]
  refine ⟨60523472553266563656179669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40348981702177709104119779 60523472553266563656179669)
  ·
    refine ⟨1418518887967185085691711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 60523472553266563656179669 1418518887967185085691711)
    ·
      refine ⟨2127778331950777628537567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418518887967185085691711 2127778331950777628537567)
      ·
        refine ⟨3191667497926166442806351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127778331950777628537567 3191667497926166442806351)
        ·
          refine ⟨4787501246889249664209527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191667497926166442806351 4787501246889249664209527)
          ·
            refine ⟨7181251870333874496314291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787501246889249664209527 7181251870333874496314291)
            ·
              refine ⟨10771877805500811744471437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181251870333874496314291 10771877805500811744471437)
              ·
                refine ⟨4039454177062804404176789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10771877805500811744471437 4039454177062804404176789)
                ·
                  refine ⟨189349414549818956445787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039454177062804404176789 189349414549818956445787)
                  ·
                    rfl

theorem cell22_1659405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1659405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659405 prefixEnd_1659405 := by exact prefixLift 1659405
  have htrace : WordTrace (prefixWord ++ tailWord_1659405) baseStart_1659405 baseEnd_1659405 := by
    simpa [prefixWord, tailWord_1659405, baseEnd_1659405] using wordTrace_append hprefix tailTrace_1659405
  have hstable : (prefixWord ++ tailWord_1659405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659405).length < 2 ^ (prefixWord ++ tailWord_1659405).sum := by decide
  have hdescent : baseEnd_1659405 < baseStart_1659405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659461 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 7]
def baseStart_1659461 : Nat := 118140960795 + 1659461 * 2 ^ 59
def prefixEnd_1659461 : Nat := 4983230072969 + 3 ^ 40 * 1659461 * 2
def baseEnd_1659461 : Nat := 189355804531297129979063

theorem tailTrace_1659461 : CollatzResearch.WordTrace tailWord_1659461 prefixEnd_1659461 189355804531297129979063 := by
  unfold tailWord_1659461
  simp only [CollatzResearch.WordTrace]
  refine ⟨60525515041063685220218237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40350343360709123480145491 60525515041063685220218237)
  ·
    refine ⟨22697068140398881957581839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60525515041063685220218237 22697068140398881957581839)
    ·
      refine ⟨34045602210598322936372759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22697068140398881957581839 34045602210598322936372759)
      ·
        refine ⟨51068403315897484404559139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34045602210598322936372759 51068403315897484404559139)
        ·
          refine ⟨76602604973846226606838709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51068403315897484404559139 76602604973846226606838709)
          ·
            refine ⟨7181494216298083744391129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76602604973846226606838709 7181494216298083744391129)
            ·
              refine ⟨5386120662223562808293347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7181494216298083744391129 5386120662223562808293347)
              ·
                refine ⟨8079180993335344212440021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386120662223562808293347 8079180993335344212440021)
                ·
                  refine ⟨189355804531297129979063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8079180993335344212440021 189355804531297129979063)
                  ·
                    rfl

theorem cell22_1659461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_1659461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659461 prefixEnd_1659461 := by exact prefixLift 1659461
  have htrace : WordTrace (prefixWord ++ tailWord_1659461) baseStart_1659461 baseEnd_1659461 := by
    simpa [prefixWord, tailWord_1659461, baseEnd_1659461] using wordTrace_append hprefix tailTrace_1659461
  have hstable : (prefixWord ++ tailWord_1659461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659461).length < 2 ^ (prefixWord ++ tailWord_1659461).sum := by decide
  have hdescent : baseEnd_1659461 < baseStart_1659461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659540 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1659540 : Nat := 118140960795 + 1659540 * 2 ^ 59
def prefixEnd_1659540 : Nat := 4983230072969 + 3 ^ 40 * 1659540 * 2
def baseEnd_1659540 : Nat := 189364818969453839070649

theorem tailTrace_1659540 : CollatzResearch.WordTrace tailWord_1659540 prefixEnd_1659540 189364818969453839070649 := by
  unfold tailWord_1659540
  simp only [CollatzResearch.WordTrace]
  refine ⟨30264198203888740856172037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40352264271851654474896049 30264198203888740856172037)
  ·
    refine ⟨5674537163229138910532257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30264198203888740856172037 5674537163229138910532257)
    ·
      refine ⟨4255902872421854182899193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5674537163229138910532257 4255902872421854182899193)
      ·
        refine ⟨3191927154316390637174395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4255902872421854182899193 3191927154316390637174395)
        ·
          refine ⟨4787890731474585955761593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191927154316390637174395 4787890731474585955761593)
          ·
            refine ⟨3590918048605939466821195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787890731474585955761593 3590918048605939466821195)
            ·
              refine ⟨5386377072908909200231793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590918048605939466821195 5386377072908909200231793)
              ·
                refine ⟨4039782804681681900173845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386377072908909200231793 4039782804681681900173845)
                ·
                  refine ⟨189364818969453839070649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039782804681681900173845 189364818969453839070649)
                  ·
                    rfl

theorem cell22_1659540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1659540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659540 prefixEnd_1659540 := by exact prefixLift 1659540
  have htrace : WordTrace (prefixWord ++ tailWord_1659540) baseStart_1659540 baseEnd_1659540 := by
    simpa [prefixWord, tailWord_1659540, baseEnd_1659540] using wordTrace_append hprefix tailTrace_1659540
  have hstable : (prefixWord ++ tailWord_1659540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659540).length < 2 ^ (prefixWord ++ tailWord_1659540).sum := by decide
  have hdescent : baseEnd_1659540 < baseStart_1659540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659602 : List Nat := [3, 2, 2, 2, 3, 2, 2, 6]
def baseStart_1659602 : Nat := 118140960795 + 1659602 * 2 ^ 59
def prefixEnd_1659602 : Nat := 4983230072969 + 3 ^ 40 * 1659602 * 2
def baseEnd_1659602 : Nat := 63123964530601558017973

theorem tailTrace_1659602 : CollatzResearch.WordTrace tailWord_1659602 prefixEnd_1659602 63123964530601558017973 := by
  unfold tailWord_1659602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15132664433388216575275265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40353771822368577534067373 15132664433388216575275265)
  ·
    refine ⟨11349498325041162431456449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15132664433388216575275265 11349498325041162431456449)
    ·
      refine ⟨8512123743780871823592337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11349498325041162431456449 8512123743780871823592337)
      ·
        refine ⟨6384092807835653867694253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8512123743780871823592337 6384092807835653867694253)
        ·
          refine ⟨2394034802938370200385345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6384092807835653867694253 2394034802938370200385345)
          ·
            refine ⟨1795526102203777650289009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394034802938370200385345 1795526102203777650289009)
            ·
              refine ⟨1346644576652833237716757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795526102203777650289009 1346644576652833237716757)
              ·
                refine ⟨63123964530601558017973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1346644576652833237716757 63123964530601558017973)
                ·
                  rfl

theorem cell22_1659602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_1659602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659602 prefixEnd_1659602 := by exact prefixLift 1659602
  have htrace : WordTrace (prefixWord ++ tailWord_1659602) baseStart_1659602 baseEnd_1659602 := by
    simpa [prefixWord, tailWord_1659602, baseEnd_1659602] using wordTrace_append hprefix tailTrace_1659602
  have hstable : (prefixWord ++ tailWord_1659602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659602).length < 2 ^ (prefixWord ++ tailWord_1659602).sum := by decide
  have hdescent : baseEnd_1659602 < baseStart_1659602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659658 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_1659658 : Nat := 118140960795 + 1659658 * 2 ^ 59
def prefixEnd_1659658 : Nat := 4983230072969 + 3 ^ 40 * 1659658 * 2
def baseEnd_1659658 : Nat := 189378283573282847587195

theorem tailTrace_1659658 : CollatzResearch.WordTrace tailWord_1659658 prefixEnd_1659658 189378283573282847587195 := by
  unfold tailWord_1659658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133175055337496966284907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40355133480899991910093085 15133175055337496966284907)
  ·
    refine ⟨22699762583006245449427361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15133175055337496966284907 22699762583006245449427361)
    ·
      refine ⟨17024821937254684087070521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22699762583006245449427361 17024821937254684087070521)
      ·
        refine ⟨12768616452941013065302891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17024821937254684087070521 12768616452941013065302891)
        ·
          refine ⟨19152924679411519597954337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12768616452941013065302891 19152924679411519597954337)
          ·
            refine ⟨14364693509558639698465753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19152924679411519597954337 14364693509558639698465753)
            ·
              refine ⟨10773520132168979773849315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14364693509558639698465753 10773520132168979773849315)
              ·
                refine ⟨16160280198253469660773973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10773520132168979773849315 16160280198253469660773973)
                ·
                  refine ⟨189378283573282847587195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16160280198253469660773973 189378283573282847587195)
                  ·
                    rfl

theorem cell22_1659658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_1659658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659658 prefixEnd_1659658 := by exact prefixLift 1659658
  have htrace : WordTrace (prefixWord ++ tailWord_1659658) baseStart_1659658 baseEnd_1659658 := by
    simpa [prefixWord, tailWord_1659658, baseEnd_1659658] using wordTrace_append hprefix tailTrace_1659658
  have hstable : (prefixWord ++ tailWord_1659658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659658).length < 2 ^ (prefixWord ++ tailWord_1659658).sum := by decide
  have hdescent : baseEnd_1659658 < baseStart_1659658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659720 : List Nat := [2, 1, 3, 1, 1, 3, 5, 6]
def baseStart_1659720 : Nat := 118140960795 + 1659720 * 2 ^ 59
def prefixEnd_1659720 : Nat := 4983230072969 + 3 ^ 40 * 1659720 * 2
def baseEnd_1659720 : Nat := 63128452731877894190155

theorem tailTrace_1659720 : CollatzResearch.WordTrace tailWord_1659720 prefixEnd_1659720 63128452731877894190155 := by
  unfold tailWord_1659720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30267480773562686226948307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40356641031416914969264409 30267480773562686226948307)
  ·
    refine ⟨45401221160344029340422461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30267480773562686226948307 45401221160344029340422461)
    ·
      refine ⟨17025457935129011002658423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45401221160344029340422461 17025457935129011002658423)
      ·
        refine ⟨25538186902693516503987635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025457935129011002658423 25538186902693516503987635)
        ·
          refine ⟨38307280354040274755981453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25538186902693516503987635 38307280354040274755981453)
          ·
            refine ⟨14365230132765103033493045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38307280354040274755981453 14365230132765103033493045)
            ·
              refine ⟨1346740324946728409389973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14365230132765103033493045 1346740324946728409389973)
              ·
                refine ⟨63128452731877894190155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1346740324946728409389973 63128452731877894190155)
                ·
                  rfl

theorem cell22_1659720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_1659720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659720 prefixEnd_1659720 := by exact prefixLift 1659720
  have htrace : WordTrace (prefixWord ++ tailWord_1659720) baseStart_1659720 baseEnd_1659720 := by
    simpa [prefixWord, tailWord_1659720, baseEnd_1659720] using wordTrace_append hprefix tailTrace_1659720
  have hstable : (prefixWord ++ tailWord_1659720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659720).length < 2 ^ (prefixWord ++ tailWord_1659720).sum := by decide
  have hdescent : baseEnd_1659720 < baseStart_1659720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659752 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1659752 : Nat := 118140960795 + 1659752 * 2 ^ 59
def prefixEnd_1659752 : Nat := 4983230072969 + 3 ^ 40 * 1659752 * 2
def baseEnd_1659752 : Nat := 568167028840863630911297

theorem tailTrace_1659752 : CollatzResearch.WordTrace tailWord_1659752 prefixEnd_1659752 568167028840863630911297 := by
  unfold tailWord_1659752
  simp only [CollatzResearch.WordTrace]
  refine ⟨30268064341504720959530755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40357419122006294612707673 30268064341504720959530755)
  ·
    refine ⟨45402096512257081439296133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30268064341504720959530755 45402096512257081439296133)
    ·
      refine ⟨8512893096048202769868025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45402096512257081439296133 8512893096048202769868025)
      ·
        refine ⟨6384669822036152077401019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8512893096048202769868025 6384669822036152077401019)
        ·
          refine ⟨9577004733054228116101529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6384669822036152077401019 9577004733054228116101529)
          ·
            refine ⟨7182753549790671087076147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9577004733054228116101529 7182753549790671087076147)
            ·
              refine ⟨10774130324686006630614221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182753549790671087076147 10774130324686006630614221)
              ·
                refine ⟨4040298871757252486480333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10774130324686006630614221 4040298871757252486480333)
                ·
                  refine ⟨1515112076908969682430125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4040298871757252486480333 1515112076908969682430125)
                  ·
                    refine ⟨568167028840863630911297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515112076908969682430125 568167028840863630911297)
                    ·
                      rfl

theorem cell22_1659752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1659752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659752 prefixEnd_1659752 := by exact prefixLift 1659752
  have htrace : WordTrace (prefixWord ++ tailWord_1659752) baseStart_1659752 baseEnd_1659752 := by
    simpa [prefixWord, tailWord_1659752, baseEnd_1659752] using wordTrace_append hprefix tailTrace_1659752
  have hstable : (prefixWord ++ tailWord_1659752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659752).length < 2 ^ (prefixWord ++ tailWord_1659752).sum := by decide
  have hdescent : baseEnd_1659752 < baseStart_1659752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659786 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1659786 : Nat := 118140960795 + 1659786 * 2 ^ 59
def prefixEnd_1659786 : Nat := 4983230072969 + 3 ^ 40 * 1659786 * 2
def baseEnd_1659786 : Nat := 568178667735698875561193

theorem tailTrace_1659786 : CollatzResearch.WordTrace tailWord_1659786 prefixEnd_1659786 568178667735698875561193 := by
  unfold tailWord_1659786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134342191221566431449803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40358245843257510483866141 15134342191221566431449803)
  ·
    refine ⟨22701513286832349647174705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134342191221566431449803 22701513286832349647174705)
    ·
      refine ⟨17026134965124262235381029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22701513286832349647174705 17026134965124262235381029)
      ·
        refine ⟨3192400305960799169133943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17026134965124262235381029 3192400305960799169133943)
        ·
          refine ⟨4788600458941198753700915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192400305960799169133943 4788600458941198753700915)
          ·
            refine ⟨7182900688411798130551373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788600458941198753700915 7182900688411798130551373)
            ·
              refine ⟨2693587758154424298956765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7182900688411798130551373 2693587758154424298956765)
              ·
                refine ⟨1010095409307909112108787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2693587758154424298956765 1010095409307909112108787)
                ·
                  refine ⟨1515143113961863668163181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010095409307909112108787 1515143113961863668163181)
                  ·
                    refine ⟨568178667735698875561193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515143113961863668163181 568178667735698875561193)
                    ·
                      rfl

theorem cell22_1659786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1659786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659786 prefixEnd_1659786 := by exact prefixLift 1659786
  have htrace : WordTrace (prefixWord ++ tailWord_1659786) baseStart_1659786 baseEnd_1659786 := by
    simpa [prefixWord, tailWord_1659786, baseEnd_1659786] using wordTrace_append hprefix tailTrace_1659786
  have hstable : (prefixWord ++ tailWord_1659786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659786).length < 2 ^ (prefixWord ++ tailWord_1659786).sum := by decide
  have hdescent : baseEnd_1659786 < baseStart_1659786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659887 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 5, 3]
def baseStart_1659887 : Nat := 118140960795 + 1659887 * 2 ^ 59
def prefixEnd_1659887 : Nat := 4983230072969 + 3 ^ 40 * 1659887 * 2
def baseEnd_1659887 : Nat := 568213242099768278785883

theorem tailTrace_1659887 : CollatzResearch.WordTrace tailWord_1659887 prefixEnd_1659887 568213242099768278785883 := by
  unfold tailWord_1659887
  simp only [CollatzResearch.WordTrace]
  refine ⟨60541052537520359975225915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40360701691680239983483943 60541052537520359975225915)
  ·
    refine ⟨90811578806280539962838873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60541052537520359975225915 90811578806280539962838873)
    ·
      refine ⟨68108684104710404972129155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90811578806280539962838873 68108684104710404972129155)
      ·
        refine ⟨102163026157065607458193733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68108684104710404972129155 102163026157065607458193733)
        ·
          refine ⟨19155567404449801398411325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102163026157065607458193733 19155567404449801398411325)
          ·
            refine ⟨7183337776668675524404247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19155567404449801398411325 7183337776668675524404247)
            ·
              refine ⟨10775006665003013286606371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7183337776668675524404247 10775006665003013286606371)
              ·
                refine ⟨16162509997504519929909557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775006665003013286606371 16162509997504519929909557)
                ·
                  refine ⟨1515235312266048743429021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16162509997504519929909557 1515235312266048743429021)
                  ·
                    refine ⟨568213242099768278785883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515235312266048743429021 568213242099768278785883)
                    ·
                      rfl

theorem cell22_1659887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 3].length) (baseStart_1659887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659887 prefixEnd_1659887 := by exact prefixLift 1659887
  have htrace : WordTrace (prefixWord ++ tailWord_1659887) baseStart_1659887 baseEnd_1659887 := by
    simpa [prefixWord, tailWord_1659887, baseEnd_1659887] using wordTrace_append hprefix tailTrace_1659887
  have hstable : (prefixWord ++ tailWord_1659887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659887).length < 2 ^ (prefixWord ++ tailWord_1659887).sum := by decide
  have hdescent : baseEnd_1659887 < baseStart_1659887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659964 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1659964 : Nat := 118140960795 + 1659964 * 2 ^ 59
def prefixEnd_1659964 : Nat := 4983230072969 + 3 ^ 40 * 1659964 * 2
def baseEnd_1659964 : Nat := 568239600773365744610647

theorem tailTrace_1659964 : CollatzResearch.WordTrace tailWord_1659964 prefixEnd_1659964 568239600773365744610647 := by
  unfold tailWord_1659964
  simp only [CollatzResearch.WordTrace]
  refine ⟨30271930479120701062889473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40362573972160934750519297 30271930479120701062889473)
  ·
    refine ⟨22703947859340525797167105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30271930479120701062889473 22703947859340525797167105)
    ·
      refine ⟨17027960894505394347875329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22703947859340525797167105 17027960894505394347875329)
      ·
        refine ⟨12770970670879045760906497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17027960894505394347875329 12770970670879045760906497)
        ·
          refine ⟨9578228003159284320679873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12770970670879045760906497 9578228003159284320679873)
          ·
            refine ⟨7183671002369463240509905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9578228003159284320679873 7183671002369463240509905)
            ·
              refine ⟨5387753251777097430382429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183671002369463240509905 5387753251777097430382429)
              ·
                refine ⟨2020407469416411536393411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5387753251777097430382429 2020407469416411536393411)
                ·
                  refine ⟨3030611204124617304590117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020407469416411536393411 3030611204124617304590117)
                  ·
                    refine ⟨568239600773365744610647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030611204124617304590117 568239600773365744610647)
                    ·
                      rfl

theorem cell22_1659964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1659964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659964 prefixEnd_1659964 := by exact prefixLift 1659964
  have htrace : WordTrace (prefixWord ++ tailWord_1659964) baseStart_1659964 baseEnd_1659964 := by
    simpa [prefixWord, tailWord_1659964, baseEnd_1659964] using wordTrace_append hprefix tailTrace_1659964
  have hstable : (prefixWord ++ tailWord_1659964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659964).length < 2 ^ (prefixWord ++ tailWord_1659964).sum := by decide
  have hdescent : baseEnd_1659964 < baseStart_1659964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659992 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_1659992 : Nat := 118140960795 + 1659992 * 2 ^ 59
def prefixEnd_1659992 : Nat := 4983230072969 + 3 ^ 40 * 1659992 * 2
def baseEnd_1659992 : Nat := 568249185745583004910561

theorem tailTrace_1659992 : CollatzResearch.WordTrace tailWord_1659992 prefixEnd_1659992 568249185745583004910561 := by
  unfold tailWord_1659992
  simp only [CollatzResearch.WordTrace]
  refine ⟨30272441101069981453899115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40363254801426641938532153 30272441101069981453899115)
  ·
    refine ⟨45408661651604972180848673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30272441101069981453899115 45408661651604972180848673)
    ·
      refine ⟨34056496238703729135636505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45408661651604972180848673 34056496238703729135636505)
      ·
        refine ⟨25542372179027796851727379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34056496238703729135636505 25542372179027796851727379)
        ·
          refine ⟨38313558268541695277591069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25542372179027796851727379 38313558268541695277591069)
          ·
            refine ⟨14367584350703135729096651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38313558268541695277591069 14367584350703135729096651)
            ·
              refine ⟨21551376526054703593644977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14367584350703135729096651 21551376526054703593644977)
              ·
                refine ⟨16163532394541027695233733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21551376526054703593644977 16163532394541027695233733)
                ·
                  refine ⟨3030662323976442692856325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16163532394541027695233733 3030662323976442692856325)
                  ·
                    refine ⟨568249185745583004910561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030662323976442692856325 568249185745583004910561)
                    ·
                      rfl

theorem cell22_1659992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_1659992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659992 prefixEnd_1659992 := by exact prefixLift 1659992
  have htrace : WordTrace (prefixWord ++ tailWord_1659992) baseStart_1659992 baseEnd_1659992 := by
    simpa [prefixWord, tailWord_1659992, baseEnd_1659992] using wordTrace_append hprefix tailTrace_1659992
  have hstable : (prefixWord ++ tailWord_1659992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659992).length < 2 ^ (prefixWord ++ tailWord_1659992).sum := by decide
  have hdescent : baseEnd_1659992 < baseStart_1659992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1659998 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1659998 : Nat := 118140960795 + 1659998 * 2 ^ 59
def prefixEnd_1659998 : Nat := 4983230072969 + 3 ^ 40 * 1659998 * 2
def baseEnd_1659998 : Nat := 568251239668200989260543

theorem tailTrace_1659998 : CollatzResearch.WordTrace tailWord_1659998 prefixEnd_1659998 568251239668200989260543 := by
  unfold tailWord_1659998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568137630014778241564581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40363400693412150621677765 7568137630014778241564581)
  ·
    refine ⟨1419025805627770920293359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7568137630014778241564581 1419025805627770920293359)
    ·
      refine ⟨2128538708441656380440039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419025805627770920293359 2128538708441656380440039)
      ·
        refine ⟨3192808062662484570660059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128538708441656380440039 3192808062662484570660059)
        ·
          refine ⟨4789212093993726855990089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192808062662484570660059 4789212093993726855990089)
          ·
            refine ⟨3591909070495295141992567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789212093993726855990089 3591909070495295141992567)
            ·
              refine ⟨5387863605742942712988851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591909070495295141992567 5387863605742942712988851)
              ·
                refine ⟨8081795408614414069483277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387863605742942712988851 8081795408614414069483277)
                ·
                  refine ⟨3030673278230405276056229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8081795408614414069483277 3030673278230405276056229)
                  ·
                    refine ⟨568251239668200989260543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030673278230405276056229 568251239668200989260543)
                    ·
                      rfl

theorem cell22_1659998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1659998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1659998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1659998 prefixEnd_1659998 := by exact prefixLift 1659998
  have htrace : WordTrace (prefixWord ++ tailWord_1659998) baseStart_1659998 baseEnd_1659998 := by
    simpa [prefixWord, tailWord_1659998, baseEnd_1659998] using wordTrace_append hprefix tailTrace_1659998
  have hstable : (prefixWord ++ tailWord_1659998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1659998).length < 2 ^ (prefixWord ++ tailWord_1659998).sum := by decide
  have hdescent : baseEnd_1659998 < baseStart_1659998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1659998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660007 : List Nat := [1, 1, 5, 1, 1, 3, 2, 8]
def baseStart_1660007 : Nat := 118140960795 + 1660007 * 2 ^ 59
def prefixEnd_1660007 : Nat := 4983230072969 + 3 ^ 40 * 1660007 * 2
def baseEnd_1660007 : Nat := 63139368950236440642835

theorem tailTrace_1660007 : CollatzResearch.WordTrace tailWord_1660007 prefixEnd_1660007 63139368950236440642835 := by
  unfold tailWord_1660007
  simp only [CollatzResearch.WordTrace]
  refine ⟨60545429297085620469594275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40363619531390413646396183 60545429297085620469594275)
  ·
    refine ⟨90818143945628430704391413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60545429297085620469594275 90818143945628430704391413)
    ·
      refine ⟨8514200994902665378536695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90818143945628430704391413 8514200994902665378536695)
      ·
        refine ⟨12771301492353998067805043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8514200994902665378536695 12771301492353998067805043)
        ·
          refine ⟨19156952238530997101707565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771301492353998067805043 19156952238530997101707565)
          ·
            refine ⟨7183857089449123913140337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19156952238530997101707565 7183857089449123913140337)
            ·
              refine ⟨5387892817086842934855253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183857089449123913140337 5387892817086842934855253)
              ·
                refine ⟨63139368950236440642835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5387892817086842934855253 63139368950236440642835)
                ·
                  rfl

theorem cell22_1660007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 8].length) (baseStart_1660007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660007 prefixEnd_1660007 := by exact prefixLift 1660007
  have htrace : WordTrace (prefixWord ++ tailWord_1660007) baseStart_1660007 baseEnd_1660007 := by
    simpa [prefixWord, tailWord_1660007, baseEnd_1660007] using wordTrace_append hprefix tailTrace_1660007
  have hstable : (prefixWord ++ tailWord_1660007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660007).length < 2 ^ (prefixWord ++ tailWord_1660007).sum := by decide
  have hdescent : baseEnd_1660007 < baseStart_1660007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660009 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_1660009 : Nat := 118140960795 + 1660009 * 2 ^ 59
def prefixEnd_1660009 : Nat := 4983230072969 + 3 ^ 40 * 1660009 * 2
def baseEnd_1660009 : Nat := 568255005193000627235509

theorem tailTrace_1660009 : CollatzResearch.WordTrace tailWord_1660009 prefixEnd_1660009 568255005193000627235509 := by
  unfold tailWord_1660009
  simp only [CollatzResearch.WordTrace]
  refine ⟨60545502243078374811167081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40363668162052249874111387 60545502243078374811167081)
  ·
    refine ⟨45409126682308781108375311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60545502243078374811167081 45409126682308781108375311)
    ·
      refine ⟨68113690023463171662562967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45409126682308781108375311 68113690023463171662562967)
      ·
        refine ⟨102170535035194757493844451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68113690023463171662562967 102170535035194757493844451)
        ·
          refine ⟨153255802552792136240766677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102170535035194757493844451 153255802552792136240766677)
          ·
            refine ⟨3591932872331065693142969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 153255802552792136240766677 3591932872331065693142969)
            ·
              refine ⟨2693949654248299269857227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3591932872331065693142969 2693949654248299269857227)
              ·
                refine ⟨4040924481372448904785841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693949654248299269857227 4040924481372448904785841)
                ·
                  refine ⟨3030693361029336678589381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040924481372448904785841 3030693361029336678589381)
                  ·
                    refine ⟨568255005193000627235509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030693361029336678589381 568255005193000627235509)
                    ·
                      rfl

theorem cell22_1660009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_1660009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660009 prefixEnd_1660009 := by exact prefixLift 1660009
  have htrace : WordTrace (prefixWord ++ tailWord_1660009) baseStart_1660009 baseEnd_1660009 := by
    simpa [prefixWord, tailWord_1660009, baseEnd_1660009] using wordTrace_append hprefix tailTrace_1660009
  have hstable : (prefixWord ++ tailWord_1660009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660009).length < 2 ^ (prefixWord ++ tailWord_1660009).sum := by decide
  have hdescent : baseEnd_1660009 < baseStart_1660009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660039 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1660039 : Nat := 118140960795 + 1660039 * 2 ^ 59
def prefixEnd_1660039 : Nat := 4983230072969 + 3 ^ 40 * 1660039 * 2
def baseEnd_1660039 : Nat := 568265274806090548985417

theorem tailTrace_1660039 : CollatzResearch.WordTrace tailWord_1660039 prefixEnd_1660039 568265274806090548985417 := by
  unfold tailWord_1660039
  simp only [CollatzResearch.WordTrace]
  refine ⟨60546596432969689934759171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40364397621979793289839447 60546596432969689934759171)
  ·
    refine ⟨90819894649454534902138757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60546596432969689934759171 90819894649454534902138757)
    ·
      refine ⟨17028730246772725294151017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90819894649454534902138757 17028730246772725294151017)
      ·
        refine ⟨12771547685079543970613263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17028730246772725294151017 12771547685079543970613263)
        ·
          refine ⟨19157321527619315955919895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12771547685079543970613263 19157321527619315955919895)
          ·
            refine ⟨28735982291428973933879843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19157321527619315955919895 28735982291428973933879843)
            ·
              refine ⟨43103973437143460900819765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28735982291428973933879843 43103973437143460900819765)
              ·
                refine ⟨4040997509732199459451853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43103973437143460900819765 4040997509732199459451853)
                ·
                  refine ⟨1515374066149574797294445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4040997509732199459451853 1515374066149574797294445)
                  ·
                    refine ⟨568265274806090548985417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515374066149574797294445 568265274806090548985417)
                    ·
                      rfl

theorem cell22_1660039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1660039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660039 prefixEnd_1660039 := by exact prefixLift 1660039
  have htrace : WordTrace (prefixWord ++ tailWord_1660039) baseStart_1660039 baseEnd_1660039 := by
    simpa [prefixWord, tailWord_1660039, baseEnd_1660039] using wordTrace_append hprefix tailTrace_1660039
  have hstable : (prefixWord ++ tailWord_1660039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660039).length < 2 ^ (prefixWord ++ tailWord_1660039).sum := by decide
  have hdescent : baseEnd_1660039 < baseStart_1660039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660056 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_1660056 : Nat := 118140960795 + 1660056 * 2 ^ 59
def prefixEnd_1660056 : Nat := 4983230072969 + 3 ^ 40 * 1660056 * 2
def baseEnd_1660056 : Nat := 568271094253508171310365

theorem tailTrace_1660056 : CollatzResearch.WordTrace tailWord_1660056 prefixEnd_1660056 568271094253508171310365 := by
  unfold tailWord_1660056
  simp only [CollatzResearch.WordTrace]
  refine ⟨30273608236954050919064011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40364810982605401225418681 30273608236954050919064011)
  ·
    refine ⟨45410412355431076378596017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30273608236954050919064011 45410412355431076378596017)
    ·
      refine ⟨34057809266573307283947013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45410412355431076378596017 34057809266573307283947013)
      ·
        refine ⟨6385839237482495115740065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34057809266573307283947013 6385839237482495115740065)
        ·
          refine ⟨4789379428111871336805049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6385839237482495115740065 4789379428111871336805049)
          ·
            refine ⟨3592034571083903502603787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789379428111871336805049 3592034571083903502603787)
            ·
              refine ⟨5388051856625855253905681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592034571083903502603787 5388051856625855253905681)
              ·
                refine ⟨4041038892469391440429261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388051856625855253905681 4041038892469391440429261)
                ·
                  refine ⟨1515389584676021790160973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4041038892469391440429261 1515389584676021790160973)
                  ·
                    refine ⟨568271094253508171310365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515389584676021790160973 568271094253508171310365)
                    ·
                      rfl

theorem cell22_1660056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_1660056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660056 prefixEnd_1660056 := by exact prefixLift 1660056
  have htrace : WordTrace (prefixWord ++ tailWord_1660056) baseStart_1660056 baseEnd_1660056 := by
    simpa [prefixWord, tailWord_1660056, baseEnd_1660056] using wordTrace_append hprefix tailTrace_1660056
  have hstable : (prefixWord ++ tailWord_1660056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660056).length < 2 ^ (prefixWord ++ tailWord_1660056).sum := by decide
  have hdescent : baseEnd_1660056 < baseStart_1660056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660114 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1660114 : Nat := 118140960795 + 1660114 * 2 ^ 59
def prefixEnd_1660114 : Nat := 4983230072969 + 3 ^ 40 * 1660114 * 2
def baseEnd_1660114 : Nat := 189430316279605117786729

theorem tailTrace_1660114 : CollatzResearch.WordTrace tailWord_1660114 prefixEnd_1660114 189430316279605117786729 := by
  unfold tailWord_1660114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15137332976924494435934849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40366221271798651829159597 15137332976924494435934849)
  ·
    refine ⟨11352999732693370826951137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15137332976924494435934849 11352999732693370826951137)
    ·
      refine ⟨8514749799520028120213353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11352999732693370826951137 8514749799520028120213353)
      ·
        refine ⟨6386062349640021090160015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8514749799520028120213353 6386062349640021090160015)
        ·
          refine ⟨9579093524460031635240023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386062349640021090160015 9579093524460031635240023)
          ·
            refine ⟨14368640286690047452860035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579093524460031635240023 14368640286690047452860035)
            ·
              refine ⟨21552960430035071179290053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14368640286690047452860035 21552960430035071179290053)
              ·
                refine ⟨4041180080631575846116885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21552960430035071179290053 4041180080631575846116885)
                ·
                  refine ⟨189430316279605117786729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4041180080631575846116885 189430316279605117786729)
                  ·
                    rfl

theorem cell22_1660114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1660114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660114 prefixEnd_1660114 := by exact prefixLift 1660114
  have htrace : WordTrace (prefixWord ++ tailWord_1660114) baseStart_1660114 baseEnd_1660114 := by
    simpa [prefixWord, tailWord_1660114, baseEnd_1660114] using wordTrace_append hprefix tailTrace_1660114
  have hstable : (prefixWord ++ tailWord_1660114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660114).length < 2 ^ (prefixWord ++ tailWord_1660114).sum := by decide
  have hdescent : baseEnd_1660114 < baseStart_1660114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660159 : List Nat := [1, 1, 2, 2, 1, 6, 2, 7]
def baseStart_1660159 : Nat := 118140960795 + 1660159 * 2 ^ 59
def prefixEnd_1660159 : Nat := 4983230072969 + 3 ^ 40 * 1660159 * 2
def baseEnd_1660159 : Nat := 63145150362050026220561

theorem tailTrace_1660159 : CollatzResearch.WordTrace tailWord_1660159 prefixEnd_1660159 63145150362050026220561 := by
  unfold tailWord_1660159
  simp only [CollatzResearch.WordTrace]
  refine ⟨60550973192534950429127531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40367315461689966952751687 60550973192534950429127531)
  ·
    refine ⟨90826459788802425643691297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60550973192534950429127531 90826459788802425643691297)
    ·
      refine ⟨68119844841601819232768473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90826459788802425643691297 68119844841601819232768473)
      ·
        refine ⟨51089883631201364424576355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68119844841601819232768473 51089883631201364424576355)
        ·
          refine ⟨76634825446802046636864533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51089883631201364424576355 76634825446802046636864533)
          ·
            refine ⟨3592257442818845936103025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76634825446802046636864533 3592257442818845936103025)
            ·
              refine ⟨2694193082114134452077269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3592257442818845936103025 2694193082114134452077269)
              ·
                refine ⟨63145150362050026220561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2694193082114134452077269 63145150362050026220561)
                ·
                  rfl

theorem cell22_1660159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 7].length) (baseStart_1660159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660159 prefixEnd_1660159 := by exact prefixLift 1660159
  have htrace : WordTrace (prefixWord ++ tailWord_1660159) baseStart_1660159 baseEnd_1660159 := by
    simpa [prefixWord, tailWord_1660159, baseEnd_1660159] using wordTrace_append hprefix tailTrace_1660159
  have hstable : (prefixWord ++ tailWord_1660159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660159).length < 2 ^ (prefixWord ++ tailWord_1660159).sum := by decide
  have hdescent : baseEnd_1660159 < baseStart_1660159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660163 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 2, 3]
def baseStart_1660163 : Nat := 118140960795 + 1660163 * 2 ^ 59
def prefixEnd_1660163 : Nat := 4983230072969 + 3 ^ 40 * 1660163 * 2
def baseEnd_1660163 : Nat := 568307722540195558885037

theorem tailTrace_1660163 : CollatzResearch.WordTrace tailWord_1660163 prefixEnd_1660163 568307722540195558885037 := by
  unfold tailWord_1660163
  simp only [CollatzResearch.WordTrace]
  refine ⟨60551119084520459112273143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40367412723013639408182095 60551119084520459112273143)
  ·
    refine ⟨90826678626780688668409715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60551119084520459112273143 90826678626780688668409715)
    ·
      refine ⟨136240017940171033002614573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90826678626780688668409715 136240017940171033002614573)
      ·
        refine ⟨51090006727564137375980465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136240017940171033002614573 51090006727564137375980465)
        ·
          refine ⟨38317505045673103031985349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51090006727564137375980465 38317505045673103031985349)
          ·
            refine ⟨7184532196063706818497253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38317505045673103031985349 7184532196063706818497253)
            ·
              refine ⟨1347099786761945028468235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7184532196063706818497253 1347099786761945028468235)
              ·
                refine ⟨2020649680142917542702353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347099786761945028468235 2020649680142917542702353)
                ·
                  refine ⟨1515487260107188157026765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2020649680142917542702353 1515487260107188157026765)
                  ·
                    refine ⟨568307722540195558885037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515487260107188157026765 568307722540195558885037)
                    ·
                      rfl

theorem cell22_1660163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 3].length) (baseStart_1660163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660163 prefixEnd_1660163 := by exact prefixLift 1660163
  have htrace : WordTrace (prefixWord ++ tailWord_1660163) baseStart_1660163 baseEnd_1660163 := by
    simpa [prefixWord, tailWord_1660163, baseEnd_1660163] using wordTrace_append hprefix tailTrace_1660163
  have hstable : (prefixWord ++ tailWord_1660163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660163).length < 2 ^ (prefixWord ++ tailWord_1660163).sum := by decide
  have hdescent : baseEnd_1660163 < baseStart_1660163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660208 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 1, 3]
def baseStart_1660208 : Nat := 118140960795 + 1660208 * 2 ^ 59
def prefixEnd_1660208 : Nat := 4983230072969 + 3 ^ 40 * 1660208 * 2
def baseEnd_1660208 : Nat := 568323126959830441509899

theorem tailTrace_1660208 : CollatzResearch.WordTrace tailWord_1660208 prefixEnd_1660208 568323126959830441509899 := by
  unfold tailWord_1660208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30276380184678715898830639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40368506912904954531774185 30276380184678715898830639)
  ·
    refine ⟨45414570277018073848245959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30276380184678715898830639 45414570277018073848245959)
    ·
      refine ⟨68121855415527110772368939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45414570277018073848245959 68121855415527110772368939)
      ·
        refine ⟨102182783123290666158553409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68121855415527110772368939 102182783123290666158553409)
        ·
          refine ⟨76637087342467999618915057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102182783123290666158553409 76637087342467999618915057)
          ·
            refine ⟨57477815506850999714186293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76637087342467999618915057 57477815506850999714186293)
            ·
              refine ⟨5388545203767281223204965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57477815506850999714186293 5388545203767281223204965)
              ·
                refine ⟨1010352225706365229350931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5388545203767281223204965 1010352225706365229350931)
                ·
                  refine ⟨1515528338559547844026397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010352225706365229350931 1515528338559547844026397)
                  ·
                    refine ⟨568323126959830441509899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515528338559547844026397 568323126959830441509899)
                    ·
                      rfl

theorem cell22_1660208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_1660208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660208 prefixEnd_1660208 := by exact prefixLift 1660208
  have htrace : WordTrace (prefixWord ++ tailWord_1660208) baseStart_1660208 baseEnd_1660208 := by
    simpa [prefixWord, tailWord_1660208, baseEnd_1660208] using wordTrace_append hprefix tailTrace_1660208
  have hstable : (prefixWord ++ tailWord_1660208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660208).length < 2 ^ (prefixWord ++ tailWord_1660208).sum := by decide
  have hdescent : baseEnd_1660208 < baseStart_1660208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660279 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1660279 : Nat := 118140960795 + 1660279 * 2 ^ 59
def prefixEnd_1660279 : Nat := 4983230072969 + 3 ^ 40 * 1660279 * 2
def baseEnd_1660279 : Nat := 568347431710809922984681

theorem tailTrace_1660279 : CollatzResearch.WordTrace tailWord_1660279 prefixEnd_1660279 568347431710809922984681 := by
  unfold tailWord_1660279
  simp only [CollatzResearch.WordTrace]
  refine ⟨60555349952100210923495891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40370233301400140615663927 60555349952100210923495891)
  ·
    refine ⟨90833024928150316385243837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60555349952100210923495891 90833024928150316385243837)
    ·
      refine ⟨34062384348056368644466439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90833024928150316385243837 34062384348056368644466439)
      ·
        refine ⟨51093576522084552966699659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34062384348056368644466439 51093576522084552966699659)
        ·
          refine ⟨76640364783126829450049489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51093576522084552966699659 76640364783126829450049489)
          ·
            refine ⟨57480273587345122087537117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76640364783126829450049489 57480273587345122087537117)
            ·
              refine ⟨21555102595254420782826419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57480273587345122087537117 21555102595254420782826419)
              ·
                refine ⟨32332653892881631174239629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21555102595254420782826419 32332653892881631174239629)
                ·
                  refine ⟨12124745209830611690339861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32332653892881631174239629 12124745209830611690339861)
                  ·
                    refine ⟨568347431710809922984681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12124745209830611690339861 568347431710809922984681)
                    ·
                      rfl

theorem cell22_1660279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1660279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660279 prefixEnd_1660279 := by exact prefixLift 1660279
  have htrace : WordTrace (prefixWord ++ tailWord_1660279) baseStart_1660279 baseEnd_1660279 := by
    simpa [prefixWord, tailWord_1660279, baseEnd_1660279] using wordTrace_append hprefix tailTrace_1660279
  have hstable : (prefixWord ++ tailWord_1660279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660279).length < 2 ^ (prefixWord ++ tailWord_1660279).sum := by decide
  have hdescent : baseEnd_1660279 < baseStart_1660279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660281 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_1660281 : Nat := 118140960795 + 1660281 * 2 ^ 59
def prefixEnd_1660281 : Nat := 4983230072969 + 3 ^ 40 * 1660281 * 2
def baseEnd_1660281 : Nat := 568348116351682584434675

theorem tailTrace_1660281 : CollatzResearch.WordTrace tailWord_1660281 prefixEnd_1660281 568348116351682584434675 := by
  unfold tailWord_1660281
  simp only [CollatzResearch.WordTrace]
  refine ⟨60555422898092965265068697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40370281932061976843379131 60555422898092965265068697)
  ·
    refine ⟨45416567173569723948801523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60555422898092965265068697 45416567173569723948801523)
    ·
      refine ⟨68124850760354585923202285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45416567173569723948801523 68124850760354585923202285)
      ·
        refine ⟨25546819035132969721200857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68124850760354585923202285 25546819035132969721200857)
        ·
          refine ⟨19160114276349727290900643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25546819035132969721200857 19160114276349727290900643)
          ·
            refine ⟨28740171414524590936350965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19160114276349727290900643 28740171414524590936350965)
            ·
              refine ⟨2694391070111680400282903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28740171414524590936350965 2694391070111680400282903)
              ·
                refine ⟨4041586605167520600424355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694391070111680400282903 4041586605167520600424355)
                ·
                  refine ⟨6062379907751280900636533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041586605167520600424355 6062379907751280900636533)
                  ·
                    refine ⟨568348116351682584434675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6062379907751280900636533 568348116351682584434675)
                    ·
                      rfl

theorem cell22_1660281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_1660281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660281 prefixEnd_1660281 := by exact prefixLift 1660281
  have htrace : WordTrace (prefixWord ++ tailWord_1660281) baseStart_1660281 baseEnd_1660281 := by
    simpa [prefixWord, tailWord_1660281, baseEnd_1660281] using wordTrace_append hprefix tailTrace_1660281
  have hstable : (prefixWord ++ tailWord_1660281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660281).length < 2 ^ (prefixWord ++ tailWord_1660281).sum := by decide
  have hdescent : baseEnd_1660281 < baseStart_1660281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660296 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1660296 : Nat := 118140960795 + 1660296 * 2 ^ 59
def prefixEnd_1660296 : Nat := 4983230072969 + 3 ^ 40 * 1660296 * 2
def baseEnd_1660296 : Nat := 568353251158227545309629

theorem tailTrace_1660296 : CollatzResearch.WordTrace tailWord_1660296 prefixEnd_1660296 568353251158227545309629 := by
  unfold tailWord_1660296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30277984996519311413432371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40370646662025748551243161 30277984996519311413432371)
  ·
    refine ⟨45416977494778967120148557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30277984996519311413432371 45416977494778967120148557)
    ·
      refine ⟨17031366560542112670055709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45416977494778967120148557 17031366560542112670055709)
      ·
        refine ⟨6386762460203292251270891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17031366560542112670055709 6386762460203292251270891)
        ·
          refine ⟨9580143690304938376906337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386762460203292251270891 9580143690304938376906337)
          ·
            refine ⟨7185107767728703782679753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580143690304938376906337 7185107767728703782679753)
            ·
              refine ⟨5388830825796527837009815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185107767728703782679753 5388830825796527837009815)
              ·
                refine ⟨8083246238694791755514723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388830825796527837009815 8083246238694791755514723)
                ·
                  refine ⟨12124869358042187633272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083246238694791755514723 12124869358042187633272085)
                  ·
                    refine ⟨568353251158227545309629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12124869358042187633272085 568353251158227545309629)
                    ·
                      rfl

theorem cell22_1660296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1660296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660296 prefixEnd_1660296 := by exact prefixLift 1660296
  have htrace : WordTrace (prefixWord ++ tailWord_1660296) baseStart_1660296 baseEnd_1660296 := by
    simpa [prefixWord, tailWord_1660296, baseEnd_1660296] using wordTrace_append hprefix tailTrace_1660296
  have hstable : (prefixWord ++ tailWord_1660296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660296).length < 2 ^ (prefixWord ++ tailWord_1660296).sum := by decide
  have hdescent : baseEnd_1660296 < baseStart_1660296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660360 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 1, 3]
def baseStart_1660360 : Nat := 118140960795 + 1660360 * 2 ^ 59
def prefixEnd_1660360 : Nat := 4983230072969 + 3 ^ 40 * 1660360 * 2
def baseEnd_1660360 : Nat := 568375159666152711709433

theorem tailTrace_1660360 : CollatzResearch.WordTrace tailWord_1660360 prefixEnd_1660360 568375159666152711709433 := by
  unfold tailWord_1660360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30279152132403380878597267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40372202843204507838129689 30279152132403380878597267)
  ·
    refine ⟨45418728198605071317895901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30279152132403380878597267 45418728198605071317895901)
    ·
      refine ⟨17032023074476901744210963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45418728198605071317895901 17032023074476901744210963)
      ·
        refine ⟨25548034611715352616316445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17032023074476901744210963 25548034611715352616316445)
        ·
          refine ⟨9580512979393257231118667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25548034611715352616316445 9580512979393257231118667)
          ·
            refine ⟨14370769469089885846678001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580512979393257231118667 14370769469089885846678001)
            ·
              refine ⟨10778077101817414385008501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14370769469089885846678001 10778077101817414385008501)
              ·
                refine ⟨1010444728295382598594547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10778077101817414385008501 1010444728295382598594547)
                ·
                  refine ⟨1515667092443073897891821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010444728295382598594547 1515667092443073897891821)
                  ·
                    refine ⟨568375159666152711709433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515667092443073897891821 568375159666152711709433)
                    ·
                      rfl

theorem cell22_1660360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_1660360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660360 prefixEnd_1660360 := by exact prefixLift 1660360
  have htrace : WordTrace (prefixWord ++ tailWord_1660360) baseStart_1660360 baseEnd_1660360 := by
    simpa [prefixWord, tailWord_1660360, baseEnd_1660360] using wordTrace_append hprefix tailTrace_1660360
  have hstable : (prefixWord ++ tailWord_1660360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660360).length < 2 ^ (prefixWord ++ tailWord_1660360).sum := by decide
  have hdescent : baseEnd_1660360 < baseStart_1660360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660373 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 5]
def baseStart_1660373 : Nat := 118140960795 + 1660373 * 2 ^ 59
def prefixEnd_1660373 : Nat := 4983230072969 + 3 ^ 40 * 1660373 * 2
def baseEnd_1660373 : Nat := 189459869943941670378131

theorem tailTrace_1660373 : CollatzResearch.WordTrace tailWord_1660373 prefixEnd_1660373 189459869943941670378131 := by
  unfold tailWord_1660373
  simp only [CollatzResearch.WordTrace]
  refine ⟨60558778413759664977417773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40372518942506443318278515 60558778413759664977417773)
  ·
    refine ⟨22709541905159874366531665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60558778413759664977417773 22709541905159874366531665)
    ·
      refine ⟨17032156428869905774898749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22709541905159874366531665 17032156428869905774898749)
      ·
        refine ⟨6387058660826214665587031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17032156428869905774898749 6387058660826214665587031)
        ·
          refine ⟨9580587991239321998380547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387058660826214665587031 9580587991239321998380547)
          ·
            refine ⟨14370881986858982997570821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580587991239321998380547 14370881986858982997570821)
            ·
              refine ⟨2694540372536059312044529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14370881986858982997570821 2694540372536059312044529)
              ·
                refine ⟨2020905279402044484033397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694540372536059312044529 2020905279402044484033397)
                ·
                  refine ⟨189459869943941670378131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020905279402044484033397 189459869943941670378131)
                  ·
                    rfl

theorem cell22_1660373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_1660373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660373 prefixEnd_1660373 := by exact prefixLift 1660373
  have htrace : WordTrace (prefixWord ++ tailWord_1660373) baseStart_1660373 baseEnd_1660373 := by
    simpa [prefixWord, tailWord_1660373, baseEnd_1660373] using wordTrace_append hprefix tailTrace_1660373
  have hstable : (prefixWord ++ tailWord_1660373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660373).length < 2 ^ (prefixWord ++ tailWord_1660373).sum := by decide
  have hdescent : baseEnd_1660373 < baseStart_1660373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660377 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 1, 3]
def baseStart_1660377 : Nat := 118140960795 + 1660377 * 2 ^ 59
def prefixEnd_1660377 : Nat := 4983230072969 + 3 ^ 40 * 1660377 * 2
def baseEnd_1660377 : Nat := 568380979113570334034381

theorem tailTrace_1660377 : CollatzResearch.WordTrace tailWord_1660377 prefixEnd_1660377 568380979113570334034381 := by
  unfold tailWord_1660377
  simp only [CollatzResearch.WordTrace]
  refine ⟨60558924305745173660563385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40372616203830115773708923 60558924305745173660563385)
  ·
    refine ⟨45419193229308880245422539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60558924305745173660563385 45419193229308880245422539)
    ·
      refine ⟨68128789843963320368133809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45419193229308880245422539 68128789843963320368133809)
      ·
        refine ⟨51096592382972490276100357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68128789843963320368133809 51096592382972490276100357)
        ·
          refine ⟨9580611071807341926768817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51096592382972490276100357 9580611071807341926768817)
          ·
            refine ⟨7185458303855506445076613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580611071807341926768817 7185458303855506445076613)
            ·
              refine ⟨1347273431972907458451865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7185458303855506445076613 1347273431972907458451865)
              ·
                refine ⟨1010455073979680593838899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347273431972907458451865 1010455073979680593838899)
                ·
                  refine ⟨1515682610969520890758349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010455073979680593838899 1515682610969520890758349)
                  ·
                    refine ⟨568380979113570334034381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515682610969520890758349 568380979113570334034381)
                    ·
                      rfl

theorem cell22_1660377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_1660377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660377 prefixEnd_1660377 := by exact prefixLift 1660377
  have htrace : WordTrace (prefixWord ++ tailWord_1660377) baseStart_1660377 baseEnd_1660377 := by
    simpa [prefixWord, tailWord_1660377, baseEnd_1660377] using wordTrace_append hprefix tailTrace_1660377
  have hstable : (prefixWord ++ tailWord_1660377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660377).length < 2 ^ (prefixWord ++ tailWord_1660377).sum := by decide
  have hdescent : baseEnd_1660377 < baseStart_1660377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660401 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 8]
def baseStart_1660401 : Nat := 118140960795 + 1660401 * 2 ^ 59
def prefixEnd_1660401 : Nat := 4983230072969 + 3 ^ 40 * 1660401 * 2
def baseEnd_1660401 : Nat := 189463064934680757144769

theorem tailTrace_1660401 : CollatzResearch.WordTrace tailWord_1660401 prefixEnd_1660401 189463064934680757144769 := by
  unfold tailWord_1660401
  simp only [CollatzResearch.WordTrace]
  refine ⟨60559799657658225759437057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40373199771772150506291371 60559799657658225759437057)
  ·
    refine ⟨45419849743243669319577793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60559799657658225759437057 45419849743243669319577793)
    ·
      refine ⟨34064887307432751989683345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45419849743243669319577793 34064887307432751989683345)
      ·
        refine ⟨25548665480574563992262509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34064887307432751989683345 25548665480574563992262509)
        ·
          refine ⟨9580749555215461497098441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25548665480574563992262509 9580749555215461497098441)
          ·
            refine ⟨7185562166411596122823831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9580749555215461497098441 7185562166411596122823831)
            ·
              refine ⟨10778343249617394184235747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185562166411596122823831 10778343249617394184235747)
              ·
                refine ⟨16167514874426091276353621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778343249617394184235747 16167514874426091276353621)
                ·
                  refine ⟨189463064934680757144769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16167514874426091276353621 189463064934680757144769)
                  ·
                    rfl

theorem cell22_1660401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_1660401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660401 prefixEnd_1660401 := by exact prefixLift 1660401
  have htrace : WordTrace (prefixWord ++ tailWord_1660401) baseStart_1660401 baseEnd_1660401 := by
    simpa [prefixWord, tailWord_1660401, baseEnd_1660401] using wordTrace_append hprefix tailTrace_1660401
  have hstable : (prefixWord ++ tailWord_1660401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660401).length < 2 ^ (prefixWord ++ tailWord_1660401).sum := by decide
  have hdescent : baseEnd_1660401 < baseStart_1660401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660433 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_1660433 : Nat := 118140960795 + 1660433 * 2 ^ 59
def prefixEnd_1660433 : Nat := 4983230072969 + 3 ^ 40 * 1660433 * 2
def baseEnd_1660433 : Nat := 568400149058004854634209

theorem tailTrace_1660433 : CollatzResearch.WordTrace tailWord_1660433 prefixEnd_1660433 568400149058004854634209 := by
  unfold tailWord_1660433
  simp only [CollatzResearch.WordTrace]
  refine ⟨60560966793542295224601953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40373977862361530149734635 60560966793542295224601953)
  ·
    refine ⟨45420725095156721418451465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60560966793542295224601953 45420725095156721418451465)
    ·
      refine ⟨34065543821367541063838599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45420725095156721418451465 34065543821367541063838599)
      ·
        refine ⟨51098315732051311595757899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34065543821367541063838599 51098315732051311595757899)
        ·
          refine ⟨76647473598076967393636849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51098315732051311595757899 76647473598076967393636849)
          ·
            refine ⟨57485605198557725545227637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76647473598076967393636849 57485605198557725545227637)
            ·
              refine ⟨5389275487364786769865091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57485605198557725545227637 5389275487364786769865091)
              ·
                refine ⟨8083913231047180154797637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389275487364786769865091 8083913231047180154797637)
                ·
                  refine ⟨1515733730821346279024557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8083913231047180154797637 1515733730821346279024557)
                  ·
                    refine ⟨568400149058004854634209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515733730821346279024557 568400149058004854634209)
                    ·
                      rfl

theorem cell22_1660433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_1660433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660433 prefixEnd_1660433 := by exact prefixLift 1660433
  have htrace : WordTrace (prefixWord ++ tailWord_1660433) baseStart_1660433 baseEnd_1660433 := by
    simpa [prefixWord, tailWord_1660433, baseEnd_1660433] using wordTrace_append hprefix tailTrace_1660433
  have hstable : (prefixWord ++ tailWord_1660433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660433).length < 2 ^ (prefixWord ++ tailWord_1660433).sum := by decide
  have hdescent : baseEnd_1660433 < baseStart_1660433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660448 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_1660448 : Nat := 118140960795 + 1660448 * 2 ^ 59
def prefixEnd_1660448 : Nat := 4983230072969 + 3 ^ 40 * 1660448 * 2
def baseEnd_1660448 : Nat := 568405283864549815509163

theorem tailTrace_1660448 : CollatzResearch.WordTrace tailWord_1660448 prefixEnd_1660448 568405283864549815509163 := by
  unfold tailWord_1660448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30280756944243976393198999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40374342592325301857598665 30280756944243976393198999)
  ·
    refine ⟨45421135416365964589798499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30280756944243976393198999 45421135416365964589798499)
    ·
      refine ⟨68131703124548946884697749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45421135416365964589798499 68131703124548946884697749)
      ·
        refine ⟨3193673583963231885220207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68131703124548946884697749 3193673583963231885220207)
        ·
          refine ⟨4790510375944847827830311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193673583963231885220207 4790510375944847827830311)
          ·
            refine ⟨7185765563917271741745467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790510375944847827830311 7185765563917271741745467)
            ·
              refine ⟨10778648345875907612618201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185765563917271741745467 10778648345875907612618201)
              ·
                refine ⟨8083986259406930709463651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778648345875907612618201 8083986259406930709463651)
                ·
                  refine ⟨12125979389110396064195477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083986259406930709463651 12125979389110396064195477)
                  ·
                    refine ⟨568405283864549815509163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12125979389110396064195477 568405283864549815509163)
                    ·
                      rfl

theorem cell22_1660448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_1660448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660448 prefixEnd_1660448 := by exact prefixLift 1660448
  have htrace : WordTrace (prefixWord ++ tailWord_1660448) baseStart_1660448 baseEnd_1660448 := by
    simpa [prefixWord, tailWord_1660448, baseEnd_1660448] using wordTrace_append hprefix tailTrace_1660448
  have hstable : (prefixWord ++ tailWord_1660448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660448).length < 2 ^ (prefixWord ++ tailWord_1660448).sum := by decide
  have hdescent : baseEnd_1660448 < baseStart_1660448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660450 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1660450 : Nat := 118140960795 + 1660450 * 2 ^ 59
def prefixEnd_1660450 : Nat := 4983230072969 + 3 ^ 40 * 1660450 * 2
def baseEnd_1660450 : Nat := 568405968505422476959157

theorem tailTrace_1660450 : CollatzResearch.WordTrace tailWord_1660450 prefixEnd_1660450 568405968505422476959157 := by
  unfold tailWord_1660450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15140396708620176781992701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40374391222987138085313869 15140396708620176781992701)
  ·
    refine ⟨5677648765732566293247263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15140396708620176781992701 5677648765732566293247263)
    ·
      refine ⟨8516473148598849439870895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5677648765732566293247263 8516473148598849439870895)
      ·
        refine ⟨12774709722898274159806343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8516473148598849439870895 12774709722898274159806343)
        ·
          refine ⟨19162064584347411239709515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12774709722898274159806343 19162064584347411239709515)
          ·
            refine ⟨28743096876521116859564273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19162064584347411239709515 28743096876521116859564273)
            ·
              refine ⟨21557322657390837644673205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28743096876521116859564273 21557322657390837644673205)
              ·
                refine ⟨2020998999130391029188113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21557322657390837644673205 2020998999130391029188113)
                ·
                  refine ⟨1515749249347793271891085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2020998999130391029188113 1515749249347793271891085)
                  ·
                    refine ⟨568405968505422476959157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515749249347793271891085 568405968505422476959157)
                    ·
                      rfl

theorem cell22_1660450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1660450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660450 prefixEnd_1660450 := by exact prefixLift 1660450
  have htrace : WordTrace (prefixWord ++ tailWord_1660450) baseStart_1660450 baseEnd_1660450 := by
    simpa [prefixWord, tailWord_1660450, baseEnd_1660450] using wordTrace_append hprefix tailTrace_1660450
  have hstable : (prefixWord ++ tailWord_1660450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660450).length < 2 ^ (prefixWord ++ tailWord_1660450).sum := by decide
  have hdescent : baseEnd_1660450 < baseStart_1660450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660486 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1660486 : Nat := 118140960795 + 1660486 * 2 ^ 59
def prefixEnd_1660486 : Nat := 4983230072969 + 3 ^ 40 * 1660486 * 2
def baseEnd_1660486 : Nat := 189472764013710127686349

theorem tailTrace_1660486 : CollatzResearch.WordTrace tailWord_1660486 prefixEnd_1660486 189472764013710127686349 := by
  unfold tailWord_1660486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892590620698446414883791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40375266574900190184187541 1892590620698446414883791)
  ·
    refine ⟨2838885931047669622325687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892590620698446414883791 2838885931047669622325687)
    ·
      refine ⟨4258328896571504433488531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838885931047669622325687 4258328896571504433488531)
      ·
        refine ⟨6387493344857256650232797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258328896571504433488531 6387493344857256650232797)
        ·
          refine ⟨2395310004321471243837299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6387493344857256650232797 2395310004321471243837299)
          ·
            refine ⟨3592965006482206865755949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395310004321471243837299 3592965006482206865755949)
            ·
              refine ⟨1347361877430827574658481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3592965006482206865755949 1347361877430827574658481)
              ·
                refine ⟨1010521408073120680993861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347361877430827574658481 1010521408073120680993861)
                ·
                  refine ⟨189472764013710127686349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010521408073120680993861 189472764013710127686349)
                  ·
                    rfl

theorem cell22_1660486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1660486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660486 prefixEnd_1660486 := by exact prefixLift 1660486
  have htrace : WordTrace (prefixWord ++ tailWord_1660486) baseStart_1660486 baseEnd_1660486 := by
    simpa [prefixWord, tailWord_1660486, baseEnd_1660486] using wordTrace_append hprefix tailTrace_1660486
  have hstable : (prefixWord ++ tailWord_1660486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660486).length < 2 ^ (prefixWord ++ tailWord_1660486).sum := by decide
  have hdescent : baseEnd_1660486 < baseStart_1660486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660602 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_1660602 : Nat := 118140960795 + 1660602 * 2 ^ 59
def prefixEnd_1660602 : Nat := 4983230072969 + 3 ^ 40 * 1660602 * 2
def baseEnd_1660602 : Nat := 568458001211744747158691

theorem tailTrace_1660602 : CollatzResearch.WordTrace tailWord_1660602 prefixEnd_1660602 568458001211744747158691 := by
  unfold tailWord_1660602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15141782682482509271876015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40378087153286691391669373 15141782682482509271876015)
  ·
    refine ⟨22712674023723763907814023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15141782682482509271876015 22712674023723763907814023)
    ·
      refine ⟨34069011035585645861721035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22712674023723763907814023 34069011035585645861721035)
      ·
        refine ⟨51103516553378468792581553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34069011035585645861721035 51103516553378468792581553)
        ·
          refine ⟨38327637415033851594436165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51103516553378468792581553 38327637415033851594436165)
          ·
            refine ⟨7186432015318847173956781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38327637415033851594436165 7186432015318847173956781)
            ·
              refine ⟨2694912005744567690233793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7186432015318847173956781 2694912005744567690233793)
              ·
                refine ⟨2021184004308425767675345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694912005744567690233793 2021184004308425767675345)
                ·
                  refine ⟨1515888003231319325756509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2021184004308425767675345 1515888003231319325756509)
                  ·
                    refine ⟨568458001211744747158691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1515888003231319325756509 568458001211744747158691)
                    ·
                      rfl

theorem cell22_1660602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_1660602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660602 prefixEnd_1660602 := by exact prefixLift 1660602
  have htrace : WordTrace (prefixWord ++ tailWord_1660602) baseStart_1660602 baseEnd_1660602 := by
    simpa [prefixWord, tailWord_1660602, baseEnd_1660602] using wordTrace_append hprefix tailTrace_1660602
  have hstable : (prefixWord ++ tailWord_1660602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660602).length < 2 ^ (prefixWord ++ tailWord_1660602).sum := by decide
  have hdescent : baseEnd_1660602 < baseStart_1660602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660771 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 2, 3]
def baseStart_1660771 : Nat := 118140960795 + 1660771 * 2 ^ 59
def prefixEnd_1660771 : Nat := 4983230072969 + 3 ^ 40 * 1660771 * 2
def baseEnd_1660771 : Nat := 568515853365484639683173

theorem tailTrace_1660771 : CollatzResearch.WordTrace tailWord_1660771 prefixEnd_1660771 568515853365484639683173 := by
  unfold tailWord_1660771
  simp only [CollatzResearch.WordTrace]
  refine ⟨60573294666317778950406167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40382196444211852633604111 60573294666317778950406167)
  ·
    refine ⟨90859941999476668425609251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60573294666317778950406167 90859941999476668425609251)
    ·
      refine ⟨136289912999215002638413877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90859941999476668425609251 136289912999215002638413877)
      ·
        refine ⟨12777179343676406497351301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136289912999215002638413877 12777179343676406497351301)
        ·
          refine ⟨2395721126939326218253369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12777179343676406497351301 2395721126939326218253369)
          ·
            refine ⟨1796790845204494663690027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395721126939326218253369 1796790845204494663690027)
            ·
              refine ⟨2695186267806741995535041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796790845204494663690027 2695186267806741995535041)
              ·
                refine ⟨2021389700855056496651281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695186267806741995535041 2021389700855056496651281)
                ·
                  refine ⟨1516042275641292372488461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2021389700855056496651281 1516042275641292372488461)
                  ·
                    refine ⟨568515853365484639683173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516042275641292372488461 568515853365484639683173)
                    ·
                      rfl

theorem cell22_1660771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 3].length) (baseStart_1660771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660771 prefixEnd_1660771 := by exact prefixLift 1660771
  have htrace : WordTrace (prefixWord ++ tailWord_1660771) baseStart_1660771 baseEnd_1660771 := by
    simpa [prefixWord, tailWord_1660771, baseEnd_1660771] using wordTrace_append hprefix tailTrace_1660771
  have hstable : (prefixWord ++ tailWord_1660771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660771).length < 2 ^ (prefixWord ++ tailWord_1660771).sum := by decide
  have hdescent : baseEnd_1660771 < baseStart_1660771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660801 : List Nat := [1, 2, 4, 4, 1, 2, 2, 6]
def baseStart_1660801 : Nat := 118140960795 + 1660801 * 2 ^ 59
def prefixEnd_1660801 : Nat := 4983230072969 + 3 ^ 40 * 1660801 * 2
def baseEnd_1660801 : Nat := 63169569219841617937009

theorem tailTrace_1660801 : CollatzResearch.WordTrace tailWord_1660801 prefixEnd_1660801 63169569219841617937009 := by
  unfold tailWord_1660801
  simp only [CollatzResearch.WordTrace]
  refine ⟨60574388856209094073998257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40382925904139396049332171 60574388856209094073998257)
  ·
    refine ⟨45430791642156820555498693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60574388856209094073998257 45430791642156820555498693)
    ·
      refine ⟨8518273432904403854156005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45430791642156820555498693 8518273432904403854156005)
      ·
        refine ⟨1597176268669575722654251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8518273432904403854156005 1597176268669575722654251)
        ·
          refine ⟨2395764403004363583981377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597176268669575722654251 2395764403004363583981377)
          ·
            refine ⟨1796823302253272687986033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395764403004363583981377 1796823302253272687986033)
            ·
              refine ⟨1347617476689954515989525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796823302253272687986033 1347617476689954515989525)
              ·
                refine ⟨63169569219841617937009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1347617476689954515989525 63169569219841617937009)
                ·
                  rfl

theorem cell22_1660801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 6].length) (baseStart_1660801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660801 prefixEnd_1660801 := by exact prefixLift 1660801
  have htrace : WordTrace (prefixWord ++ tailWord_1660801) baseStart_1660801 baseEnd_1660801 := by
    simpa [prefixWord, tailWord_1660801, baseEnd_1660801] using wordTrace_append hprefix tailTrace_1660801
  have hstable : (prefixWord ++ tailWord_1660801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660801).length < 2 ^ (prefixWord ++ tailWord_1660801).sum := by decide
  have hdescent : baseEnd_1660801 < baseStart_1660801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660833 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1660833 : Nat := 118140960795 + 1660833 * 2 ^ 59
def prefixEnd_1660833 : Nat := 4983230072969 + 3 ^ 40 * 1660833 * 2
def baseEnd_1660833 : Nat := 568537077232537144632983

theorem tailTrace_1660833 : CollatzResearch.WordTrace tailWord_1660833 prefixEnd_1660833 568537077232537144632983 := by
  unfold tailWord_1660833
  simp only [CollatzResearch.WordTrace]
  refine ⟨60575555992093163539163153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40383703994728775692775435 60575555992093163539163153)
  ·
    refine ⟨45431666994069872654372365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60575555992093163539163153 45431666994069872654372365)
    ·
      refine ⟨17036875122776202245389637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45431666994069872654372365 17036875122776202245389637)
      ·
        refine ⟨3194414085520537921010557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17036875122776202245389637 3194414085520537921010557)
        ·
          refine ⟨1197905282070201720378959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3194414085520537921010557 1197905282070201720378959)
          ·
            refine ⟨1796857923105302580568439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197905282070201720378959 1796857923105302580568439)
            ·
              refine ⟨2695286884657953870852659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796857923105302580568439 2695286884657953870852659)
              ·
                refine ⟨4042930326986930806278989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695286884657953870852659 4042930326986930806278989)
                ·
                  refine ⟨1516098872620099052354621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4042930326986930806278989 1516098872620099052354621)
                  ·
                    refine ⟨568537077232537144632983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516098872620099052354621 568537077232537144632983)
                    ·
                      rfl

theorem cell22_1660833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1660833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660833 prefixEnd_1660833 := by exact prefixLift 1660833
  have htrace : WordTrace (prefixWord ++ tailWord_1660833) baseStart_1660833 baseEnd_1660833 := by
    simpa [prefixWord, tailWord_1660833, baseEnd_1660833] using wordTrace_append hprefix tailTrace_1660833
  have hstable : (prefixWord ++ tailWord_1660833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660833).length < 2 ^ (prefixWord ++ tailWord_1660833).sum := by decide
  have hdescent : baseEnd_1660833 < baseStart_1660833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660872 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1660872 : Nat := 118140960795 + 1660872 * 2 ^ 59
def prefixEnd_1660872 : Nat := 4983230072969 + 3 ^ 40 * 1660872 * 2
def baseEnd_1660872 : Nat := 568550427729554042907863

theorem tailTrace_1660872 : CollatzResearch.WordTrace tailWord_1660872 prefixEnd_1660872 568550427729554042907863 := by
  unfold tailWord_1660872
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288489219475936599916435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40384652292634582133221913 30288489219475936599916435)
  ·
    refine ⟨45432733829213904899874653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30288489219475936599916435 45432733829213904899874653)
    ·
      refine ⟨17037275185955214337452995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45432733829213904899874653 17037275185955214337452995)
      ·
        refine ⟨25555912778932821506179493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17037275185955214337452995 25555912778932821506179493)
        ·
          refine ⟨4791733646049904032408655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25555912778932821506179493 4791733646049904032408655)
          ·
            refine ⟨7187600469074856048612983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791733646049904032408655 7187600469074856048612983)
            ·
              refine ⟨10781400703612284072919475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187600469074856048612983 10781400703612284072919475)
              ·
                refine ⟨16172101055418426109379213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10781400703612284072919475 16172101055418426109379213)
                ·
                  refine ⟨6064537895781909791017205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16172101055418426109379213 6064537895781909791017205)
                  ·
                    refine ⟨568550427729554042907863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6064537895781909791017205 568550427729554042907863)
                    ·
                      rfl

theorem cell22_1660872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1660872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660872 prefixEnd_1660872 := by exact prefixLift 1660872
  have htrace : WordTrace (prefixWord ++ tailWord_1660872) baseStart_1660872 baseEnd_1660872 := by
    simpa [prefixWord, tailWord_1660872, baseEnd_1660872] using wordTrace_append hprefix tailTrace_1660872
  have hstable : (prefixWord ++ tailWord_1660872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660872).length < 2 ^ (prefixWord ++ tailWord_1660872).sum := by decide
  have hdescent : baseEnd_1660872 < baseStart_1660872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660876 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_1660876 : Nat := 118140960795 + 1660876 * 2 ^ 59
def prefixEnd_1660876 : Nat := 4983230072969 + 3 ^ 40 * 1660876 * 2
def baseEnd_1660876 : Nat := 568551797011299365807851

theorem tailTrace_1660876 : CollatzResearch.WordTrace tailWord_1660876 prefixEnd_1660876 568551797011299365807851 := by
  unfold tailWord_1660876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288562165468690941489241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40384749553958254588652321 30288562165468690941489241)
  ·
    refine ⟨22716421624101518206116931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30288562165468690941489241 22716421624101518206116931)
    ·
      refine ⟨34074632436152277309175397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22716421624101518206116931 34074632436152277309175397)
      ·
        refine ⟨6388993581778551995470387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34074632436152277309175397 6388993581778551995470387)
        ·
          refine ⟨9583490372667827993205581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6388993581778551995470387 9583490372667827993205581)
          ·
            refine ⟨3593808889750435497452093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9583490372667827993205581 3593808889750435497452093)
            ·
              refine ⟨1347678333656413311544535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3593808889750435497452093 1347678333656413311544535)
              ·
                refine ⟨2021517500484619967316803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347678333656413311544535 2021517500484619967316803)
                ·
                  refine ⟨3032276250726929950975205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021517500484619967316803 3032276250726929950975205)
                  ·
                    refine ⟨568551797011299365807851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032276250726929950975205 568551797011299365807851)
                    ·
                      rfl

theorem cell22_1660876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_1660876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660876 prefixEnd_1660876 := by exact prefixLift 1660876
  have htrace : WordTrace (prefixWord ++ tailWord_1660876) baseStart_1660876 baseEnd_1660876 := by
    simpa [prefixWord, tailWord_1660876, baseEnd_1660876] using wordTrace_append hprefix tailTrace_1660876
  have hstable : (prefixWord ++ tailWord_1660876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660876).length < 2 ^ (prefixWord ++ tailWord_1660876).sum := by decide
  have hdescent : baseEnd_1660876 < baseStart_1660876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660887 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1660887 : Nat := 118140960795 + 1660887 * 2 ^ 59
def prefixEnd_1660887 : Nat := 4983230072969 + 3 ^ 40 * 1660887 * 2
def baseEnd_1660887 : Nat := 568555562536099003782817

theorem tailTrace_1660887 : CollatzResearch.WordTrace tailWord_1660887 prefixEnd_1660887 568555562536099003782817 := by
  unfold tailWord_1660887
  simp only [CollatzResearch.WordTrace]
  refine ⟨60577525533897530761628915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40385017022598353841085943 60577525533897530761628915)
  ·
    refine ⟨90866288300846296142443373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60577525533897530761628915 90866288300846296142443373)
    ·
      refine ⟨34074858112817361053416265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90866288300846296142443373 34074858112817361053416265)
      ·
        refine ⟨25556143584613020790062199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34074858112817361053416265 25556143584613020790062199)
        ·
          refine ⟨38334215376919531185093299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25556143584613020790062199 38334215376919531185093299)
          ·
            refine ⟨57501323065379296777639949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38334215376919531185093299 57501323065379296777639949)
            ·
              refine ⟨21562996149517236291614981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57501323065379296777639949 21562996149517236291614981)
              ·
                refine ⟨4043061778034481804677809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21562996149517236291614981 4043061778034481804677809)
                ·
                  refine ⟨3032296333525861353508357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043061778034481804677809 3032296333525861353508357)
                  ·
                    refine ⟨568555562536099003782817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032296333525861353508357 568555562536099003782817)
                    ·
                      rfl

theorem cell22_1660887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1660887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660887 prefixEnd_1660887 := by exact prefixLift 1660887
  have htrace : WordTrace (prefixWord ++ tailWord_1660887) baseStart_1660887 baseEnd_1660887 := by
    simpa [prefixWord, tailWord_1660887, baseEnd_1660887] using wordTrace_append hprefix tailTrace_1660887
  have hstable : (prefixWord ++ tailWord_1660887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660887).length < 2 ^ (prefixWord ++ tailWord_1660887).sum := by decide
  have hdescent : baseEnd_1660887 < baseStart_1660887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1660985 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 1, 3]
def baseStart_1660985 : Nat := 118140960795 + 1660985 * 2 ^ 59
def prefixEnd_1660985 : Nat := 4983230072969 + 3 ^ 40 * 1660985 * 2
def baseEnd_1660985 : Nat := 568589109938859414832517

theorem tailTrace_1660985 : CollatzResearch.WordTrace tailWord_1660985 prefixEnd_1660985 568589109938859414832517 := by
  unfold tailWord_1660985
  simp only [CollatzResearch.WordTrace]
  refine ⟨60581099887542493498696409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40387399925028328999130939 60581099887542493498696409)
  ·
    refine ⟨45435824915656870124022307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60581099887542493498696409 45435824915656870124022307)
    ·
      refine ⟨68153737373485305186033461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45435824915656870124022307 68153737373485305186033461)
      ·
        refine ⟨6389412878764247361190637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68153737373485305186033461 6389412878764247361190637)
        ·
          refine ⟨2396029829536592760446489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6389412878764247361190637 2396029829536592760446489)
          ·
            refine ⟨1797022372152444570334867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396029829536592760446489 1797022372152444570334867)
            ·
              refine ⟨2695533558228666855502301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797022372152444570334867 2695533558228666855502301)
              ·
                refine ⟨1010825084335750070813363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2695533558228666855502301 1010825084335750070813363)
                ·
                  refine ⟨1516237626503625106220045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010825084335750070813363 1516237626503625106220045)
                  ·
                    refine ⟨568589109938859414832517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516237626503625106220045 568589109938859414832517)
                    ·
                      rfl

theorem cell22_1660985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_1660985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1660985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1660985 prefixEnd_1660985 := by exact prefixLift 1660985
  have htrace : WordTrace (prefixWord ++ tailWord_1660985) baseStart_1660985 baseEnd_1660985 := by
    simpa [prefixWord, tailWord_1660985, baseEnd_1660985] using wordTrace_append hprefix tailTrace_1660985
  have hstable : (prefixWord ++ tailWord_1660985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1660985).length < 2 ^ (prefixWord ++ tailWord_1660985).sum := by decide
  have hdescent : baseEnd_1660985 < baseStart_1660985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1660985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661007 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1661007 : Nat := 118140960795 + 1661007 * 2 ^ 59
def prefixEnd_1661007 : Nat := 4983230072969 + 3 ^ 40 * 1661007 * 2
def baseEnd_1661007 : Nat := 568596640988458690782449

theorem tailTrace_1661007 : CollatzResearch.WordTrace tailWord_1661007 prefixEnd_1661007 568596640988458690782449 := by
  unfold tailWord_1661007
  simp only [CollatzResearch.WordTrace]
  refine ⟨60581902293462791255997275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40387934862308527503998183 60581902293462791255997275)
  ·
    refine ⟨90872853440194186883995913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60581902293462791255997275 90872853440194186883995913)
    ·
      refine ⟨68154640080145640162996935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90872853440194186883995913 68154640080145640162996935)
      ·
        refine ⟨102231960120218460244495403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68154640080145640162996935 102231960120218460244495403)
        ·
          refine ⟨153347940180327690366743105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102231960120218460244495403 153347940180327690366743105)
          ·
            refine ⟨115010955135245767775057329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153347940180327690366743105 115010955135245767775057329)
            ·
              refine ⟨86258216351434325831292997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115010955135245767775057329 86258216351434325831292997)
              ·
                refine ⟨16173415565893936093367437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86258216351434325831292997 16173415565893936093367437)
                ·
                  refine ⟨6065030837210226035012789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16173415565893936093367437 6065030837210226035012789)
                  ·
                    refine ⟨568596640988458690782449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6065030837210226035012789 568596640988458690782449)
                    ·
                      rfl

theorem cell22_1661007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1661007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661007 prefixEnd_1661007 := by exact prefixLift 1661007
  have htrace : WordTrace (prefixWord ++ tailWord_1661007) baseStart_1661007 baseEnd_1661007 := by
    simpa [prefixWord, tailWord_1661007, baseEnd_1661007] using wordTrace_append hprefix tailTrace_1661007
  have hstable : (prefixWord ++ tailWord_1661007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661007).length < 2 ^ (prefixWord ++ tailWord_1661007).sum := by decide
  have hdescent : baseEnd_1661007 < baseStart_1661007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661039 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1661039 : Nat := 118140960795 + 1661039 * 2 ^ 59
def prefixEnd_1661039 : Nat := 4983230072969 + 3 ^ 40 * 1661039 * 2
def baseEnd_1661039 : Nat := 568607595242421273982351

theorem tailTrace_1661039 : CollatzResearch.WordTrace tailWord_1661039 prefixEnd_1661039 568607595242421273982351 := by
  unfold tailWord_1661039
  simp only [CollatzResearch.WordTrace]
  refine ⟨60583069429346860721162171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40388712952897907147441447 60583069429346860721162171)
  ·
    refine ⟨90874604144020291081743257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60583069429346860721162171 90874604144020291081743257)
    ·
      refine ⟨68155953108015218311307443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90874604144020291081743257 68155953108015218311307443)
      ·
        refine ⟨102233929662022827466961165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68155953108015218311307443 102233929662022827466961165)
        ·
          refine ⟨38337723623258560300110437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102233929662022827466961165 38337723623258560300110437)
          ·
            refine ⟨7188323179360980056270707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38337723623258560300110437 7188323179360980056270707)
            ·
              refine ⟨10782484769041470084406061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188323179360980056270707 10782484769041470084406061)
              ·
                refine ⟨4043431788390551281652273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10782484769041470084406061 4043431788390551281652273)
                ·
                  refine ⟨3032573841292913461239205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043431788390551281652273 3032573841292913461239205)
                  ·
                    refine ⟨568607595242421273982351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032573841292913461239205 568607595242421273982351)
                    ·
                      rfl

theorem cell22_1661039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1661039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661039 prefixEnd_1661039 := by exact prefixLift 1661039
  have htrace : WordTrace (prefixWord ++ tailWord_1661039) baseStart_1661039 baseEnd_1661039 := by
    simpa [prefixWord, tailWord_1661039, baseEnd_1661039] using wordTrace_append hprefix tailTrace_1661039
  have hstable : (prefixWord ++ tailWord_1661039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661039).length < 2 ^ (prefixWord ++ tailWord_1661039).sum := by decide
  have hdescent : baseEnd_1661039 < baseStart_1661039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661084 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1661084 : Nat := 118140960795 + 1661084 * 2 ^ 59
def prefixEnd_1661084 : Nat := 4983230072969 + 3 ^ 40 * 1661084 * 2
def baseEnd_1661084 : Nat := 568622999662056156607213

theorem tailTrace_1661084 : CollatzResearch.WordTrace tailWord_1661084 prefixEnd_1661084 568622999662056156607213 := by
  unfold tailWord_1661084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292355357091916703275153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40389807142789222271033537 30292355357091916703275153)
  ·
    refine ⟨22719266517818937527456365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30292355357091916703275153 22719266517818937527456365)
    ·
      refine ⟨8519724944182101572796137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22719266517818937527456365 8519724944182101572796137)
      ·
        refine ⟨6389793708136576179597103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8519724944182101572796137 6389793708136576179597103)
        ·
          refine ⟨9584690562204864269395655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389793708136576179597103 9584690562204864269395655)
          ·
            refine ⟨14377035843307296404093483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584690562204864269395655 14377035843307296404093483)
            ·
              refine ⟨21565553764960944606140225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377035843307296404093483 21565553764960944606140225)
              ·
                refine ⟨16174165323720708454605169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21565553764960944606140225 16174165323720708454605169)
                ·
                  refine ⟨12130623992790531340953877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16174165323720708454605169 12130623992790531340953877)
                  ·
                    refine ⟨568622999662056156607213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12130623992790531340953877 568622999662056156607213)
                    ·
                      rfl

theorem cell22_1661084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1661084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661084 prefixEnd_1661084 := by exact prefixLift 1661084
  have htrace : WordTrace (prefixWord ++ tailWord_1661084) baseStart_1661084 baseEnd_1661084 := by
    simpa [prefixWord, tailWord_1661084, baseEnd_1661084] using wordTrace_append hprefix tailTrace_1661084
  have hstable : (prefixWord ++ tailWord_1661084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661084).length < 2 ^ (prefixWord ++ tailWord_1661084).sum := by decide
  have hdescent : baseEnd_1661084 < baseStart_1661084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661114 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1661114 : Nat := 118140960795 + 1661114 * 2 ^ 59
def prefixEnd_1661114 : Nat := 4983230072969 + 3 ^ 40 * 1661114 * 2
def baseEnd_1661114 : Nat := 568633269275146078357121

theorem tailTrace_1661114 : CollatzResearch.WordTrace tailWord_1661114 prefixEnd_1661114 568633269275146078357121 := by
  unfold tailWord_1661114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146451226018787132535599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40390536602716765686761597 15146451226018787132535599)
  ·
    refine ⟨22719676839028180698803399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15146451226018787132535599 22719676839028180698803399)
    ·
      refine ⟨34079515258542271048205099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22719676839028180698803399 34079515258542271048205099)
      ·
        refine ⟨51119272887813406572307649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34079515258542271048205099 51119272887813406572307649)
        ·
          refine ⟨38339454665860054929230737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51119272887813406572307649 38339454665860054929230737)
          ·
            refine ⟨28754590999395041196923053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38339454665860054929230737 28754590999395041196923053)
            ·
              refine ⟨10782971624773140448846145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28754590999395041196923053 10782971624773140448846145)
              ·
                refine ⟨8087228718579855336634609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10782971624773140448846145 8087228718579855336634609)
                ·
                  refine ⟨6065421538934891502475957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087228718579855336634609 6065421538934891502475957)
                  ·
                    refine ⟨568633269275146078357121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6065421538934891502475957 568633269275146078357121)
                    ·
                      rfl

theorem cell22_1661114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1661114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661114 prefixEnd_1661114 := by exact prefixLift 1661114
  have htrace : WordTrace (prefixWord ++ tailWord_1661114) baseStart_1661114 baseEnd_1661114 := by
    simpa [prefixWord, tailWord_1661114, baseEnd_1661114] using wordTrace_append hprefix tailTrace_1661114
  have hstable : (prefixWord ++ tailWord_1661114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661114).length < 2 ^ (prefixWord ++ tailWord_1661114).sum := by decide
  have hdescent : baseEnd_1661114 < baseStart_1661114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661116 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_1661116 : Nat := 118140960795 + 1661116 * 2 ^ 59
def prefixEnd_1661116 : Nat := 4983230072969 + 3 ^ 40 * 1661116 * 2
def baseEnd_1661116 : Nat := 189544651305339579935705

theorem tailTrace_1661116 : CollatzResearch.WordTrace tailWord_1661116 prefixEnd_1661116 189544651305339579935705 := by
  unfold tailWord_1661116
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292938925033951435857601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40390585233378601914476801 30292938925033951435857601)
  ·
    refine ⟨22719704193775463576893201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30292938925033951435857601 22719704193775463576893201)
    ·
      refine ⟨17039778145331597682669901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22719704193775463576893201 17039778145331597682669901)
      ·
        refine ⟨6389916804499349131001213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17039778145331597682669901 6389916804499349131001213)
        ·
          refine ⟨2396218801687255924125455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6389916804499349131001213 2396218801687255924125455)
          ·
            refine ⟨3594328202530883886188183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396218801687255924125455 3594328202530883886188183)
            ·
              refine ⟨5391492303796325829282275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594328202530883886188183 5391492303796325829282275)
              ·
                refine ⟨8087238455694488743923413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391492303796325829282275 8087238455694488743923413)
                ·
                  refine ⟨189544651305339579935705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8087238455694488743923413 189544651305339579935705)
                  ·
                    rfl

theorem cell22_1661116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_1661116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661116 prefixEnd_1661116 := by exact prefixLift 1661116
  have htrace : WordTrace (prefixWord ++ tailWord_1661116) baseStart_1661116 baseEnd_1661116 := by
    simpa [prefixWord, tailWord_1661116, baseEnd_1661116] using wordTrace_append hprefix tailTrace_1661116
  have hstable : (prefixWord ++ tailWord_1661116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661116).length < 2 ^ (prefixWord ++ tailWord_1661116).sum := by decide
  have hdescent : baseEnd_1661116 < baseStart_1661116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661129 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_1661129 : Nat := 118140960795 + 1661129 * 2 ^ 59
def prefixEnd_1661129 : Nat := 4983230072969 + 3 ^ 40 * 1661129 * 2
def baseEnd_1661129 : Nat := 568638404081691039232075

theorem tailTrace_1661129 : CollatzResearch.WordTrace tailWord_1661129 prefixEnd_1661129 568638404081691039232075 := by
  unfold tailWord_1661129
  simp only [CollatzResearch.WordTrace]
  refine ⟨60586351999020806091938441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40390901332680537394625627 60586351999020806091938441)
  ·
    refine ⟨45439763999265604568953831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60586351999020806091938441 45439763999265604568953831)
    ·
      refine ⟨68159645998898406853430747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45439763999265604568953831 68159645998898406853430747)
      ·
        refine ⟨102239468998347610280146121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68159645998898406853430747 102239468998347610280146121)
        ·
          refine ⟨76679601748760707710109591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102239468998347610280146121 76679601748760707710109591)
          ·
            refine ⟨115019402623141061565164387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76679601748760707710109591 115019402623141061565164387)
            ·
              refine ⟨172529103934711592347746581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115019402623141061565164387 172529103934711592347746581)
              ·
                refine ⟨8087301746939605891300621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172529103934711592347746581 8087301746939605891300621)
                ·
                  refine ⟨3032738155102352209237733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8087301746939605891300621 3032738155102352209237733)
                  ·
                    refine ⟨568638404081691039232075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032738155102352209237733 568638404081691039232075)
                    ·
                      rfl

theorem cell22_1661129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_1661129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661129 prefixEnd_1661129 := by exact prefixLift 1661129
  have htrace : WordTrace (prefixWord ++ tailWord_1661129) baseStart_1661129 baseEnd_1661129 := by
    simpa [prefixWord, tailWord_1661129, baseEnd_1661129] using wordTrace_append hprefix tailTrace_1661129
  have hstable : (prefixWord ++ tailWord_1661129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661129).length < 2 ^ (prefixWord ++ tailWord_1661129).sum := by decide
  have hdescent : baseEnd_1661129 < baseStart_1661129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661146 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1661146 : Nat := 118140960795 + 1661146 * 2 ^ 59
def prefixEnd_1661146 : Nat := 4983230072969 + 3 ^ 40 * 1661146 * 2
def baseEnd_1661146 : Nat := 568644223529108661557023

theorem tailTrace_1661146 : CollatzResearch.WordTrace tailWord_1661146 prefixEnd_1661146 568644223529108661557023 := by
  unfold tailWord_1661146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15146743009989804498826823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40391314693306145330204861 15146743009989804498826823)
  ·
    refine ⟨22720114514984706748240235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15146743009989804498826823 22720114514984706748240235)
    ·
      refine ⟨34080171772477060122360353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22720114514984706748240235 34080171772477060122360353)
      ·
        refine ⟨25560128829357795091770265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34080171772477060122360353 25560128829357795091770265)
        ·
          refine ⟨19170096622018346318827699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25560128829357795091770265 19170096622018346318827699)
          ·
            refine ⟨28755144933027519478241549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19170096622018346318827699 28755144933027519478241549)
            ·
              refine ⟨10783179349885319804340581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28755144933027519478241549 10783179349885319804340581)
              ·
                refine ⟨2021846128103497463313859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10783179349885319804340581 2021846128103497463313859)
                ·
                  refine ⟨3032769192155246194970789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021846128103497463313859 3032769192155246194970789)
                  ·
                    refine ⟨568644223529108661557023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032769192155246194970789 568644223529108661557023)
                    ·
                      rfl

theorem cell22_1661146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1661146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661146 prefixEnd_1661146 := by exact prefixLift 1661146
  have htrace : WordTrace (prefixWord ++ tailWord_1661146) baseStart_1661146 baseEnd_1661146 := by
    simpa [prefixWord, tailWord_1661146, baseEnd_1661146] using wordTrace_append hprefix tailTrace_1661146
  have hstable : (prefixWord ++ tailWord_1661146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661146).length < 2 ^ (prefixWord ++ tailWord_1661146).sum := by decide
  have hdescent : baseEnd_1661146 < baseStart_1661146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661193 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_1661193 : Nat := 118140960795 + 1661193 * 2 ^ 59
def prefixEnd_1661193 : Nat := 4983230072969 + 3 ^ 40 * 1661193 * 2
def baseEnd_1661193 : Nat := 568660312589616205631879

theorem tailTrace_1661193 : CollatzResearch.WordTrace tailWord_1661193 prefixEnd_1661193 568660312589616205631879 := by
  unfold tailWord_1661193
  simp only [CollatzResearch.WordTrace]
  refine ⟨60588686270788945022268233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40392457513859296681512155 60588686270788945022268233)
  ·
    refine ⟨45441514703091708766701175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60588686270788945022268233 45441514703091708766701175)
    ·
      refine ⟨68162272054637563150051763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45441514703091708766701175 68162272054637563150051763)
      ·
        refine ⟨102243408081956344725077645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68162272054637563150051763 102243408081956344725077645)
        ·
          refine ⟨38341278030733629271904117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102243408081956344725077645 38341278030733629271904117)
          ·
            refine ⟨3594494815381277744241011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38341278030733629271904117 3594494815381277744241011)
            ·
              refine ⟨5391742223071916616361517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594494815381277744241011 5391742223071916616361517)
              ·
                refine ⟨2021903333651968731135569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5391742223071916616361517 2021903333651968731135569)
                ·
                  refine ⟨1516427500238976548351677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2021903333651968731135569 1516427500238976548351677)
                  ·
                    refine ⟨568660312589616205631879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516427500238976548351677 568660312589616205631879)
                    ·
                      rfl

theorem cell22_1661193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_1661193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661193 prefixEnd_1661193 := by exact prefixLift 1661193
  have htrace : WordTrace (prefixWord ++ tailWord_1661193) baseStart_1661193 baseEnd_1661193 := by
    simpa [prefixWord, tailWord_1661193, baseEnd_1661193] using wordTrace_append hprefix tailTrace_1661193
  have hstable : (prefixWord ++ tailWord_1661193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661193).length < 2 ^ (prefixWord ++ tailWord_1661193).sum := by decide
  have hdescent : baseEnd_1661193 < baseStart_1661193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661223 : List Nat := [1, 1, 8, 1, 11]
def baseStart_1661223 : Nat := 118140960795 + 1661223 * 2 ^ 59
def prefixEnd_1661223 : Nat := 4983230072969 + 3 ^ 40 * 1661223 * 2
def baseEnd_1661223 : Nat := 2340208157212782417209

theorem tailTrace_1661223 : CollatzResearch.WordTrace tailWord_1661223 prefixEnd_1661223 2340208157212782417209 := by
  unfold tailWord_1661223
  simp only [CollatzResearch.WordTrace]
  refine ⟨60589780460680260145860323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40393186973786840097240215 60589780460680260145860323)
  ·
    refine ⟨90884670691020390218790485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60589780460680260145860323 90884670691020390218790485)
    ·
      refine ⟨1065054734660395197876451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 90884670691020390218790485 1065054734660395197876451)
      ·
        refine ⟨1597582101990592796814677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065054734660395197876451 1597582101990592796814677)
        ·
          refine ⟨2340208157212782417209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1597582101990592796814677 2340208157212782417209)
          ·
            rfl

theorem cell22_1661223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 11].length) (baseStart_1661223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661223 prefixEnd_1661223 := by exact prefixLift 1661223
  have htrace : WordTrace (prefixWord ++ tailWord_1661223) baseStart_1661223 baseEnd_1661223 := by
    simpa [prefixWord, tailWord_1661223, baseEnd_1661223] using wordTrace_append hprefix tailTrace_1661223
  have hstable : (prefixWord ++ tailWord_1661223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661223).length < 2 ^ (prefixWord ++ tailWord_1661223).sum := by decide
  have hdescent : baseEnd_1661223 < baseStart_1661223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661229 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1661229 : Nat := 118140960795 + 1661229 * 2 ^ 59
def prefixEnd_1661229 : Nat := 4983230072969 + 3 ^ 40 * 1661229 * 2
def baseEnd_1661229 : Nat := 189557545375108037243923

theorem tailTrace_1661229 : CollatzResearch.WordTrace tailWord_1661229 prefixEnd_1661229 189557545375108037243923 := by
  unfold tailWord_1661229
  simp only [CollatzResearch.WordTrace]
  refine ⟨60589999298658523170578741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40393332865772348780385827 60589999298658523170578741)
  ·
    refine ⟨5680312434249236547241757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60589999298658523170578741 5680312434249236547241757)
    ·
      refine ⟨2130117162843463705215659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5680312434249236547241757 2130117162843463705215659)
      ·
        refine ⟨3195175744265195557823489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130117162843463705215659 3195175744265195557823489)
        ·
          refine ⟨2396381808198896668367617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195175744265195557823489 2396381808198896668367617)
          ·
            refine ⟨1797286356149172501275713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396381808198896668367617 1797286356149172501275713)
            ·
              refine ⟨1347964767111879375956785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797286356149172501275713 1347964767111879375956785)
              ·
                refine ⟨1010973575333909531967589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347964767111879375956785 1010973575333909531967589)
                ·
                  refine ⟨189557545375108037243923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010973575333909531967589 189557545375108037243923)
                  ·
                    rfl

theorem cell22_1661229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1661229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661229 prefixEnd_1661229 := by exact prefixLift 1661229
  have htrace : WordTrace (prefixWord ++ tailWord_1661229) baseStart_1661229 baseEnd_1661229 := by
    simpa [prefixWord, tailWord_1661229, baseEnd_1661229] using wordTrace_append hprefix tailTrace_1661229
  have hstable : (prefixWord ++ tailWord_1661229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661229).length < 2 ^ (prefixWord ++ tailWord_1661229).sum := by decide
  have hdescent : baseEnd_1661229 < baseStart_1661229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661251 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 5]
def baseStart_1661251 : Nat := 118140960795 + 1661251 * 2 ^ 59
def prefixEnd_1661251 : Nat := 4983230072969 + 3 ^ 40 * 1661251 * 2
def baseEnd_1661251 : Nat := 189560055724974462560567

theorem tailTrace_1661251 : CollatzResearch.WordTrace tailWord_1661251 prefixEnd_1661251 189560055724974462560567 := by
  unfold tailWord_1661251
  simp only [CollatzResearch.WordTrace]
  refine ⟨60590801704578820927879607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40393867803052547285253071 60590801704578820927879607)
  ·
    refine ⟨90886202556868231391819411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60590801704578820927879607 90886202556868231391819411)
    ·
      refine ⟨136329303835302347087729117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90886202556868231391819411 136329303835302347087729117)
      ·
        refine ⟨51123488938238380157898419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136329303835302347087729117 51123488938238380157898419)
        ·
          refine ⟨76685233407357570236847629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51123488938238380157898419 76685233407357570236847629)
          ·
            refine ⟨28756962527759088838817861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76685233407357570236847629 28756962527759088838817861)
            ·
              refine ⟨5391930473954829157278349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28756962527759088838817861 5391930473954829157278349)
              ·
                refine ⟨2021973927733060933979381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5391930473954829157278349 2021973927733060933979381)
                ·
                  refine ⟨189560055724974462560567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2021973927733060933979381 189560055724974462560567)
                  ·
                    rfl

theorem cell22_1661251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 5].length) (baseStart_1661251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661251 prefixEnd_1661251 := by exact prefixLift 1661251
  have htrace : WordTrace (prefixWord ++ tailWord_1661251) baseStart_1661251 baseEnd_1661251 := by
    simpa [prefixWord, tailWord_1661251, baseEnd_1661251] using wordTrace_append hprefix tailTrace_1661251
  have hstable : (prefixWord ++ tailWord_1661251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661251).length < 2 ^ (prefixWord ++ tailWord_1661251).sum := by decide
  have hdescent : baseEnd_1661251 < baseStart_1661251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661278 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1661278 : Nat := 118140960795 + 1661278 * 2 ^ 59
def prefixEnd_1661278 : Nat := 4983230072969 + 3 ^ 40 * 1661278 * 2
def baseEnd_1661278 : Nat := 568689409826704317256619

theorem tailTrace_1661278 : CollatzResearch.WordTrace tailWord_1661278 prefixEnd_1661278 568689409826704317256619 := by
  unfold tailWord_1661278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7573973309435125567389061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40394524316987336359408325 7573973309435125567389061)
  ·
    refine ⟨1420119995519086043885449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7573973309435125567389061 1420119995519086043885449)
    ·
      refine ⟨1065089996639314532914087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1420119995519086043885449 1065089996639314532914087)
      ·
        refine ⟨1597634994958971799371131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065089996639314532914087 1597634994958971799371131)
        ·
          refine ⟨2396452492438457699056697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597634994958971799371131 2396452492438457699056697)
          ·
            refine ⟨1797339369328843274292523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396452492438457699056697 1797339369328843274292523)
            ·
              refine ⟨2696009053993264911438785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797339369328843274292523 2696009053993264911438785)
              ·
                refine ⟨2022006790494948683579089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696009053993264911438785 2022006790494948683579089)
                ·
                  refine ⟨1516505092871211512684317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2022006790494948683579089 1516505092871211512684317)
                  ·
                    refine ⟨568689409826704317256619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516505092871211512684317 568689409826704317256619)
                    ·
                      rfl

theorem cell22_1661278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1661278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661278 prefixEnd_1661278 := by exact prefixLift 1661278
  have htrace : WordTrace (prefixWord ++ tailWord_1661278) baseStart_1661278 baseEnd_1661278 := by
    simpa [prefixWord, tailWord_1661278, baseEnd_1661278] using wordTrace_append hprefix tailTrace_1661278
  have hstable : (prefixWord ++ tailWord_1661278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661278).length < 2 ^ (prefixWord ++ tailWord_1661278).sum := by decide
  have hdescent : baseEnd_1661278 < baseStart_1661278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661296 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_1661296 : Nat := 118140960795 + 1661296 * 2 ^ 59
def prefixEnd_1661296 : Nat := 4983230072969 + 3 ^ 40 * 1661296 * 2
def baseEnd_1661296 : Nat := 189565190531519423435521

theorem tailTrace_1661296 : CollatzResearch.WordTrace tailWord_1661296 prefixEnd_1661296 189565190531519423435521 := by
  unfold tailWord_1661296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30296221494707896806633871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40394961992943862408845161 30296221494707896806633871)
  ·
    refine ⟨45444332242061845209950807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30296221494707896806633871 45444332242061845209950807)
    ·
      refine ⟨68166498363092767814926211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45444332242061845209950807 68166498363092767814926211)
      ·
        refine ⟨102249747544639151722389317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68166498363092767814926211 102249747544639151722389317)
        ·
          refine ⟨19171827664619840947947997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102249747544639151722389317 19171827664619840947947997)
          ·
            refine ⟨7189435374232440355480499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19171827664619840947947997 7189435374232440355480499)
            ·
              refine ⟨10784153061348660533220749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189435374232440355480499 10784153061348660533220749)
              ·
                refine ⟨4044057398005747699957781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10784153061348660533220749 4044057398005747699957781)
                ·
                  refine ⟨189565190531519423435521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4044057398005747699957781 189565190531519423435521)
                  ·
                    rfl

theorem cell22_1661296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_1661296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661296 prefixEnd_1661296 := by exact prefixLift 1661296
  have htrace : WordTrace (prefixWord ++ tailWord_1661296) baseStart_1661296 baseEnd_1661296 := by
    simpa [prefixWord, tailWord_1661296, baseEnd_1661296] using wordTrace_append hprefix tailTrace_1661296
  have hstable : (prefixWord ++ tailWord_1661296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661296).length < 2 ^ (prefixWord ++ tailWord_1661296).sum := by decide
  have hdescent : baseEnd_1661296 < baseStart_1661296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661313 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 6]
def baseStart_1661313 : Nat := 118140960795 + 1661313 * 2 ^ 59
def prefixEnd_1661313 : Nat := 4983230072969 + 3 ^ 40 * 1661313 * 2
def baseEnd_1661313 : Nat := 189567130347325297543837

theorem tailTrace_1661313 : CollatzResearch.WordTrace tailWord_1661313 prefixEnd_1661313 189567130347325297543837 := by
  unfold tailWord_1661313
  simp only [CollatzResearch.WordTrace]
  refine ⟨60593063030354205516636593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40395375353569470344424395 60593063030354205516636593)
  ·
    refine ⟨45444797272765654137477445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60593063030354205516636593 45444797272765654137477445)
    ·
      refine ⟨8520899488643560150777021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45444797272765654137477445 8520899488643560150777021)
      ·
        refine ⟨3195337308241335056541383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8520899488643560150777021 3195337308241335056541383)
        ·
          refine ⟨4793005962362002584812075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195337308241335056541383 4793005962362002584812075)
          ·
            refine ⟨7189508943543003877218113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793005962362002584812075 7189508943543003877218113)
            ·
              refine ⟨5392131707657252907913585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7189508943543003877218113 5392131707657252907913585)
              ·
                refine ⟨4044098780742939680935189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392131707657252907913585 4044098780742939680935189)
                ·
                  refine ⟨189567130347325297543837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4044098780742939680935189 189567130347325297543837)
                  ·
                    rfl

theorem cell22_1661313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_1661313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661313 prefixEnd_1661313 := by exact prefixLift 1661313
  have htrace : WordTrace (prefixWord ++ tailWord_1661313) baseStart_1661313 baseEnd_1661313 := by
    simpa [prefixWord, tailWord_1661313, baseEnd_1661313] using wordTrace_append hprefix tailTrace_1661313
  have hstable : (prefixWord ++ tailWord_1661313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661313).length < 2 ^ (prefixWord ++ tailWord_1661313).sum := by decide
  have hdescent : baseEnd_1661313 < baseStart_1661313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661315 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 1, 4]
def baseStart_1661315 : Nat := 118140960795 + 1661315 * 2 ^ 59
def prefixEnd_1661315 : Nat := 4983230072969 + 3 ^ 40 * 1661315 * 2
def baseEnd_1661315 : Nat := 568702075682848554081505

theorem tailTrace_1661315 : CollatzResearch.WordTrace tailWord_1661315 prefixEnd_1661315 568702075682848554081505 := by
  unfold tailWord_1661315
  simp only [CollatzResearch.WordTrace]
  refine ⟨60593135976346959858209399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40395423984231306572139599 60593135976346959858209399)
  ·
    refine ⟨90889703964520439787314099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60593135976346959858209399 90889703964520439787314099)
    ·
      refine ⟨136334555946780659680971149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90889703964520439787314099 136334555946780659680971149)
      ·
        refine ⟨51125458480042747380364181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136334555946780659680971149 51125458480042747380364181)
        ·
          refine ⟨2396505866252003783454571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51125458480042747380364181 2396505866252003783454571)
          ·
            refine ⟨3594758799378005675181857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396505866252003783454571 3594758799378005675181857)
            ·
              refine ⟨2696069099533504256386393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594758799378005675181857 2696069099533504256386393)
              ·
                refine ⟨2022051824650128192289795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696069099533504256386393 2022051824650128192289795)
                ·
                  refine ⟨3033077736975192288434693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022051824650128192289795 3033077736975192288434693)
                  ·
                    refine ⟨568702075682848554081505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033077736975192288434693 568702075682848554081505)
                    ·
                      rfl

theorem cell22_1661315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 4].length) (baseStart_1661315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661315 prefixEnd_1661315 := by exact prefixLift 1661315
  have htrace : WordTrace (prefixWord ++ tailWord_1661315) baseStart_1661315 baseEnd_1661315 := by
    simpa [prefixWord, tailWord_1661315, baseEnd_1661315] using wordTrace_append hprefix tailTrace_1661315
  have hstable : (prefixWord ++ tailWord_1661315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661315).length < 2 ^ (prefixWord ++ tailWord_1661315).sum := by decide
  have hdescent : baseEnd_1661315 < baseStart_1661315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661343 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 2, 4]
def baseStart_1661343 : Nat := 118140960795 + 1661343 * 2 ^ 59
def prefixEnd_1661343 : Nat := 4983230072969 + 3 ^ 40 * 1661343 * 2
def baseEnd_1661343 : Nat := 568711660655065814381419

theorem tailTrace_1661343 : CollatzResearch.WordTrace tailWord_1661343 prefixEnd_1661343 568711660655065814381419 := by
  unfold tailWord_1661343
  simp only [CollatzResearch.WordTrace]
  refine ⟨60594157220245520640228683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40396104813497013760152455 60594157220245520640228683)
  ·
    refine ⟨90891235830368280960343025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60594157220245520640228683 90891235830368280960343025)
    ·
      refine ⟨68168426872776210720257269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90891235830368280960343025 68168426872776210720257269)
      ·
        refine ⟨6390790019322769755024119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68168426872776210720257269 6390790019322769755024119)
        ·
          refine ⟨9586185028984154632536179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6390790019322769755024119 9586185028984154632536179)
          ·
            refine ⟨14379277543476231948804269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9586185028984154632536179 14379277543476231948804269)
            ·
              refine ⟨5392229078803586980801601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14379277543476231948804269 5392229078803586980801601)
              ·
                refine ⟨4044171809102690235601201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392229078803586980801601 4044171809102690235601201)
                ·
                  refine ⟨3033128856827017676700901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044171809102690235601201 3033128856827017676700901)
                  ·
                    refine ⟨568711660655065814381419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033128856827017676700901 568711660655065814381419)
                    ·
                      rfl

theorem cell22_1661343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_1661343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661343 prefixEnd_1661343 := by exact prefixLift 1661343
  have htrace : WordTrace (prefixWord ++ tailWord_1661343) baseStart_1661343 baseEnd_1661343 := by
    simpa [prefixWord, tailWord_1661343, baseEnd_1661343] using wordTrace_append hprefix tailTrace_1661343
  have hstable : (prefixWord ++ tailWord_1661343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661343).length < 2 ^ (prefixWord ++ tailWord_1661343).sum := by decide
  have hdescent : baseEnd_1661343 < baseStart_1661343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661407 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 1, 3]
def baseStart_1661407 : Nat := 118140960795 + 1661407 * 2 ^ 59
def prefixEnd_1661407 : Nat := 4983230072969 + 3 ^ 40 * 1661407 * 2
def baseEnd_1661407 : Nat := 568733569162990980781223

theorem tailTrace_1661407 : CollatzResearch.WordTrace tailWord_1661407 prefixEnd_1661407 568733569162990980781223 := by
  unfold tailWord_1661407
  simp only [CollatzResearch.WordTrace]
  refine ⟨60596491492013659570558475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40397660994675773047038983 60596491492013659570558475)
  ·
    refine ⟨90894737238020489355837713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60596491492013659570558475 90894737238020489355837713)
    ·
      refine ⟨68171052928515367016878285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90894737238020489355837713 68171052928515367016878285)
      ·
        refine ⟨25564144848193262631329357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68171052928515367016878285 25564144848193262631329357)
        ·
          refine ⟨9586554318072473486748509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25564144848193262631329357 9586554318072473486748509)
          ·
            refine ⟨3594957869277177557530691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9586554318072473486748509 3594957869277177557530691)
            ·
              refine ⟨5392436803915766336296037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594957869277177557530691 5392436803915766336296037)
              ·
                refine ⟨1011081900734206188055507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5392436803915766336296037 1011081900734206188055507)
                ·
                  refine ⟨1516622851101309282083261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011081900734206188055507 1516622851101309282083261)
                  ·
                    refine ⟨568733569162990980781223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516622851101309282083261 568733569162990980781223)
                    ·
                      rfl

theorem cell22_1661407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 3].length) (baseStart_1661407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661407 prefixEnd_1661407 := by exact prefixLift 1661407
  have htrace : WordTrace (prefixWord ++ tailWord_1661407) baseStart_1661407 baseEnd_1661407 := by
    simpa [prefixWord, tailWord_1661407, baseEnd_1661407] using wordTrace_append hprefix tailTrace_1661407
  have hstable : (prefixWord ++ tailWord_1661407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661407).length < 2 ^ (prefixWord ++ tailWord_1661407).sum := by decide
  have hdescent : baseEnd_1661407 < baseStart_1661407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661418 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1661418 : Nat := 118140960795 + 1661418 * 2 ^ 59
def prefixEnd_1661418 : Nat := 4983230072969 + 3 ^ 40 * 1661418 * 2
def baseEnd_1661418 : Nat := 568737334687790618756189

theorem tailTrace_1661418 : CollatzResearch.WordTrace tailWord_1661418 prefixEnd_1661418 568737334687790618756189 := by
  unfold tailWord_1661418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149223173743452112302227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40397928463315872299472605 15149223173743452112302227)
  ·
    refine ⟨22723834760615178168453341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15149223173743452112302227 22723834760615178168453341)
    ·
      refine ⟨8521438035230691813170003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22723834760615178168453341 8521438035230691813170003)
      ·
        refine ⟨12782157052846037719755005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521438035230691813170003 12782157052846037719755005)
        ·
          refine ⟨4793308894817264144908127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12782157052846037719755005 4793308894817264144908127)
          ·
            refine ⟨7189963342225896217362191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793308894817264144908127 7189963342225896217362191)
            ·
              refine ⟨10784945013338844326043287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189963342225896217362191 10784945013338844326043287)
              ·
                refine ⟨16177417520008266489064931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784945013338844326043287 16177417520008266489064931)
                ·
                  refine ⟨24266126280012399733597397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16177417520008266489064931 24266126280012399733597397)
                  ·
                    refine ⟨568737334687790618756189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24266126280012399733597397 568737334687790618756189)
                    ·
                      rfl

theorem cell22_1661418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1661418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661418 prefixEnd_1661418 := by exact prefixLift 1661418
  have htrace : WordTrace (prefixWord ++ tailWord_1661418) baseStart_1661418 baseEnd_1661418 := by
    simpa [prefixWord, tailWord_1661418, baseEnd_1661418] using wordTrace_append hprefix tailTrace_1661418
  have hstable : (prefixWord ++ tailWord_1661418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661418).length < 2 ^ (prefixWord ++ tailWord_1661418).sum := by decide
  have hdescent : baseEnd_1661418 < baseStart_1661418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661433 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_1661433 : Nat := 118140960795 + 1661433 * 2 ^ 59
def prefixEnd_1661433 : Nat := 4983230072969 + 3 ^ 40 * 1661433 * 2
def baseEnd_1661433 : Nat := 568742469494335579631143

theorem tailTrace_1661433 : CollatzResearch.WordTrace tailWord_1661433 prefixEnd_1661433 568742469494335579631143 := by
  unfold tailWord_1661433
  simp only [CollatzResearch.WordTrace]
  refine ⟨60597439789919466011004953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40398293193279644007336635 60597439789919466011004953)
  ·
    refine ⟨45448079842439599508253715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60597439789919466011004953 45448079842439599508253715)
    ·
      refine ⟨68172119763659399262380573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45448079842439599508253715 68172119763659399262380573)
      ·
        refine ⟨25564544911372274723392715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68172119763659399262380573 25564544911372274723392715)
        ·
          refine ⟨38346817367058412085089073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25564544911372274723392715 38346817367058412085089073)
          ·
            refine ⟨28760113025293809063816805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38346817367058412085089073 28760113025293809063816805)
            ·
              refine ⟨5392521192242589199465651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28760113025293809063816805 5392521192242589199465651)
              ·
                refine ⟨8088781788363883799198477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392521192242589199465651 8088781788363883799198477)
                ·
                  refine ⟨3033293170636456424699429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8088781788363883799198477 3033293170636456424699429)
                  ·
                    refine ⟨568742469494335579631143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033293170636456424699429 568742469494335579631143)
                    ·
                      rfl

theorem cell22_1661433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_1661433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661433 prefixEnd_1661433 := by exact prefixLift 1661433
  have htrace : WordTrace (prefixWord ++ tailWord_1661433) baseStart_1661433 baseEnd_1661433 := by
    simpa [prefixWord, tailWord_1661433, baseEnd_1661433] using wordTrace_append hprefix tailTrace_1661433
  have hstable : (prefixWord ++ tailWord_1661433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661433).length < 2 ^ (prefixWord ++ tailWord_1661433).sum := by decide
  have hdescent : baseEnd_1661433 < baseStart_1661433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661450 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1661450 : Nat := 118140960795 + 1661450 * 2 ^ 59
def prefixEnd_1661450 : Nat := 4983230072969 + 3 ^ 40 * 1661450 * 2
def baseEnd_1661450 : Nat := 568748288941753201956091

theorem tailTrace_1661450 : CollatzResearch.WordTrace tailWord_1661450 prefixEnd_1661450 568748288941753201956091 := by
  unfold tailWord_1661450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15149514957714469478593451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40398706553905251942915869 15149514957714469478593451)
  ·
    refine ⟨22724272436571704217890177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15149514957714469478593451 22724272436571704217890177)
    ·
      refine ⟨17043204327428778163417633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22724272436571704217890177 17043204327428778163417633)
      ·
        refine ⟨12782403245571583622563225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17043204327428778163417633 12782403245571583622563225)
        ·
          refine ⟨9586802434178687716922419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12782403245571583622563225 9586802434178687716922419)
          ·
            refine ⟨14380203651268031575383629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9586802434178687716922419 14380203651268031575383629)
            ·
              refine ⟨5392576369225511840768861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14380203651268031575383629 5392576369225511840768861)
              ·
                refine ⟨2022216138459566940288323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5392576369225511840768861 2022216138459566940288323)
                ·
                  refine ⟨3033324207689350410432485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022216138459566940288323 3033324207689350410432485)
                  ·
                    refine ⟨568748288941753201956091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033324207689350410432485 568748288941753201956091)
                    ·
                      rfl

theorem cell22_1661450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1661450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661450 prefixEnd_1661450 := by exact prefixLift 1661450
  have htrace : WordTrace (prefixWord ++ tailWord_1661450) baseStart_1661450 baseEnd_1661450 := by
    simpa [prefixWord, tailWord_1661450, baseEnd_1661450] using wordTrace_append hprefix tailTrace_1661450
  have hstable : (prefixWord ++ tailWord_1661450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661450).length < 2 ^ (prefixWord ++ tailWord_1661450).sum := by decide
  have hdescent : baseEnd_1661450 < baseStart_1661450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661493 : List Nat := [1, 3, 3, 1, 1, 2, 3, 8]
def baseStart_1661493 : Nat := 118140960795 + 1661493 * 2 ^ 59
def prefixEnd_1661493 : Nat := 4983230072969 + 3 ^ 40 * 1661493 * 2
def baseEnd_1661493 : Nat := 63195889857835047014551

theorem tailTrace_1661493 : CollatzResearch.WordTrace tailWord_1661493 prefixEnd_1661493 63195889857835047014551 := by
  unfold tailWord_1661493
  simp only [CollatzResearch.WordTrace]
  refine ⟨60599628169702096258189133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40399752113134730838792755 60599628169702096258189133)
  ·
    refine ⟨22724860563638286096820925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60599628169702096258189133 22724860563638286096820925)
    ·
      refine ⟨8521822711364357286307847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22724860563638286096820925 8521822711364357286307847)
      ·
        refine ⟨12782734067046535929461771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521822711364357286307847 12782734067046535929461771)
        ·
          refine ⟨19174101100569803894192657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12782734067046535929461771 19174101100569803894192657)
          ·
            refine ⟨14380575825427352920644493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19174101100569803894192657 14380575825427352920644493)
            ·
              refine ⟨5392715934535257345241685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14380575825427352920644493 5392715934535257345241685)
              ·
                refine ⟨63195889857835047014551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5392715934535257345241685 63195889857835047014551)
                ·
                  rfl

theorem cell22_1661493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 8].length) (baseStart_1661493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661493 prefixEnd_1661493 := by exact prefixLift 1661493
  have htrace : WordTrace (prefixWord ++ tailWord_1661493) baseStart_1661493 baseEnd_1661493 := by
    simpa [prefixWord, tailWord_1661493, baseEnd_1661493] using wordTrace_append hprefix tailTrace_1661493
  have hstable : (prefixWord ++ tailWord_1661493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661493).length < 2 ^ (prefixWord ++ tailWord_1661493).sum := by decide
  have hdescent : baseEnd_1661493 < baseStart_1661493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661553 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1661553 : Nat := 118140960795 + 1661553 * 2 ^ 59
def prefixEnd_1661553 : Nat := 4983230072969 + 3 ^ 40 * 1661553 * 2
def baseEnd_1661553 : Nat := 568783547946695266630775

theorem tailTrace_1661553 : CollatzResearch.WordTrace tailWord_1661553 prefixEnd_1661553 568783547946695266630775 := by
  unfold tailWord_1661553
  simp only [CollatzResearch.WordTrace]
  refine ⟨60601816549484726505373313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40401211032989817670248875 60601816549484726505373313)
  ·
    refine ⟨45451362412113544879029985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60601816549484726505373313 45451362412113544879029985)
    ·
      refine ⟨34088521809085158659272489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45451362412113544879029985 34088521809085158659272489)
      ·
        refine ⟨25566391356813868994454367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34088521809085158659272489 25566391356813868994454367)
        ·
          refine ⟨38349587035220803491681551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25566391356813868994454367 38349587035220803491681551)
          ·
            refine ⟨57524380552831205237522327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38349587035220803491681551 57524380552831205237522327)
            ·
              refine ⟨86286570829246807856283491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57524380552831205237522327 86286570829246807856283491)
              ·
                refine ⟨129429856243870211784425237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86286570829246807856283491 129429856243870211784425237)
                ·
                  refine ⟨6067024511431416177394933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129429856243870211784425237 6067024511431416177394933)
                  ·
                    refine ⟨568783547946695266630775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6067024511431416177394933 568783547946695266630775)
                    ·
                      rfl

theorem cell22_1661553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1661553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661553 prefixEnd_1661553 := by exact prefixLift 1661553
  have htrace : WordTrace (prefixWord ++ tailWord_1661553) baseStart_1661553 baseEnd_1661553 := by
    simpa [prefixWord, tailWord_1661553, baseEnd_1661553] using wordTrace_append hprefix tailTrace_1661553
  have hstable : (prefixWord ++ tailWord_1661553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661553).length < 2 ^ (prefixWord ++ tailWord_1661553).sum := by decide
  have hdescent : baseEnd_1661553 < baseStart_1661553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661572 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1661572 : Nat := 118140960795 + 1661572 * 2 ^ 59
def prefixEnd_1661572 : Nat := 4983230072969 + 3 ^ 40 * 1661572 * 2
def baseEnd_1661572 : Nat := 189596684011661850135239

theorem tailTrace_1661572 : CollatzResearch.WordTrace tailWord_1661572 prefixEnd_1661572 189596684011661850135239 := by
  unfold tailWord_1661572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30301254768207946375157485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40401673024277261833543313 30301254768207946375157485)
  ·
    refine ⟨11362970538077979890684057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30301254768207946375157485 11362970538077979890684057)
    ·
      refine ⟨8522227903558484918013043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11362970538077979890684057 8522227903558484918013043)
      ·
        refine ⟨12783341855337727377019565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522227903558484918013043 12783341855337727377019565)
        ·
          refine ⟨4793753195751647766382337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12783341855337727377019565 4793753195751647766382337)
          ·
            refine ⟨3595314896813735824786753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4793753195751647766382337 3595314896813735824786753)
            ·
              refine ⟨2696486172610301868590065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595314896813735824786753 2696486172610301868590065)
              ·
                refine ⟨2022364629457726401442549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696486172610301868590065 2022364629457726401442549)
                ·
                  refine ⟨189596684011661850135239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2022364629457726401442549 189596684011661850135239)
                  ·
                    rfl

theorem cell22_1661572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1661572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661572 prefixEnd_1661572 := by exact prefixLift 1661572
  have htrace : WordTrace (prefixWord ++ tailWord_1661572) baseStart_1661572 baseEnd_1661572 := by
    simpa [prefixWord, tailWord_1661572, baseEnd_1661572] using wordTrace_append hprefix tailTrace_1661572
  have hstable : (prefixWord ++ tailWord_1661572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661572).length < 2 ^ (prefixWord ++ tailWord_1661572).sum := by decide
  have hdescent : baseEnd_1661572 < baseStart_1661572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661615 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1661615 : Nat := 118140960795 + 1661615 * 2 ^ 59
def prefixEnd_1661615 : Nat := 4983230072969 + 3 ^ 40 * 1661615 * 2
def baseEnd_1661615 : Nat := 568804771813747771580585

theorem tailTrace_1661615 : CollatzResearch.WordTrace tailWord_1661615 prefixEnd_1661615 568804771813747771580585 := by
  unfold tailWord_1661615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60604077875260111094130299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40402718583506740729420199 60604077875260111094130299)
  ·
    refine ⟨90906116812890166641195449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60604077875260111094130299 90906116812890166641195449)
    ·
      refine ⟨68179587609667624980896587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90906116812890166641195449 68179587609667624980896587)
      ·
        refine ⟨102269381414501437471344881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68179587609667624980896587 102269381414501437471344881)
        ·
          refine ⟨76702036060876078103508661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102269381414501437471344881 76702036060876078103508661)
          ·
            refine ⟨7190815880707132322203937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76702036060876078103508661 7190815880707132322203937)
            ·
              refine ⟨5393111910530349241652953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190815880707132322203937 5393111910530349241652953)
              ·
                refine ⟨4044833932897761931239715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393111910530349241652953 4044833932897761931239715)
                ·
                  refine ⟨6067250899346642896859573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044833932897761931239715 6067250899346642896859573)
                  ·
                    refine ⟨568804771813747771580585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6067250899346642896859573 568804771813747771580585)
                    ·
                      rfl

theorem cell22_1661615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1661615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661615 prefixEnd_1661615 := by exact prefixLift 1661615
  have htrace : WordTrace (prefixWord ++ tailWord_1661615) baseStart_1661615 baseEnd_1661615 := by
    simpa [prefixWord, tailWord_1661615, baseEnd_1661615] using wordTrace_append hprefix tailTrace_1661615
  have hstable : (prefixWord ++ tailWord_1661615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661615).length < 2 ^ (prefixWord ++ tailWord_1661615).sum := by decide
  have hdescent : baseEnd_1661615 < baseStart_1661615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661619 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 1, 4]
def baseStart_1661619 : Nat := 118140960795 + 1661619 * 2 ^ 59
def prefixEnd_1661619 : Nat := 4983230072969 + 3 ^ 40 * 1661619 * 2
def baseEnd_1661619 : Nat := 568806141095493094480573

theorem tailTrace_1661619 : CollatzResearch.WordTrace tailWord_1661619 prefixEnd_1661619 568806141095493094480573 := by
  unfold tailWord_1661619
  simp only [CollatzResearch.WordTrace]
  refine ⟨60604223767245619777275911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40402815844830413184850607 60604223767245619777275911)
  ·
    refine ⟨90906335650868429665913867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60604223767245619777275911 90906335650868429665913867)
    ·
      refine ⟨136359503476302644498870801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90906335650868429665913867 136359503476302644498870801)
      ·
        refine ⟨102269627607226983374153101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136359503476302644498870801 102269627607226983374153101)
        ·
          refine ⟨38351110352710118765307413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102269627607226983374153101 38351110352710118765307413)
          ·
            refine ⟨1797708297783286817123785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38351110352710118765307413 1797708297783286817123785)
            ·
              refine ⟨1348281223337465112842839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797708297783286817123785 1348281223337465112842839)
              ·
                refine ⟨2022421835006197669264259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348281223337465112842839 2022421835006197669264259)
                ·
                  refine ⟨3033632752509296503896389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022421835006197669264259 3033632752509296503896389)
                  ·
                    refine ⟨568806141095493094480573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033632752509296503896389 568806141095493094480573)
                    ·
                      rfl

theorem cell22_1661619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 4].length) (baseStart_1661619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661619 prefixEnd_1661619 := by exact prefixLift 1661619
  have htrace : WordTrace (prefixWord ++ tailWord_1661619) baseStart_1661619 baseEnd_1661619 := by
    simpa [prefixWord, tailWord_1661619, baseEnd_1661619] using wordTrace_append hprefix tailTrace_1661619
  have hstable : (prefixWord ++ tailWord_1661619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661619).length < 2 ^ (prefixWord ++ tailWord_1661619).sum := by decide
  have hdescent : baseEnd_1661619 < baseStart_1661619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661632 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_1661632 : Nat := 118140960795 + 1661632 * 2 ^ 59
def prefixEnd_1661632 : Nat := 4983230072969 + 3 ^ 40 * 1661632 * 2
def baseEnd_1661632 : Nat := 568810591261165393905533

theorem tailTrace_1661632 : CollatzResearch.WordTrace tailWord_1661632 prefixEnd_1661632 568810591261165393905533 := by
  unfold tailWord_1661632
  simp only [CollatzResearch.WordTrace]
  refine ⟨30302348958099261498749575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40403131944132348664999433 30302348958099261498749575)
  ·
    refine ⟨45453523437148892248124363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30302348958099261498749575 45453523437148892248124363)
    ·
      refine ⟨68180285155723338372186545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45453523437148892248124363 68180285155723338372186545)
      ·
        refine ⟨51135213866792503779139909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68180285155723338372186545 51135213866792503779139909)
        ·
          refine ⟨9587852600023594458588733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51135213866792503779139909 9587852600023594458588733)
          ·
            refine ⟨3595444725008847921970775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9587852600023594458588733 3595444725008847921970775)
            ·
              refine ⟨5393167087513271882956163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595444725008847921970775 5393167087513271882956163)
              ·
                refine ⟨8089750631269907824434245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393167087513271882956163 8089750631269907824434245)
                ·
                  refine ⟨1516828243363107717081421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8089750631269907824434245 1516828243363107717081421)
                  ·
                    refine ⟨568810591261165393905533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516828243363107717081421 568810591261165393905533)
                    ·
                      rfl

theorem cell22_1661632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_1661632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661632 prefixEnd_1661632 := by exact prefixLift 1661632
  have htrace : WordTrace (prefixWord ++ tailWord_1661632) baseStart_1661632 baseEnd_1661632 := by
    simpa [prefixWord, tailWord_1661632, baseEnd_1661632] using wordTrace_append hprefix tailTrace_1661632
  have hstable : (prefixWord ++ tailWord_1661632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661632).length < 2 ^ (prefixWord ++ tailWord_1661632).sum := by decide
  have hdescent : baseEnd_1661632 < baseStart_1661632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661649 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_1661649 : Nat := 118140960795 + 1661649 * 2 ^ 59
def prefixEnd_1661649 : Nat := 4983230072969 + 3 ^ 40 * 1661649 * 2
def baseEnd_1661649 : Nat := 568816410708583016230481

theorem tailTrace_1661649 : CollatzResearch.WordTrace tailWord_1661649 prefixEnd_1661649 568816410708583016230481 := by
  unfold tailWord_1661649
  simp only [CollatzResearch.WordTrace]
  refine ⟨60605317957136934900868001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40403545304757956600578667 60605317957136934900868001)
  ·
    refine ⟨45453988467852701175651001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60605317957136934900868001 45453988467852701175651001)
    ·
      refine ⟨34090491350889525881738251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45453988467852701175651001 34090491350889525881738251)
      ·
        refine ⟨51135737026334288822607377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34090491350889525881738251 51135737026334288822607377)
        ·
          refine ⟨38351802769750716616955533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51135737026334288822607377 38351802769750716616955533)
          ·
            refine ⟨14381926038656518731358325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38351802769750716616955533 14381926038656518731358325)
            ·
              refine ⟨1348305566124048631064843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14381926038656518731358325 1348305566124048631064843)
              ·
                refine ⟨2022458349186072946597265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348305566124048631064843 2022458349186072946597265)
                ·
                  refine ⟨1516843761889554709947949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2022458349186072946597265 1516843761889554709947949)
                  ·
                    refine ⟨568816410708583016230481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516843761889554709947949 568816410708583016230481)
                    ·
                      rfl

theorem cell22_1661649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_1661649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661649 prefixEnd_1661649 := by exact prefixLift 1661649
  have htrace : WordTrace (prefixWord ++ tailWord_1661649) baseStart_1661649 baseEnd_1661649 := by
    simpa [prefixWord, tailWord_1661649, baseEnd_1661649] using wordTrace_append hprefix tailTrace_1661649
  have hstable : (prefixWord ++ tailWord_1661649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661649).length < 2 ^ (prefixWord ++ tailWord_1661649).sum := by decide
  have hdescent : baseEnd_1661649 < baseStart_1661649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661685 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 4]
def baseStart_1661685 : Nat := 118140960795 + 1661685 * 2 ^ 59
def prefixEnd_1661685 : Nat := 4983230072969 + 3 ^ 40 * 1661685 * 2
def baseEnd_1661685 : Nat := 189609578081430307443457

theorem tailTrace_1661685 : CollatzResearch.WordTrace tailWord_1661685 prefixEnd_1661685 189609578081430307443457 := by
  unfold tailWord_1661685
  simp only [CollatzResearch.WordTrace]
  refine ⟨60606630985006513049178509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40404420656671008699452339 60606630985006513049178509)
  ·
    refine ⟨22727486619377442393441941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60606630985006513049178509 22727486619377442393441941)
    ·
      refine ⟨1065350935283317612192591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22727486619377442393441941 1065350935283317612192591)
      ·
        refine ⟨1598026402924976418288887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065350935283317612192591 1598026402924976418288887)
        ·
          refine ⟨2397039604387464627433331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598026402924976418288887 2397039604387464627433331)
          ·
            refine ⟨3595559406581196941149997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397039604387464627433331 3595559406581196941149997)
            ·
              refine ⟨1348334777467948852931249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3595559406581196941149997 1348334777467948852931249)
              ·
                refine ⟨1011251083100961639698437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348334777467948852931249 1011251083100961639698437)
                ·
                  refine ⟨189609578081430307443457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011251083100961639698437 189609578081430307443457)
                  ·
                    rfl

theorem cell22_1661685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_1661685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661685 prefixEnd_1661685 := by exact prefixLift 1661685
  have htrace : WordTrace (prefixWord ++ tailWord_1661685) baseStart_1661685 baseEnd_1661685 := by
    simpa [prefixWord, tailWord_1661685, baseEnd_1661685] using wordTrace_append hprefix tailTrace_1661685
  have hstable : (prefixWord ++ tailWord_1661685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661685).length < 2 ^ (prefixWord ++ tailWord_1661685).sum := by decide
  have hdescent : baseEnd_1661685 < baseStart_1661685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661690 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1661690 : Nat := 118140960795 + 1661690 * 2 ^ 59
def prefixEnd_1661690 : Nat := 4983230072969 + 3 ^ 40 * 1661690 * 2
def baseEnd_1661690 : Nat := 189610148615490858651785

theorem tailTrace_1661690 : CollatzResearch.WordTrace tailWord_1661690 prefixEnd_1661690 189610148615490858651785 := by
  unfold tailWord_1661690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151703337497099725777631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40404542233325599268740349 15151703337497099725777631)
  ·
    refine ⟨22727555006245649588666447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15151703337497099725777631 22727555006245649588666447)
    ·
      refine ⟨34091332509368474382999671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22727555006245649588666447 34091332509368474382999671)
      ·
        refine ⟨51136998764052711574499507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34091332509368474382999671 51136998764052711574499507)
        ·
          refine ⟨76705498146079067361749261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51136998764052711574499507 76705498146079067361749261)
          ·
            refine ⟨28764561804779650260655973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76705498146079067361749261 28764561804779650260655973)
            ·
              refine ⟨5393355338396184423872995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28764561804779650260655973 5393355338396184423872995)
              ·
                refine ⟨8090033007594276635809493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393355338396184423872995 8090033007594276635809493)
                ·
                  refine ⟨189610148615490858651785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8090033007594276635809493 189610148615490858651785)
                  ·
                    rfl

theorem cell22_1661690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1661690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661690 prefixEnd_1661690 := by exact prefixLift 1661690
  have htrace : WordTrace (prefixWord ++ tailWord_1661690) baseStart_1661690 baseEnd_1661690 := by
    simpa [prefixWord, tailWord_1661690, baseEnd_1661690] using wordTrace_append hprefix tailTrace_1661690
  have hstable : (prefixWord ++ tailWord_1661690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661690).length < 2 ^ (prefixWord ++ tailWord_1661690).sum := by decide
  have hdescent : baseEnd_1661690 < baseStart_1661690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661705 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_1661705 : Nat := 118140960795 + 1661705 * 2 ^ 59
def prefixEnd_1661705 : Nat := 4983230072969 + 3 ^ 40 * 1661705 * 2
def baseEnd_1661705 : Nat := 568835580653017536830309

theorem tailTrace_1661705 : CollatzResearch.WordTrace tailWord_1661705 prefixEnd_1661705 568835580653017536830309 := by
  unfold tailWord_1661705
  simp only [CollatzResearch.WordTrace]
  refine ⟨60607360444934056464906569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40404906963289370976604379 60607360444934056464906569)
  ·
    refine ⟨45455520333700542348679927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60607360444934056464906569 45455520333700542348679927)
    ·
      refine ⟨68183280500550813523019891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45455520333700542348679927 68183280500550813523019891)
      ·
        refine ⟨102274920750826220284529837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68183280500550813523019891 102274920750826220284529837)
        ·
          refine ⟨38353095281559832606698689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102274920750826220284529837 38353095281559832606698689)
          ·
            refine ⟨28764821461169874455024017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38353095281559832606698689 28764821461169874455024017)
            ·
              refine ⟨21573616095877405841268013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28764821461169874455024017 21573616095877405841268013)
              ·
                refine ⟨8090106035954027190475505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21573616095877405841268013 8090106035954027190475505)
                ·
                  refine ⟨6067579526965520392856629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8090106035954027190475505 6067579526965520392856629)
                  ·
                    refine ⟨568835580653017536830309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6067579526965520392856629 568835580653017536830309)
                    ·
                      rfl

theorem cell22_1661705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_1661705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661705 prefixEnd_1661705 := by exact prefixLift 1661705
  have htrace : WordTrace (prefixWord ++ tailWord_1661705) baseStart_1661705 baseEnd_1661705 := by
    simpa [prefixWord, tailWord_1661705, baseEnd_1661705] using wordTrace_append hprefix tailTrace_1661705
  have hstable : (prefixWord ++ tailWord_1661705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661705).length < 2 ^ (prefixWord ++ tailWord_1661705).sum := by decide
  have hdescent : baseEnd_1661705 < baseStart_1661705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661767 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1661767 : Nat := 118140960795 + 1661767 * 2 ^ 59
def prefixEnd_1661767 : Nat := 4983230072969 + 3 ^ 40 * 1661767 * 2
def baseEnd_1661767 : Nat := 568856804520070041780119

theorem tailTrace_1661767 : CollatzResearch.WordTrace tailWord_1661767 prefixEnd_1661767 568856804520070041780119 := by
  unfold tailWord_1661767
  simp only [CollatzResearch.WordTrace]
  refine ⟨60609621770709441053663555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40406414513806294035775703 60609621770709441053663555)
  ·
    refine ⟨90914432656064161580495333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60609621770709441053663555 90914432656064161580495333)
    ·
      refine ⟨17046456123012030296342875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90914432656064161580495333 17046456123012030296342875)
      ·
        refine ⟨25569684184518045444514313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17046456123012030296342875 25569684184518045444514313)
        ·
          refine ⟨19177263138388534083385735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25569684184518045444514313 19177263138388534083385735)
          ·
            refine ⟨28765894707582801125078603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177263138388534083385735 28765894707582801125078603)
            ·
              refine ⟨43148842061374201687617905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28765894707582801125078603 43148842061374201687617905)
              ·
                refine ⟨32361631546030651265713429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43148842061374201687617905 32361631546030651265713429)
                ·
                  refine ⟨1516951478720186778080317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32361631546030651265713429 1516951478720186778080317)
                  ·
                    refine ⟨568856804520070041780119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1516951478720186778080317 568856804520070041780119)
                    ·
                      rfl

theorem cell22_1661767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1661767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661767 prefixEnd_1661767 := by exact prefixLift 1661767
  have htrace : WordTrace (prefixWord ++ tailWord_1661767) baseStart_1661767 baseEnd_1661767 := by
    simpa [prefixWord, tailWord_1661767, baseEnd_1661767] using wordTrace_append hprefix tailTrace_1661767
  have hstable : (prefixWord ++ tailWord_1661767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661767).length < 2 ^ (prefixWord ++ tailWord_1661767).sum := by decide
  have hdescent : baseEnd_1661767 < baseStart_1661767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661788 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1661788 : Nat := 118140960795 + 1661788 * 2 ^ 59
def prefixEnd_1661788 : Nat := 4983230072969 + 3 ^ 40 * 1661788 * 2
def baseEnd_1661788 : Nat := 568863993249232987005055

theorem tailTrace_1661788 : CollatzResearch.WordTrace tailWord_1661788 prefixEnd_1661788 568863993249232987005055 := by
  unfold tailWord_1661788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305193851816680820089009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40406925135755574426785345 30305193851816680820089009)
  ·
    refine ⟨22728895388862510615066757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30305193851816680820089009 22728895388862510615066757)
    ·
      refine ⟨4261667885411720740325017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22728895388862510615066757 4261667885411720740325017)
      ·
        refine ⟨3196250914058790555243763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4261667885411720740325017 3196250914058790555243763)
        ·
          refine ⟨4794376371088185832865645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196250914058790555243763 4794376371088185832865645)
          ·
            refine ⟨1797891139158069687324617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4794376371088185832865645 1797891139158069687324617)
            ·
              refine ⟨1348418354368552265493463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797891139158069687324617 1348418354368552265493463)
              ·
                refine ⟨2022627531552828398240195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348418354368552265493463 2022627531552828398240195)
                ·
                  refine ⟨3033941297329242597360293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022627531552828398240195 3033941297329242597360293)
                  ·
                    refine ⟨568863993249232987005055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033941297329242597360293 568863993249232987005055)
                    ·
                      rfl

theorem cell22_1661788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1661788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661788 prefixEnd_1661788 := by exact prefixLift 1661788
  have htrace : WordTrace (prefixWord ++ tailWord_1661788) baseStart_1661788 baseEnd_1661788 := by
    simpa [prefixWord, tailWord_1661788, baseEnd_1661788] using wordTrace_append hprefix tailTrace_1661788
  have hstable : (prefixWord ++ tailWord_1661788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661788).length < 2 ^ (prefixWord ++ tailWord_1661788).sum := by decide
  have hdescent : baseEnd_1661788 < baseStart_1661788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661829 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_1661829 : Nat := 118140960795 + 1661829 * 2 ^ 59
def prefixEnd_1661829 : Nat := 4983230072969 + 3 ^ 40 * 1661829 * 2
def baseEnd_1661829 : Nat := 568878028387122546729929

theorem tailTrace_1661829 : CollatzResearch.WordTrace tailWord_1661829 prefixEnd_1661829 568878028387122546729929 := by
  unfold tailWord_1661829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60611883096484825642420541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40407922064323217094947027 60611883096484825642420541)
  ·
    refine ⟨22729456161181809615907703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60611883096484825642420541 22729456161181809615907703)
    ·
      refine ⟨34094184241772714423861555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729456161181809615907703 34094184241772714423861555)
      ·
        refine ⟨51141276362659071635792333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34094184241772714423861555 51141276362659071635792333)
        ·
          refine ⟨19177978635997151863422125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51141276362659071635792333 19177978635997151863422125)
          ·
            refine ⟨7191741988498931948783297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19177978635997151863422125 7191741988498931948783297)
            ·
              refine ⟨5393806491374198961587473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7191741988498931948783297 5393806491374198961587473)
              ·
                refine ⟨4045354868530649221190605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393806491374198961587473 4045354868530649221190605)
                ·
                  refine ⟨1517008075698993457946477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4045354868530649221190605 1517008075698993457946477)
                  ·
                    refine ⟨568878028387122546729929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517008075698993457946477 568878028387122546729929)
                    ·
                      rfl

theorem cell22_1661829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_1661829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661829 prefixEnd_1661829 := by exact prefixLift 1661829
  have htrace : WordTrace (prefixWord ++ tailWord_1661829) baseStart_1661829 baseEnd_1661829 := by
    simpa [prefixWord, tailWord_1661829, baseEnd_1661829] using wordTrace_append hprefix tailTrace_1661829
  have hstable : (prefixWord ++ tailWord_1661829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661829).length < 2 ^ (prefixWord ++ tailWord_1661829).sum := by decide
  have hdescent : baseEnd_1661829 < baseStart_1661829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661863 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1661863 : Nat := 118140960795 + 1661863 * 2 ^ 59
def prefixEnd_1661863 : Nat := 4983230072969 + 3 ^ 40 * 1661863 * 2
def baseEnd_1661863 : Nat := 568889667281957791379825

theorem tailTrace_1661863 : CollatzResearch.WordTrace tailWord_1661863 prefixEnd_1661863 568889667281957791379825 := by
  unfold tailWord_1661863
  simp only [CollatzResearch.WordTrace]
  refine ⟨60613123178361649449158243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40408748785574432966105495 60613123178361649449158243)
  ·
    refine ⟨90919684767542474173737365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60613123178361649449158243 90919684767542474173737365)
    ·
      refine ⟨4261860223478553476893939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90919684767542474173737365 4261860223478553476893939)
      ·
        refine ⟨6392790335217830215340909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261860223478553476893939 6392790335217830215340909)
        ·
          refine ⟨2397296375706686330752841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6392790335217830215340909 2397296375706686330752841)
          ·
            refine ⟨1797972281780014748064631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397296375706686330752841 1797972281780014748064631)
            ·
              refine ⟨2696958422670022122096947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797972281780014748064631 2696958422670022122096947)
              ·
                refine ⟨4045437634005033183145421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696958422670022122096947 4045437634005033183145421)
                ·
                  refine ⟨1517039112751887443679533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4045437634005033183145421 1517039112751887443679533)
                  ·
                    refine ⟨568889667281957791379825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517039112751887443679533 568889667281957791379825)
                    ·
                      rfl

theorem cell22_1661863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1661863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661863 prefixEnd_1661863 := by exact prefixLift 1661863
  have htrace : WordTrace (prefixWord ++ tailWord_1661863) baseStart_1661863 baseEnd_1661863 := by
    simpa [prefixWord, tailWord_1661863, baseEnd_1661863] using wordTrace_append hprefix tailTrace_1661863
  have hstable : (prefixWord ++ tailWord_1661863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661863).length < 2 ^ (prefixWord ++ tailWord_1661863).sum := by decide
  have hdescent : baseEnd_1661863 < baseStart_1661863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661904 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_1661904 : Nat := 118140960795 + 1661904 * 2 ^ 59
def prefixEnd_1661904 : Nat := 4983230072969 + 3 ^ 40 * 1661904 * 2
def baseEnd_1661904 : Nat := 189634567473282450368233

theorem tailTrace_1661904 : CollatzResearch.WordTrace tailWord_1661904 prefixEnd_1661904 189634567473282450368233 := by
  unfold tailWord_1661904
  simp only [CollatzResearch.WordTrace]
  refine ⟨30307309285606556725700383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40409745714142075634267177 30307309285606556725700383)
  ·
    refine ⟨45460963928409835088550575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30307309285606556725700383 45460963928409835088550575)
    ·
      refine ⟨68191445892614752632825863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45460963928409835088550575 68191445892614752632825863)
      ·
        refine ⟨102287168838922128949238795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68191445892614752632825863 102287168838922128949238795)
        ·
          refine ⟨153430753258383193423858193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102287168838922128949238795 153430753258383193423858193)
          ·
            refine ⟨115073064943787395067893645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153430753258383193423858193 115073064943787395067893645)
            ·
              refine ⟨43152399353920273150460117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115073064943787395067893645 43152399353920273150460117)
              ·
                refine ⟨1011384359857506401963909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43152399353920273150460117 1011384359857506401963909)
                ·
                  refine ⟨189634567473282450368233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011384359857506401963909 189634567473282450368233)
                  ·
                    rfl

theorem cell22_1661904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_1661904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1661904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1661904 prefixEnd_1661904 := by exact prefixLift 1661904
  have htrace : WordTrace (prefixWord ++ tailWord_1661904) baseStart_1661904 baseEnd_1661904 := by
    simpa [prefixWord, tailWord_1661904, baseEnd_1661904] using wordTrace_append hprefix tailTrace_1661904
  have hstable : (prefixWord ++ tailWord_1661904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661904).length < 2 ^ (prefixWord ++ tailWord_1661904).sum := by decide
  have hdescent : baseEnd_1661904 < baseStart_1661904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662058 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1662058 : Nat := 118140960795 + 1662058 * 2 ^ 59
def prefixEnd_1662058 : Nat := 4983230072969 + 3 ^ 40 * 1662058 * 2
def baseEnd_1662058 : Nat := 568956419767042282754227

theorem tailTrace_1662058 : CollatzResearch.WordTrace tailWord_1662058 prefixEnd_1662058 568956419767042282754227 := by
  unfold tailWord_1662058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155058853163799438126707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40413490275103465168337885 15155058853163799438126707)
  ·
    refine ⟨22732588279745699157190061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15155058853163799438126707 22732588279745699157190061)
    ·
      refine ⟨8524720604904637183946273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22732588279745699157190061 8524720604904637183946273)
      ·
        refine ⟨6393540453678477887959705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8524720604904637183946273 6393540453678477887959705)
        ·
          refine ⟨4795155340258858415969779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6393540453678477887959705 4795155340258858415969779)
          ·
            refine ⟨7192733010388287623954669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795155340258858415969779 7192733010388287623954669)
            ·
              refine ⟨2697274878895607858983001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7192733010388287623954669 2697274878895607858983001)
              ·
                refine ⟨2022956159171705894237251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697274878895607858983001 2022956159171705894237251)
                ·
                  refine ⟨3034434238757558841355877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022956159171705894237251 3034434238757558841355877)
                  ·
                    refine ⟨568956419767042282754227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3034434238757558841355877 568956419767042282754227)
                    ·
                      rfl

theorem cell22_1662058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1662058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662058 prefixEnd_1662058 := by exact prefixLift 1662058
  have htrace : WordTrace (prefixWord ++ tailWord_1662058) baseStart_1662058 baseEnd_1662058 := by
    simpa [prefixWord, tailWord_1662058, baseEnd_1662058] using wordTrace_append hprefix tailTrace_1662058
  have hstable : (prefixWord ++ tailWord_1662058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662058).length < 2 ^ (prefixWord ++ tailWord_1662058).sum := by decide
  have hdescent : baseEnd_1662058 < baseStart_1662058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662084 : List Nat := [2, 3, 2, 1, 2, 12]
def baseStart_1662084 : Nat := 118140960795 + 1662084 * 2 ^ 59
def prefixEnd_1662084 : Nat := 4983230072969 + 3 ^ 40 * 1662084 * 2
def baseEnd_1662084 : Nat := 7024263211091196069187

theorem tailTrace_1662084 : CollatzResearch.WordTrace tailWord_1662084 prefixEnd_1662084 7024263211091196069187 := by
  unfold tailWord_1662084
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310591855280502096476653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40414122473707336128635537 30310591855280502096476653)
  ·
    refine ⟨11366471945730188286178745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30310591855280502096476653 11366471945730188286178745)
    ·
      refine ⟨8524853959297641214634059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11366471945730188286178745 8524853959297641214634059)
      ·
        refine ⟨12787280938946461821951089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524853959297641214634059 12787280938946461821951089)
        ·
          refine ⟨9590460704209846366463317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12787280938946461821951089 9590460704209846366463317)
          ·
            refine ⟨7024263211091196069187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9590460704209846366463317 7024263211091196069187)
            ·
              rfl

theorem cell22_1662084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 12].length) (baseStart_1662084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662084 prefixEnd_1662084 := by exact prefixLift 1662084
  have htrace : WordTrace (prefixWord ++ tailWord_1662084) baseStart_1662084 baseEnd_1662084 := by
    simpa [prefixWord, tailWord_1662084, baseEnd_1662084] using wordTrace_append hprefix tailTrace_1662084
  have hstable : (prefixWord ++ tailWord_1662084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662084).length < 2 ^ (prefixWord ++ tailWord_1662084).sum := by decide
  have hdescent : baseEnd_1662084 < baseStart_1662084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662159 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1662159 : Nat := 118140960795 + 1662159 * 2 ^ 59
def prefixEnd_1662159 : Nat := 4983230072969 + 3 ^ 40 * 1662159 * 2
def baseEnd_1662159 : Nat := 568990994131111685978917

theorem tailTrace_1662159 : CollatzResearch.WordTrace tailWord_1662159 prefixEnd_1662159 568990994131111685978917 := by
  unfold tailWord_1662159
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623919185289292001933531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40415946123526194667955687 60623919185289292001933531)
  ·
    refine ⟨90935878777933938002900297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60623919185289292001933531 90935878777933938002900297)
    ·
      refine ⟨68201909083450453502175223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90935878777933938002900297 68201909083450453502175223)
      ·
        refine ⟨102302863625175680253262835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68201909083450453502175223 102302863625175680253262835)
        ·
          refine ⟨153454295437763520379894253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102302863625175680253262835 153454295437763520379894253)
          ·
            refine ⟨57545360789161320142460345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153454295437763520379894253 57545360789161320142460345)
            ·
              refine ⟨43159020591870990106845259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57545360789161320142460345 43159020591870990106845259)
              ·
                refine ⟨64738530887806485160267889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43159020591870990106845259 64738530887806485160267889)
                ·
                  refine ⟨48553898165854863870200917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64738530887806485160267889 48553898165854863870200917)
                  ·
                    refine ⟨568990994131111685978917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48553898165854863870200917 568990994131111685978917)
                    ·
                      rfl

theorem cell22_1662159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1662159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662159 prefixEnd_1662159 := by exact prefixLift 1662159
  have htrace : WordTrace (prefixWord ++ tailWord_1662159) baseStart_1662159 baseEnd_1662159 := by
    simpa [prefixWord, tailWord_1662159, baseEnd_1662159] using wordTrace_append hprefix tailTrace_1662159
  have hstable : (prefixWord ++ tailWord_1662159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662159).length < 2 ^ (prefixWord ++ tailWord_1662159).sum := by decide
  have hdescent : baseEnd_1662159 < baseStart_1662159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662236 : List Nat := [2, 2, 3, 1, 1, 1, 4, 8]
def baseStart_1662236 : Nat := 118140960795 + 1662236 * 2 ^ 59
def prefixEnd_1662236 : Nat := 4983230072969 + 3 ^ 40 * 1662236 * 2
def baseEnd_1662236 : Nat := 63224150311634350200409

theorem tailTrace_1662236 : CollatzResearch.WordTrace tailWord_1662236 prefixEnd_1662236 63224150311634350200409 := by
  unfold tailWord_1662236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30313363803005167076243281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40417818404006889434991041 30313363803005167076243281)
  ·
    refine ⟨22735022852253875307182461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30313363803005167076243281 22735022852253875307182461)
    ·
      refine ⟨8525633569595203240193423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22735022852253875307182461 8525633569595203240193423)
      ·
        refine ⟨12788450354392804860290135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8525633569595203240193423 12788450354392804860290135)
        ·
          refine ⟨19182675531589207290435203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12788450354392804860290135 19182675531589207290435203)
          ·
            refine ⟨28774013297383810935652805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19182675531589207290435203 28774013297383810935652805)
            ·
              refine ⟨5395127493259464550434901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28774013297383810935652805 5395127493259464550434901)
              ·
                refine ⟨63224150311634350200409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5395127493259464550434901 63224150311634350200409)
                ·
                  rfl

theorem cell22_1662236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_1662236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662236 prefixEnd_1662236 := by exact prefixLift 1662236
  have htrace : WordTrace (prefixWord ++ tailWord_1662236) baseStart_1662236 baseEnd_1662236 := by
    simpa [prefixWord, tailWord_1662236, baseEnd_1662236] using wordTrace_append hprefix tailTrace_1662236
  have hstable : (prefixWord ++ tailWord_1662236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662236).length < 2 ^ (prefixWord ++ tailWord_1662236).sum := by decide
  have hdescent : baseEnd_1662236 < baseStart_1662236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662253 : List Nat := [1, 5, 3, 1, 1, 11]
def baseStart_1662253 : Nat := 118140960795 + 1662253 * 2 ^ 59
def prefixEnd_1662253 : Nat := 4983230072969 + 3 ^ 40 * 1662253 * 2
def baseEnd_1662253 : Nat := 7024977435211441655909

theorem tailTrace_1662253 : CollatzResearch.WordTrace tailWord_1662253 prefixEnd_1662253 7024977435211441655909 := by
  unfold tailWord_1662253
  simp only [CollatzResearch.WordTrace]
  refine ⟨60627347646948746055855413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40418231764632497370570275 60627347646948746055855413)
  ·
    refine ⟨5683813841901444942736445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60627347646948746055855413 5683813841901444942736445)
    ·
      refine ⟨2131430190713041853526167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5683813841901444942736445 2131430190713041853526167)
      ·
        refine ⟨3197145286069562780289251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131430190713041853526167 3197145286069562780289251)
        ·
          refine ⟨4795717929104344170433877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197145286069562780289251 4795717929104344170433877)
          ·
            refine ⟨7024977435211441655909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4795717929104344170433877 7024977435211441655909)
            ·
              rfl

theorem cell22_1662253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 11].length) (baseStart_1662253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662253 prefixEnd_1662253 := by exact prefixLift 1662253
  have htrace : WordTrace (prefixWord ++ tailWord_1662253) baseStart_1662253 baseEnd_1662253 := by
    simpa [prefixWord, tailWord_1662253, baseEnd_1662253] using wordTrace_append hprefix tailTrace_1662253
  have hstable : (prefixWord ++ tailWord_1662253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662253).length < 2 ^ (prefixWord ++ tailWord_1662253).sum := by decide
  have hdescent : baseEnd_1662253 < baseStart_1662253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662266 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1662266 : Nat := 118140960795 + 1662266 * 2 ^ 59
def prefixEnd_1662266 : Nat := 4983230072969 + 3 ^ 40 * 1662266 * 2
def baseEnd_1662266 : Nat := 569027622417799073553589

theorem tailTrace_1662266 : CollatzResearch.WordTrace tailWord_1662266 prefixEnd_1662266 569027622417799073553589 := by
  unfold tailWord_1662266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156955448975412319019663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40418547863934432850719101 15156955448975412319019663)
  ·
    refine ⟨22735433173463118478529495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15156955448975412319019663 22735433173463118478529495)
    ·
      refine ⟨34103149760194677717794243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22735433173463118478529495 34103149760194677717794243)
      ·
        refine ⟨51154724640292016576691365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34103149760194677717794243 51154724640292016576691365)
        ·
          refine ⟨9591510870054753108129631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51154724640292016576691365 9591510870054753108129631)
          ·
            refine ⟨14387266305082129662194447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9591510870054753108129631 14387266305082129662194447)
            ·
              refine ⟨21580899457623194493291671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387266305082129662194447 21580899457623194493291671)
              ·
                refine ⟨32371349186434791739937507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21580899457623194493291671 32371349186434791739937507)
                ·
                  refine ⟨48557023779652187609906261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32371349186434791739937507 48557023779652187609906261)
                  ·
                    refine ⟨569027622417799073553589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48557023779652187609906261 569027622417799073553589)
                    ·
                      rfl

theorem cell22_1662266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1662266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662266 prefixEnd_1662266 := by exact prefixLift 1662266
  have htrace : WordTrace (prefixWord ++ tailWord_1662266) baseStart_1662266 baseEnd_1662266 := by
    simpa [prefixWord, tailWord_1662266, baseEnd_1662266] using wordTrace_append hprefix tailTrace_1662266
  have hstable : (prefixWord ++ tailWord_1662266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662266).length < 2 ^ (prefixWord ++ tailWord_1662266).sum := by decide
  have hdescent : baseEnd_1662266 < baseStart_1662266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662296 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_1662296 : Nat := 118140960795 + 1662296 * 2 ^ 59
def prefixEnd_1662296 : Nat := 4983230072969 + 3 ^ 40 * 1662296 * 2
def baseEnd_1662296 : Nat := 569037892030888995303497

theorem tailTrace_1662296 : CollatzResearch.WordTrace tailWord_1662296 prefixEnd_1662296 569037892030888995303497 := by
  unfold tailWord_1662296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30314457992896482199835371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40419277323861976266447161 30314457992896482199835371)
  ·
    refine ⟨45471686989344723299753057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30314457992896482199835371 45471686989344723299753057)
    ·
      refine ⟨34103765242008542474814793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45471686989344723299753057 34103765242008542474814793)
      ·
        refine ⟨25577823931506406856111095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34103765242008542474814793 25577823931506406856111095)
        ·
          refine ⟨38366735897259610284166643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25577823931506406856111095 38366735897259610284166643)
          ·
            refine ⟨57550103845889415426249965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38366735897259610284166643 57550103845889415426249965)
            ·
              refine ⟨21581288942208530784843737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57550103845889415426249965 21581288942208530784843737)
              ·
                refine ⟨16185966706656398088632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21581288942208530784843737 16185966706656398088632803)
                ·
                  refine ⟨24278950059984597132949205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16185966706656398088632803 24278950059984597132949205)
                  ·
                    refine ⟨569037892030888995303497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24278950059984597132949205 569037892030888995303497)
                    ·
                      rfl

theorem cell22_1662296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_1662296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662296 prefixEnd_1662296 := by exact prefixLift 1662296
  have htrace : WordTrace (prefixWord ++ tailWord_1662296) baseStart_1662296 baseEnd_1662296 := by
    simpa [prefixWord, tailWord_1662296, baseEnd_1662296] using wordTrace_append hprefix tailTrace_1662296
  have hstable : (prefixWord ++ tailWord_1662296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662296).length < 2 ^ (prefixWord ++ tailWord_1662296).sum := by decide
  have hdescent : baseEnd_1662296 < baseStart_1662296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662343 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 6]
def baseStart_1662343 : Nat := 118140960795 + 1662343 * 2 ^ 59
def prefixEnd_1662343 : Nat := 4983230072969 + 3 ^ 40 * 1662343 * 2
def baseEnd_1662343 : Nat := 189684660363798846459451

theorem tailTrace_1662343 : CollatzResearch.WordTrace tailWord_1662343 prefixEnd_1662343 189684660363798846459451 := by
  unfold tailWord_1662343
  simp only [CollatzResearch.WordTrace]
  refine ⟨60630630216622691426631683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40420420144415127617754455 60630630216622691426631683)
  ·
    refine ⟨90945945324934037139947525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60630630216622691426631683 90945945324934037139947525)
    ·
      refine ⟨17052364748425131963740161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90945945324934037139947525 17052364748425131963740161)
      ·
        refine ⟨12789273561318848972805121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17052364748425131963740161 12789273561318848972805121)
        ·
          refine ⟨9591955170989136729603841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12789273561318848972805121 9591955170989136729603841)
          ·
            refine ⟨7193966378241852547202881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9591955170989136729603841 7193966378241852547202881)
            ·
              refine ⟨5395474783681389410402161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7193966378241852547202881 5395474783681389410402161)
              ·
                refine ⟨4046606087761042057801621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395474783681389410402161 4046606087761042057801621)
                ·
                  refine ⟨189684660363798846459451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4046606087761042057801621 189684660363798846459451)
                  ·
                    rfl

theorem cell22_1662343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_1662343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662343 prefixEnd_1662343 := by exact prefixLift 1662343
  have htrace : WordTrace (prefixWord ++ tailWord_1662343) baseStart_1662343 baseEnd_1662343 := by
    simpa [prefixWord, tailWord_1662343, baseEnd_1662343] using wordTrace_append hprefix tailTrace_1662343
  have hstable : (prefixWord ++ tailWord_1662343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662343).length < 2 ^ (prefixWord ++ tailWord_1662343).sum := by decide
  have hdescent : baseEnd_1662343 < baseStart_1662343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662375 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1662375 : Nat := 118140960795 + 1662375 * 2 ^ 59
def prefixEnd_1662375 : Nat := 4983230072969 + 3 ^ 40 * 1662375 * 2
def baseEnd_1662375 : Nat := 569064935345359122578255

theorem tailTrace_1662375 : CollatzResearch.WordTrace tailWord_1662375 prefixEnd_1662375 569064935345359122578255 := by
  unfold tailWord_1662375
  simp only [CollatzResearch.WordTrace]
  refine ⟨60631797352506760891796579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40421198235004507261197719 60631797352506760891796579)
  ·
    refine ⟨90947696028760141337694869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60631797352506760891796579 90947696028760141337694869)
    ·
      refine ⟨4263173251348131625204447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90947696028760141337694869 4263173251348131625204447)
      ·
        refine ⟨6394759877022197437806671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263173251348131625204447 6394759877022197437806671)
        ·
          refine ⟨9592139815533296156710007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6394759877022197437806671 9592139815533296156710007)
          ·
            refine ⟨14388209723299944235065011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592139815533296156710007 14388209723299944235065011)
            ·
              refine ⟨21582314584949916352597517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14388209723299944235065011 21582314584949916352597517)
              ·
                refine ⟨8093367969356218632224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21582314584949916352597517 8093367969356218632224069)
                ·
                  refine ⟨1517506494254290993542013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8093367969356218632224069 1517506494254290993542013)
                  ·
                    refine ⟨569064935345359122578255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517506494254290993542013 569064935345359122578255)
                    ·
                      rfl

theorem cell22_1662375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1662375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662375 prefixEnd_1662375 := by exact prefixLift 1662375
  have htrace : WordTrace (prefixWord ++ tailWord_1662375) baseStart_1662375 baseEnd_1662375 := by
    simpa [prefixWord, tailWord_1662375, baseEnd_1662375] using wordTrace_append hprefix tailTrace_1662375
  have hstable : (prefixWord ++ tailWord_1662375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662375).length < 2 ^ (prefixWord ++ tailWord_1662375).sum := by decide
  have hdescent : baseEnd_1662375 < baseStart_1662375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662392 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_1662392 : Nat := 118140960795 + 1662392 * 2 ^ 59
def prefixEnd_1662392 : Nat := 4983230072969 + 3 ^ 40 * 1662392 * 2
def baseEnd_1662392 : Nat := 569070754792776744903203

theorem tailTrace_1662392 : CollatzResearch.WordTrace tailWord_1662392 prefixEnd_1662392 569070754792776744903203 := by
  unfold tailWord_1662392
  simp only [CollatzResearch.WordTrace]
  refine ⟨30316208696722586397582715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40421611595630115196776953 30316208696722586397582715)
  ·
    refine ⟨45474313045083879596374073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30316208696722586397582715 45474313045083879596374073)
    ·
      refine ⟨34105734783812909697280555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45474313045083879596374073 34105734783812909697280555)
      ·
        refine ⟨51158602175719364545920833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34105734783812909697280555 51158602175719364545920833)
        ·
          refine ⟨38368951631789523409440625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51158602175719364545920833 38368951631789523409440625)
          ·
            refine ⟨28776713723842142557080469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38368951631789523409440625 28776713723842142557080469)
            ·
              refine ⟨1348908455805100432363147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28776713723842142557080469 1348908455805100432363147)
              ·
                refine ⟨2023362683707650648544721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348908455805100432363147 2023362683707650648544721)
                ·
                  refine ⟨1517522012780737986408541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2023362683707650648544721 1517522012780737986408541)
                  ·
                    refine ⟨569070754792776744903203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517522012780737986408541 569070754792776744903203)
                    ·
                      rfl

theorem cell22_1662392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_1662392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662392 prefixEnd_1662392 := by exact prefixLift 1662392
  have htrace : WordTrace (prefixWord ++ tailWord_1662392) baseStart_1662392 baseEnd_1662392 := by
    simpa [prefixWord, tailWord_1662392, baseEnd_1662392] using wordTrace_append hprefix tailTrace_1662392
  have hstable : (prefixWord ++ tailWord_1662392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662392).length < 2 ^ (prefixWord ++ tailWord_1662392).sum := by decide
  have hdescent : baseEnd_1662392 < baseStart_1662392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662448 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_1662448 : Nat := 118140960795 + 1662448 * 2 ^ 59
def prefixEnd_1662448 : Nat := 4983230072969 + 3 ^ 40 * 1662448 * 2
def baseEnd_1662448 : Nat := 569089924737211265503031

theorem tailTrace_1662448 : CollatzResearch.WordTrace tailWord_1662448 prefixEnd_1662448 569089924737211265503031 := by
  unfold tailWord_1662448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30317229940621147179601999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40422973254161529572802665 30317229940621147179601999)
  ·
    refine ⟨45475844910931720769402999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30317229940621147179601999 45475844910931720769402999)
    ·
      refine ⟨68213767366397581154104499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45475844910931720769402999 68213767366397581154104499)
      ·
        refine ⟨102320651049596371731156749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68213767366397581154104499 102320651049596371731156749)
        ·
          refine ⟨38370244143598639399183781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102320651049596371731156749 38370244143598639399183781)
          ·
            refine ⟨7194420776924744887346959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38370244143598639399183781 7194420776924744887346959)
            ·
              refine ⟨10791631165387117331020439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7194420776924744887346959 10791631165387117331020439)
              ·
                refine ⟨16187446748080675996530659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10791631165387117331020439 16187446748080675996530659)
                ·
                  refine ⟨24281170122121013994795989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16187446748080675996530659 24281170122121013994795989)
                  ·
                    refine ⟨569089924737211265503031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24281170122121013994795989 569089924737211265503031)
                    ·
                      rfl

theorem cell22_1662448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_1662448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662448 prefixEnd_1662448 := by exact prefixLift 1662448
  have htrace : WordTrace (prefixWord ++ tailWord_1662448) baseStart_1662448 baseEnd_1662448 := by
    simpa [prefixWord, tailWord_1662448, baseEnd_1662448] using wordTrace_append hprefix tailTrace_1662448
  have hstable : (prefixWord ++ tailWord_1662448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662448).length < 2 ^ (prefixWord ++ tailWord_1662448).sum := by decide
  have hdescent : baseEnd_1662448 < baseStart_1662448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662540 : List Nat := [2, 2, 1, 3, 1, 5, 8]
def baseStart_1662540 : Nat := 118140960795 + 1662540 * 2 ^ 59
def prefixEnd_1662540 : Nat := 4983230072969 + 3 ^ 40 * 1662540 * 2
def baseEnd_1662540 : Nat := 21078571045087173785287

theorem tailTrace_1662540 : CollatzResearch.WordTrace tailWord_1662540 prefixEnd_1662540 21078571045087173785287 := by
  unfold tailWord_1662540
  simp only [CollatzResearch.WordTrace]
  refine ⟨30318907698454497035776537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40425210264605996047702049 30318907698454497035776537)
  ·
    refine ⟨22739180773840872776832403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30318907698454497035776537 22739180773840872776832403)
    ·
      refine ⟨34108771160761309165248605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22739180773840872776832403 34108771160761309165248605)
      ·
        refine ⟨12790789185285490936968227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34108771160761309165248605 12790789185285490936968227)
        ·
          refine ⟨19186183777928236405452341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12790789185285490936968227 19186183777928236405452341)
          ·
            refine ⟨1798704729180772163011157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19186183777928236405452341 1798704729180772163011157)
            ·
              refine ⟨21078571045087173785287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1798704729180772163011157 21078571045087173785287)
              ·
                rfl

theorem cell22_1662540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 8].length) (baseStart_1662540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662540 prefixEnd_1662540 := by exact prefixLift 1662540
  have htrace : WordTrace (prefixWord ++ tailWord_1662540) baseStart_1662540 baseEnd_1662540 := by
    simpa [prefixWord, tailWord_1662540, baseEnd_1662540] using wordTrace_append hprefix tailTrace_1662540
  have hstable : (prefixWord ++ tailWord_1662540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662540).length < 2 ^ (prefixWord ++ tailWord_1662540).sum := by decide
  have hdescent : baseEnd_1662540 < baseStart_1662540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662602 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_1662602 : Nat := 118140960795 + 1662602 * 2 ^ 59
def prefixEnd_1662602 : Nat := 4983230072969 + 3 ^ 40 * 1662602 * 2
def baseEnd_1662602 : Nat := 189714214028135399050853

theorem tailTrace_1662602 : CollatzResearch.WordTrace tailWord_1662602 prefixEnd_1662602 189714214028135399050853 := by
  unfold tailWord_1662602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15160019180671094665077515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40426717815122919106873373 15160019180671094665077515)
  ·
    refine ⟨22740028771006641997616273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15160019180671094665077515 22740028771006641997616273)
    ·
      refine ⟨17055021578254981498212205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22740028771006641997616273 17055021578254981498212205)
      ·
        refine ⟨6395633091845618061829577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17055021578254981498212205 6395633091845618061829577)
        ·
          refine ⟨4796724818884213546372183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6395633091845618061829577 4796724818884213546372183)
          ·
            refine ⟨7195087228326320319558275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796724818884213546372183 7195087228326320319558275)
            ·
              refine ⟨10792630842489480479337413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7195087228326320319558275 10792630842489480479337413)
              ·
                refine ⟨2023618282966777589875765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10792630842489480479337413 2023618282966777589875765)
                ·
                  refine ⟨189714214028135399050853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2023618282966777589875765 189714214028135399050853)
                  ·
                    rfl

theorem cell22_1662602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_1662602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662602 prefixEnd_1662602 := by exact prefixLift 1662602
  have htrace : WordTrace (prefixWord ++ tailWord_1662602) baseStart_1662602 baseEnd_1662602 := by
    simpa [prefixWord, tailWord_1662602, baseEnd_1662602] using wordTrace_append hprefix tailTrace_1662602
  have hstable : (prefixWord ++ tailWord_1662602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662602).length < 2 ^ (prefixWord ++ tailWord_1662602).sum := by decide
  have hdescent : baseEnd_1662602 < baseStart_1662602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662606 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_1662606 : Nat := 118140960795 + 1662606 * 2 ^ 59
def prefixEnd_1662606 : Nat := 4983230072969 + 3 ^ 40 * 1662606 * 2
def baseEnd_1662606 : Nat := 569144011366151520052547

theorem tailTrace_1662606 : CollatzResearch.WordTrace tailWord_1662606 prefixEnd_1662606 569144011366151520052547 := by
  unfold tailWord_1662606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580027826833735917931959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40426815076446591562303781 7580027826833735917931959)
  ·
    refine ⟨11370041740250603876897939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580027826833735917931959 11370041740250603876897939)
    ·
      refine ⟨17055062610375905815346909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11370041740250603876897939 17055062610375905815346909)
      ·
        refine ⟨6395648478890964680755091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17055062610375905815346909 6395648478890964680755091)
        ·
          refine ⟨9593472718336447021132637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395648478890964680755091 9593472718336447021132637)
          ·
            refine ⟨3597552269376167632924739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9593472718336447021132637 3597552269376167632924739)
            ·
              refine ⟨5396328404064251449387109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597552269376167632924739 5396328404064251449387109)
              ·
                refine ⟨1011811575762047146760083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5396328404064251449387109 1011811575762047146760083)
                ·
                  refine ⟨1517717363643070720140125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011811575762047146760083 1517717363643070720140125)
                  ·
                    refine ⟨569144011366151520052547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517717363643070720140125 569144011366151520052547)
                    ·
                      rfl

theorem cell22_1662606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_1662606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662606 prefixEnd_1662606 := by exact prefixLift 1662606
  have htrace : WordTrace (prefixWord ++ tailWord_1662606) baseStart_1662606 baseEnd_1662606 := by
    simpa [prefixWord, tailWord_1662606, baseEnd_1662606] using wordTrace_append hprefix tailTrace_1662606
  have hstable : (prefixWord ++ tailWord_1662606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662606).length < 2 ^ (prefixWord ++ tailWord_1662606).sum := by decide
  have hdescent : baseEnd_1662606 < baseStart_1662606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662649 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_1662649 : Nat := 118140960795 + 1662649 * 2 ^ 59
def prefixEnd_1662649 : Nat := 4983230072969 + 3 ^ 40 * 1662649 * 2
def baseEnd_1662649 : Nat := 569158731144913741227415

theorem tailTrace_1662649 : CollatzResearch.WordTrace tailWord_1662649 prefixEnd_1662649 569158731144913741227415 := by
  unfold tailWord_1662649
  simp only [CollatzResearch.WordTrace]
  refine ⟨60641790953514105687271001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40427860635676070458180667 60641790953514105687271001)
  ·
    refine ⟨45481343215135579265453251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60641790953514105687271001 45481343215135579265453251)
    ·
      refine ⟨68222014822703368898179877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45481343215135579265453251 68222014822703368898179877)
      ·
        refine ⟨12791627779256881668408727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68222014822703368898179877 12791627779256881668408727)
        ·
          refine ⟨19187441668885322502613091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791627779256881668408727 19187441668885322502613091)
          ·
            refine ⟨28781162503327983753919637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19187441668885322502613091 28781162503327983753919637)
            ·
              refine ⟨1349116992343499238464983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28781162503327983753919637 1349116992343499238464983)
              ·
                refine ⟨2023675488515248857697475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349116992343499238464983 2023675488515248857697475)
                ·
                  refine ⟨3035513232772873286546213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023675488515248857697475 3035513232772873286546213)
                  ·
                    refine ⟨569158731144913741227415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035513232772873286546213 569158731144913741227415)
                    ·
                      rfl

theorem cell22_1662649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_1662649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662649 prefixEnd_1662649 := by exact prefixLift 1662649
  have htrace : WordTrace (prefixWord ++ tailWord_1662649) baseStart_1662649 baseEnd_1662649 := by
    simpa [prefixWord, tailWord_1662649, baseEnd_1662649] using wordTrace_append hprefix tailTrace_1662649
  have hstable : (prefixWord ++ tailWord_1662649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662649).length < 2 ^ (prefixWord ++ tailWord_1662649).sum := by decide
  have hdescent : baseEnd_1662649 < baseStart_1662649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662707 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 5, 3]
def baseStart_1662707 : Nat := 118140960795 + 1662707 * 2 ^ 59
def prefixEnd_1662707 : Nat := 4983230072969 + 3 ^ 40 * 1662707 * 2
def baseEnd_1662707 : Nat := 569178585730220923277237

theorem tailTrace_1662707 : CollatzResearch.WordTrace tailWord_1662707 prefixEnd_1662707 569178585730220923277237 := by
  unfold tailWord_1662707
  simp only [CollatzResearch.WordTrace]
  refine ⟨60643906387303981592882375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40429270924869321061921583 60643906387303981592882375)
  ·
    refine ⟨90965859580955972389323563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60643906387303981592882375 90965859580955972389323563)
    ·
      refine ⟨136448789371433958583985345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90965859580955972389323563 136448789371433958583985345)
      ·
        refine ⟨102336592028575468937989009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136448789371433958583985345 102336592028575468937989009)
        ·
          refine ⟨76752444021431601703491757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102336592028575468937989009 76752444021431601703491757)
          ·
            refine ⟨28782166508036850638809409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76752444021431601703491757 28782166508036850638809409)
            ·
              refine ⟨21586624881027637979107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28782166508036850638809409 21586624881027637979107057)
              ·
                refine ⟨16189968660770728484330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21586624881027637979107057 16189968660770728484330293)
                ·
                  refine ⟨1517809561947255795405965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16189968660770728484330293 1517809561947255795405965)
                  ·
                    refine ⟨569178585730220923277237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517809561947255795405965 569178585730220923277237)
                    ·
                      rfl

theorem cell22_1662707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 3].length) (baseStart_1662707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662707 prefixEnd_1662707 := by exact prefixLift 1662707
  have htrace : WordTrace (prefixWord ++ tailWord_1662707) baseStart_1662707 baseEnd_1662707 := by
    simpa [prefixWord, tailWord_1662707, baseEnd_1662707] using wordTrace_append hprefix tailTrace_1662707
  have hstable : (prefixWord ++ tailWord_1662707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662707).length < 2 ^ (prefixWord ++ tailWord_1662707).sum := by decide
  have hdescent : baseEnd_1662707 < baseStart_1662707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662816 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_1662816 : Nat := 118140960795 + 1662816 * 2 ^ 59
def prefixEnd_1662816 : Nat := 4983230072969 + 3 ^ 40 * 1662816 * 2
def baseEnd_1662816 : Nat := 189738632885926990767301

theorem tailTrace_1662816 : CollatzResearch.WordTrace tailWord_1662816 prefixEnd_1662816 189738632885926990767301 := by
  unfold tailWord_1662816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30323940971954546604300151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40431921295939395472400201 30323940971954546604300151)
  ·
    refine ⟨45485911457931819906450227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30323940971954546604300151 45485911457931819906450227)
    ·
      refine ⟨68228867186897729859675341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45485911457931819906450227 68228867186897729859675341)
      ·
        refine ⟨25585825195086648697378253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68228867186897729859675341 25585825195086648697378253)
        ·
          refine ⟨9594684448157493261516845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25585825195086648697378253 9594684448157493261516845)
          ·
            refine ⟨3598006668059059973068817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9594684448157493261516845 3598006668059059973068817)
            ·
              refine ⟨2698505001044294979801613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3598006668059059973068817 2698505001044294979801613)
              ·
                refine ⟨1011939375391610617425605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2698505001044294979801613 1011939375391610617425605)
                ·
                  refine ⟨189738632885926990767301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011939375391610617425605 189738632885926990767301)
                  ·
                    rfl

theorem cell22_1662816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_1662816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662816 prefixEnd_1662816 := by exact prefixLift 1662816
  have htrace : WordTrace (prefixWord ++ tailWord_1662816) baseStart_1662816 baseEnd_1662816 := by
    simpa [prefixWord, tailWord_1662816, baseEnd_1662816] using wordTrace_append hprefix tailTrace_1662816
  have hstable : (prefixWord ++ tailWord_1662816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662816).length < 2 ^ (prefixWord ++ tailWord_1662816).sum := by decide
  have hdescent : baseEnd_1662816 < baseStart_1662816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662818 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1662818 : Nat := 118140960795 + 1662818 * 2 ^ 59
def prefixEnd_1662818 : Nat := 4983230072969 + 3 ^ 40 * 1662818 * 2
def baseEnd_1662818 : Nat := 569216583298653633751897

theorem tailTrace_1662818 : CollatzResearch.WordTrace tailWord_1662818 prefixEnd_1662818 569216583298653633751897 := by
  unfold tailWord_1662818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161988722475461887543277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40431969926601231700115405 15161988722475461887543277)
  ·
    refine ⟨5685745770928298207828729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15161988722475461887543277 5685745770928298207828729)
    ·
      refine ⟨4264309328196223655871547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5685745770928298207828729 4264309328196223655871547)
      ·
        refine ⟨6396463992294335483807321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264309328196223655871547 6396463992294335483807321)
        ·
          refine ⟨4797347994220751612855491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6396463992294335483807321 4797347994220751612855491)
          ·
            refine ⟨7196021991331127419283237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797347994220751612855491 7196021991331127419283237)
            ·
              refine ⟨1349254123374586391115607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7196021991331127419283237 1349254123374586391115607)
              ·
                refine ⟨2023881185061879586673411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349254123374586391115607 2023881185061879586673411)
                ·
                  refine ⟨3035821777592819380010117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023881185061879586673411 3035821777592819380010117)
                  ·
                    refine ⟨569216583298653633751897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035821777592819380010117 569216583298653633751897)
                    ·
                      rfl

theorem cell22_1662818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1662818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662818 prefixEnd_1662818 := by exact prefixLift 1662818
  have htrace : WordTrace (prefixWord ++ tailWord_1662818) baseStart_1662818 baseEnd_1662818 := by
    simpa [prefixWord, tailWord_1662818, baseEnd_1662818] using wordTrace_append hprefix tailTrace_1662818
  have hstable : (prefixWord ++ tailWord_1662818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662818).length < 2 ^ (prefixWord ++ tailWord_1662818).sum := by decide
  have hdescent : baseEnd_1662818 < baseStart_1662818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662829 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1662829 : Nat := 118140960795 + 1662829 * 2 ^ 59
def prefixEnd_1662829 : Nat := 4983230072969 + 3 ^ 40 * 1662829 * 2
def baseEnd_1662829 : Nat := 569220348823453271726863

theorem tailTrace_1662829 : CollatzResearch.WordTrace tailWord_1662829 prefixEnd_1662829 569220348823453271726863 := by
  unfold tailWord_1662829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60648356092861996428823541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40432237395241330952549027 60648356092861996428823541)
  ·
    refine ⟨5685783383705812165202207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60648356092861996428823541 5685783383705812165202207)
    ·
      refine ⟨8528675075558718247803311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5685783383705812165202207 8528675075558718247803311)
      ·
        refine ⟨12793012613338077371704967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528675075558718247803311 12793012613338077371704967)
        ·
          refine ⟨19189518920007116057557451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12793012613338077371704967 19189518920007116057557451)
          ·
            refine ⟨28784278380010674086336177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19189518920007116057557451 28784278380010674086336177)
            ·
              refine ⟨21588208785008005564752133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28784278380010674086336177 21588208785008005564752133)
              ·
                refine ⟨4047789147189001043391025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21588208785008005564752133 4047789147189001043391025)
                ·
                  refine ⟨3035841860391750782543269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4047789147189001043391025 3035841860391750782543269)
                  ·
                    refine ⟨569220348823453271726863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035841860391750782543269 569220348823453271726863)
                    ·
                      rfl

theorem cell22_1662829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1662829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662829 prefixEnd_1662829 := by exact prefixLift 1662829
  have htrace : WordTrace (prefixWord ++ tailWord_1662829) baseStart_1662829 baseEnd_1662829 := by
    simpa [prefixWord, tailWord_1662829, baseEnd_1662829] using wordTrace_append hprefix tailTrace_1662829
  have hstable : (prefixWord ++ tailWord_1662829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662829).length < 2 ^ (prefixWord ++ tailWord_1662829).sum := by decide
  have hdescent : baseEnd_1662829 < baseStart_1662829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662846 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1662846 : Nat := 118140960795 + 1662846 * 2 ^ 59
def prefixEnd_1662846 : Nat := 4983230072969 + 3 ^ 40 * 1662846 * 2
def baseEnd_1662846 : Nat := 569226168270870894051811

theorem tailTrace_1662846 : CollatzResearch.WordTrace tailWord_1662846 prefixEnd_1662846 569226168270870894051811 := by
  unfold tailWord_1662846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581122016725051041524049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40432650755866938888128261 7581122016725051041524049)
  ·
    refine ⟨5685841512543788281143037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7581122016725051041524049 5685841512543788281143037)
    ·
      refine ⟨2132190567203920605428639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5685841512543788281143037 2132190567203920605428639)
      ·
        refine ⟨3198285850805880908142959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132190567203920605428639 3198285850805880908142959)
        ·
          refine ⟨4797428776208821362214439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198285850805880908142959 4797428776208821362214439)
          ·
            refine ⟨7196143164313232043321659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797428776208821362214439 7196143164313232043321659)
            ·
              refine ⟨10794214746469848064982489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196143164313232043321659 10794214746469848064982489)
              ·
                refine ⟨8095661059852386048736867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10794214746469848064982489 8095661059852386048736867)
                ·
                  refine ⟨12143491589778579073105301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095661059852386048736867 12143491589778579073105301)
                  ·
                    refine ⟨569226168270870894051811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12143491589778579073105301 569226168270870894051811)
                    ·
                      rfl

theorem cell22_1662846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1662846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662846 prefixEnd_1662846 := by exact prefixLift 1662846
  have htrace : WordTrace (prefixWord ++ tailWord_1662846) baseStart_1662846 baseEnd_1662846 := by
    simpa [prefixWord, tailWord_1662846, baseEnd_1662846] using wordTrace_append hprefix tailTrace_1662846
  have hstable : (prefixWord ++ tailWord_1662846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662846).length < 2 ^ (prefixWord ++ tailWord_1662846).sum := by decide
  have hdescent : baseEnd_1662846 < baseStart_1662846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662878 : List Nat := [4, 3, 1, 3, 1, 2, 8]
def baseStart_1662878 : Nat := 118140960795 + 1662878 * 2 ^ 59
def prefixEnd_1662878 : Nat := 4983230072969 + 3 ^ 40 * 1662878 * 2
def baseEnd_1662878 : Nat := 21082856389808647305619

theorem tailTrace_1662878 : CollatzResearch.WordTrace tailWord_1662878 prefixEnd_1662878 21082856389808647305619 := by
  unfold tailWord_1662878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7581267908710559724669661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40433428846456318531571525 7581267908710559724669661)
  ·
    refine ⟨2842975465766459896751123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7581267908710559724669661 2842975465766459896751123)
    ·
      refine ⟨4264463198649689845126685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2842975465766459896751123 4264463198649689845126685)
      ·
        refine ⟨1599173699493633691922507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4264463198649689845126685 1599173699493633691922507)
        ·
          refine ⟨2398760549240450537883761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599173699493633691922507 2398760549240450537883761)
          ·
            refine ⟨1799070411930337903412821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398760549240450537883761 1799070411930337903412821)
            ·
              refine ⟨21082856389808647305619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1799070411930337903412821 21082856389808647305619)
              ·
                rfl

theorem cell22_1662878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 8].length) (baseStart_1662878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662878 prefixEnd_1662878 := by exact prefixLift 1662878
  have htrace : WordTrace (prefixWord ++ tailWord_1662878) baseStart_1662878 baseEnd_1662878 := by
    simpa [prefixWord, tailWord_1662878, baseEnd_1662878] using wordTrace_append hprefix tailTrace_1662878
  have hstable : (prefixWord ++ tailWord_1662878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662878).length < 2 ^ (prefixWord ++ tailWord_1662878).sum := by decide
  have hdescent : baseEnd_1662878 < baseStart_1662878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662981 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_1662981 : Nat := 118140960795 + 1662981 * 2 ^ 59
def prefixEnd_1662981 : Nat := 4983230072969 + 3 ^ 40 * 1662981 * 2
def baseEnd_1662981 : Nat := 569272381529775541926397

theorem tailTrace_1662981 : CollatzResearch.WordTrace tailWord_1662981 prefixEnd_1662981 569272381529775541926397 := by
  unfold tailWord_1662981
  simp only [CollatzResearch.WordTrace]
  refine ⟨60653899988311326388356797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40435933325540884258904531 60653899988311326388356797)
  ·
    refine ⟨22745212495616747395633799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60653899988311326388356797 22745212495616747395633799)
    ·
      refine ⟨34117818743425121093450699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22745212495616747395633799 34117818743425121093450699)
      ·
        refine ⟨51176728115137681640176049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34117818743425121093450699 51176728115137681640176049)
        ·
          refine ⟨38382546086353261230132037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51176728115137681640176049 38382546086353261230132037)
          ·
            refine ⟨7196727391191236480649757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38382546086353261230132037 7196727391191236480649757)
            ·
              refine ⟨2698772771696713680243659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7196727391191236480649757 2698772771696713680243659)
              ·
                refine ⟨4048159157545070520365489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698772771696713680243659 4048159157545070520365489)
                ·
                  refine ⟨3036119368158802890274117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4048159157545070520365489 3036119368158802890274117)
                  ·
                    refine ⟨569272381529775541926397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3036119368158802890274117 569272381529775541926397)
                    ·
                      rfl

theorem cell22_1662981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_1662981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1662981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1662981 prefixEnd_1662981 := by exact prefixLift 1662981
  have htrace : WordTrace (prefixWord ++ tailWord_1662981) baseStart_1662981 baseEnd_1662981 := by
    simpa [prefixWord, tailWord_1662981, baseEnd_1662981] using wordTrace_append hprefix tailTrace_1662981
  have hstable : (prefixWord ++ tailWord_1662981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662981).length < 2 ^ (prefixWord ++ tailWord_1662981).sum := by decide
  have hdescent : baseEnd_1662981 < baseStart_1662981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663039 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1663039 : Nat := 118140960795 + 1663039 * 2 ^ 59
def prefixEnd_1663039 : Nat := 4983230072969 + 3 ^ 40 * 1663039 * 2
def baseEnd_1663039 : Nat := 569292236115082723976219

theorem tailTrace_1663039 : CollatzResearch.WordTrace tailWord_1663039 prefixEnd_1663039 569292236115082723976219 := by
  unfold tailWord_1663039
  simp only [CollatzResearch.WordTrace]
  refine ⟨60656015422101202293968171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40437343614734134862645447 60656015422101202293968171)
  ·
    refine ⟨90984023133151803440952257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60656015422101202293968171 90984023133151803440952257)
    ·
      refine ⟨68238017349863852580714193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90984023133151803440952257 68238017349863852580714193)
      ·
        refine ⟨51178513012397889435535645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68238017349863852580714193 51178513012397889435535645)
        ·
          refine ⟨19191942379649208538325867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51178513012397889435535645 19191942379649208538325867)
          ·
            refine ⟨28787913569473812807488801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19191942379649208538325867 28787913569473812807488801)
            ·
              refine ⟨21590935177105359605616601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28787913569473812807488801 21590935177105359605616601)
              ·
                refine ⟨16193201382829019704212451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21590935177105359605616601 16193201382829019704212451)
                ·
                  refine ⟨24289802074243529556318677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16193201382829019704212451 24289802074243529556318677)
                  ·
                    refine ⟨569292236115082723976219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24289802074243529556318677 569292236115082723976219)
                    ·
                      rfl

theorem cell22_1663039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1663039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663039 prefixEnd_1663039 := by exact prefixLift 1663039
  have htrace : WordTrace (prefixWord ++ tailWord_1663039) baseStart_1663039 baseEnd_1663039 := by
    simpa [prefixWord, tailWord_1663039, baseEnd_1663039] using wordTrace_append hprefix tailTrace_1663039
  have hstable : (prefixWord ++ tailWord_1663039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663039).length < 2 ^ (prefixWord ++ tailWord_1663039).sum := by decide
  have hdescent : baseEnd_1663039 < baseStart_1663039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663041 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 7]
def baseStart_1663041 : Nat := 118140960795 + 1663041 * 2 ^ 59
def prefixEnd_1663041 : Nat := 4983230072969 + 3 ^ 40 * 1663041 * 2
def baseEnd_1663041 : Nat := 189764306918651795142071

theorem tailTrace_1663041 : CollatzResearch.WordTrace tailWord_1663041 prefixEnd_1663041 189764306918651795142071 := by
  unfold tailWord_1663041
  simp only [CollatzResearch.WordTrace]
  refine ⟨60656088368093956635540977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40437392245395971090360651 60656088368093956635540977)
  ·
    refine ⟨45492066276070467476655733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60656088368093956635540977 45492066276070467476655733)
    ·
      refine ⟨4264881213381606325936475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45492066276070467476655733 4264881213381606325936475)
      ·
        refine ⟨6397321820072409488904713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264881213381606325936475 6397321820072409488904713)
        ·
          refine ⟨4797991365054307116678535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6397321820072409488904713 4797991365054307116678535)
          ·
            refine ⟨7196987047581460675017803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797991365054307116678535 7196987047581460675017803)
            ·
              refine ⟨10795480571372191012526705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196987047581460675017803 10795480571372191012526705)
              ·
                refine ⟨8096610428529143259395029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10795480571372191012526705 8096610428529143259395029)
                ·
                  refine ⟨189764306918651795142071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8096610428529143259395029 189764306918651795142071)
                  ·
                    rfl

theorem cell22_1663041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_1663041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663041 prefixEnd_1663041 := by exact prefixLift 1663041
  have htrace : WordTrace (prefixWord ++ tailWord_1663041) baseStart_1663041 baseEnd_1663041 := by
    simpa [prefixWord, tailWord_1663041, baseEnd_1663041] using wordTrace_append hprefix tailTrace_1663041
  have hstable : (prefixWord ++ tailWord_1663041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663041).length < 2 ^ (prefixWord ++ tailWord_1663041).sum := by decide
  have hdescent : baseEnd_1663041 < baseStart_1663041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663062 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1663062 : Nat := 118140960795 + 1663062 * 2 ^ 59
def prefixEnd_1663062 : Nat := 4983230072969 + 3 ^ 40 * 1663062 * 2
def baseEnd_1663062 : Nat := 569300109485118330651149

theorem tailTrace_1663062 : CollatzResearch.WordTrace tailWord_1663062 prefixEnd_1663062 569300109485118330651149 := by
  unfold tailWord_1663062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791053393813617326378465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40437902867345251481370293 3791053393813617326378465)
  ·
    refine ⟨2843290045360212994783849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3791053393813617326378465 2843290045360212994783849)
    ·
      refine ⟨2132467534020159746087887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843290045360212994783849 2132467534020159746087887)
      ·
        refine ⟨3198701301030239619131831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132467534020159746087887 3198701301030239619131831)
        ·
          refine ⟨4798051951545359428697747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198701301030239619131831 4798051951545359428697747)
          ·
            refine ⟨7197077927318039143046621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798051951545359428697747 7197077927318039143046621)
            ·
              refine ⟨2698904222744264678642483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7197077927318039143046621 2698904222744264678642483)
              ·
                refine ⟨4048356334116397017963725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698904222744264678642483 4048356334116397017963725)
                ·
                  refine ⟨1518133625293648881736397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4048356334116397017963725 1518133625293648881736397)
                  ·
                    refine ⟨569300109485118330651149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518133625293648881736397 569300109485118330651149)
                    ·
                      rfl

theorem cell22_1663062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1663062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663062 prefixEnd_1663062 := by exact prefixLift 1663062
  have htrace : WordTrace (prefixWord ++ tailWord_1663062) baseStart_1663062 baseEnd_1663062 := by
    simpa [prefixWord, tailWord_1663062, baseEnd_1663062] using wordTrace_append hprefix tailTrace_1663062
  have hstable : (prefixWord ++ tailWord_1663062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663062).length < 2 ^ (prefixWord ++ tailWord_1663062).sum := by decide
  have hdescent : baseEnd_1663062 < baseStart_1663062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663086 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_1663086 : Nat := 118140960795 + 1663086 * 2 ^ 59
def prefixEnd_1663086 : Nat := 4983230072969 + 3 ^ 40 * 1663086 * 2
def baseEnd_1663086 : Nat := 189769441725196756017025

theorem tailTrace_1663086 : CollatzResearch.WordTrace tailWord_1663086 prefixEnd_1663086 189769441725196756017025 := by
  unfold tailWord_1663086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582216206616366165116139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40438486435287286213952741 7582216206616366165116139)
  ·
    refine ⟨11373324309924549247674209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7582216206616366165116139 11373324309924549247674209)
    ·
      refine ⟨8529993232443411935755657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11373324309924549247674209 8529993232443411935755657)
      ·
        refine ⟨6397494924332558951816743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8529993232443411935755657 6397494924332558951816743)
        ·
          refine ⟨9596242386498838427725115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397494924332558951816743 9596242386498838427725115)
          ·
            refine ⟨14394363579748257641587673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596242386498838427725115 14394363579748257641587673)
            ·
              refine ⟨10795772684811193231190755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14394363579748257641587673 10795772684811193231190755)
              ·
                refine ⟨16193659027216789846786133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10795772684811193231190755 16193659027216789846786133)
                ·
                  refine ⟨189769441725196756017025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16193659027216789846786133 189769441725196756017025)
                  ·
                    rfl

theorem cell22_1663086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_1663086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663086 prefixEnd_1663086 := by exact prefixLift 1663086
  have htrace : WordTrace (prefixWord ++ tailWord_1663086) baseStart_1663086 baseEnd_1663086 := by
    simpa [prefixWord, tailWord_1663086, baseEnd_1663086] using wordTrace_append hprefix tailTrace_1663086
  have hstable : (prefixWord ++ tailWord_1663086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663086).length < 2 ^ (prefixWord ++ tailWord_1663086).sum := by decide
  have hdescent : baseEnd_1663086 < baseStart_1663086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663088 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_1663088 : Nat := 118140960795 + 1663088 * 2 ^ 59
def prefixEnd_1663088 : Nat := 4983230072969 + 3 ^ 40 * 1663088 * 2
def baseEnd_1663088 : Nat := 569309009816462929501069

theorem tailTrace_1663088 : CollatzResearch.WordTrace tailWord_1663088 prefixEnd_1663088 569309009816462929501069 := by
  unfold tailWord_1663088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30328901299461841831250959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40438535065949122441667945 30328901299461841831250959)
  ·
    refine ⟨45493351949192762746876439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30328901299461841831250959 45493351949192762746876439)
    ·
      refine ⟨68240027923789144120314659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45493351949192762746876439 68240027923789144120314659)
      ·
        refine ⟨102360041885683716180471989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68240027923789144120314659 102360041885683716180471989)
        ·
          refine ⟨9596253926782848391919249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102360041885683716180471989 9596253926782848391919249)
          ·
            refine ⟨7197190445087136293939437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9596253926782848391919249 7197190445087136293939437)
            ·
              refine ⟨2698946416907676110227289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7197190445087136293939437 2698946416907676110227289)
              ·
                refine ⟨2024209812680757082670467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698946416907676110227289 2024209812680757082670467)
                ·
                  refine ⟨3036314719021135624005701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024209812680757082670467 3036314719021135624005701)
                  ·
                    refine ⟨569309009816462929501069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3036314719021135624005701 569309009816462929501069)
                    ·
                      rfl

theorem cell22_1663088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_1663088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663088 prefixEnd_1663088 := by exact prefixLift 1663088
  have htrace : WordTrace (prefixWord ++ tailWord_1663088) baseStart_1663088 baseEnd_1663088 := by
    simpa [prefixWord, tailWord_1663088, baseEnd_1663088] using wordTrace_append hprefix tailTrace_1663088
  have hstable : (prefixWord ++ tailWord_1663088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663088).length < 2 ^ (prefixWord ++ tailWord_1663088).sum := by decide
  have hdescent : baseEnd_1663088 < baseStart_1663088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663101 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1663101 : Nat := 118140960795 + 1663101 * 2 ^ 59
def prefixEnd_1663101 : Nat := 4983230072969 + 3 ^ 40 * 1663101 * 2
def baseEnd_1663101 : Nat := 569313459982135228926029

theorem tailTrace_1663101 : CollatzResearch.WordTrace tailWord_1663101 prefixEnd_1663101 569313459982135228926029 := by
  unfold tailWord_1663101
  simp only [CollatzResearch.WordTrace]
  refine ⟨60658276747876586882725157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40438851165251057921816771 60658276747876586882725157)
  ·
    refine ⟨11373426890226860040510967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60658276747876586882725157 11373426890226860040510967)
    ·
      refine ⟨17060140335340290060766451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11373426890226860040510967 17060140335340290060766451)
      ·
        refine ⟨25590210503010435091149677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17060140335340290060766451 25590210503010435091149677)
        ·
          refine ⟨9596328938628913159181129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25590210503010435091149677 9596328938628913159181129)
          ·
            refine ⟨7197246703971684869385847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9596328938628913159181129 7197246703971684869385847)
            ·
              refine ⟨10795870055957527304078771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197246703971684869385847 10795870055957527304078771)
              ·
                refine ⟨16193805083936290956118157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10795870055957527304078771 16193805083936290956118157)
                ·
                  refine ⟨6072676906476109108544309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16193805083936290956118157 6072676906476109108544309)
                  ·
                    refine ⟨569313459982135228926029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6072676906476109108544309 569313459982135228926029)
                    ·
                      rfl

theorem cell22_1663101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1663101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663101 prefixEnd_1663101 := by exact prefixLift 1663101
  have htrace : WordTrace (prefixWord ++ tailWord_1663101) baseStart_1663101 baseEnd_1663101 := by
    simpa [prefixWord, tailWord_1663101, baseEnd_1663101] using wordTrace_append hprefix tailTrace_1663101
  have hstable : (prefixWord ++ tailWord_1663101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663101).length < 2 ^ (prefixWord ++ tailWord_1663101).sum := by decide
  have hdescent : baseEnd_1663101 < baseStart_1663101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663135 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 2, 3]
def baseStart_1663135 : Nat := 118140960795 + 1663135 * 2 ^ 59
def prefixEnd_1663135 : Nat := 4983230072969 + 3 ^ 40 * 1663135 * 2
def baseEnd_1663135 : Nat := 569325098876970473575925

theorem tailTrace_1663135 : CollatzResearch.WordTrace tailWord_1663135 prefixEnd_1663135 569325098876970473575925 := by
  unfold tailWord_1663135
  simp only [CollatzResearch.WordTrace]
  refine ⟨60659516829753410689462859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40439677886502273792975239 60659516829753410689462859)
  ·
    refine ⟨90989275244630116034194289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60659516829753410689462859 90989275244630116034194289)
    ·
      refine ⟨68241956433472587025645717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90989275244630116034194289 68241956433472587025645717)
      ·
        refine ⟨3198841707819027516827143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68241956433472587025645717 3198841707819027516827143)
        ·
          refine ⟨4798262561728541275240715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198841707819027516827143 4798262561728541275240715)
          ·
            refine ⟨7197393842592811912861073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798262561728541275240715 7197393842592811912861073)
            ·
              refine ⟨5398045381944608934645805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7197393842592811912861073 5398045381944608934645805)
              ·
                refine ⟨2024267018229228350492177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5398045381944608934645805 2024267018229228350492177)
                ·
                  refine ⟨1518200263671921262869133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2024267018229228350492177 1518200263671921262869133)
                  ·
                    refine ⟨569325098876970473575925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518200263671921262869133 569325098876970473575925)
                    ·
                      rfl

theorem cell22_1663135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_1663135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663135 prefixEnd_1663135 := by exact prefixLift 1663135
  have htrace : WordTrace (prefixWord ++ tailWord_1663135) baseStart_1663135 baseEnd_1663135 := by
    simpa [prefixWord, tailWord_1663135, baseEnd_1663135] using wordTrace_append hprefix tailTrace_1663135
  have hstable : (prefixWord ++ tailWord_1663135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663135).length < 2 ^ (prefixWord ++ tailWord_1663135).sum := by decide
  have hdescent : baseEnd_1663135 < baseStart_1663135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663169 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1663169 : Nat := 118140960795 + 1663169 * 2 ^ 59
def prefixEnd_1663169 : Nat := 4983230072969 + 3 ^ 40 * 1663169 * 2
def baseEnd_1663169 : Nat := 569336737771805718225821

theorem tailTrace_1663169 : CollatzResearch.WordTrace tailWord_1663169 prefixEnd_1663169 569336737771805718225821 := by
  unfold tailWord_1663169
  simp only [CollatzResearch.WordTrace]
  refine ⟨60660756911630234496200561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40440504607753489664133707 60660756911630234496200561)
  ·
    refine ⟨45495567683722675872150421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60660756911630234496200561 45495567683722675872150421)
    ·
      refine ⟨2132604735174500431507051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45495567683722675872150421 2132604735174500431507051)
      ·
        refine ⟨3198907102761750647260577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132604735174500431507051 3198907102761750647260577)
        ·
          refine ⟨2399180327071312985445433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198907102761750647260577 2399180327071312985445433)
          ·
            refine ⟨1799385245303484739084075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399180327071312985445433 1799385245303484739084075)
            ·
              refine ⟨2699077867955227108626113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799385245303484739084075 2699077867955227108626113)
              ·
                refine ⟨2024308400966420331469585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699077867955227108626113 2024308400966420331469585)
                ·
                  refine ⟨1518231300724815248602189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2024308400966420331469585 1518231300724815248602189)
                  ·
                    refine ⟨569336737771805718225821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518231300724815248602189 569336737771805718225821)
                    ·
                      rfl

theorem cell22_1663169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1663169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663169 prefixEnd_1663169 := by exact prefixLift 1663169
  have htrace : WordTrace (prefixWord ++ tailWord_1663169) baseStart_1663169 baseEnd_1663169 := by
    simpa [prefixWord, tailWord_1663169, baseEnd_1663169] using wordTrace_append hprefix tailTrace_1663169
  have hstable : (prefixWord ++ tailWord_1663169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663169).length < 2 ^ (prefixWord ++ tailWord_1663169).sum := by decide
  have hdescent : baseEnd_1663169 < baseStart_1663169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663251 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_1663251 : Nat := 118140960795 + 1663251 * 2 ^ 59
def prefixEnd_1663251 : Nat := 4983230072969 + 3 ^ 40 * 1663251 * 2
def baseEnd_1663251 : Nat := 569364808047584837675569

theorem tailTrace_1663251 : CollatzResearch.WordTrace tailWord_1663251 prefixEnd_1663251 569364808047584837675569 := by
  unfold tailWord_1663251
  simp only [CollatzResearch.WordTrace]
  refine ⟨60663747697333162500685607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40442498464888775000457071 60663747697333162500685607)
  ·
    refine ⟨90995621545999743751028411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60663747697333162500685607 90995621545999743751028411)
    ·
      refine ⟨136493432318999615626542617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90995621545999743751028411 136493432318999615626542617)
      ·
        refine ⟨102370074239249711719906963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136493432318999615626542617 102370074239249711719906963)
        ·
          refine ⟨153555111358874567579860445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102370074239249711719906963 153555111358874567579860445)
          ·
            refine ⟨57583166759577962842447667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153555111358874567579860445 57583166759577962842447667)
            ·
              refine ⟨86374750139366944263671501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57583166759577962842447667 86374750139366944263671501)
              ·
                refine ⟨32390531302262604098876813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86374750139366944263671501 32390531302262604098876813)
                ·
                  refine ⟨12146449238348476537078805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32390531302262604098876813 12146449238348476537078805)
                  ·
                    refine ⟨569364808047584837675569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12146449238348476537078805 569364808047584837675569)
                    ·
                      rfl

theorem cell22_1663251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_1663251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663251 prefixEnd_1663251 := by exact prefixLift 1663251
  have htrace : WordTrace (prefixWord ++ tailWord_1663251) baseStart_1663251 baseEnd_1663251 := by
    simpa [prefixWord, tailWord_1663251, baseEnd_1663251] using wordTrace_append hprefix tailTrace_1663251
  have hstable : (prefixWord ++ tailWord_1663251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663251).length < 2 ^ (prefixWord ++ tailWord_1663251).sum := by decide
  have hdescent : baseEnd_1663251 < baseStart_1663251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663274 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1663274 : Nat := 118140960795 + 1663274 * 2 ^ 59
def prefixEnd_1663274 : Nat := 4983230072969 + 3 ^ 40 * 1663274 * 2
def baseEnd_1663274 : Nat := 569372681417620444350499

theorem tailTrace_1663274 : CollatzResearch.WordTrace tailWord_1663274 prefixEnd_1663274 569372681417620444350499 := by
  unfold tailWord_1663274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166146644062459357193219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40443057717499891619181917 15166146644062459357193219)
  ·
    refine ⟨22749219966093689035789829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15166146644062459357193219 22749219966093689035789829)
    ·
      refine ⟨4265478743642566694210593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22749219966093689035789829 4265478743642566694210593)
      ·
        refine ⟨3199109057731925020657945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265478743642566694210593 3199109057731925020657945)
        ·
          refine ⟨2399331793298943765493459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199109057731925020657945 2399331793298943765493459)
          ·
            refine ⟨3598997689948415648240189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399331793298943765493459 3598997689948415648240189)
            ·
              refine ⟨1349624133730655868090071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3598997689948415648240189 1349624133730655868090071)
              ·
                refine ⟨2024436200595983802135107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349624133730655868090071 2024436200595983802135107)
                ·
                  refine ⟨3036654300893975703202661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024436200595983802135107 3036654300893975703202661)
                  ·
                    refine ⟨569372681417620444350499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3036654300893975703202661 569372681417620444350499)
                    ·
                      rfl

theorem cell22_1663274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1663274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663274 prefixEnd_1663274 := by exact prefixLift 1663274
  have htrace : WordTrace (prefixWord ++ tailWord_1663274) baseStart_1663274 baseEnd_1663274 := by
    simpa [prefixWord, tailWord_1663274, baseEnd_1663274] using wordTrace_append hprefix tailTrace_1663274
  have hstable : (prefixWord ++ tailWord_1663274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663274).length < 2 ^ (prefixWord ++ tailWord_1663274).sum := by decide
  have hdescent : baseEnd_1663274 < baseStart_1663274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663289 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 4]
def baseStart_1663289 : Nat := 118140960795 + 1663289 * 2 ^ 59
def prefixEnd_1663289 : Nat := 4983230072969 + 3 ^ 40 * 1663289 * 2
def baseEnd_1663289 : Nat := 189792605408055135075151

theorem tailTrace_1663289 : CollatzResearch.WordTrace tailWord_1663289 prefixEnd_1663289 189792605408055135075151 := by
  unfold tailWord_1663289
  simp only [CollatzResearch.WordTrace]
  refine ⟨60665133671195494990568921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40443422447463663327045947 60665133671195494990568921)
  ·
    refine ⟨45498850253396621242926691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60665133671195494990568921 45498850253396621242926691)
    ·
      refine ⟨68248275380094931864390037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45498850253396621242926691 68248275380094931864390037)
      ·
        refine ⟨3199137908441949931143283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68248275380094931864390037 3199137908441949931143283)
        ·
          refine ⟨4798706862662924896714925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199137908441949931143283 4798706862662924896714925)
          ·
            refine ⟨1799515073498596836268097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4798706862662924896714925 1799515073498596836268097)
            ·
              refine ⟨1349636305123947627201073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799515073498596836268097 1349636305123947627201073)
              ·
                refine ⟨1012227228842960720400805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349636305123947627201073 1012227228842960720400805)
                ·
                  refine ⟨189792605408055135075151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012227228842960720400805 189792605408055135075151)
                  ·
                    rfl

theorem cell22_1663289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_1663289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663289 prefixEnd_1663289 := by exact prefixLift 1663289
  have htrace : WordTrace (prefixWord ++ tailWord_1663289) baseStart_1663289 baseEnd_1663289 := by
    simpa [prefixWord, tailWord_1663289, baseEnd_1663289] using wordTrace_append hprefix tailTrace_1663289
  have hstable : (prefixWord ++ tailWord_1663289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663289).length < 2 ^ (prefixWord ++ tailWord_1663289).sum := by decide
  have hdescent : baseEnd_1663289 < baseStart_1663289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663349 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1663349 : Nat := 118140960795 + 1663349 * 2 ^ 59
def prefixEnd_1663349 : Nat := 4983230072969 + 3 ^ 40 * 1663349 * 2
def baseEnd_1663349 : Nat := 569398355450345248725269

theorem tailTrace_1663349 : CollatzResearch.WordTrace tailWord_1663349 prefixEnd_1663349 569398355450345248725269 := by
  unfold tailWord_1663349
  simp only [CollatzResearch.WordTrace]
  refine ⟨60667322050978125237753101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40444881367318750158502067 60667322050978125237753101)
  ·
    refine ⟨22750245769116796964157413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60667322050978125237753101 22750245769116796964157413)
    ·
      refine ⟨4265671081709399430779515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22750245769116796964157413 4265671081709399430779515)
      ·
        refine ⟨6398506622564099146169273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265671081709399430779515 6398506622564099146169273)
        ·
          refine ⟨4798879966923074359626955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6398506622564099146169273 4798879966923074359626955)
          ·
            refine ⟨7198319950384611539440433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798879966923074359626955 7198319950384611539440433)
            ·
              refine ⟨5398739962788458654580325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198319950384611539440433 5398739962788458654580325)
              ·
                refine ⟨1012263743022835997733811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5398739962788458654580325 1012263743022835997733811)
                ·
                  refine ⟨1518395614534253996600717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012263743022835997733811 1518395614534253996600717)
                  ·
                    refine ⟨569398355450345248725269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518395614534253996600717 569398355450345248725269)
                    ·
                      rfl

theorem cell22_1663349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1663349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663349 prefixEnd_1663349 := by exact prefixLift 1663349
  have htrace : WordTrace (prefixWord ++ tailWord_1663349) baseStart_1663349 baseEnd_1663349 := by
    simpa [prefixWord, tailWord_1663349, baseEnd_1663349] using wordTrace_append hprefix tailTrace_1663349
  have hstable : (prefixWord ++ tailWord_1663349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663349).length < 2 ^ (prefixWord ++ tailWord_1663349).sum := by decide
  have hdescent : baseEnd_1663349 < baseStart_1663349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663433 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_1663433 : Nat := 118140960795 + 1663433 * 2 ^ 59
def prefixEnd_1663433 : Nat := 4983230072969 + 3 ^ 40 * 1663433 * 2
def baseEnd_1663433 : Nat := 569427110366997029625011

theorem tailTrace_1663433 : CollatzResearch.WordTrace tailWord_1663433 prefixEnd_1663433 569427110366997029625011 := by
  unfold tailWord_1663433
  simp only [CollatzResearch.WordTrace]
  refine ⟨60670385782673807583810953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40446923855115871722540635 60670385782673807583810953)
  ·
    refine ⟨45502789337005355687858215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60670385782673807583810953 45502789337005355687858215)
    ·
      refine ⟨68254184005508033531787323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45502789337005355687858215 68254184005508033531787323)
      ·
        refine ⟨102381276008262050297680985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68254184005508033531787323 102381276008262050297680985)
        ·
          refine ⟨76785957006196537723260739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102381276008262050297680985 76785957006196537723260739)
          ·
            refine ⟨115178935509294806584891109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76785957006196537723260739 115178935509294806584891109)
            ·
              refine ⟨21596050407992776234667083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115178935509294806584891109 21596050407992776234667083)
              ·
                refine ⟨32394075611989164352000625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21596050407992776234667083 32394075611989164352000625)
                ·
                  refine ⟨24295556708991873264000469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32394075611989164352000625 24295556708991873264000469)
                  ·
                    refine ⟨569427110366997029625011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24295556708991873264000469 569427110366997029625011)
                    ·
                      rfl

theorem cell22_1663433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_1663433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663433 prefixEnd_1663433 := by exact prefixLift 1663433
  have htrace : WordTrace (prefixWord ++ tailWord_1663433) baseStart_1663433 baseEnd_1663433 := by
    simpa [prefixWord, tailWord_1663433, baseEnd_1663433] using wordTrace_append hprefix tailTrace_1663433
  have hstable : (prefixWord ++ tailWord_1663433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663433).length < 2 ^ (prefixWord ++ tailWord_1663433).sum := by decide
  have hdescent : baseEnd_1663433 < baseStart_1663433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663480 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_1663480 : Nat := 118140960795 + 1663480 * 2 ^ 59
def prefixEnd_1663480 : Nat := 4983230072969 + 3 ^ 40 * 1663480 * 2
def baseEnd_1663480 : Nat := 189814399809168191233289

theorem tailTrace_1663480 : CollatzResearch.WordTrace tailWord_1663480 prefixEnd_1663480 189814399809168191233289 := by
  unfold tailWord_1663480
  simp only [CollatzResearch.WordTrace]
  refine ⟨30336050006751767305385947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40448066675669023073847929 30336050006751767305385947)
  ·
    refine ⟨45504075010127650958078921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30336050006751767305385947 45504075010127650958078921)
    ·
      refine ⟨34128056257595738218559191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45504075010127650958078921 34128056257595738218559191)
      ·
        refine ⟨51192084386393607327838787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34128056257595738218559191 51192084386393607327838787)
        ·
          refine ⟨76788126579590410991758181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51192084386393607327838787 76788126579590410991758181)
          ·
            refine ⟨14397773733673202060954659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76788126579590410991758181 14397773733673202060954659)
            ·
              refine ⟨21596660600509803091431989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397773733673202060954659 21596660600509803091431989)
              ·
                refine ⟨2024686931297794039821749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21596660600509803091431989 2024686931297794039821749)
                ·
                  refine ⟨189814399809168191233289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2024686931297794039821749 189814399809168191233289)
                  ·
                    rfl

theorem cell22_1663480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_1663480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663480 prefixEnd_1663480 := by exact prefixLift 1663480
  have htrace : WordTrace (prefixWord ++ tailWord_1663480) baseStart_1663480 baseEnd_1663480 := by
    simpa [prefixWord, tailWord_1663480, baseEnd_1663480] using wordTrace_append hprefix tailTrace_1663480
  have hstable : (prefixWord ++ tailWord_1663480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663480).length < 2 ^ (prefixWord ++ tailWord_1663480).sum := by decide
  have hdescent : baseEnd_1663480 < baseStart_1663480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663525 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1663525 : Nat := 118140960795 + 1663525 * 2 ^ 59
def prefixEnd_1663525 : Nat := 4983230072969 + 3 ^ 40 * 1663525 * 2
def baseEnd_1663525 : Nat := 189819534615713152108243

theorem tailTrace_1663525 : CollatzResearch.WordTrace tailWord_1663525 prefixEnd_1663525 189819534615713152108243 := by
  unfold tailWord_1663525
  simp only [CollatzResearch.WordTrace]
  refine ⟨60673741298340507296160029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40449160865560338197440019 60673741298340507296160029)
  ·
    refine ⟨22752652986877690236060011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60673741298340507296160029 22752652986877690236060011)
    ·
      refine ⟨34128979480316535354090017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22752652986877690236060011 34128979480316535354090017)
      ·
        refine ⟨25596734610237401515567513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34128979480316535354090017 25596734610237401515567513)
        ·
          refine ⟨19197550957678051136675635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25596734610237401515567513 19197550957678051136675635)
          ·
            refine ⟨28796326436517076705013453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19197550957678051136675635 28796326436517076705013453)
            ·
              refine ⟨10798622413693903764380045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28796326436517076705013453 10798622413693903764380045)
              ·
                refine ⟨4049483405135213911642517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10798622413693903764380045 4049483405135213911642517)
                ·
                  refine ⟨189819534615713152108243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4049483405135213911642517 189819534615713152108243)
                  ·
                    rfl

theorem cell22_1663525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1663525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663525 prefixEnd_1663525 := by exact prefixLift 1663525
  have htrace : WordTrace (prefixWord ++ tailWord_1663525) baseStart_1663525 baseEnd_1663525 := by
    simpa [prefixWord, tailWord_1663525, baseEnd_1663525] using wordTrace_append hprefix tailTrace_1663525
  have hstable : (prefixWord ++ tailWord_1663525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663525).length < 2 ^ (prefixWord ++ tailWord_1663525).sum := by decide
  have hdescent : baseEnd_1663525 < baseStart_1663525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663555 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_1663555 : Nat := 118140960795 + 1663555 * 2 ^ 59
def prefixEnd_1663555 : Nat := 4983230072969 + 3 ^ 40 * 1663555 * 2
def baseEnd_1663555 : Nat := 569468873460229378074637

theorem tailTrace_1663555 : CollatzResearch.WordTrace tailWord_1663555 prefixEnd_1663555 569468873460229378074637 := by
  unfold tailWord_1663555
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674835488231822419752119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40449890325487881613168079 60674835488231822419752119)
  ·
    refine ⟨91012253232347733629628179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60674835488231822419752119 91012253232347733629628179)
    ·
      refine ⟨136518379848521600444442269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91012253232347733629628179 136518379848521600444442269)
      ·
        refine ⟨51194392443195600166665851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136518379848521600444442269 51194392443195600166665851)
        ·
          refine ⟨76791588664793400249998777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51194392443195600166665851 76791588664793400249998777)
          ·
            refine ⟨57593691498595050187499083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76791588664793400249998777 57593691498595050187499083)
            ·
              refine ⟨86390537247892575281248625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57593691498595050187499083 86390537247892575281248625)
              ·
                refine ⟨64792902935919431460936469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86390537247892575281248625 64792902935919431460936469)
                ·
                  refine ⟨3037167325121223349731397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64792902935919431460936469 3037167325121223349731397)
                  ·
                    refine ⟨569468873460229378074637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037167325121223349731397 569468873460229378074637)
                    ·
                      rfl

theorem cell22_1663555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_1663555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663555 prefixEnd_1663555 := by exact prefixLift 1663555
  have htrace : WordTrace (prefixWord ++ tailWord_1663555) baseStart_1663555 baseEnd_1663555 := by
    simpa [prefixWord, tailWord_1663555, baseEnd_1663555] using wordTrace_append hprefix tailTrace_1663555
  have hstable : (prefixWord ++ tailWord_1663555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663555).length < 2 ^ (prefixWord ++ tailWord_1663555).sum := by decide
  have hdescent : baseEnd_1663555 < baseStart_1663555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663557 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_1663557 : Nat := 118140960795 + 1663557 * 2 ^ 59
def prefixEnd_1663557 : Nat := 4983230072969 + 3 ^ 40 * 1663557 * 2
def baseEnd_1663557 : Nat := 569469558101102039524631

theorem tailTrace_1663557 : CollatzResearch.WordTrace tailWord_1663557 prefixEnd_1663557 569469558101102039524631 := by
  unfold tailWord_1663557
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674908434224576761324925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40449938956149717840883283 60674908434224576761324925)
  ·
    refine ⟨22753090662834216285496847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60674908434224576761324925 22753090662834216285496847)
    ·
      refine ⟨34129635994251324428245271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22753090662834216285496847 34129635994251324428245271)
      ·
        refine ⟨51194453991376986642367907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34129635994251324428245271 51194453991376986642367907)
        ·
          refine ⟨76791680987065479963551861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51194453991376986642367907 76791680987065479963551861)
          ·
            refine ⟨7199220092537388746582987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76791680987065479963551861 7199220092537388746582987)
            ·
              refine ⟨10798830138806083119874481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199220092537388746582987 10798830138806083119874481)
              ·
                refine ⟨8099122604104562339905861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10798830138806083119874481 8099122604104562339905861)
                ·
                  refine ⟨1518585488269605438732349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8099122604104562339905861 1518585488269605438732349)
                  ·
                    refine ⟨569469558101102039524631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518585488269605438732349 569469558101102039524631)
                    ·
                      rfl

theorem cell22_1663557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_1663557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663557 prefixEnd_1663557 := by exact prefixLift 1663557
  have htrace : WordTrace (prefixWord ++ tailWord_1663557) baseStart_1663557 baseEnd_1663557 := by
    simpa [prefixWord, tailWord_1663557, baseEnd_1663557] using wordTrace_append hprefix tailTrace_1663557
  have hstable : (prefixWord ++ tailWord_1663557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663557).length < 2 ^ (prefixWord ++ tailWord_1663557).sum := by decide
  have hdescent : baseEnd_1663557 < baseStart_1663557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663559 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 4]
def baseStart_1663559 : Nat := 118140960795 + 1663559 * 2 ^ 59
def prefixEnd_1663559 : Nat := 4983230072969 + 3 ^ 40 * 1663559 * 2
def baseEnd_1663559 : Nat := 189823414247324900324875

theorem tailTrace_1663559 : CollatzResearch.WordTrace tailWord_1663559 prefixEnd_1663559 189823414247324900324875 := by
  unfold tailWord_1663559
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674981380217331102897731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40449987586811554068598487 60674981380217331102897731)
  ·
    refine ⟨91012472070325996654346597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60674981380217331102897731 91012472070325996654346597)
    ·
      refine ⟨17064838513186124372689987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91012472070325996654346597 17064838513186124372689987)
      ·
        refine ⟨25597257769779186559034981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17064838513186124372689987 25597257769779186559034981)
        ·
          refine ⟨4799485831833597479819059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25597257769779186559034981 4799485831833597479819059)
          ·
            refine ⟨7199228747750396219728589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799485831833597479819059 7199228747750396219728589)
            ·
              refine ⟨2699710780406398582398221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7199228747750396219728589 2699710780406398582398221)
              ·
                refine ⟨1012391542652399468399333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2699710780406398582398221 1012391542652399468399333)
                ·
                  refine ⟨189823414247324900324875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012391542652399468399333 189823414247324900324875)
                  ·
                    rfl

theorem cell22_1663559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 4].length) (baseStart_1663559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663559 prefixEnd_1663559 := by exact prefixLift 1663559
  have htrace : WordTrace (prefixWord ++ tailWord_1663559) baseStart_1663559 baseEnd_1663559 := by
    simpa [prefixWord, tailWord_1663559, baseEnd_1663559] using wordTrace_append hprefix tailTrace_1663559
  have hstable : (prefixWord ++ tailWord_1663559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663559).length < 2 ^ (prefixWord ++ tailWord_1663559).sum := by decide
  have hdescent : baseEnd_1663559 < baseStart_1663559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663572 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1663572 : Nat := 118140960795 + 1663572 * 2 ^ 59
def prefixEnd_1663572 : Nat := 4983230072969 + 3 ^ 40 * 1663572 * 2
def baseEnd_1663572 : Nat := 569474692907647000399585

theorem tailTrace_1663572 : CollatzResearch.WordTrace tailWord_1663572 prefixEnd_1663572 569474692907647000399585 := by
  unfold tailWord_1663572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337727764585117161560485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40450303686113489548747313 30337727764585117161560485)
  ·
    refine ⟨5688323955859709467792591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30337727764585117161560485 5688323955859709467792591)
    ·
      refine ⟨8532485933789564201688887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5688323955859709467792591 8532485933789564201688887)
      ·
        refine ⟨12798728900684346302533331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8532485933789564201688887 12798728900684346302533331)
        ·
          refine ⟨19198093351026519453799997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12798728900684346302533331 19198093351026519453799997)
          ·
            refine ⟨7199285006634944795174999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19198093351026519453799997 7199285006634944795174999)
            ·
              refine ⟨10798927509952417192762499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199285006634944795174999 10798927509952417192762499)
              ·
                refine ⟨16198391264928625789143749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798927509952417192762499 16198391264928625789143749)
                ·
                  refine ⟨3037198362174117335464453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16198391264928625789143749 3037198362174117335464453)
                  ·
                    refine ⟨569474692907647000399585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037198362174117335464453 569474692907647000399585)
                    ·
                      rfl

theorem cell22_1663572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1663572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663572 prefixEnd_1663572 := by exact prefixLift 1663572
  have htrace : WordTrace (prefixWord ++ tailWord_1663572) baseStart_1663572 baseEnd_1663572 := by
    simpa [prefixWord, tailWord_1663572, baseEnd_1663572] using wordTrace_append hprefix tailTrace_1663572
  have hstable : (prefixWord ++ tailWord_1663572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663572).length < 2 ^ (prefixWord ++ tailWord_1663572).sum := by decide
  have hdescent : baseEnd_1663572 < baseStart_1663572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663582 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1663582 : Nat := 118140960795 + 1663582 * 2 ^ 59
def prefixEnd_1663582 : Nat := 4983230072969 + 3 ^ 40 * 1663582 * 2
def baseEnd_1663582 : Nat := 189826038704003435883185

theorem tailTrace_1663582 : CollatzResearch.WordTrace tailWord_1663582 prefixEnd_1663582 189826038704003435883185 := by
  unfold tailWord_1663582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584477532391750753873125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40450546839422670687323333 7584477532391750753873125)
  ·
    refine ⟨1422089537323453266351211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7584477532391750753873125 1422089537323453266351211)
    ·
      refine ⟨2133134305985179899526817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422089537323453266351211 2133134305985179899526817)
      ·
        refine ⟨1599850729488884924645113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2133134305985179899526817 1599850729488884924645113)
        ·
          refine ⟨1199888047116663693483835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599850729488884924645113 1199888047116663693483835)
          ·
            refine ⟨1799832070674995540225753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199888047116663693483835 1799832070674995540225753)
            ·
              refine ⟨1349874053006246655169315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799832070674995540225753 1349874053006246655169315)
              ·
                refine ⟨2024811079509369982753973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349874053006246655169315 2024811079509369982753973)
                ·
                  refine ⟨189826038704003435883185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2024811079509369982753973 189826038704003435883185)
                  ·
                    rfl

theorem cell22_1663582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1663582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663582 prefixEnd_1663582 := by exact prefixLift 1663582
  have htrace : WordTrace (prefixWord ++ tailWord_1663582) baseStart_1663582 baseEnd_1663582 := by
    simpa [prefixWord, tailWord_1663582, baseEnd_1663582] using wordTrace_append hprefix tailTrace_1663582
  have hstable : (prefixWord ++ tailWord_1663582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663582).length < 2 ^ (prefixWord ++ tailWord_1663582).sum := by decide
  have hdescent : baseEnd_1663582 < baseStart_1663582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663606 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1663606 : Nat := 118140960795 + 1663606 * 2 ^ 59
def prefixEnd_1663606 : Nat := 4983230072969 + 3 ^ 40 * 1663606 * 2
def baseEnd_1663606 : Nat := 569486331802482245049481

theorem tailTrace_1663606 : CollatzResearch.WordTrace tailWord_1663606 prefixEnd_1663606 569486331802482245049481 := by
  unfold tailWord_1663606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792293475690441133116167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40451130407364705419905781 3792293475690441133116167)
  ·
    refine ⟨5688440213535661699674251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3792293475690441133116167 5688440213535661699674251)
    ·
      refine ⟨8532660320303492549511377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5688440213535661699674251 8532660320303492549511377)
      ·
        refine ⟨6399495240227619412133533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8532660320303492549511377 6399495240227619412133533)
        ·
          refine ⟨2399810715085357279550075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6399495240227619412133533 2399810715085357279550075)
          ·
            refine ⟨3599716072628035919325113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399810715085357279550075 3599716072628035919325113)
            ·
              refine ⟨2699787054471026939493835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599716072628035919325113 2699787054471026939493835)
              ·
                refine ⟨4049680581706540409240753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699787054471026939493835 4049680581706540409240753)
                ·
                  refine ⟨3037260436279905306930565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049680581706540409240753 3037260436279905306930565)
                  ·
                    refine ⟨569486331802482245049481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037260436279905306930565 569486331802482245049481)
                    ·
                      rfl

theorem cell22_1663606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1663606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663606 prefixEnd_1663606 := by exact prefixLift 1663606
  have htrace : WordTrace (prefixWord ++ tailWord_1663606) baseStart_1663606 baseEnd_1663606 := by
    simpa [prefixWord, tailWord_1663606, baseEnd_1663606] using wordTrace_append hprefix tailTrace_1663606
  have hstable : (prefixWord ++ tailWord_1663606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663606).length < 2 ^ (prefixWord ++ tailWord_1663606).sum := by decide
  have hdescent : baseEnd_1663606 < baseStart_1663606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663615 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 7]
def baseStart_1663615 : Nat := 118140960795 + 1663615 * 2 ^ 59
def prefixEnd_1663615 : Nat := 4983230072969 + 3 ^ 40 * 1663615 * 2
def baseEnd_1663615 : Nat := 189829804228803073858151

theorem tailTrace_1663615 : CollatzResearch.WordTrace tailWord_1663615 prefixEnd_1663615 189829804228803073858151 := by
  unfold tailWord_1663615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60677023868014452666936299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40451349245342968444624199 60677023868014452666936299)
  ·
    refine ⟨91015535802021679000404449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60677023868014452666936299 91015535802021679000404449)
    ·
      refine ⟨68261651851516259250303337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91015535802021679000404449 68261651851516259250303337)
      ·
        refine ⟨51196238888637194437727503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68261651851516259250303337 51196238888637194437727503)
        ·
          refine ⟨76794358332955791656591255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51196238888637194437727503 76794358332955791656591255)
          ·
            refine ⟨115191537499433687484886883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76794358332955791656591255 115191537499433687484886883)
            ·
              refine ⟨172787306249150531227330325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115191537499433687484886883 172787306249150531227330325)
              ·
                refine ⟨8099404980428931151281109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172787306249150531227330325 8099404980428931151281109)
                ·
                  refine ⟨189829804228803073858151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8099404980428931151281109 189829804228803073858151)
                  ·
                    rfl

theorem cell22_1663615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_1663615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663615 prefixEnd_1663615 := by exact prefixLift 1663615
  have htrace : WordTrace (prefixWord ++ tailWord_1663615) baseStart_1663615 baseEnd_1663615 := by
    simpa [prefixWord, tailWord_1663615, baseEnd_1663615] using wordTrace_append hprefix tailTrace_1663615
  have hstable : (prefixWord ++ tailWord_1663615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663615).length < 2 ^ (prefixWord ++ tailWord_1663615).sum := by decide
  have hdescent : baseEnd_1663615 < baseStart_1663615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663679 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 1, 4]
def baseStart_1663679 : Nat := 118140960795 + 1663679 * 2 ^ 59
def prefixEnd_1663679 : Nat := 4983230072969 + 3 ^ 40 * 1663679 * 2
def baseEnd_1663679 : Nat := 569511321194334387974257

theorem tailTrace_1663679 : CollatzResearch.WordTrace tailWord_1663679 prefixEnd_1663679 569511321194334387974257 := by
  unfold tailWord_1663679
  simp only [CollatzResearch.WordTrace]
  refine ⟨60679358139782591597266091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40452905426521727731510727 60679358139782591597266091)
  ·
    refine ⟨91019037209673887395899137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60679358139782591597266091 91019037209673887395899137)
    ·
      refine ⟨68264277907255415546924353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91019037209673887395899137 68264277907255415546924353)
      ·
        refine ⟨51198208430441561660193265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68264277907255415546924353 51198208430441561660193265)
        ·
          refine ⟨38398656322831171245144949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51198208430441561660193265 38398656322831171245144949)
          ·
            refine ⟨3599874030265422304232339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38398656322831171245144949 3599874030265422304232339)
            ·
              refine ⟨5399811045398133456348509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599874030265422304232339 5399811045398133456348509)
              ·
                refine ⟨2024929142024300046130691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5399811045398133456348509 2024929142024300046130691)
                ·
                  refine ⟨3037393713036450069196037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024929142024300046130691 3037393713036450069196037)
                  ·
                    refine ⟨569511321194334387974257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037393713036450069196037 569511321194334387974257)
                    ·
                      rfl

theorem cell22_1663679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_1663679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663679 prefixEnd_1663679 := by exact prefixLift 1663679
  have htrace : WordTrace (prefixWord ++ tailWord_1663679) baseStart_1663679 baseEnd_1663679 := by
    simpa [prefixWord, tailWord_1663679, baseEnd_1663679] using wordTrace_append hprefix tailTrace_1663679
  have hstable : (prefixWord ++ tailWord_1663679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663679).length < 2 ^ (prefixWord ++ tailWord_1663679).sum := by decide
  have hdescent : baseEnd_1663679 < baseStart_1663679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663694 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_1663694 : Nat := 118140960795 + 1663694 * 2 ^ 59
def prefixEnd_1663694 : Nat := 4983230072969 + 3 ^ 40 * 1663694 * 2
def baseEnd_1663694 : Nat := 189838818666959782949737

theorem tailTrace_1663694 : CollatzResearch.WordTrace tailWord_1663694 prefixEnd_1663694 189838818666959782949737 := by
  unfold tailWord_1663694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584988154341031144882767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40453270156485499439374757 7584988154341031144882767)
  ·
    refine ⟨11377482231511546717324151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7584988154341031144882767 11377482231511546717324151)
    ·
      refine ⟨17066223347267320075986227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11377482231511546717324151 17066223347267320075986227)
      ·
        refine ⟨25599335020900980113979341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17066223347267320075986227 25599335020900980113979341)
        ·
          refine ⟨9599750632837867542742253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25599335020900980113979341 9599750632837867542742253)
          ·
            refine ⟨3599906487314200328528345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9599750632837867542742253 3599906487314200328528345)
            ·
              refine ⟨2699929865485650246396259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599906487314200328528345 2699929865485650246396259)
              ·
                refine ⟨4049894798228475369594389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699929865485650246396259 4049894798228475369594389)
                ·
                  refine ⟨189838818666959782949737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4049894798228475369594389 189838818666959782949737)
                  ·
                    rfl

theorem cell22_1663694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_1663694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663694 prefixEnd_1663694 := by exact prefixLift 1663694
  have htrace : WordTrace (prefixWord ++ tailWord_1663694) baseStart_1663694 baseEnd_1663694 := by
    simpa [prefixWord, tailWord_1663694, baseEnd_1663694] using wordTrace_append hprefix tailTrace_1663694
  have hstable : (prefixWord ++ tailWord_1663694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663694).length < 2 ^ (prefixWord ++ tailWord_1663694).sum := by decide
  have hdescent : baseEnd_1663694 < baseStart_1663694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663805 : List Nat := [1, 4, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_1663805 : Nat := 118140960795 + 1663805 * 2 ^ 59
def prefixEnd_1663805 : Nat := 4983230072969 + 3 ^ 40 * 1663805 * 2
def baseEnd_1663805 : Nat := 569554453569312059323871

theorem tailTrace_1663805 : CollatzResearch.WordTrace tailWord_1663805 prefixEnd_1663805 569554453569312059323871 := by
  unfold tailWord_1663805
  simp only [CollatzResearch.WordTrace]
  refine ⟨60683953737326115116352869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40455969158217410077568579 60683953737326115116352869)
  ·
    refine ⟨11378241325748646584316163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60683953737326115116352869 11378241325748646584316163)
    ·
      refine ⟨17067361988622969876474245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11378241325748646584316163 17067361988622969876474245)
      ·
        refine ⟨3200130372866806851838921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17067361988622969876474245 3200130372866806851838921)
        ·
          refine ⟨2400097779650105138879191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3200130372866806851838921 2400097779650105138879191)
          ·
            refine ⟨3600146669475157708318787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400097779650105138879191 3600146669475157708318787)
            ·
              refine ⟨5400220004212736562478181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600146669475157708318787 5400220004212736562478181)
              ·
                refine ⟨1012541250789888105464659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5400220004212736562478181 1012541250789888105464659)
                ·
                  refine ⟨1518811876184832158196989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012541250789888105464659 1518811876184832158196989)
                  ·
                    refine ⟨569554453569312059323871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1518811876184832158196989 569554453569312059323871)
                    ·
                      rfl

theorem cell22_1663805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_1663805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663805 prefixEnd_1663805 := by exact prefixLift 1663805
  have htrace : WordTrace (prefixWord ++ tailWord_1663805) baseStart_1663805 baseEnd_1663805 := by
    simpa [prefixWord, tailWord_1663805, baseEnd_1663805] using wordTrace_append hprefix tailTrace_1663805
  have hstable : (prefixWord ++ tailWord_1663805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663805).length < 2 ^ (prefixWord ++ tailWord_1663805).sum := by decide
  have hdescent : baseEnd_1663805 < baseStart_1663805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663829 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 6]
def baseStart_1663829 : Nat := 118140960795 + 1663829 * 2 ^ 59
def prefixEnd_1663829 : Nat := 4983230072969 + 3 ^ 40 * 1663829 * 2
def baseEnd_1663829 : Nat := 189854223086594665574599

theorem tailTrace_1663829 : CollatzResearch.WordTrace tailWord_1663829 prefixEnd_1663829 189854223086594665574599 := by
  unfold tailWord_1663829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60684829089239167215226541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40456552726159444810151027 60684829089239167215226541)
  ·
    refine ⟨22756810908464687705709953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60684829089239167215226541 22756810908464687705709953)
    ·
      refine ⟨17067608181348515779282465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22756810908464687705709953 17067608181348515779282465)
      ·
        refine ⟨12800706136011386834461849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17067608181348515779282465 12800706136011386834461849)
        ·
          refine ⟨9600529602008540125846387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800706136011386834461849 9600529602008540125846387)
          ·
            refine ⟨14400794403012810188769581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600529602008540125846387 14400794403012810188769581)
            ·
              refine ⟨5400297901129803820788593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14400794403012810188769581 5400297901129803820788593)
              ·
                refine ⟨4050223425847352865591445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400297901129803820788593 4050223425847352865591445)
                ·
                  refine ⟨189854223086594665574599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4050223425847352865591445 189854223086594665574599)
                  ·
                    rfl

theorem cell22_1663829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_1663829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663829 prefixEnd_1663829 := by exact prefixLift 1663829
  have htrace : WordTrace (prefixWord ++ tailWord_1663829) baseStart_1663829 baseEnd_1663829 := by
    simpa [prefixWord, tailWord_1663829, baseEnd_1663829] using wordTrace_append hprefix tailTrace_1663829
  have hstable : (prefixWord ++ tailWord_1663829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663829).length < 2 ^ (prefixWord ++ tailWord_1663829).sum := by decide
  have hdescent : baseEnd_1663829 < baseStart_1663829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663848 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_1663848 : Nat := 118140960795 + 1663848 * 2 ^ 59
def prefixEnd_1663848 : Nat := 4983230072969 + 3 ^ 40 * 1663848 * 2
def baseEnd_1663848 : Nat := 569569173348074280498739

theorem tailTrace_1663848 : CollatzResearch.WordTrace tailWord_1663848 prefixEnd_1663848 569569173348074280498739 := by
  unfold tailWord_1663848
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342761038085166730084099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40457014717446888973445465 30342761038085166730084099)
  ·
    refine ⟨45514141557127750095126149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30342761038085166730084099 45514141557127750095126149)
    ·
      refine ⟨8533901541961453142836153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45514141557127750095126149 8533901541961453142836153)
      ·
        refine ⟨6400426156471089857127115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8533901541961453142836153 6400426156471089857127115)
        ·
          refine ⟨9600639234706634785690673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6400426156471089857127115 9600639234706634785690673)
          ·
            refine ⟨7200479426029976089268005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9600639234706634785690673 7200479426029976089268005)
            ·
              refine ⟨1350089892380620516737751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7200479426029976089268005 1350089892380620516737751)
              ·
                refine ⟨2025134838570930775106627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350089892380620516737751 2025134838570930775106627)
                ·
                  refine ⟨3037702257856396162659941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025134838570930775106627 3037702257856396162659941)
                  ·
                    refine ⟨569569173348074280498739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037702257856396162659941 569569173348074280498739)
                    ·
                      rfl

theorem cell22_1663848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_1663848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663848 prefixEnd_1663848 := by exact prefixLift 1663848
  have htrace : WordTrace (prefixWord ++ tailWord_1663848) baseStart_1663848 baseEnd_1663848 := by
    simpa [prefixWord, tailWord_1663848, baseEnd_1663848] using wordTrace_append hprefix tailTrace_1663848
  have hstable : (prefixWord ++ tailWord_1663848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663848).length < 2 ^ (prefixWord ++ tailWord_1663848).sum := by decide
  have hdescent : baseEnd_1663848 < baseStart_1663848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663859 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_1663859 : Nat := 118140960795 + 1663859 * 2 ^ 59
def prefixEnd_1663859 : Nat := 4983230072969 + 3 ^ 40 * 1663859 * 2
def baseEnd_1663859 : Nat := 569572938872873918473705

theorem tailTrace_1663859 : CollatzResearch.WordTrace tailWord_1663859 prefixEnd_1663859 569572938872873918473705 := by
  unfold tailWord_1663859
  simp only [CollatzResearch.WordTrace]
  refine ⟨60685923279130482338818631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40457282186086988225879087 60685923279130482338818631)
  ·
    refine ⟨91028884918695723508227947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60685923279130482338818631 91028884918695723508227947)
    ·
      refine ⟨136543327378043585262341921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91028884918695723508227947 136543327378043585262341921)
      ·
        refine ⟨102407495533532688946756441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136543327378043585262341921 102407495533532688946756441)
        ·
          refine ⟨76805621650149516710067331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102407495533532688946756441 76805621650149516710067331)
          ·
            refine ⟨115208432475224275065100997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76805621650149516710067331 115208432475224275065100997)
            ·
              refine ⟨21601581089104551574706437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115208432475224275065100997 21601581089104551574706437)
              ·
                refine ⟨4050296454207103420257457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21601581089104551574706437 4050296454207103420257457)
                ·
                  refine ⟨3037722340655327565193093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050296454207103420257457 3037722340655327565193093)
                  ·
                    refine ⟨569572938872873918473705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037722340655327565193093 569572938872873918473705)
                    ·
                      rfl

theorem cell22_1663859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_1663859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663859 prefixEnd_1663859 := by exact prefixLift 1663859
  have htrace : WordTrace (prefixWord ++ tailWord_1663859) baseStart_1663859 baseEnd_1663859 := by
    simpa [prefixWord, tailWord_1663859, baseEnd_1663859] using wordTrace_append hprefix tailTrace_1663859
  have hstable : (prefixWord ++ tailWord_1663859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663859).length < 2 ^ (prefixWord ++ tailWord_1663859).sum := by decide
  have hdescent : baseEnd_1663859 < baseStart_1663859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663936 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_1663936 : Nat := 118140960795 + 1663936 * 2 ^ 59
def prefixEnd_1663936 : Nat := 4983230072969 + 3 ^ 40 * 1663936 * 2
def baseEnd_1663936 : Nat := 189866432515490461432823

theorem tailTrace_1663936 : CollatzResearch.WordTrace tailWord_1663936 prefixEnd_1663936 189866432515490461432823 := by
  unfold tailWord_1663936
  simp only [CollatzResearch.WordTrace]
  refine ⟨30344365849925762244685831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40459154466567682992914441 30344365849925762244685831)
  ·
    refine ⟨45516548774888643367028747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30344365849925762244685831 45516548774888643367028747)
    ·
      refine ⟨68274823162332965050543121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45516548774888643367028747 68274823162332965050543121)
      ·
        refine ⟨51206117371749723787907341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68274823162332965050543121 51206117371749723787907341)
        ·
          refine ⟨19202294014406146420465253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51206117371749723787907341 19202294014406146420465253)
          ·
            refine ⟨3600430127701152453837235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19202294014406146420465253 3600430127701152453837235)
            ·
              refine ⟨5400645191551728680755853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600430127701152453837235 5400645191551728680755853)
              ·
                refine ⟨2025241946831898255283445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5400645191551728680755853 2025241946831898255283445)
                ·
                  refine ⟨189866432515490461432823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025241946831898255283445 189866432515490461432823)
                  ·
                    rfl

theorem cell22_1663936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_1663936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663936 prefixEnd_1663936 := by exact prefixLift 1663936
  have htrace : WordTrace (prefixWord ++ tailWord_1663936) baseStart_1663936 baseEnd_1663936 := by
    simpa [prefixWord, tailWord_1663936, baseEnd_1663936] using wordTrace_append hprefix tailTrace_1663936
  have hstable : (prefixWord ++ tailWord_1663936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663936).length < 2 ^ (prefixWord ++ tailWord_1663936).sum := by decide
  have hdescent : baseEnd_1663936 < baseStart_1663936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663970 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1663970 : Nat := 118140960795 + 1663970 * 2 ^ 59
def prefixEnd_1663970 : Nat := 4983230072969 + 3 ^ 40 * 1663970 * 2
def baseEnd_1663970 : Nat := 189870312147102209649455

theorem tailTrace_1663970 : CollatzResearch.WordTrace tailWord_1663970 prefixEnd_1663970 189870312147102209649455 := by
  unfold tailWord_1663970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172492945432087074027341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40459981187818898864072909 15172492945432087074027341)
  ·
    refine ⟨5689684854537032652760253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15172492945432087074027341 5689684854537032652760253)
    ·
      refine ⟨2133631820451387244785095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5689684854537032652760253 2133631820451387244785095)
      ·
        refine ⟨3200447730677080867177643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133631820451387244785095 3200447730677080867177643)
        ·
          refine ⟨4800671596015621300766465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200447730677080867177643 4800671596015621300766465)
          ·
            refine ⟨3600503697011715975574849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4800671596015621300766465 3600503697011715975574849)
            ·
              refine ⟨2700377772758786981681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600503697011715975574849 2700377772758786981681137)
              ·
                refine ⟨2025283329569090236260853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700377772758786981681137 2025283329569090236260853)
                ·
                  refine ⟨189870312147102209649455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025283329569090236260853 189870312147102209649455)
                  ·
                    rfl

theorem cell22_1663970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1663970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663970 prefixEnd_1663970 := by exact prefixLift 1663970
  have htrace : WordTrace (prefixWord ++ tailWord_1663970) baseStart_1663970 baseEnd_1663970 := by
    simpa [prefixWord, tailWord_1663970, baseEnd_1663970] using wordTrace_append hprefix tailTrace_1663970
  have hstable : (prefixWord ++ tailWord_1663970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663970).length < 2 ^ (prefixWord ++ tailWord_1663970).sum := by decide
  have hdescent : baseEnd_1663970 < baseStart_1663970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663996 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1663996 : Nat := 118140960795 + 1663996 * 2 ^ 59
def prefixEnd_1663996 : Nat := 4983230072969 + 3 ^ 40 * 1663996 * 2
def baseEnd_1663996 : Nat := 569619836772651227798285

theorem tailTrace_1663996 : CollatzResearch.WordTrace tailWord_1663996 prefixEnd_1663996 569619836772651227798285 := by
  unfold tailWord_1663996
  simp only [CollatzResearch.WordTrace]
  refine ⟨30345460039817077368277921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40460613386422769824370561 30345460039817077368277921)
  ·
    refine ⟨22759095029862808026208441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30345460039817077368277921 22759095029862808026208441)
    ·
      refine ⟨17069321272397106019656331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22759095029862808026208441 17069321272397106019656331)
      ·
        refine ⟨25603981908595659029484497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17069321272397106019656331 25603981908595659029484497)
        ·
          refine ⟨19202986431446744272113373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25603981908595659029484497 19202986431446744272113373)
          ·
            refine ⟨7201119911792529102042515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19202986431446744272113373 7201119911792529102042515)
            ·
              refine ⟨10801679867688793653063773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201119911792529102042515 10801679867688793653063773)
              ·
                refine ⟨4050629950383297619898915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10801679867688793653063773 4050629950383297619898915)
                ·
                  refine ⟨6075944925574946429848373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050629950383297619898915 6075944925574946429848373)
                  ·
                    refine ⟨569619836772651227798285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6075944925574946429848373 569619836772651227798285)
                    ·
                      rfl

theorem cell22_1663996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1663996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1663996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1663996 prefixEnd_1663996 := by exact prefixLift 1663996
  have htrace : WordTrace (prefixWord ++ tailWord_1663996) baseStart_1663996 baseEnd_1663996 := by
    simpa [prefixWord, tailWord_1663996, baseEnd_1663996] using wordTrace_append hprefix tailTrace_1663996
  have hstable : (prefixWord ++ tailWord_1663996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663996).length < 2 ^ (prefixWord ++ tailWord_1663996).sum := by decide
  have hdescent : baseEnd_1663996 < baseStart_1663996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664009 : List Nat := [1, 2, 1, 1, 3, 1, 1, 12]
def baseStart_1664009 : Nat := 118140960795 + 1664009 * 2 ^ 59
def prefixEnd_1664009 : Nat := 4983230072969 + 3 ^ 40 * 1664009 * 2
def baseEnd_1664009 : Nat := 63291587437591503024805

theorem tailTrace_1664009 : CollatzResearch.WordTrace tailWord_1664009 prefixEnd_1664009 63291587437591503024805 := by
  unfold tailWord_1664009
  simp only [CollatzResearch.WordTrace]
  refine ⟨60691394228587057956779081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40460929485724705304519387 60691394228587057956779081)
  ·
    refine ⟨45518545671440293467584311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60691394228587057956779081 45518545671440293467584311)
    ·
      refine ⟨68277818507160440201376467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45518545671440293467584311 68277818507160440201376467)
      ·
        refine ⟨102416727760740660302064701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68277818507160440201376467 102416727760740660302064701)
        ·
          refine ⟨38406272910277747613274263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102416727760740660302064701 38406272910277747613274263)
          ·
            refine ⟨57609409365416621419911395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38406272910277747613274263 57609409365416621419911395)
            ·
              refine ⟨86414114048124932129867093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57609409365416621419911395 86414114048124932129867093)
              ·
                refine ⟨63291587437591503024805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 86414114048124932129867093 63291587437591503024805)
                ·
                  rfl

theorem cell22_1664009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 12].length) (baseStart_1664009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664009 prefixEnd_1664009 := by exact prefixLift 1664009
  have htrace : WordTrace (prefixWord ++ tailWord_1664009) baseStart_1664009 baseEnd_1664009 := by
    simpa [prefixWord, tailWord_1664009, baseEnd_1664009] using wordTrace_append hprefix tailTrace_1664009
  have hstable : (prefixWord ++ tailWord_1664009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664009).length < 2 ^ (prefixWord ++ tailWord_1664009).sum := by decide
  have hdescent : baseEnd_1664009 < baseStart_1664009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664011 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_1664011 : Nat := 118140960795 + 1664011 * 2 ^ 59
def prefixEnd_1664011 : Nat := 4983230072969 + 3 ^ 40 * 1664011 * 2
def baseEnd_1664011 : Nat := 569624971579196188673239

theorem tailTrace_1664011 : CollatzResearch.WordTrace tailWord_1664011 prefixEnd_1664011 569624971579196188673239 := by
  unfold tailWord_1664011
  simp only [CollatzResearch.WordTrace]
  refine ⟨60691467174579812298351887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40460978116386541532234591 60691467174579812298351887)
  ·
    refine ⟨91037200761869718447527831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60691467174579812298351887 91037200761869718447527831)
    ·
      refine ⟨136555801142804577671291747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91037200761869718447527831 136555801142804577671291747)
      ·
        refine ⟨204833701714206866506937621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136555801142804577671291747 204833701714206866506937621)
        ·
          refine ⟨9601579767853446867512701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204833701714206866506937621 9601579767853446867512701)
          ·
            refine ⟨3600592412945042575317263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9601579767853446867512701 3600592412945042575317263)
            ·
              refine ⟨5400888619417563862975895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600592412945042575317263 5400888619417563862975895)
              ·
                refine ⟨8101332929126345794463843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400888619417563862975895 8101332929126345794463843)
                ·
                  refine ⟨12151999393689518691695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101332929126345794463843 12151999393689518691695765)
                  ·
                    refine ⟨569624971579196188673239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12151999393689518691695765 569624971579196188673239)
                    ·
                      rfl

theorem cell22_1664011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_1664011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664011 prefixEnd_1664011 := by exact prefixLift 1664011
  have htrace : WordTrace (prefixWord ++ tailWord_1664011) baseStart_1664011 baseEnd_1664011 := by
    simpa [prefixWord, tailWord_1664011, baseEnd_1664011] using wordTrace_append hprefix tailTrace_1664011
  have hstable : (prefixWord ++ tailWord_1664011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664011).length < 2 ^ (prefixWord ++ tailWord_1664011).sum := by decide
  have hdescent : baseEnd_1664011 < baseStart_1664011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664058 : List Nat := [3, 1, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1664058 : Nat := 118140960795 + 1664058 * 2 ^ 59
def prefixEnd_1664058 : Nat := 4983230072969 + 3 ^ 40 * 1664058 * 2
def baseEnd_1664058 : Nat := 569641060639703732748095

theorem tailTrace_1664058 : CollatzResearch.WordTrace tailWord_1664058 prefixEnd_1664058 569641060639703732748095 := by
  unfold tailWord_1664058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173295351352384831328207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40462120936939692883541885 15173295351352384831328207)
  ·
    refine ⟨22759943027028577246992311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15173295351352384831328207 22759943027028577246992311)
    ·
      refine ⟨34139914540542865870488467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22759943027028577246992311 34139914540542865870488467)
      ·
        refine ⟨51209871810814298805732701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34139914540542865870488467 51209871810814298805732701)
        ·
          refine ⟨19203701929055362052149763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51209871810814298805732701 19203701929055362052149763)
          ·
            refine ⟨28805552893583043078224645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19203701929055362052149763 28805552893583043078224645)
            ·
              refine ⟨5401041167546820577167121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28805552893583043078224645 5401041167546820577167121)
              ·
                refine ⟨4050780875660115432875341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401041167546820577167121 4050780875660115432875341)
                ·
                  refine ⟨1519042828372543287328253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4050780875660115432875341 1519042828372543287328253)
                  ·
                    refine ⟨569641060639703732748095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519042828372543287328253 569641060639703732748095)
                    ·
                      rfl

theorem cell22_1664058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1664058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664058 prefixEnd_1664058 := by exact prefixLift 1664058
  have htrace : WordTrace (prefixWord ++ tailWord_1664058) baseStart_1664058 baseEnd_1664058 := by
    simpa [prefixWord, tailWord_1664058, baseEnd_1664058] using wordTrace_append hprefix tailTrace_1664058
  have hstable : (prefixWord ++ tailWord_1664058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664058).length < 2 ^ (prefixWord ++ tailWord_1664058).sum := by decide
  have hdescent : baseEnd_1664058 < baseStart_1664058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664071 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 7]
def baseStart_1664071 : Nat := 118140960795 + 1664071 * 2 ^ 59
def prefixEnd_1664071 : Nat := 4983230072969 + 3 ^ 40 * 1664071 * 2
def baseEnd_1664071 : Nat := 189881836935125344057685

theorem tailTrace_1664071 : CollatzResearch.WordTrace tailWord_1664071 prefixEnd_1664071 189881836935125344057685 := by
  unfold tailWord_1664071
  simp only [CollatzResearch.WordTrace]
  refine ⟨60693655554362442545536067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40462437036241628363690711 60693655554362442545536067)
  ·
    refine ⟨91040483331543663818304101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60693655554362442545536067 91040483331543663818304101)
    ·
      refine ⟨17070090624664436965932019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91040483331543663818304101 17070090624664436965932019)
      ·
        refine ⟨25605135936996655448898029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070090624664436965932019 25605135936996655448898029)
        ·
          refine ⟨9601925976373745793336761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25605135936996655448898029 9601925976373745793336761)
          ·
            refine ⟨7201444482280309345002571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9601925976373745793336761 7201444482280309345002571)
            ·
              refine ⟨10802166723420464017503857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201444482280309345002571 10802166723420464017503857)
              ·
                refine ⟨8101625042565348013127893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10802166723420464017503857 8101625042565348013127893)
                ·
                  refine ⟨189881836935125344057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8101625042565348013127893 189881836935125344057685)
                  ·
                    rfl

theorem cell22_1664071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_1664071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664071 prefixEnd_1664071 := by exact prefixLift 1664071
  have htrace : WordTrace (prefixWord ++ tailWord_1664071) baseStart_1664071 baseEnd_1664071 := by
    simpa [prefixWord, tailWord_1664071, baseEnd_1664071] using wordTrace_append hprefix tailTrace_1664071
  have hstable : (prefixWord ++ tailWord_1664071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664071).length < 2 ^ (prefixWord ++ tailWord_1664071).sum := by decide
  have hdescent : baseEnd_1664071 < baseStart_1664071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664105 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 5]
def baseStart_1664105 : Nat := 118140960795 + 1664105 * 2 ^ 59
def prefixEnd_1664105 : Nat := 4983230072969 + 3 ^ 40 * 1664105 * 2
def baseEnd_1664105 : Nat := 189885716566737092274317

theorem tailTrace_1664105 : CollatzResearch.WordTrace tailWord_1664105 prefixEnd_1664105 189885716566737092274317 := by
  unfold tailWord_1664105
  simp only [CollatzResearch.WordTrace]
  refine ⟨60694895636239266352273769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40463263757492844234849179 60694895636239266352273769)
  ·
    refine ⟨45521171727179449764205327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60694895636239266352273769 45521171727179449764205327)
    ·
      refine ⟨68281757590769174646307991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45521171727179449764205327 68281757590769174646307991)
      ·
        refine ⟨102422636386153761969461987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68281757590769174646307991 102422636386153761969461987)
        ·
          refine ⟨153633954579230642954192981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102422636386153761969461987 153633954579230642954192981)
          ·
            refine ⟨1800397905225359097119449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 153633954579230642954192981 1800397905225359097119449)
            ·
              refine ⟨1350298428919019322839587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800397905225359097119449 1350298428919019322839587)
              ·
                refine ⟨2025447643378528984259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350298428919019322839587 2025447643378528984259381)
                ·
                  refine ⟨189885716566737092274317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025447643378528984259381 189885716566737092274317)
                  ·
                    rfl

theorem cell22_1664105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_1664105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664105 prefixEnd_1664105 := by exact prefixLift 1664105
  have htrace : WordTrace (prefixWord ++ tailWord_1664105) baseStart_1664105 baseEnd_1664105 := by
    simpa [prefixWord, tailWord_1664105, baseEnd_1664105] using wordTrace_append hprefix tailTrace_1664105
  have hstable : (prefixWord ++ tailWord_1664105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664105).length < 2 ^ (prefixWord ++ tailWord_1664105).sum := by decide
  have hdescent : baseEnd_1664105 < baseStart_1664105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664165 : List Nat := [1, 3, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_1664165 : Nat := 118140960795 + 1664165 * 2 ^ 59
def prefixEnd_1664165 : Nat := 4983230072969 + 3 ^ 40 * 1664165 * 2
def baseEnd_1664165 : Nat := 569677688926391120322767

theorem tailTrace_1664165 : CollatzResearch.WordTrace tailWord_1664165 prefixEnd_1664165 569677688926391120322767 := by
  unfold tailWord_1664165
  simp only [CollatzResearch.WordTrace]
  refine ⟨60697084016021896599457949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40464722677347931066305299 60697084016021896599457949)
  ·
    refine ⟨22761406506008211224796731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60697084016021896599457949 22761406506008211224796731)
    ·
      refine ⟨34142109759012316837195097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22761406506008211224796731 34142109759012316837195097)
      ·
        refine ⟨25606582319259237627896323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34142109759012316837195097 25606582319259237627896323)
        ·
          refine ⟨38409873478888856441844485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25606582319259237627896323 38409873478888856441844485)
          ·
            refine ⟨7201851277291660582845841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38409873478888856441844485 7201851277291660582845841)
            ·
              refine ⟨5401388457968745437134381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201851277291660582845841 5401388457968745437134381)
              ·
                refine ⟨2025520671738279538925393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401388457968745437134381 2025520671738279538925393)
                ·
                  refine ⟨1519140503803709654194045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025520671738279538925393 1519140503803709654194045)
                  ·
                    refine ⟨569677688926391120322767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519140503803709654194045 569677688926391120322767)
                    ·
                      rfl

theorem cell22_1664165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_1664165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664165 prefixEnd_1664165 := by exact prefixLift 1664165
  have htrace : WordTrace (prefixWord ++ tailWord_1664165) baseStart_1664165 baseEnd_1664165 := by
    simpa [prefixWord, tailWord_1664165, baseEnd_1664165] using wordTrace_append hprefix tailTrace_1664165
  have hstable : (prefixWord ++ tailWord_1664165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664165).length < 2 ^ (prefixWord ++ tailWord_1664165).sum := by decide
  have hdescent : baseEnd_1664165 < baseStart_1664165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_1664176 : Nat := 118140960795 + 1664176 * 2 ^ 59
def prefixEnd_1664176 : Nat := 4983230072969 + 3 ^ 40 * 1664176 * 2
def baseEnd_1664176 : Nat := 569681454451190758297733

theorem tailTrace_1664176 : CollatzResearch.WordTrace tailWord_1664176 prefixEnd_1664176 569681454451190758297733 := by
  unfold tailWord_1664176
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348742609491022739054191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40464990145988030318738921 30348742609491022739054191)
  ·
    refine ⟨45523113914236534108581287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30348742609491022739054191 45523113914236534108581287)
    ·
      refine ⟨68284670871354801162871931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45523113914236534108581287 68284670871354801162871931)
      ·
        refine ⟨102427006307032201744307897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68284670871354801162871931 102427006307032201744307897)
        ·
          refine ⟨76820254730274151308230923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102427006307032201744307897 76820254730274151308230923)
          ·
            refine ⟨115230382095411226962346385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76820254730274151308230923 115230382095411226962346385)
            ·
              refine ⟨86422786571558420221759789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115230382095411226962346385 86422786571558420221759789)
              ·
                refine ⟨32408544964334407583159921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86422786571558420221759789 32408544964334407583159921)
                ·
                  refine ⟨24306408723250805687369941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32408544964334407583159921 24306408723250805687369941)
                  ·
                    refine ⟨569681454451190758297733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24306408723250805687369941 569681454451190758297733)
                    ·
                      rfl

theorem cell22_1664176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_1664176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664176 prefixEnd_1664176 := by exact prefixLift 1664176
  have htrace : WordTrace (prefixWord ++ tailWord_1664176) baseStart_1664176 baseEnd_1664176 := by
    simpa [prefixWord, tailWord_1664176, baseEnd_1664176] using wordTrace_append hprefix tailTrace_1664176
  have hstable : (prefixWord ++ tailWord_1664176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664176).length < 2 ^ (prefixWord ++ tailWord_1664176).sum := by decide
  have hdescent : baseEnd_1664176 < baseStart_1664176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664223 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 5]
def baseStart_1664223 : Nat := 118140960795 + 1664223 * 2 ^ 59
def prefixEnd_1664223 : Nat := 4983230072969 + 3 ^ 40 * 1664223 * 2
def baseEnd_1664223 : Nat := 189899181170566100790863

theorem tailTrace_1664223 : CollatzResearch.WordTrace tailWord_1664223 prefixEnd_1664223 189899181170566100790863 := by
  unfold tailWord_1664223
  simp only [CollatzResearch.WordTrace]
  refine ⟨60699199449811772505069323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40466132966541181670046215 60699199449811772505069323)
  ·
    refine ⟨91048799174717658757603985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60699199449811772505069323 91048799174717658757603985)
    ·
      refine ⟨68286599381038244068202989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91048799174717658757603985 68286599381038244068202989)
      ·
        refine ⟨25607474767889341525576121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68286599381038244068202989 25607474767889341525576121)
        ·
          refine ⟨19205606075917006144182091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25607474767889341525576121 19205606075917006144182091)
          ·
            refine ⟨28808409113875509216273137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19205606075917006144182091 28808409113875509216273137)
            ·
              refine ⟨21606306835406631912204853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28808409113875509216273137 21606306835406631912204853)
              ·
                refine ⟨2025591265819371741769205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21606306835406631912204853 2025591265819371741769205)
                ·
                  refine ⟨189899181170566100790863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025591265819371741769205 189899181170566100790863)
                  ·
                    rfl

theorem cell22_1664223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 5].length) (baseStart_1664223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664223 prefixEnd_1664223 := by exact prefixLift 1664223
  have htrace : WordTrace (prefixWord ++ tailWord_1664223) baseStart_1664223 baseEnd_1664223 := by
    simpa [prefixWord, tailWord_1664223, baseEnd_1664223] using wordTrace_append hprefix tailTrace_1664223
  have hstable : (prefixWord ++ tailWord_1664223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664223).length < 2 ^ (prefixWord ++ tailWord_1664223).sum := by decide
  have hdescent : baseEnd_1664223 < baseStart_1664223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664238 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1664238 : Nat := 118140960795 + 1664238 * 2 ^ 59
def prefixEnd_1664238 : Nat := 4983230072969 + 3 ^ 40 * 1664238 * 2
def baseEnd_1664238 : Nat := 569702678318243263247543

theorem tailTrace_1664238 : CollatzResearch.WordTrace tailWord_1664238 prefixEnd_1664238 569702678318243263247543 := by
  unfold tailWord_1664238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587468318094678758358171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40466497696504953377910245 7587468318094678758358171)
  ·
    refine ⟨11381202477142018137537257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7587468318094678758358171 11381202477142018137537257)
    ·
      refine ⟨8535901857856513603152943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11381202477142018137537257 8535901857856513603152943)
      ·
        refine ⟨12803852786784770404729415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8535901857856513603152943 12803852786784770404729415)
        ·
          refine ⟨19205779180177155607094123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12803852786784770404729415 19205779180177155607094123)
          ·
            refine ⟨28808668770265733410641185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19205779180177155607094123 28808668770265733410641185)
            ·
              refine ⟨21606501577699300057980889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28808668770265733410641185 21606501577699300057980889)
              ·
                refine ⟨16204876183274475043485667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21606501577699300057980889 16204876183274475043485667)
                ·
                  refine ⟨24307314274911712565228501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16204876183274475043485667 24307314274911712565228501)
                  ·
                    refine ⟨569702678318243263247543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24307314274911712565228501 569702678318243263247543)
                    ·
                      rfl

theorem cell22_1664238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1664238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664238 prefixEnd_1664238 := by exact prefixLift 1664238
  have htrace : WordTrace (prefixWord ++ tailWord_1664238) baseStart_1664238 baseEnd_1664238 := by
    simpa [prefixWord, tailWord_1664238, baseEnd_1664238] using wordTrace_append hprefix tailTrace_1664238
  have hstable : (prefixWord ++ tailWord_1664238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664238).length < 2 ^ (prefixWord ++ tailWord_1664238).sum := by decide
  have hdescent : baseEnd_1664238 < baseStart_1664238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664253 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1664253 : Nat := 118140960795 + 1664253 * 2 ^ 59
def prefixEnd_1664253 : Nat := 4983230072969 + 3 ^ 40 * 1664253 * 2
def baseEnd_1664253 : Nat := 569707813124788224122497

theorem tailTrace_1664253 : CollatzResearch.WordTrace tailWord_1664253 prefixEnd_1664253 569707813124788224122497 := by
  unfold tailWord_1664253
  simp only [CollatzResearch.WordTrace]
  refine ⟨60700293639703087628661413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40466862426468725085774275 60700293639703087628661413)
  ·
    refine ⟨11381305057444328930374015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60700293639703087628661413 11381305057444328930374015)
    ·
      refine ⟨17071957586166493395561023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11381305057444328930374015 17071957586166493395561023)
      ·
        refine ⟨25607936379249740093341535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17071957586166493395561023 25607936379249740093341535)
        ·
          refine ⟨38411904568874610140012303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25607936379249740093341535 38411904568874610140012303)
          ·
            refine ⟨57617856853311915210018455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38411904568874610140012303 57617856853311915210018455)
            ·
              refine ⟨86426785279967872815027683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57617856853311915210018455 86426785279967872815027683)
              ·
                refine ⟨129640177919951809222541525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86426785279967872815027683 129640177919951809222541525)
                ·
                  refine ⟨3038441669998870528653317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129640177919951809222541525 3038441669998870528653317)
                  ·
                    refine ⟨569707813124788224122497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3038441669998870528653317 569707813124788224122497)
                    ·
                      rfl

theorem cell22_1664253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1664253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664253 prefixEnd_1664253 := by exact prefixLift 1664253
  have htrace : WordTrace (prefixWord ++ tailWord_1664253) baseStart_1664253 baseEnd_1664253 := by
    simpa [prefixWord, tailWord_1664253, baseEnd_1664253] using wordTrace_append hprefix tailTrace_1664253
  have hstable : (prefixWord ++ tailWord_1664253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664253).length < 2 ^ (prefixWord ++ tailWord_1664253).sum := by decide
  have hdescent : baseEnd_1664253 < baseStart_1664253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664274 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1664274 : Nat := 118140960795 + 1664274 * 2 ^ 59
def prefixEnd_1664274 : Nat := 4983230072969 + 3 ^ 40 * 1664274 * 2
def baseEnd_1664274 : Nat := 189905000617983723115811

theorem tailTrace_1664274 : CollatzResearch.WordTrace tailWord_1664274 prefixEnd_1664274 189905000617983723115811 := by
  unfold tailWord_1664274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175264893156752053793969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40467373048418005476783917 15175264893156752053793969)
  ·
    refine ⟨11381448669867564040345477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15175264893156752053793969 11381448669867564040345477)
    ·
      refine ⟨2134021625600168257564777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11381448669867564040345477 2134021625600168257564777)
      ·
        refine ⟨1600516219200126193173583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2134021625600168257564777 1600516219200126193173583)
        ·
          refine ⟨2400774328800189289760375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600516219200126193173583 2400774328800189289760375)
          ·
            refine ⟨3601161493200283934640563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400774328800189289760375 3601161493200283934640563)
            ·
              refine ⟨5401742239800425901960845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601161493200283934640563 5401742239800425901960845)
              ·
                refine ⟨2025653339925159713235317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401742239800425901960845 2025653339925159713235317)
                ·
                  refine ⟨189905000617983723115811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025653339925159713235317 189905000617983723115811)
                  ·
                    rfl

theorem cell22_1664274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1664274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664274 prefixEnd_1664274 := by exact prefixLift 1664274
  have htrace : WordTrace (prefixWord ++ tailWord_1664274) baseStart_1664274 baseEnd_1664274 := by
    simpa [prefixWord, tailWord_1664274, baseEnd_1664274] using wordTrace_append hprefix tailTrace_1664274
  have hstable : (prefixWord ++ tailWord_1664274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664274).length < 2 ^ (prefixWord ++ tailWord_1664274).sum := by decide
  have hdescent : baseEnd_1664274 < baseStart_1664274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664283 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_1664283 : Nat := 118140960795 + 1664283 * 2 ^ 59
def prefixEnd_1664283 : Nat := 4983230072969 + 3 ^ 40 * 1664283 * 2
def baseEnd_1664283 : Nat := 569718082737878145872405

theorem tailTrace_1664283 : CollatzResearch.WordTrace tailWord_1664283 prefixEnd_1664283 569718082737878145872405 := by
  unfold tailWord_1664283
  simp only [CollatzResearch.WordTrace]
  refine ⟨60701387829594402752253503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40467591886396268501502335 60701387829594402752253503)
  ·
    refine ⟨91052081744391604128380255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60701387829594402752253503 91052081744391604128380255)
    ·
      refine ⟨136578122616587406192570383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91052081744391604128380255 136578122616587406192570383)
      ·
        refine ⟨204867183924881109288855575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136578122616587406192570383 204867183924881109288855575)
        ·
          refine ⟨307300775887321663933283363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204867183924881109288855575 307300775887321663933283363)
          ·
            refine ⟨460951163830982495899925045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307300775887321663933283363 460951163830982495899925045)
            ·
              refine ⟨43214171609154608990617973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460951163830982495899925045 43214171609154608990617973)
              ·
                refine ⟨4051328588358244592870435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43214171609154608990617973 4051328588358244592870435)
                ·
                  refine ⟨6076992882537366889305653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051328588358244592870435 6076992882537366889305653)
                  ·
                    refine ⟨569718082737878145872405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6076992882537366889305653 569718082737878145872405)
                    ·
                      rfl

theorem cell22_1664283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_1664283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664283 prefixEnd_1664283 := by exact prefixLift 1664283
  have htrace : WordTrace (prefixWord ++ tailWord_1664283) baseStart_1664283 baseEnd_1664283 := by
    simpa [prefixWord, tailWord_1664283, baseEnd_1664283] using wordTrace_append hprefix tailTrace_1664283
  have hstable : (prefixWord ++ tailWord_1664283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664283).length < 2 ^ (prefixWord ++ tailWord_1664283).sum := by decide
  have hdescent : baseEnd_1664283 < baseStart_1664283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664313 : List Nat := [1, 2, 1, 6, 12]
def baseStart_1664313 : Nat := 118140960795 + 1664313 * 2 ^ 59
def prefixEnd_1664313 : Nat := 4983230072969 + 3 ^ 40 * 1664313 * 2
def baseEnd_1664313 : Nat := 2344561120785876821491

theorem tailTrace_1664313 : CollatzResearch.WordTrace tailWord_1664313 prefixEnd_1664313 2344561120785876821491 := by
  unfold tailWord_1664313
  simp only [CollatzResearch.WordTrace]
  refine ⟨60702482019485717875845593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40468321346323811917230395 60702482019485717875845593)
  ·
    refine ⟨45526861514614288406884195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60702482019485717875845593 45526861514614288406884195)
    ·
      refine ⟨68290292271921432610326293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45526861514614288406884195 68290292271921432610326293)
      ·
        refine ⟨3201107450246317153609045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68290292271921432610326293 3201107450246317153609045)
        ·
          refine ⟨2344561120785876821491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3201107450246317153609045 2344561120785876821491)
          ·
            rfl

theorem cell22_1664313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 12].length) (baseStart_1664313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664313 prefixEnd_1664313 := by exact prefixLift 1664313
  have htrace : WordTrace (prefixWord ++ tailWord_1664313) baseStart_1664313 baseEnd_1664313 := by
    simpa [prefixWord, tailWord_1664313, baseEnd_1664313] using wordTrace_append hprefix tailTrace_1664313
  have hstable : (prefixWord ++ tailWord_1664313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664313).length < 2 ^ (prefixWord ++ tailWord_1664313).sum := by decide
  have hdescent : baseEnd_1664313 < baseStart_1664313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664319 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 4]
def baseStart_1664319 : Nat := 118140960795 + 1664319 * 2 ^ 59
def prefixEnd_1664319 : Nat := 4983230072969 + 3 ^ 40 * 1664319 * 2
def baseEnd_1664319 : Nat := 189910135424528683990765

theorem tailTrace_1664319 : CollatzResearch.WordTrace tailWord_1664319 prefixEnd_1664319 189910135424528683990765 := by
  unfold tailWord_1664319
  simp only [CollatzResearch.WordTrace]
  refine ⟨60702700857463980900564011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40468467238309320600376007 60702700857463980900564011)
  ·
    refine ⟨91054051286195971350846017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60702700857463980900564011 91054051286195971350846017)
    ·
      refine ⟨68290538464646978513134513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91054051286195971350846017 68290538464646978513134513)
      ·
        refine ⟨51217903848485233884850885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68290538464646978513134513 51217903848485233884850885)
        ·
          refine ⟨9603356971590981353409541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51217903848485233884850885 9603356971590981353409541)
          ·
            refine ⟨1800629432173309003764289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9603356971590981353409541 1800629432173309003764289)
            ·
              refine ⟨1350472074129981752823217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800629432173309003764289 1350472074129981752823217)
              ·
                refine ⟨1012854055597486314617413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350472074129981752823217 1012854055597486314617413)
                ·
                  refine ⟨189910135424528683990765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012854055597486314617413 189910135424528683990765)
                  ·
                    rfl

theorem cell22_1664319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 4].length) (baseStart_1664319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664319 prefixEnd_1664319 := by exact prefixLift 1664319
  have htrace : WordTrace (prefixWord ++ tailWord_1664319) baseStart_1664319 baseEnd_1664319 := by
    simpa [prefixWord, tailWord_1664319, baseEnd_1664319] using wordTrace_append hprefix tailTrace_1664319
  have hstable : (prefixWord ++ tailWord_1664319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664319).length < 2 ^ (prefixWord ++ tailWord_1664319).sum := by decide
  have hdescent : baseEnd_1664319 < baseStart_1664319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664328 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1664328 : Nat := 118140960795 + 1664328 * 2 ^ 59
def prefixEnd_1664328 : Nat := 4983230072969 + 3 ^ 40 * 1664328 * 2
def baseEnd_1664328 : Nat := 569733487157513028497267

theorem tailTrace_1664328 : CollatzResearch.WordTrace tailWord_1664328 prefixEnd_1664328 569733487157513028497267 := by
  unfold tailWord_1664328
  simp only [CollatzResearch.WordTrace]
  refine ⟨30351514557215687718820819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40468686076287583625094425 30351514557215687718820819)
  ·
    refine ⟨45527271835823531578231229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30351514557215687718820819 45527271835823531578231229)
    ·
      refine ⟨17072726938433824341836711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45527271835823531578231229 17072726938433824341836711)
      ·
        refine ⟨25609090407650736512755067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17072726938433824341836711 25609090407650736512755067)
        ·
          refine ⟨38413635611476104769132601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25609090407650736512755067 38413635611476104769132601)
          ·
            refine ⟨28810226708607078576849451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38413635611476104769132601 28810226708607078576849451)
            ·
              refine ⟨43215340062910617865274177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28810226708607078576849451 43215340062910617865274177)
              ·
                refine ⟨32411505047182963398955633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43215340062910617865274177 32411505047182963398955633)
                ·
                  refine ⟨24308628785387222549216725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32411505047182963398955633 24308628785387222549216725)
                  ·
                    refine ⟨569733487157513028497267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24308628785387222549216725 569733487157513028497267)
                    ·
                      rfl

theorem cell22_1664328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1664328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664328 prefixEnd_1664328 := by exact prefixLift 1664328
  have htrace : WordTrace (prefixWord ++ tailWord_1664328) baseStart_1664328 baseEnd_1664328 := by
    simpa [prefixWord, tailWord_1664328, baseEnd_1664328] using wordTrace_append hprefix tailTrace_1664328
  have hstable : (prefixWord ++ tailWord_1664328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664328).length < 2 ^ (prefixWord ++ tailWord_1664328).sum := by decide
  have hdescent : baseEnd_1664328 < baseStart_1664328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664345 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_1664345 : Nat := 118140960795 + 1664345 * 2 ^ 59
def prefixEnd_1664345 : Nat := 4983230072969 + 3 ^ 40 * 1664345 * 2
def baseEnd_1664345 : Nat := 569739306604930650822215

theorem tailTrace_1664345 : CollatzResearch.WordTrace tailWord_1664345 prefixEnd_1664345 569739306604930650822215 := by
  unfold tailWord_1664345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60703649155369787341010489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40469099436913191560673659 60703649155369787341010489)
  ·
    refine ⟨45527736866527340505757867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60703649155369787341010489 45527736866527340505757867)
    ·
      refine ⟨68291605299791010758636801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45527736866527340505757867 68291605299791010758636801)
      ·
        refine ⟨51218703974843258068977601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68291605299791010758636801 51218703974843258068977601)
        ·
          refine ⟨38414027981132443551733201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51218703974843258068977601 38414027981132443551733201)
          ·
            refine ⟨28810520985849332663799901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38414027981132443551733201 28810520985849332663799901)
            ·
              refine ⟨10803945369693499748924963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28810520985849332663799901 10803945369693499748924963)
              ·
                refine ⟨16205918054540249623387445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803945369693499748924963 16205918054540249623387445)
                ·
                  refine ⟨1519304817613148402192573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16205918054540249623387445 1519304817613148402192573)
                  ·
                    refine ⟨569739306604930650822215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519304817613148402192573 569739306604930650822215)
                    ·
                      rfl

theorem cell22_1664345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_1664345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664345 prefixEnd_1664345 := by exact prefixLift 1664345
  have htrace : WordTrace (prefixWord ++ tailWord_1664345) baseStart_1664345 baseEnd_1664345 := by
    simpa [prefixWord, tailWord_1664345, baseEnd_1664345] using wordTrace_append hprefix tailTrace_1664345
  have hstable : (prefixWord ++ tailWord_1664345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664345).length < 2 ^ (prefixWord ++ tailWord_1664345).sum := by decide
  have hdescent : baseEnd_1664345 < baseStart_1664345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664405 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_1664405 : Nat := 118140960795 + 1664405 * 2 ^ 59
def prefixEnd_1664405 : Nat := 4983230072969 + 3 ^ 40 * 1664405 * 2
def baseEnd_1664405 : Nat := 569759845831110494322031

theorem tailTrace_1664405 : CollatzResearch.WordTrace tailWord_1664405 prefixEnd_1664405 569759845831110494322031 := by
  unfold tailWord_1664405
  simp only [CollatzResearch.WordTrace]
  refine ⟨60705837535152417588194669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40470558356768278392129779 60705837535152417588194669)
  ·
    refine ⟨22764689075682156595573001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60705837535152417588194669 22764689075682156595573001)
    ·
      refine ⟨17073516806761617446679751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22764689075682156595573001 17073516806761617446679751)
      ·
        refine ⟨25610275210142426170019627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17073516806761617446679751 25610275210142426170019627)
        ·
          refine ⟨38415412815213639255029441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25610275210142426170019627 38415412815213639255029441)
          ·
            refine ⟨28811559611410229441272081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38415412815213639255029441 28811559611410229441272081)
            ·
              refine ⟨21608669708557672080954061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28811559611410229441272081 21608669708557672080954061)
              ·
                refine ⟨8103251140709127030357773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21608669708557672080954061 8103251140709127030357773)
                ·
                  refine ⟨3038719177765922636384165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8103251140709127030357773 3038719177765922636384165)
                  ·
                    refine ⟨569759845831110494322031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3038719177765922636384165 569759845831110494322031)
                    ·
                      rfl

theorem cell22_1664405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_1664405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664405 prefixEnd_1664405 := by exact prefixLift 1664405
  have htrace : WordTrace (prefixWord ++ tailWord_1664405) baseStart_1664405 baseEnd_1664405 := by
    simpa [prefixWord, tailWord_1664405, baseEnd_1664405] using wordTrace_append hprefix tailTrace_1664405
  have hstable : (prefixWord ++ tailWord_1664405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664405).length < 2 ^ (prefixWord ++ tailWord_1664405).sum := by decide
  have hdescent : baseEnd_1664405 < baseStart_1664405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664437 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 6]
def baseStart_1664437 : Nat := 118140960795 + 1664437 * 2 ^ 59
def prefixEnd_1664437 : Nat := 4983230072969 + 3 ^ 40 * 1664437 * 2
def baseEnd_1664437 : Nat := 189923600028357692507311

theorem tailTrace_1664437 : CollatzResearch.WordTrace tailWord_1664437 prefixEnd_1664437 189923600028357692507311 := by
  unfold tailWord_1664437
  simp only [CollatzResearch.WordTrace]
  refine ⟨60707004671036487053359565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40471336447357658035573043 60707004671036487053359565)
  ·
    refine ⟨22765126751638682645009837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60707004671036487053359565 22765126751638682645009837)
    ·
      refine ⟨8536922531864505991878689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22765126751638682645009837 8536922531864505991878689)
      ·
        refine ⟨6402691898898379493909017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8536922531864505991878689 6402691898898379493909017)
        ·
          refine ⟨4802018924173784620431763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6402691898898379493909017 4802018924173784620431763)
          ·
            refine ⟨7203028386260676930647645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802018924173784620431763 7203028386260676930647645)
            ·
              refine ⟨2701135644847753848992867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7203028386260676930647645 2701135644847753848992867)
              ·
                refine ⟨4051703467271630773489301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701135644847753848992867 4051703467271630773489301)
                ·
                  refine ⟨189923600028357692507311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4051703467271630773489301 189923600028357692507311)
                  ·
                    rfl

theorem cell22_1664437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_1664437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664437 prefixEnd_1664437 := by exact prefixLift 1664437
  have htrace : WordTrace (prefixWord ++ tailWord_1664437) baseStart_1664437 baseEnd_1664437 := by
    simpa [prefixWord, tailWord_1664437, baseEnd_1664437] using wordTrace_append hprefix tailTrace_1664437
  have hstable : (prefixWord ++ tailWord_1664437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664437).length < 2 ^ (prefixWord ++ tailWord_1664437).sum := by decide
  have hdescent : baseEnd_1664437 < baseStart_1664437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664495 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1664495 : Nat := 118140960795 + 1664495 * 2 ^ 59
def prefixEnd_1664495 : Nat := 4983230072969 + 3 ^ 40 * 1664495 * 2
def baseEnd_1664495 : Nat := 569790654670380259571755

theorem tailTrace_1664495 : CollatzResearch.WordTrace tailWord_1664495 prefixEnd_1664495 569790654670380259571755 := by
  unfold tailWord_1664495
  simp only [CollatzResearch.WordTrace]
  refine ⟨60709120104826362958970939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40472746736550908639313959 60709120104826362958970939)
  ·
    refine ⟨91063680157239544438456409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60709120104826362958970939 91063680157239544438456409)
    ·
      refine ⟨68297760117929658328842307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91063680157239544438456409 68297760117929658328842307)
      ·
        refine ⟨102446640176894487493263461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68297760117929658328842307 102446640176894487493263461)
        ·
          refine ⟨19208745033167716404986899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102446640176894487493263461 19208745033167716404986899)
          ·
            refine ⟨28813117549751574607480349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19208745033167716404986899 28813117549751574607480349)
            ·
              refine ⟨10804919081156840477805131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28813117549751574607480349 10804919081156840477805131)
              ·
                refine ⟨16207378621735260716707697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10804919081156840477805131 16207378621735260716707697)
                ·
                  refine ⟨12155533966301445537530773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16207378621735260716707697 12155533966301445537530773)
                  ·
                    refine ⟨569790654670380259571755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12155533966301445537530773 569790654670380259571755)
                    ·
                      rfl

theorem cell22_1664495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1664495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664495 prefixEnd_1664495 := by exact prefixLift 1664495
  have htrace : WordTrace (prefixWord ++ tailWord_1664495) baseStart_1664495 baseEnd_1664495 := by
    simpa [prefixWord, tailWord_1664495, baseEnd_1664495] using wordTrace_append hprefix tailTrace_1664495
  have hstable : (prefixWord ++ tailWord_1664495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664495).length < 2 ^ (prefixWord ++ tailWord_1664495).sum := by decide
  have hdescent : baseEnd_1664495 < baseStart_1664495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664518 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1664518 : Nat := 118140960795 + 1664518 * 2 ^ 59
def prefixEnd_1664518 : Nat := 4983230072969 + 3 ^ 40 * 1664518 * 2
def baseEnd_1664518 : Nat := 569798528040415866246685

theorem tailTrace_1664518 : CollatzResearch.WordTrace tailWord_1664518 prefixEnd_1664518 569798528040415866246685 := by
  unfold tailWord_1664518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897186218241969933970569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40473305989162025258038805 1897186218241969933970569)
  ·
    refine ⟨1422889663681477450477927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1897186218241969933970569 1422889663681477450477927)
    ·
      refine ⟨2134334495522216175716891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422889663681477450477927 2134334495522216175716891)
      ·
        refine ⟨3201501743283324263575337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134334495522216175716891 3201501743283324263575337)
        ·
          refine ⟨2401126307462493197681503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201501743283324263575337 2401126307462493197681503)
          ·
            refine ⟨3601689461193739796522255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401126307462493197681503 3601689461193739796522255)
            ·
              refine ⟨5402534191790609694783383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601689461193739796522255 5402534191790609694783383)
              ·
                refine ⟨8103801287685914542175075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5402534191790609694783383 8103801287685914542175075)
                ·
                  refine ⟨12155701931528871813262613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103801287685914542175075 12155701931528871813262613)
                  ·
                    refine ⟨569798528040415866246685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12155701931528871813262613 569798528040415866246685)
                    ·
                      rfl

theorem cell22_1664518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1664518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664518 prefixEnd_1664518 := by exact prefixLift 1664518
  have htrace : WordTrace (prefixWord ++ tailWord_1664518) baseStart_1664518 baseEnd_1664518 := by
    simpa [prefixWord, tailWord_1664518, baseEnd_1664518] using wordTrace_append hprefix tailTrace_1664518
  have hstable : (prefixWord ++ tailWord_1664518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664518).length < 2 ^ (prefixWord ++ tailWord_1664518).sum := by decide
  have hdescent : baseEnd_1664518 < baseStart_1664518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664531 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 1, 3]
def baseStart_1664531 : Nat := 118140960795 + 1664531 * 2 ^ 59
def prefixEnd_1664531 : Nat := 4983230072969 + 3 ^ 40 * 1664531 * 2
def baseEnd_1664531 : Nat := 569802978206088165671645

theorem tailTrace_1664531 : CollatzResearch.WordTrace tailWord_1664531 prefixEnd_1664531 569802978206088165671645 := by
  unfold tailWord_1664531
  simp only [CollatzResearch.WordTrace]
  refine ⟨60710433132695941107281447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40473622088463960738187631 60710433132695941107281447)
  ·
    refine ⟨91065649699043911660922171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60710433132695941107281447 91065649699043911660922171)
    ·
      refine ⟨136598474548565867491383257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91065649699043911660922171 136598474548565867491383257)
      ·
        refine ⟨102448855911424400618537443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136598474548565867491383257 102448855911424400618537443)
        ·
          refine ⟨153673283867136600927806165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102448855911424400618537443 153673283867136600927806165)
          ·
            refine ⟨3601717590636014084245457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 153673283867136600927806165 3601717590636014084245457)
            ·
              refine ⟨2701288192977010563184093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601717590636014084245457 2701288192977010563184093)
              ·
                refine ⟨1012983072366378961194035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701288192977010563184093 1012983072366378961194035)
                ·
                  refine ⟨1519474608549568441791053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012983072366378961194035 1519474608549568441791053)
                  ·
                    refine ⟨569802978206088165671645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519474608549568441791053 569802978206088165671645)
                    ·
                      rfl

theorem cell22_1664531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 3].length) (baseStart_1664531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664531 prefixEnd_1664531 := by exact prefixLift 1664531
  have htrace : WordTrace (prefixWord ++ tailWord_1664531) baseStart_1664531 baseEnd_1664531 := by
    simpa [prefixWord, tailWord_1664531, baseEnd_1664531] using wordTrace_append hprefix tailTrace_1664531
  have hstable : (prefixWord ++ tailWord_1664531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664531).length < 2 ^ (prefixWord ++ tailWord_1664531).sum := by decide
  have hdescent : baseEnd_1664531 < baseStart_1664531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664544 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_1664544 : Nat := 118140960795 + 1664544 * 2 ^ 59
def prefixEnd_1664544 : Nat := 4983230072969 + 3 ^ 40 * 1664544 * 2
def baseEnd_1664544 : Nat := 189935809457253488365535

theorem tailTrace_1664544 : CollatzResearch.WordTrace tailWord_1664544 prefixEnd_1664544 189935809457253488365535 := by
  unfold tailWord_1664544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355453640824422163752343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40473938187765896218336457 30355453640824422163752343)
  ·
    refine ⟨45533180461236633245628515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30355453640824422163752343 45533180461236633245628515)
    ·
      refine ⟨68299770691854949868442773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45533180461236633245628515 68299770691854949868442773)
      ·
        refine ⟨3201551751180700775083255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68299770691854949868442773 3201551751180700775083255)
        ·
          refine ⟨4802327626771051162624883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201551751180700775083255 4802327626771051162624883)
          ·
            refine ⟨7203491440156576743937325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802327626771051162624883 7203491440156576743937325)
            ·
              refine ⟨2701309290058716278976497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7203491440156576743937325 2701309290058716278976497)
              ·
                refine ⟨2025981967544037209232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701309290058716278976497 2025981967544037209232373)
                ·
                  refine ⟨189935809457253488365535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025981967544037209232373 189935809457253488365535)
                  ·
                    rfl

theorem cell22_1664544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_1664544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664544 prefixEnd_1664544 := by exact prefixLift 1664544
  have htrace : WordTrace (prefixWord ++ tailWord_1664544) baseStart_1664544 baseEnd_1664544 := by
    simpa [prefixWord, tailWord_1664544, baseEnd_1664544] using wordTrace_append hprefix tailTrace_1664544
  have hstable : (prefixWord ++ tailWord_1664544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664544).length < 2 ^ (prefixWord ++ tailWord_1664544).sum := by decide
  have hdescent : baseEnd_1664544 < baseStart_1664544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664582 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1664582 : Nat := 118140960795 + 1664582 * 2 ^ 59
def prefixEnd_1664582 : Nat := 4983230072969 + 3 ^ 40 * 1664582 * 2
def baseEnd_1664582 : Nat := 569820436548341032646489

theorem tailTrace_1664582 : CollatzResearch.WordTrace tailWord_1664582 prefixEnd_1664582 569820436548341032646489 := by
  unfold tailWord_1664582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897259164234724275543375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40474862170340784544925333 1897259164234724275543375)
  ·
    refine ⟨2845888746352086413315063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1897259164234724275543375 2845888746352086413315063)
    ·
      refine ⟨4268833119528129619972595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845888746352086413315063 4268833119528129619972595)
      ·
        refine ⟨6403249679292194429958893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4268833119528129619972595 6403249679292194429958893)
        ·
          refine ⟨2401218629734572911234585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6403249679292194429958893 2401218629734572911234585)
          ·
            refine ⟨1800913972300929683425939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401218629734572911234585 1800913972300929683425939)
            ·
              refine ⟨2701370958451394525138909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800913972300929683425939 2701370958451394525138909)
              ·
                refine ⟨1013014109419272946927091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701370958451394525138909 1013014109419272946927091)
                ·
                  refine ⟨1519521164128909420390637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013014109419272946927091 1519521164128909420390637)
                  ·
                    refine ⟨569820436548341032646489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519521164128909420390637 569820436548341032646489)
                    ·
                      rfl

theorem cell22_1664582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1664582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664582 prefixEnd_1664582 := by exact prefixLift 1664582
  have htrace : WordTrace (prefixWord ++ tailWord_1664582) baseStart_1664582 baseEnd_1664582 := by
    simpa [prefixWord, tailWord_1664582, baseEnd_1664582] using wordTrace_append hprefix tailTrace_1664582
  have hstable : (prefixWord ++ tailWord_1664582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664582).length < 2 ^ (prefixWord ++ tailWord_1664582).sum := by decide
  have hdescent : baseEnd_1664582 < baseStart_1664582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664677 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1664677 : Nat := 118140960795 + 1664677 * 2 ^ 59
def prefixEnd_1664677 : Nat := 4983230072969 + 3 ^ 40 * 1664677 * 2
def baseEnd_1664677 : Nat := 569852956989792451521197

theorem tailTrace_1664677 : CollatzResearch.WordTrace tailWord_1664677 prefixEnd_1664677 569852956989792451521197 := by
  unfold tailWord_1664677
  simp only [CollatzResearch.WordTrace]
  refine ⟨60715758190167008042096285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40477172126778005361397523 60715758190167008042096285)
  ·
    refine ⟨22768409321312628015786107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60715758190167008042096285 22768409321312628015786107)
    ·
      refine ⟨34152613981968942023679161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22768409321312628015786107 34152613981968942023679161)
      ·
        refine ⟨25614460486476706517759371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34152613981968942023679161 25614460486476706517759371)
        ·
          refine ⟨38421690729715059776639057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25614460486476706517759371 38421690729715059776639057)
          ·
            refine ⟨28816268047286294832479293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38421690729715059776639057 28816268047286294832479293)
            ·
              refine ⟨10806100517732360562179735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28816268047286294832479293 10806100517732360562179735)
              ·
                refine ⟨16209150776598540843269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806100517732360562179735 16209150776598540843269603)
                ·
                  refine ⟨24313726164897811264904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16209150776598540843269603 24313726164897811264904405)
                  ·
                    refine ⟨569852956989792451521197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24313726164897811264904405 569852956989792451521197)
                    ·
                      rfl

theorem cell22_1664677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1664677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664677 prefixEnd_1664677 := by exact prefixLift 1664677
  have htrace : WordTrace (prefixWord ++ tailWord_1664677) baseStart_1664677 baseEnd_1664677 := by
    simpa [prefixWord, tailWord_1664677, baseEnd_1664677] using wordTrace_append hprefix tailTrace_1664677
  have hstable : (prefixWord ++ tailWord_1664677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664677).length < 2 ^ (prefixWord ++ tailWord_1664677).sum := by decide
  have hdescent : baseEnd_1664677 < baseStart_1664677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664709 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_1664709 : Nat := 118140960795 + 1664709 * 2 ^ 59
def prefixEnd_1664709 : Nat := 4983230072969 + 3 ^ 40 * 1664709 * 2
def baseEnd_1664709 : Nat := 569863911243755034721099

theorem tailTrace_1664709 : CollatzResearch.WordTrace tailWord_1664709 prefixEnd_1664709 569863911243755034721099 := by
  unfold tailWord_1664709
  simp only [CollatzResearch.WordTrace]
  refine ⟨60716925326051077507261181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40477950217367385004840787 60716925326051077507261181)
  ·
    refine ⟨22768846997269154065222943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60716925326051077507261181 22768846997269154065222943)
    ·
      refine ⟨34153270495903731097834415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22768846997269154065222943 34153270495903731097834415)
      ·
        refine ⟨51229905743855596646751623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34153270495903731097834415 51229905743855596646751623)
        ·
          refine ⟨76844858615783394970127435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51229905743855596646751623 76844858615783394970127435)
          ·
            refine ⟨115267287923675092455191153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76844858615783394970127435 115267287923675092455191153)
            ·
              refine ⟨86450465942756319341393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115267287923675092455191153 86450465942756319341393365)
              ·
                refine ⟨2026182795533351234563907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86450465942756319341393365 2026182795533351234563907)
                ·
                  refine ⟨3039274193300026851845861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026182795533351234563907 3039274193300026851845861)
                  ·
                    refine ⟨569863911243755034721099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039274193300026851845861 569863911243755034721099)
                    ·
                      rfl

theorem cell22_1664709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_1664709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664709 prefixEnd_1664709 := by exact prefixLift 1664709
  have htrace : WordTrace (prefixWord ++ tailWord_1664709) baseStart_1664709 baseEnd_1664709 := by
    simpa [prefixWord, tailWord_1664709, baseEnd_1664709] using wordTrace_append hprefix tailTrace_1664709
  have hstable : (prefixWord ++ tailWord_1664709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664709).length < 2 ^ (prefixWord ++ tailWord_1664709).sum := by decide
  have hdescent : baseEnd_1664709 < baseStart_1664709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664754 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1664754 : Nat := 118140960795 + 1664754 * 2 ^ 59
def prefixEnd_1664754 : Nat := 4983230072969 + 3 ^ 40 * 1664754 * 2
def baseEnd_1664754 : Nat := 569879315663389917345961

theorem tailTrace_1664754 : CollatzResearch.WordTrace tailWord_1664754 prefixEnd_1664754 569879315663389917345961 := by
  unfold tailWord_1664754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179641652722012548162329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40479044407258700128432877 15179641652722012548162329)
  ·
    refine ⟨11384731239541509411121747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15179641652722012548162329 11384731239541509411121747)
    ·
      refine ⟨17077096859312264116682621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11384731239541509411121747 17077096859312264116682621)
      ·
        refine ⟨6403911322242099043755983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17077096859312264116682621 6403911322242099043755983)
        ·
          refine ⟨9605866983363148565633975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403911322242099043755983 9605866983363148565633975)
          ·
            refine ⟨14408800475044722848450963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605866983363148565633975 14408800475044722848450963)
            ·
              refine ⟨21613200712567084272676445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14408800475044722848450963 21613200712567084272676445)
              ·
                refine ⟨8104950267212656602253667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21613200712567084272676445 8104950267212656602253667)
                ·
                  refine ⟨12157425400818984903380501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8104950267212656602253667 12157425400818984903380501)
                  ·
                    refine ⟨569879315663389917345961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12157425400818984903380501 569879315663389917345961)
                    ·
                      rfl

theorem cell22_1664754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1664754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664754 prefixEnd_1664754 := by exact prefixLift 1664754
  have htrace : WordTrace (prefixWord ++ tailWord_1664754) baseStart_1664754 baseEnd_1664754 := by
    simpa [prefixWord, tailWord_1664754, baseEnd_1664754] using wordTrace_append hprefix tailTrace_1664754
  have hstable : (prefixWord ++ tailWord_1664754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664754).length < 2 ^ (prefixWord ++ tailWord_1664754).sum := by decide
  have hdescent : baseEnd_1664754 < baseStart_1664754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664758 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1664758 : Nat := 118140960795 + 1664758 * 2 ^ 59
def prefixEnd_1664758 : Nat := 4983230072969 + 3 ^ 40 * 1664758 * 2
def baseEnd_1664758 : Nat := 189960228315045080081983

theorem tailTrace_1664758 : CollatzResearch.WordTrace tailWord_1664758 prefixEnd_1664758 189960228315045080081983 := by
  unfold tailWord_1664758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794919531429597429737183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40479141668582372583863285 3794919531429597429737183)
  ·
    refine ⟨5692379297144396144605775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3794919531429597429737183 5692379297144396144605775)
    ·
      refine ⟨8538568945716594216908663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692379297144396144605775 8538568945716594216908663)
      ·
        refine ⟨12807853418574891325362995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8538568945716594216908663 12807853418574891325362995)
        ·
          refine ⟨19211780127862336988044493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12807853418574891325362995 19211780127862336988044493)
          ·
            refine ⟨7204417547948376370516685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19211780127862336988044493 7204417547948376370516685)
            ·
              refine ⟨2701656580480641138943757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7204417547948376370516685 2701656580480641138943757)
              ·
                refine ⟨1013121217680240427103909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701656580480641138943757 1013121217680240427103909)
                ·
                  refine ⟨189960228315045080081983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013121217680240427103909 189960228315045080081983)
                  ·
                    rfl

theorem cell22_1664758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1664758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664758 prefixEnd_1664758 := by exact prefixLift 1664758
  have htrace : WordTrace (prefixWord ++ tailWord_1664758) baseStart_1664758 baseEnd_1664758 := by
    simpa [prefixWord, tailWord_1664758, baseEnd_1664758] using wordTrace_append hprefix tailTrace_1664758
  have hstable : (prefixWord ++ tailWord_1664758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664758).length < 2 ^ (prefixWord ++ tailWord_1664758).sum := by decide
  have hdescent : baseEnd_1664758 < baseStart_1664758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664775 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 4]
def baseStart_1664775 : Nat := 118140960795 + 1664775 * 2 ^ 59
def prefixEnd_1664775 : Nat := 4983230072969 + 3 ^ 40 * 1664775 * 2
def baseEnd_1664775 : Nat := 189962168130850954190299

theorem tailTrace_1664775 : CollatzResearch.WordTrace tailWord_1664775 prefixEnd_1664775 189962168130850954190299 := by
  unfold tailWord_1664775
  simp only [CollatzResearch.WordTrace]
  refine ⟨60719332543811970779163779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40479555029207980519442519 60719332543811970779163779)
  ·
    refine ⟨91078998815717956168745669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60719332543811970779163779 91078998815717956168745669)
    ·
      refine ⟨17077312277947116781639813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91078998815717956168745669 17077312277947116781639813)
      ·
        refine ⟨3201996052115084396557465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17077312277947116781639813 3201996052115084396557465)
        ·
          refine ⟨2401497039086313297418099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201996052115084396557465 2401497039086313297418099)
          ·
            refine ⟨3602245558629469946127149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401497039086313297418099 3602245558629469946127149)
            ·
              refine ⟨1350842084486051229797681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602245558629469946127149 1350842084486051229797681)
              ·
                refine ⟨1013131563364538422348261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350842084486051229797681 1013131563364538422348261)
                ·
                  refine ⟨189962168130850954190299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013131563364538422348261 189962168130850954190299)
                  ·
                    rfl

theorem cell22_1664775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 4].length) (baseStart_1664775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664775 prefixEnd_1664775 := by exact prefixLift 1664775
  have htrace : WordTrace (prefixWord ++ tailWord_1664775) baseStart_1664775 baseEnd_1664775 := by
    simpa [prefixWord, tailWord_1664775, baseEnd_1664775] using wordTrace_append hprefix tailTrace_1664775
  have hstable : (prefixWord ++ tailWord_1664775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664775).length < 2 ^ (prefixWord ++ tailWord_1664775).sum := by decide
  have hdescent : baseEnd_1664775 < baseStart_1664775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664781 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1664781 : Nat := 118140960795 + 1664781 * 2 ^ 59
def prefixEnd_1664781 : Nat := 4983230072969 + 3 ^ 40 * 1664781 * 2
def baseEnd_1664781 : Nat := 189962852771723615640293

theorem tailTrace_1664781 : CollatzResearch.WordTrace tailWord_1664781 prefixEnd_1664781 189962852771723615640293 := by
  unfold tailWord_1664781
  simp only [CollatzResearch.WordTrace]
  refine ⟨60719551381790233803882197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40479700921193489202588131 60719551381790233803882197)
  ·
    refine ⟨1423114485510708604778489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 60719551381790233803882197 1423114485510708604778489)
    ·
      refine ⟨1067335864133031453583867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423114485510708604778489 1067335864133031453583867)
      ·
        refine ⟨1601003796199547180375801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067335864133031453583867 1601003796199547180375801)
        ·
          refine ⟨1200752847149660385281851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1601003796199547180375801 1200752847149660385281851)
          ·
            refine ⟨1801129270724490577922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200752847149660385281851 1801129270724490577922777)
            ·
              refine ⟨1350846953043367933442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801129270724490577922777 1350846953043367933442083)
              ·
                refine ⟨2026270429565051900163125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350846953043367933442083 2026270429565051900163125)
                ·
                  refine ⟨189962852771723615640293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2026270429565051900163125 189962852771723615640293)
                  ·
                    rfl

theorem cell22_1664781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1664781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664781 prefixEnd_1664781 := by exact prefixLift 1664781
  have htrace : WordTrace (prefixWord ++ tailWord_1664781) baseStart_1664781 baseEnd_1664781 := by
    simpa [prefixWord, tailWord_1664781, baseEnd_1664781] using wordTrace_append hprefix tailTrace_1664781
  have hstable : (prefixWord ++ tailWord_1664781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664781).length < 2 ^ (prefixWord ++ tailWord_1664781).sum := by decide
  have hdescent : baseEnd_1664781 < baseStart_1664781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664786 : List Nat := [3, 2, 4, 1, 1, 1, 1, 9]
def baseStart_1664786 : Nat := 118140960795 + 1664786 * 2 ^ 59
def prefixEnd_1664786 : Nat := 4983230072969 + 3 ^ 40 * 1664786 * 2
def baseEnd_1664786 : Nat := 63321141101928055616207

theorem tailTrace_1664786 : CollatzResearch.WordTrace tailWord_1664786 prefixEnd_1664786 63321141101928055616207 := by
  unfold tailWord_1664786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179933436693029914453553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40479822497848079771876141 15179933436693029914453553)
  ·
    refine ⟨11384950077519772435840165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15179933436693029914453553 11384950077519772435840165)
    ·
      refine ⟨2134678139534957331720031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11384950077519772435840165 2134678139534957331720031)
      ·
        refine ⟨3202017209302435997580047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134678139534957331720031 3202017209302435997580047)
        ·
          refine ⟨4803025813953653996370071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202017209302435997580047 4803025813953653996370071)
          ·
            refine ⟨7204538720930480994555107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803025813953653996370071 7204538720930480994555107)
            ·
              refine ⟨10806808081395721491832661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204538720930480994555107 10806808081395721491832661)
              ·
                refine ⟨63321141101928055616207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10806808081395721491832661 63321141101928055616207)
                ·
                  rfl

theorem cell22_1664786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_1664786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664786 prefixEnd_1664786 := by exact prefixLift 1664786
  have htrace : WordTrace (prefixWord ++ tailWord_1664786) baseStart_1664786 baseEnd_1664786 := by
    simpa [prefixWord, tailWord_1664786, baseEnd_1664786] using wordTrace_append hprefix tailTrace_1664786
  have hstable : (prefixWord ++ tailWord_1664786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664786).length < 2 ^ (prefixWord ++ tailWord_1664786).sum := by decide
  have hdescent : baseEnd_1664786 < baseStart_1664786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664835 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 1, 3]
def baseStart_1664835 : Nat := 118140960795 + 1664835 * 2 ^ 59
def prefixEnd_1664835 : Nat := 4983230072969 + 3 ^ 40 * 1664835 * 2
def baseEnd_1664835 : Nat := 569907043618732706070713

theorem tailTrace_1664835 : CollatzResearch.WordTrace tailWord_1664835 prefixEnd_1664835 569907043618732706070713 := by
  unfold tailWord_1664835
  simp only [CollatzResearch.WordTrace]
  refine ⟨60721520923594601026347959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40481013949063067350898639 60721520923594601026347959)
  ·
    refine ⟨91082281385391901539521939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60721520923594601026347959 91082281385391901539521939)
    ·
      refine ⟨136623422078087852309282909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91082281385391901539521939 136623422078087852309282909)
      ·
        refine ⟨51233783279282944615981091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136623422078087852309282909 51233783279282944615981091)
        ·
          refine ⟨76850674918924416923971637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51233783279282944615981091 76850674918924416923971637)
          ·
            refine ⟨7204750773649164086622341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76850674918924416923971637 7204750773649164086622341)
            ·
              refine ⟨1350890770059218266241689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7204750773649164086622341 1350890770059218266241689)
              ·
                refine ⟨1013168077544413699681267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350890770059218266241689 1013168077544413699681267)
                ·
                  refine ⟨1519752116316620549521901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013168077544413699681267 1519752116316620549521901)
                  ·
                    refine ⟨569907043618732706070713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1519752116316620549521901 569907043618732706070713)
                    ·
                      rfl

theorem cell22_1664835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 3].length) (baseStart_1664835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664835 prefixEnd_1664835 := by exact prefixLift 1664835
  have htrace : WordTrace (prefixWord ++ tailWord_1664835) baseStart_1664835 baseEnd_1664835 := by
    simpa [prefixWord, tailWord_1664835, baseEnd_1664835] using wordTrace_append hprefix tailTrace_1664835
  have hstable : (prefixWord ++ tailWord_1664835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664835).length < 2 ^ (prefixWord ++ tailWord_1664835).sum := by decide
  have hdescent : baseEnd_1664835 < baseStart_1664835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664921 : List Nat := [1, 2, 1, 2, 1, 3, 6, 6]
def baseStart_1664921 : Nat := 118140960795 + 1664921 * 2 ^ 59
def prefixEnd_1664921 : Nat := 4983230072969 + 3 ^ 40 * 1664921 * 2
def baseEnd_1664921 : Nat := 63326275908473016491161

theorem tailTrace_1664921 : CollatzResearch.WordTrace tailWord_1664921 prefixEnd_1664921 63326275908473016491161 := by
  unfold tailWord_1664921
  simp only [CollatzResearch.WordTrace]
  refine ⟨60724657601283037713978617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40483105067522025142652411 60724657601283037713978617)
  ·
    refine ⟨45543493200962278285483963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60724657601283037713978617 45543493200962278285483963)
    ·
      refine ⟨68315239801443417428225945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45543493200962278285483963 68315239801443417428225945)
      ·
        refine ⟨51236429851082563071169459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68315239801443417428225945 51236429851082563071169459)
        ·
          refine ⟨76854644776623844606754189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51236429851082563071169459 76854644776623844606754189)
          ·
            refine ⟨28820491791233941727532821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76854644776623844606754189 28820491791233941727532821)
            ·
              refine ⟨1350960552714091018478101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28820491791233941727532821 1350960552714091018478101)
              ·
                refine ⟨63326275908473016491161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1350960552714091018478101 63326275908473016491161)
                ·
                  rfl

theorem cell22_1664921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 6].length) (baseStart_1664921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664921 prefixEnd_1664921 := by exact prefixLift 1664921
  have htrace : WordTrace (prefixWord ++ tailWord_1664921) baseStart_1664921 baseEnd_1664921 := by
    simpa [prefixWord, tailWord_1664921, baseEnd_1664921] using wordTrace_append hprefix tailTrace_1664921
  have hstable : (prefixWord ++ tailWord_1664921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664921).length < 2 ^ (prefixWord ++ tailWord_1664921).sum := by decide
  have hdescent : baseEnd_1664921 < baseStart_1664921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664927 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 4]
def baseStart_1664927 : Nat := 118140960795 + 1664927 * 2 ^ 59
def prefixEnd_1664927 : Nat := 4983230072969 + 3 ^ 40 * 1664927 * 2
def baseEnd_1664927 : Nat := 189979512366291710923477

theorem tailTrace_1664927 : CollatzResearch.WordTrace tailWord_1664927 prefixEnd_1664927 189979512366291710923477 := by
  unfold tailWord_1664927
  simp only [CollatzResearch.WordTrace]
  refine ⟨60724876439261300738697035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40483250959507533825798023 60724876439261300738697035)
  ·
    refine ⟨91087314658891951108045553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60724876439261300738697035 91087314658891951108045553)
    ·
      refine ⟨68315485994168963331034165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91087314658891951108045553 68315485994168963331034165)
      ·
        refine ⟨6404576811953340312284453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68315485994168963331034165 6404576811953340312284453)
        ·
          refine ⟨1200858152241251308553335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6404576811953340312284453 1200858152241251308553335)
          ·
            refine ⟨1801287228361876962830003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200858152241251308553335 1801287228361876962830003)
            ·
              refine ⟨2701930842542815444245005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801287228361876962830003 2701930842542815444245005)
              ·
                refine ⟨1013224065953555791591877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701930842542815444245005 1013224065953555791591877)
                ·
                  refine ⟨189979512366291710923477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013224065953555791591877 189979512366291710923477)
                  ·
                    rfl

theorem cell22_1664927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 4].length) (baseStart_1664927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1664927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1664927 prefixEnd_1664927 := by exact prefixLift 1664927
  have htrace : WordTrace (prefixWord ++ tailWord_1664927) baseStart_1664927 baseEnd_1664927 := by
    simpa [prefixWord, tailWord_1664927, baseEnd_1664927] using wordTrace_append hprefix tailTrace_1664927
  have hstable : (prefixWord ++ tailWord_1664927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664927).length < 2 ^ (prefixWord ++ tailWord_1664927).sum := by decide
  have hdescent : baseEnd_1664927 < baseStart_1664927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665058 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1665058 : Nat := 118140960795 + 1665058 * 2 ^ 59
def prefixEnd_1665058 : Nat := 4983230072969 + 3 ^ 40 * 1665058 * 2
def baseEnd_1665058 : Nat := 569983381076034457745029

theorem tailTrace_1665058 : CollatzResearch.WordTrace tailWord_1665058 prefixEnd_1665058 569983381076034457745029 := by
  unfold tailWord_1665058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182413600446677527928957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40486436267857806741143885 15182413600446677527928957)
  ·
    refine ⟨5693405100167504072973359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15182413600446677527928957 5693405100167504072973359)
    ·
      refine ⟨8540107650251256109460039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693405100167504072973359 8540107650251256109460039)
      ·
        refine ⟨12810161475376884164190059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540107650251256109460039 12810161475376884164190059)
        ·
          refine ⟨19215242213065326246285089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12810161475376884164190059 19215242213065326246285089)
          ·
            refine ⟨14411431659798994684713817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19215242213065326246285089 14411431659798994684713817)
            ·
              refine ⟨10808573744849246013535363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14411431659798994684713817 10808573744849246013535363)
              ·
                refine ⟨16212860617273869020303045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808573744849246013535363 16212860617273869020303045)
                ·
                  refine ⟨3039911365738850441306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16212860617273869020303045 3039911365738850441306821)
                  ·
                    refine ⟨569983381076034457745029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3039911365738850441306821 569983381076034457745029)
                    ·
                      rfl

theorem cell22_1665058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1665058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665058 prefixEnd_1665058 := by exact prefixLift 1665058
  have htrace : WordTrace (prefixWord ++ tailWord_1665058) baseStart_1665058 baseEnd_1665058 := by
    simpa [prefixWord, tailWord_1665058, baseEnd_1665058] using wordTrace_append hprefix tailTrace_1665058
  have hstable : (prefixWord ++ tailWord_1665058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665058).length < 2 ^ (prefixWord ++ tailWord_1665058).sum := by decide
  have hdescent : baseEnd_1665058 < baseStart_1665058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665133 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1665133 : Nat := 118140960795 + 1665133 * 2 ^ 59
def prefixEnd_1665133 : Nat := 4983230072969 + 3 ^ 40 * 1665133 * 2
def baseEnd_1665133 : Nat := 570009055108759262119799

theorem tailTrace_1665133 : CollatzResearch.WordTrace tailWord_1665133 prefixEnd_1665133 570009055108759262119799 := by
  unfold tailWord_1665133
  simp only [CollatzResearch.WordTrace]
  refine ⟨60732389876514997920696053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40488259917676665280464035 60732389876514997920696053)
  ·
    refine ⟨5693661550923281055065255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60732389876514997920696053 5693661550923281055065255)
    ·
      refine ⟨8540492326384921582597883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693661550923281055065255 8540492326384921582597883)
      ·
        refine ⟨12810738489577382373896825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540492326384921582597883 12810738489577382373896825)
        ·
          refine ⟨9608053867183036780422619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12810738489577382373896825 9608053867183036780422619)
          ·
            refine ⟨14412080800774555170633929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9608053867183036780422619 14412080800774555170633929)
            ·
              refine ⟨10809060600580916377975447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14412080800774555170633929 10809060600580916377975447)
              ·
                refine ⟨16213590900871374566963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809060600580916377975447 16213590900871374566963171)
                ·
                  refine ⟨24320386351307061850444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16213590900871374566963171 24320386351307061850444757)
                  ·
                    refine ⟨570009055108759262119799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24320386351307061850444757 570009055108759262119799)
                    ·
                      rfl

theorem cell22_1665133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1665133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665133 prefixEnd_1665133 := by exact prefixLift 1665133
  have htrace : WordTrace (prefixWord ++ tailWord_1665133) baseStart_1665133 baseEnd_1665133 := by
    simpa [prefixWord, tailWord_1665133, baseEnd_1665133] using wordTrace_append hprefix tailTrace_1665133
  have hstable : (prefixWord ++ tailWord_1665133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665133).length < 2 ^ (prefixWord ++ tailWord_1665133).sum := by decide
  have hdescent : baseEnd_1665133 < baseStart_1665133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665135 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 5]
def baseStart_1665135 : Nat := 118140960795 + 1665135 * 2 ^ 59
def prefixEnd_1665135 : Nat := 4983230072969 + 3 ^ 40 * 1665135 * 2
def baseEnd_1665135 : Nat := 190003246583210641189931

theorem tailTrace_1665135 : CollatzResearch.WordTrace tailWord_1665135 prefixEnd_1665135 190003246583210641189931 := by
  unfold tailWord_1665135
  simp only [CollatzResearch.WordTrace]
  refine ⟨60732462822507752262268859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40488308548338501508179239 60732462822507752262268859)
  ·
    refine ⟨91098694233761628393403289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60732462822507752262268859 91098694233761628393403289)
    ·
      refine ⟨68324020675321221295052467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91098694233761628393403289 68324020675321221295052467)
      ·
        refine ⟨102486031012981831942578701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68324020675321221295052467 102486031012981831942578701)
        ·
          refine ⟨38432261629868186978467013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102486031012981831942578701 38432261629868186978467013)
          ·
            refine ⟨7206049055600285058462565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38432261629868186978467013 7206049055600285058462565)
            ·
              refine ⟨1351134197925053448461731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7206049055600285058462565 1351134197925053448461731)
              ·
                refine ⟨2026701296887580172692597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351134197925053448461731 2026701296887580172692597)
                ·
                  refine ⟨190003246583210641189931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2026701296887580172692597 190003246583210641189931)
                  ·
                    rfl

theorem cell22_1665135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 5].length) (baseStart_1665135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665135 prefixEnd_1665135 := by exact prefixLift 1665135
  have htrace : WordTrace (prefixWord ++ tailWord_1665135) baseStart_1665135 baseEnd_1665135 := by
    simpa [prefixWord, tailWord_1665135, baseEnd_1665135] using wordTrace_append hprefix tailTrace_1665135
  have hstable : (prefixWord ++ tailWord_1665135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665135).length < 2 ^ (prefixWord ++ tailWord_1665135).sum := by decide
  have hdescent : baseEnd_1665135 < baseStart_1665135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665210 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1665210 : Nat := 118140960795 + 1665210 * 2 ^ 59
def prefixEnd_1665210 : Nat := 4983230072969 + 3 ^ 40 * 1665210 * 2
def baseEnd_1665210 : Nat := 570035413782356727944563

theorem tailTrace_1665210 : CollatzResearch.WordTrace tailWord_1665210 prefixEnd_1665210 570035413782356727944563 := by
  unfold tailWord_1665210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183799574309010017812271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40490132198157360047499389 15183799574309010017812271)
  ·
    refine ⟨22775699361463515026718407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15183799574309010017812271 22775699361463515026718407)
    ·
      refine ⟨34163549042195272540077611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22775699361463515026718407 34163549042195272540077611)
      ·
        refine ⟨51245323563292908810116417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34163549042195272540077611 51245323563292908810116417)
        ·
          refine ⟨38433992672469681607587313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51245323563292908810116417 38433992672469681607587313)
          ·
            refine ⟨28825494504352261205690485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38433992672469681607587313 28825494504352261205690485)
            ·
              refine ⟨2702390109783024488033483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28825494504352261205690485 2702390109783024488033483)
              ·
                refine ⟨4053585164674536732050225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702390109783024488033483 4053585164674536732050225)
                ·
                  refine ⟨3040188873505902549037669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4053585164674536732050225 3040188873505902549037669)
                  ·
                    refine ⟨570035413782356727944563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3040188873505902549037669 570035413782356727944563)
                    ·
                      rfl

theorem cell22_1665210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1665210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665210 prefixEnd_1665210 := by exact prefixLift 1665210
  have htrace : WordTrace (prefixWord ++ tailWord_1665210) baseStart_1665210 baseEnd_1665210 := by
    simpa [prefixWord, tailWord_1665210, baseEnd_1665210] using wordTrace_append hprefix tailTrace_1665210
  have hstable : (prefixWord ++ tailWord_1665210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665210).length < 2 ^ (prefixWord ++ tailWord_1665210).sum := by decide
  have hdescent : baseEnd_1665210 < baseStart_1665210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665214 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1665214 : Nat := 118140960795 + 1665214 * 2 ^ 59
def prefixEnd_1665214 : Nat := 4983230072969 + 3 ^ 40 * 1665214 * 2
def baseEnd_1665214 : Nat := 190012261021367350281517

theorem tailTrace_1665214 : CollatzResearch.WordTrace tailWord_1665214 prefixEnd_1665214 190012261021367350281517 := by
  unfold tailWord_1665214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7591918023652693594299337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40490229459481032502929797 7591918023652693594299337)
  ·
    refine ⟨5693938517739520195724503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7591918023652693594299337 5693938517739520195724503)
    ·
      refine ⟨8540907776609280293586755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693938517739520195724503 8540907776609280293586755)
      ·
        refine ⟨12811361664913920440380133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540907776609280293586755 12811361664913920440380133)
        ·
          refine ⟨2402130312171360082571275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12811361664913920440380133 2402130312171360082571275)
          ·
            refine ⟨3603195468257040123856913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402130312171360082571275 3603195468257040123856913)
            ·
              refine ⟨2702396601192780092892685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603195468257040123856913 2702396601192780092892685)
              ·
                refine ⟨1013398725447292534834757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2702396601192780092892685 1013398725447292534834757)
                ·
                  refine ⟨190012261021367350281517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013398725447292534834757 190012261021367350281517)
                  ·
                    rfl

theorem cell22_1665214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1665214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665214 prefixEnd_1665214 := by exact prefixLift 1665214
  have htrace : WordTrace (prefixWord ++ tailWord_1665214) baseStart_1665214 baseEnd_1665214 := by
    simpa [prefixWord, tailWord_1665214, baseEnd_1665214] using wordTrace_append hprefix tailTrace_1665214
  have hstable : (prefixWord ++ tailWord_1665214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665214).length < 2 ^ (prefixWord ++ tailWord_1665214).sum := by decide
  have hdescent : baseEnd_1665214 < baseStart_1665214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665270 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_1665270 : Nat := 118140960795 + 1665270 * 2 ^ 59
def prefixEnd_1665270 : Nat := 4983230072969 + 3 ^ 40 * 1665270 * 2
def baseEnd_1665270 : Nat := 190018651002845523814793

theorem tailTrace_1665270 : CollatzResearch.WordTrace tailWord_1665270 prefixEnd_1665270 190018651002845523814793 := by
  unfold tailWord_1665270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796086667313666894902079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40491591118012446878955509 3796086667313666894902079)
  ·
    refine ⟨5694130000970500342353119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3796086667313666894902079 5694130000970500342353119)
    ·
      refine ⟨8541195001455750513529679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694130000970500342353119 8541195001455750513529679)
      ·
        refine ⟨12811792502183625770294519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8541195001455750513529679 12811792502183625770294519)
        ·
          refine ⟨19217688753275438655441779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12811792502183625770294519 19217688753275438655441779)
          ·
            refine ⟨28826533129913157983162669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19217688753275438655441779 28826533129913157983162669)
            ·
              refine ⟨10809949923717434243686001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28826533129913157983162669 10809949923717434243686001)
              ·
                refine ⟨8107462442788075682764501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809949923717434243686001 8107462442788075682764501)
                ·
                  refine ⟨190018651002845523814793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8107462442788075682764501 190018651002845523814793)
                  ·
                    rfl

theorem cell22_1665270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_1665270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665270 prefixEnd_1665270 := by exact prefixLift 1665270
  have htrace : WordTrace (prefixWord ++ tailWord_1665270) baseStart_1665270 baseEnd_1665270 := by
    simpa [prefixWord, tailWord_1665270, baseEnd_1665270] using wordTrace_append hprefix tailTrace_1665270
  have hstable : (prefixWord ++ tailWord_1665270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665270).length < 2 ^ (prefixWord ++ tailWord_1665270).sum := by decide
  have hdescent : baseEnd_1665270 < baseStart_1665270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665274 : List Nat := [3, 1, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_1665274 : Nat := 118140960795 + 1665274 * 2 ^ 59
def prefixEnd_1665274 : Nat := 4983230072969 + 3 ^ 40 * 1665274 * 2
def baseEnd_1665274 : Nat := 570057322290281894344367

theorem tailTrace_1665274 : CollatzResearch.WordTrace tailWord_1665274 prefixEnd_1665274 570057322290281894344367 := by
  unfold tailWord_1665274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15184383142251044750394719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40491688379336119334385917 15184383142251044750394719)
  ·
    refine ⟨22776574713376567125592079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15184383142251044750394719 22776574713376567125592079)
    ·
      refine ⟨34164862070064850688388119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22776574713376567125592079 34164862070064850688388119)
      ·
        refine ⟨51247293105097276032582179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34164862070064850688388119 51247293105097276032582179)
        ·
          refine ⟨76870939657645914048873269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51247293105097276032582179 76870939657645914048873269)
          ·
            refine ⟨7206650592904304442081869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76870939657645914048873269 7206650592904304442081869)
            ·
              refine ⟨2702493972339114165780701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7206650592904304442081869 2702493972339114165780701)
              ·
                refine ⟨1013435239627167812167763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2702493972339114165780701 1013435239627167812167763)
                ·
                  refine ⟨1520152859440751718251645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013435239627167812167763 1520152859440751718251645)
                  ·
                    refine ⟨570057322290281894344367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520152859440751718251645 570057322290281894344367)
                    ·
                      rfl

theorem cell22_1665274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_1665274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665274 prefixEnd_1665274 := by exact prefixLift 1665274
  have htrace : WordTrace (prefixWord ++ tailWord_1665274) baseStart_1665274 baseEnd_1665274 := by
    simpa [prefixWord, tailWord_1665274, baseEnd_1665274] using wordTrace_append hprefix tailTrace_1665274
  have hstable : (prefixWord ++ tailWord_1665274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665274).length < 2 ^ (prefixWord ++ tailWord_1665274).sum := by decide
  have hdescent : baseEnd_1665274 < baseStart_1665274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665317 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_1665317 : Nat := 118140960795 + 1665317 * 2 ^ 59
def prefixEnd_1665317 : Nat := 4983230072969 + 3 ^ 40 * 1665317 * 2
def baseEnd_1665317 : Nat := 570072042069044115519235

theorem tailTrace_1665317 : CollatzResearch.WordTrace tailWord_1665317 prefixEnd_1665317 570072042069044115519235 := by
  unfold tailWord_1665317
  simp only [CollatzResearch.WordTrace]
  refine ⟨60739100907848397345394205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40492733938565598230262803 60739100907848397345394205)
  ·
    refine ⟨22777162840443149004522827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60739100907848397345394205 22777162840443149004522827)
    ·
      refine ⟨34165744260664723506784241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22777162840443149004522827 34165744260664723506784241)
      ·
        refine ⟨25624308195498542630088181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34165744260664723506784241 25624308195498542630088181)
        ·
          refine ⟨2402278893327988371570767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25624308195498542630088181 2402278893327988371570767)
          ·
            refine ⟨3603418339991982557356151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402278893327988371570767 3603418339991982557356151)
            ·
              refine ⟨5405127509987973836034227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603418339991982557356151 5405127509987973836034227)
              ·
                refine ⟨8107691264981960754051341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405127509987973836034227 8107691264981960754051341)
                ·
                  refine ⟨3040384224368235282769253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8107691264981960754051341 3040384224368235282769253)
                  ·
                    refine ⟨570072042069044115519235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3040384224368235282769253 570072042069044115519235)
                    ·
                      rfl

theorem cell22_1665317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_1665317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665317 prefixEnd_1665317 := by exact prefixLift 1665317
  have htrace : WordTrace (prefixWord ++ tailWord_1665317) baseStart_1665317 baseEnd_1665317 := by
    simpa [prefixWord, tailWord_1665317, baseEnd_1665317] using wordTrace_append hprefix tailTrace_1665317
  have hstable : (prefixWord ++ tailWord_1665317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665317).length < 2 ^ (prefixWord ++ tailWord_1665317).sum := by decide
  have hdescent : baseEnd_1665317 < baseStart_1665317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665347 : List Nat := [1, 1, 1, 3, 1, 3, 3, 4, 2, 3]
def baseStart_1665347 : Nat := 118140960795 + 1665347 * 2 ^ 59
def prefixEnd_1665347 : Nat := 4983230072969 + 3 ^ 40 * 1665347 * 2
def baseEnd_1665347 : Nat := 570082311682134037269143

theorem tailTrace_1665347 : CollatzResearch.WordTrace tailWord_1665347 prefixEnd_1665347 570082311682134037269143 := by
  unfold tailWord_1665347
  simp only [CollatzResearch.WordTrace]
  refine ⟨60740195097739712468986295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40493463398493141645990863 60740195097739712468986295)
  ·
    refine ⟨91110292646609568703479443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60740195097739712468986295 91110292646609568703479443)
    ·
      refine ⟨136665438969914353055219165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91110292646609568703479443 136665438969914353055219165)
      ·
        refine ⟨51249539613717882395707187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136665438969914353055219165 51249539613717882395707187)
        ·
          refine ⟨76874309420576823593560781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51249539613717882395707187 76874309420576823593560781)
          ·
            refine ⟨28827866032716308847585293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76874309420576823593560781 28827866032716308847585293)
            ·
              refine ⟨10810449762268615817844485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28827866032716308847585293 10810449762268615817844485)
              ·
                refine ⟨2026959330425365465845841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10810449762268615817844485 2026959330425365465845841)
                ·
                  refine ⟨1520219497819024099384381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026959330425365465845841 1520219497819024099384381)
                  ·
                    refine ⟨570082311682134037269143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520219497819024099384381 570082311682134037269143)
                    ·
                      rfl

theorem cell22_1665347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 2, 3].length) (baseStart_1665347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665347 prefixEnd_1665347 := by exact prefixLift 1665347
  have htrace : WordTrace (prefixWord ++ tailWord_1665347) baseStart_1665347 baseEnd_1665347 := by
    simpa [prefixWord, tailWord_1665347, baseEnd_1665347] using wordTrace_append hprefix tailTrace_1665347
  have hstable : (prefixWord ++ tailWord_1665347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665347).length < 2 ^ (prefixWord ++ tailWord_1665347).sum := by decide
  have hdescent : baseEnd_1665347 < baseStart_1665347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665360 : List Nat := [2, 1, 1, 1, 1, 6, 3, 7]
def baseStart_1665360 : Nat := 118140960795 + 1665360 * 2 ^ 59
def prefixEnd_1665360 : Nat := 4983230072969 + 3 ^ 40 * 1665360 * 2
def baseEnd_1665360 : Nat := 63342973538645148521567

theorem tailTrace_1665360 : CollatzResearch.WordTrace tailWord_1665360 prefixEnd_1665360 63342973538645148521567 := by
  unfold tailWord_1665360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30370334623346307844604767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40493779497795077126139689 30370334623346307844604767)
  ·
    refine ⟨45555501935019461766907151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30370334623346307844604767 45555501935019461766907151)
    ·
      refine ⟨68333252902529192650360727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45555501935019461766907151 68333252902529192650360727)
      ·
        refine ⟨102499879353793788975541091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68333252902529192650360727 102499879353793788975541091)
        ·
          refine ⟨153749819030690683463311637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102499879353793788975541091 153749819030690683463311637)
          ·
            refine ⟨7207022767063625787342733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153749819030690683463311637 7207022767063625787342733)
            ·
              refine ⟨2702633537648859670253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7207022767063625787342733 2702633537648859670253525)
              ·
                refine ⟨63342973538645148521567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2702633537648859670253525 63342973538645148521567)
                ·
                  rfl

theorem cell22_1665360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_1665360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665360 prefixEnd_1665360 := by exact prefixLift 1665360
  have htrace : WordTrace (prefixWord ++ tailWord_1665360) baseStart_1665360 baseEnd_1665360 := by
    simpa [prefixWord, tailWord_1665360, baseEnd_1665360] using wordTrace_append hprefix tailTrace_1665360
  have hstable : (prefixWord ++ tailWord_1665360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665360).length < 2 ^ (prefixWord ++ tailWord_1665360).sum := by decide
  have hdescent : baseEnd_1665360 < baseStart_1665360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665364 : List Nat := [2, 4, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1665364 : Nat := 118140960795 + 1665364 * 2 ^ 59
def prefixEnd_1665364 : Nat := 4983230072969 + 3 ^ 40 * 1665364 * 2
def baseEnd_1665364 : Nat := 570088131129551659594091

theorem tailTrace_1665364 : CollatzResearch.WordTrace tailWord_1665364 prefixEnd_1665364 570088131129551659594091 := by
  unfold tailWord_1665364
  simp only [CollatzResearch.WordTrace]
  refine ⟨30370407569339062186177573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40493876759118749581570097 30370407569339062186177573)
  ·
    refine ⟨5694451419251074159908295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30370407569339062186177573 5694451419251074159908295)
    ·
      refine ⟨8541677128876611239862443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694451419251074159908295 8541677128876611239862443)
      ·
        refine ⟨12812515693314916859793665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8541677128876611239862443 12812515693314916859793665)
        ·
          refine ⟨9609386769986187644845249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12812515693314916859793665 9609386769986187644845249)
          ·
            refine ⟨7207040077489640733633937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9609386769986187644845249 7207040077489640733633937)
            ·
              refine ⟨5405280058117230550225453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207040077489640733633937 5405280058117230550225453)
              ·
                refine ⟨2026980021793961456334545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5405280058117230550225453 2026980021793961456334545)
                ·
                  refine ⟨1520235016345471092250909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026980021793961456334545 1520235016345471092250909)
                  ·
                    refine ⟨570088131129551659594091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520235016345471092250909 570088131129551659594091)
                    ·
                      rfl

theorem cell22_1665364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1665364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665364 prefixEnd_1665364 := by exact prefixLift 1665364
  have htrace : WordTrace (prefixWord ++ tailWord_1665364) baseStart_1665364 baseEnd_1665364 := by
    simpa [prefixWord, tailWord_1665364, baseEnd_1665364] using wordTrace_append hprefix tailTrace_1665364
  have hstable : (prefixWord ++ tailWord_1665364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665364).length < 2 ^ (prefixWord ++ tailWord_1665364).sum := by decide
  have hdescent : baseEnd_1665364 < baseStart_1665364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665409 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1665409 : Nat := 118140960795 + 1665409 * 2 ^ 59
def prefixEnd_1665409 : Nat := 4983230072969 + 3 ^ 40 * 1665409 * 2
def baseEnd_1665409 : Nat := 570103535549186542218953

theorem tailTrace_1665409 : CollatzResearch.WordTrace tailWord_1665409 prefixEnd_1665409 570103535549186542218953 := by
  unfold tailWord_1665409
  simp only [CollatzResearch.WordTrace]
  refine ⟨60742456423515097057743281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40494970949010064705162187 60742456423515097057743281)
  ·
    refine ⟨45556842317636322793307461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60742456423515097057743281 45556842317636322793307461)
    ·
      refine ⟨8541907934556810523745149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45556842317636322793307461 8541907934556810523745149)
      ·
        refine ⟨3203215475458803946404431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8541907934556810523745149 3203215475458803946404431)
        ·
          refine ⟨4804823213188205919606647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203215475458803946404431 4804823213188205919606647)
          ·
            refine ⟨7207234819782308879409971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804823213188205919606647 7207234819782308879409971)
            ·
              refine ⟨10810852229673463319114957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207234819782308879409971 10810852229673463319114957)
              ·
                refine ⟨4054069586127548744668109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10810852229673463319114957 4054069586127548744668109)
                ·
                  refine ⟨1520276094797830779250541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4054069586127548744668109 1520276094797830779250541)
                  ·
                    refine ⟨570103535549186542218953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520276094797830779250541 570103535549186542218953)
                    ·
                      rfl

theorem cell22_1665409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1665409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665409 prefixEnd_1665409 := by exact prefixLift 1665409
  have htrace : WordTrace (prefixWord ++ tailWord_1665409) baseStart_1665409 baseEnd_1665409 := by
    simpa [prefixWord, tailWord_1665409, baseEnd_1665409] using wordTrace_append hprefix tailTrace_1665409
  have hstable : (prefixWord ++ tailWord_1665409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665409).length < 2 ^ (prefixWord ++ tailWord_1665409).sum := by decide
  have hdescent : baseEnd_1665409 < baseStart_1665409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665460 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1665460 : Nat := 118140960795 + 1665460 * 2 ^ 59
def prefixEnd_1665460 : Nat := 4983230072969 + 3 ^ 40 * 1665460 * 2
def baseEnd_1665460 : Nat := 570120993891439409193797

theorem tailTrace_1665460 : CollatzResearch.WordTrace tailWord_1665460 prefixEnd_1665460 570120993891439409193797 := by
  unfold tailWord_1665460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30372158273165166383924917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40496211030886888511899889 30372158273165166383924917)
  ·
    refine ⟨2847389838109234348492961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30372158273165166383924917 2847389838109234348492961)
    ·
      refine ⟨2135542378581925761369721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2847389838109234348492961 2135542378581925761369721)
      ·
        refine ⟨1601656783936444321027291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2135542378581925761369721 1601656783936444321027291)
        ·
          refine ⟨2402485175904666481540937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601656783936444321027291 2402485175904666481540937)
          ·
            refine ⟨1801863881928499861155703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402485175904666481540937 1801863881928499861155703)
            ·
              refine ⟨2702795822892749791733555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801863881928499861155703 2702795822892749791733555)
              ·
                refine ⟨4054193734339124687600333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702795822892749791733555 4054193734339124687600333)
                ·
                  refine ⟨1520322650377171757850125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4054193734339124687600333 1520322650377171757850125)
                  ·
                    refine ⟨570120993891439409193797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520322650377171757850125 570120993891439409193797)
                    ·
                      rfl

theorem cell22_1665460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1665460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665460 prefixEnd_1665460 := by exact prefixLift 1665460
  have htrace : WordTrace (prefixWord ++ tailWord_1665460) baseStart_1665460 baseEnd_1665460 := by
    simpa [prefixWord, tailWord_1665460, baseEnd_1665460] using wordTrace_append hprefix tailTrace_1665460
  have hstable : (prefixWord ++ tailWord_1665460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665460).length < 2 ^ (prefixWord ++ tailWord_1665460).sum := by decide
  have hdescent : baseEnd_1665460 < baseStart_1665460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665473 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 5]
def baseStart_1665473 : Nat := 118140960795 + 1665473 * 2 ^ 59
def prefixEnd_1665473 : Nat := 4983230072969 + 3 ^ 40 * 1665473 * 2
def baseEnd_1665473 : Nat := 190041814685703902872919

theorem tailTrace_1665473 : CollatzResearch.WordTrace tailWord_1665473 prefixEnd_1665473 190041814685703902872919 := by
  unfold tailWord_1665473
  simp only [CollatzResearch.WordTrace]
  refine ⟨60744790695283235988073073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40496527130188823992048715 60744790695283235988073073)
  ·
    refine ⟨45558593021462426991054805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60744790695283235988073073 45558593021462426991054805)
    ·
      refine ⟨1067779523940525632602847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45558593021462426991054805 1067779523940525632602847)
      ·
        refine ⟨1601669285910788448904271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067779523940525632602847 1601669285910788448904271)
        ·
          refine ⟨2402503928866182673356407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601669285910788448904271 2402503928866182673356407)
          ·
            refine ⟨3603755893299274010034611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402503928866182673356407 3603755893299274010034611)
            ·
              refine ⟨5405633839948911015051917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603755893299274010034611 5405633839948911015051917)
              ·
                refine ⟨2027112689980841630644469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5405633839948911015051917 2027112689980841630644469)
                ·
                  refine ⟨190041814685703902872919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2027112689980841630644469 190041814685703902872919)
                  ·
                    rfl

theorem cell22_1665473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_1665473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665473 prefixEnd_1665473 := by exact prefixLift 1665473
  have htrace : WordTrace (prefixWord ++ tailWord_1665473) baseStart_1665473 baseEnd_1665473 := by
    simpa [prefixWord, tailWord_1665473, baseEnd_1665473] using wordTrace_append hprefix tailTrace_1665473
  have hstable : (prefixWord ++ tailWord_1665473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665473).length < 2 ^ (prefixWord ++ tailWord_1665473).sum := by decide
  have hdescent : baseEnd_1665473 < baseStart_1665473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665482 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1665482 : Nat := 118140960795 + 1665482 * 2 ^ 59
def prefixEnd_1665482 : Nat := 4983230072969 + 3 ^ 40 * 1665482 * 2
def baseEnd_1665482 : Nat := 570128524941038685143729

theorem tailTrace_1665482 : CollatzResearch.WordTrace tailWord_1665482 prefixEnd_1665482 570128524941038685143729 := by
  unfold tailWord_1665482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186279738062657631287675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40496745968167087016767133 15186279738062657631287675)
  ·
    refine ⟨22779419607093986446931513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186279738062657631287675 22779419607093986446931513)
    ·
      refine ⟨17084564705320489835198635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22779419607093986446931513 17084564705320489835198635)
      ·
        refine ⟨25626847057980734752797953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17084564705320489835198635 25626847057980734752797953)
        ·
          refine ⟨19220135293485551064598465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25626847057980734752797953 19220135293485551064598465)
          ·
            refine ⟨14415101470114163298448849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19220135293485551064598465 14415101470114163298448849)
            ·
              refine ⟨10811326102585622473836637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14415101470114163298448849 10811326102585622473836637)
              ·
                refine ⟨4054247288469608427688739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10811326102585622473836637 4054247288469608427688739)
                ·
                  refine ⟨6081370932704412641533109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054247288469608427688739 6081370932704412641533109)
                  ·
                    refine ⟨570128524941038685143729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6081370932704412641533109 570128524941038685143729)
                    ·
                      rfl

theorem cell22_1665482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1665482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665482 prefixEnd_1665482 := by exact prefixLift 1665482
  have htrace : WordTrace (prefixWord ++ tailWord_1665482) baseStart_1665482 baseEnd_1665482 := by
    simpa [prefixWord, tailWord_1665482, baseEnd_1665482] using wordTrace_append hprefix tailTrace_1665482
  have hstable : (prefixWord ++ tailWord_1665482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665482).length < 2 ^ (prefixWord ++ tailWord_1665482).sum := by decide
  have hdescent : baseEnd_1665482 < baseStart_1665482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665514 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1665514 : Nat := 118140960795 + 1665514 * 2 ^ 59
def prefixEnd_1665514 : Nat := 4983230072969 + 3 ^ 40 * 1665514 * 2
def baseEnd_1665514 : Nat := 570139479195001268343631

theorem tailTrace_1665514 : CollatzResearch.WordTrace tailWord_1665514 prefixEnd_1665514 570139479195001268343631 := by
  unfold tailWord_1665514
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186571522033674997578899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40497524058756466660210397 15186571522033674997578899)
  ·
    refine ⟨22779857283050512496368349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186571522033674997578899 22779857283050512496368349)
    ·
      refine ⟨8542446481143942186138131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22779857283050512496368349 8542446481143942186138131)
      ·
        refine ⟨12813669721715913279207197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542446481143942186138131 12813669721715913279207197)
        ·
          refine ⟨4805126145643467479702699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12813669721715913279207197 4805126145643467479702699)
          ·
            refine ⟨7207689218465201219554049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805126145643467479702699 7207689218465201219554049)
            ·
              refine ⟨5405766913848900914665537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207689218465201219554049 5405766913848900914665537)
              ·
                refine ⟨4054325185386675685999153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405766913848900914665537 4054325185386675685999153)
                ·
                  refine ⟨3040743889040006764499365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054325185386675685999153 3040743889040006764499365)
                  ·
                    refine ⟨570139479195001268343631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3040743889040006764499365 570139479195001268343631)
                    ·
                      rfl

theorem cell22_1665514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1665514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665514 prefixEnd_1665514 := by exact prefixLift 1665514
  have htrace : WordTrace (prefixWord ++ tailWord_1665514) baseStart_1665514 baseEnd_1665514 := by
    simpa [prefixWord, tailWord_1665514, baseEnd_1665514] using wordTrace_append hprefix tailTrace_1665514
  have hstable : (prefixWord ++ tailWord_1665514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665514).length < 2 ^ (prefixWord ++ tailWord_1665514).sum := by decide
  have hdescent : baseEnd_1665514 < baseStart_1665514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665518 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1665518 : Nat := 118140960795 + 1665518 * 2 ^ 59
def prefixEnd_1665518 : Nat := 4983230072969 + 3 ^ 40 * 1665518 * 2
def baseEnd_1665518 : Nat := 190046949492248863747873

theorem tailTrace_1665518 : CollatzResearch.WordTrace tailWord_1665518 prefixEnd_1665518 190046949492248863747873 := by
  unfold tailWord_1665518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593303997515026084182651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40497621320080139115640805 7593303997515026084182651)
  ·
    refine ⟨11389955996272539126273977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7593303997515026084182651 11389955996272539126273977)
    ·
      refine ⟨8542466997204404344705483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11389955996272539126273977 8542466997204404344705483)
      ·
        refine ⟨12813700495806606517058225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542466997204404344705483 12813700495806606517058225)
        ·
          refine ⟨9610275371854954887793669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12813700495806606517058225 9610275371854954887793669)
          ·
            refine ⟨1801926632222804041461313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9610275371854954887793669 1801926632222804041461313)
            ·
              refine ⟨1351444974167103031095985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801926632222804041461313 1351444974167103031095985)
              ·
                refine ⟨1013583730625327273321989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351444974167103031095985 1013583730625327273321989)
                ·
                  refine ⟨190046949492248863747873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013583730625327273321989 190046949492248863747873)
                  ·
                    rfl

theorem cell22_1665518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1665518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665518 prefixEnd_1665518 := by exact prefixLift 1665518
  have htrace : WordTrace (prefixWord ++ tailWord_1665518) baseStart_1665518 baseEnd_1665518 := by
    simpa [prefixWord, tailWord_1665518, baseEnd_1665518] using wordTrace_append hprefix tailTrace_1665518
  have hstable : (prefixWord ++ tailWord_1665518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665518).length < 2 ^ (prefixWord ++ tailWord_1665518).sum := by decide
  have hdescent : baseEnd_1665518 < baseStart_1665518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665557 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 7]
def baseStart_1665557 : Nat := 118140960795 + 1665557 * 2 ^ 59
def prefixEnd_1665557 : Nat := 4983230072969 + 3 ^ 40 * 1665557 * 2
def baseEnd_1665557 : Nat := 190051399657921163172833

theorem tailTrace_1665557 : CollatzResearch.WordTrace tailWord_1665557 prefixEnd_1665557 190051399657921163172833 := by
  unfold tailWord_1665557
  simp only [CollatzResearch.WordTrace]
  refine ⟨60747854426978918334130925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40498569617985945556087283 60747854426978918334130925)
  ·
    refine ⟨22780445410117094375299097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60747854426978918334130925 22780445410117094375299097)
    ·
      refine ⟨17085334057587820781474323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22780445410117094375299097 17085334057587820781474323)
      ·
        refine ⟨25628001086381731172211485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17085334057587820781474323 25628001086381731172211485)
        ·
          refine ⟨9610500407393149189579307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25628001086381731172211485 9610500407393149189579307)
          ·
            refine ⟨14415750611089723784368961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610500407393149189579307 14415750611089723784368961)
            ·
              refine ⟨10811812958317292838276721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14415750611089723784368961 10811812958317292838276721)
              ·
                refine ⟨8108859718737969628707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10811812958317292838276721 8108859718737969628707541)
                ·
                  refine ⟨190051399657921163172833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8108859718737969628707541 190051399657921163172833)
                  ·
                    rfl

theorem cell22_1665557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_1665557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665557 prefixEnd_1665557 := by exact prefixLift 1665557
  have htrace : WordTrace (prefixWord ++ tailWord_1665557) baseStart_1665557 baseEnd_1665557 := by
    simpa [prefixWord, tailWord_1665557, baseEnd_1665557] using wordTrace_append hprefix tailTrace_1665557
  have hstable : (prefixWord ++ tailWord_1665557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665557).length < 2 ^ (prefixWord ++ tailWord_1665557).sum := by decide
  have hdescent : baseEnd_1665557 < baseStart_1665557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665578 : List Nat := [3, 1, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1665578 : Nat := 118140960795 + 1665578 * 2 ^ 59
def prefixEnd_1665578 : Nat := 4983230072969 + 3 ^ 40 * 1665578 * 2
def baseEnd_1665578 : Nat := 570161387702926434743435

theorem tailTrace_1665578 : CollatzResearch.WordTrace tailWord_1665578 prefixEnd_1665578 570161387702926434743435 := by
  unfold tailWord_1665578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15187155089975709730161347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40499080239935225947096925 15187155089975709730161347)
  ·
    refine ⟨22780732634963564595242021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15187155089975709730161347 22780732634963564595242021)
    ·
      refine ⟨4271387369055668361607879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22780732634963564595242021 4271387369055668361607879)
      ·
        refine ⟨6407081053583502542411819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271387369055668361607879 6407081053583502542411819)
        ·
          refine ⟨9610621580375253813617729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407081053583502542411819 9610621580375253813617729)
          ·
            refine ⟨7207966185281440360213297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9610621580375253813617729 7207966185281440360213297)
            ·
              refine ⟨5405974638961080270159973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207966185281440360213297 5405974638961080270159973)
              ·
                refine ⟨1013620244805202550654995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5405974638961080270159973 1013620244805202550654995)
                ·
                  refine ⟨1520430367207803825982493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013620244805202550654995 1520430367207803825982493)
                  ·
                    refine ⟨570161387702926434743435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520430367207803825982493 570161387702926434743435)
                    ·
                      rfl

theorem cell22_1665578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1665578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665578 prefixEnd_1665578 := by exact prefixLift 1665578
  have htrace : WordTrace (prefixWord ++ tailWord_1665578) baseStart_1665578 baseEnd_1665578 := by
    simpa [prefixWord, tailWord_1665578, baseEnd_1665578] using wordTrace_append hprefix tailTrace_1665578
  have hstable : (prefixWord ++ tailWord_1665578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665578).length < 2 ^ (prefixWord ++ tailWord_1665578).sum := by decide
  have hdescent : baseEnd_1665578 < baseStart_1665578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665647 : List Nat := [1, 1, 2, 1, 3, 2, 3, 9]
def baseStart_1665647 : Nat := 118140960795 + 1665647 * 2 ^ 59
def prefixEnd_1665647 : Nat := 4983230072969 + 3 ^ 40 * 1665647 * 2
def baseEnd_1665647 : Nat := 63353889757003694974247

theorem tailTrace_1665647 : CollatzResearch.WordTrace tailWord_1665647 prefixEnd_1665647 63353889757003694974247 := by
  unfold tailWord_1665647
  simp only [CollatzResearch.WordTrace]
  refine ⟨60751136996652863704907195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40500757997768575803271463 60751136996652863704907195)
  ·
    refine ⟨91126705494979295557360793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60751136996652863704907195 91126705494979295557360793)
    ·
      refine ⟨68345029121234471668020595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91126705494979295557360793 68345029121234471668020595)
      ·
        refine ⟨102517543681851707502030893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68345029121234471668020595 102517543681851707502030893)
        ·
          refine ⟨38444078880694390313261585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102517543681851707502030893 38444078880694390313261585)
          ·
            refine ⟨28833059160520792734946189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38444078880694390313261585 28833059160520792734946189)
            ·
              refine ⟨10812397185195297275604821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28833059160520792734946189 10812397185195297275604821)
              ·
                refine ⟨63353889757003694974247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10812397185195297275604821 63353889757003694974247)
                ·
                  rfl

theorem cell22_1665647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 9].length) (baseStart_1665647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665647 prefixEnd_1665647 := by exact prefixLift 1665647
  have htrace : WordTrace (prefixWord ++ tailWord_1665647) baseStart_1665647 baseEnd_1665647 := by
    simpa [prefixWord, tailWord_1665647, baseEnd_1665647] using wordTrace_append hprefix tailTrace_1665647
  have hstable : (prefixWord ++ tailWord_1665647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665647).length < 2 ^ (prefixWord ++ tailWord_1665647).sum := by decide
  have hdescent : baseEnd_1665647 < baseStart_1665647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665679 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 5, 3]
def baseStart_1665679 : Nat := 118140960795 + 1665679 * 2 ^ 59
def prefixEnd_1665679 : Nat := 4983230072969 + 3 ^ 40 * 1665679 * 2
def baseEnd_1665679 : Nat := 570195962066995837968125

theorem tailTrace_1665679 : CollatzResearch.WordTrace tailWord_1665679 prefixEnd_1665679 570195962066995837968125 := by
  unfold tailWord_1665679
  simp only [CollatzResearch.WordTrace]
  refine ⟨60752304132536933170072091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40501536088357955446714727 60752304132536933170072091)
  ·
    refine ⟨91128456198805399755108137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60752304132536933170072091 91128456198805399755108137)
    ·
      refine ⟨68346342149104049816331103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91128456198805399755108137 68346342149104049816331103)
      ·
        refine ⟨102519513223656074724496655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68346342149104049816331103 102519513223656074724496655)
        ·
          refine ⟨153779269835484112086744983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102519513223656074724496655 153779269835484112086744983)
          ·
            refine ⟨230668904753226168130117475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153779269835484112086744983 230668904753226168130117475)
            ·
              refine ⟨346003357129839252195176213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230668904753226168130117475 346003357129839252195176213)
              ·
                refine ⟨16218907365461214946648885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 346003357129839252195176213 16218907365461214946648885)
                ·
                  refine ⟨1520522565511988901248333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16218907365461214946648885 1520522565511988901248333)
                  ·
                    refine ⟨570195962066995837968125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520522565511988901248333 570195962066995837968125)
                    ·
                      rfl

theorem cell22_1665679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_1665679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665679 prefixEnd_1665679 := by exact prefixLift 1665679
  have htrace : WordTrace (prefixWord ++ tailWord_1665679) baseStart_1665679 baseEnd_1665679 := by
    simpa [prefixWord, tailWord_1665679, baseEnd_1665679] using wordTrace_append hprefix tailTrace_1665679
  have hstable : (prefixWord ++ tailWord_1665679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665679).length < 2 ^ (prefixWord ++ tailWord_1665679).sum := by decide
  have hdescent : baseEnd_1665679 < baseStart_1665679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665724 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1665724 : Nat := 118140960795 + 1665724 * 2 ^ 59
def prefixEnd_1665724 : Nat := 4983230072969 + 3 ^ 40 * 1665724 * 2
def baseEnd_1665724 : Nat := 570211366486630720592987

theorem tailTrace_1665724 : CollatzResearch.WordTrace tailWord_1665724 prefixEnd_1665724 570211366486630720592987 := by
  unfold tailWord_1665724
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376972708686952927730113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40502630278249270570306817 30376972708686952927730113)
  ·
    refine ⟨22782729531515214695797585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30376972708686952927730113 22782729531515214695797585)
    ·
      refine ⟨17087047148636411021848189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22782729531515214695797585 17087047148636411021848189)
      ·
        refine ⟨6407642680738654133193071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17087047148636411021848189 6407642680738654133193071)
        ·
          refine ⟨9611464021107981199789607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407642680738654133193071 9611464021107981199789607)
          ·
            refine ⟨14417196031661971799684411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611464021107981199789607 14417196031661971799684411)
            ·
              refine ⟨21625794047492957699526617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14417196031661971799684411 21625794047492957699526617)
              ·
                refine ⟨16219345535619718274644963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21625794047492957699526617 16219345535619718274644963)
                ·
                  refine ⟨24329018303429577411967445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16219345535619718274644963 24329018303429577411967445)
                  ·
                    refine ⟨570211366486630720592987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24329018303429577411967445 570211366486630720592987)
                    ·
                      rfl

theorem cell22_1665724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1665724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665724 prefixEnd_1665724 := by exact prefixLift 1665724
  have htrace : WordTrace (prefixWord ++ tailWord_1665724) baseStart_1665724 baseEnd_1665724 := by
    simpa [prefixWord, tailWord_1665724, baseEnd_1665724] using wordTrace_append hprefix tailTrace_1665724
  have hstable : (prefixWord ++ tailWord_1665724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665724).length < 2 ^ (prefixWord ++ tailWord_1665724).sum := by decide
  have hdescent : baseEnd_1665724 < baseStart_1665724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665773 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1665773 : Nat := 118140960795 + 1665773 * 2 ^ 59
def prefixEnd_1665773 : Nat := 4983230072969 + 3 ^ 40 * 1665773 * 2
def baseEnd_1665773 : Nat := 570228140188010926117837

theorem tailTrace_1665773 : CollatzResearch.WordTrace tailWord_1665773 prefixEnd_1665773 570228140188010926117837 := by
  unfold tailWord_1665773
  simp only [CollatzResearch.WordTrace]
  refine ⟨60755732594196387223993973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40503821729464258149329315 60755732594196387223993973)
  ·
    refine ⟨5695849930705911302249435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60755732594196387223993973 5695849930705911302249435)
    ·
      refine ⟨8543774896058866953374153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695849930705911302249435 8543774896058866953374153)
      ·
        refine ⟨6407831172044150215030615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543774896058866953374153 6407831172044150215030615)
        ·
          refine ⟨9611746758066225322545923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407831172044150215030615 9611746758066225322545923)
          ·
            refine ⟨14417620137099337983818885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611746758066225322545923 14417620137099337983818885)
            ·
              refine ⟨2703303775706125871966041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14417620137099337983818885 2703303775706125871966041)
              ·
                refine ⟨2027477831779594403974531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703303775706125871966041 2027477831779594403974531)
                ·
                  refine ⟨3041216747669391605961797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027477831779594403974531 3041216747669391605961797)
                  ·
                    refine ⟨570228140188010926117837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3041216747669391605961797 570228140188010926117837)
                    ·
                      rfl

theorem cell22_1665773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1665773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665773 prefixEnd_1665773 := by exact prefixLift 1665773
  have htrace : WordTrace (prefixWord ++ tailWord_1665773) baseStart_1665773 baseEnd_1665773 := by
    simpa [prefixWord, tailWord_1665773, baseEnd_1665773] using wordTrace_append hprefix tailTrace_1665773
  have hstable : (prefixWord ++ tailWord_1665773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665773).length < 2 ^ (prefixWord ++ tailWord_1665773).sum := by decide
  have hdescent : baseEnd_1665773 < baseStart_1665773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665781 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1665781 : Nat := 118140960795 + 1665781 * 2 ^ 59
def prefixEnd_1665781 : Nat := 4983230072969 + 3 ^ 40 * 1665781 * 2
def baseEnd_1665781 : Nat := 570230878751501571917813

theorem tailTrace_1665781 : CollatzResearch.WordTrace tailWord_1665781 prefixEnd_1665781 570230878751501571917813 := by
  unfold tailWord_1665781
  simp only [CollatzResearch.WordTrace]
  refine ⟨60756024378167404590285197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40504016252111603060190131 60756024378167404590285197)
  ·
    refine ⟨22783509141812776721356949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60756024378167404590285197 22783509141812776721356949)
    ·
      refine ⟨1067976991022473908813607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22783509141812776721356949 1067976991022473908813607)
      ·
        refine ⟨1601965486533710863220411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067976991022473908813607 1601965486533710863220411)
        ·
          refine ⟨2402948229800566294830617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601965486533710863220411 2402948229800566294830617)
          ·
            refine ⟨1802211172350424721122963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402948229800566294830617 1802211172350424721122963)
            ·
              refine ⟨2703316758525637081684445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802211172350424721122963 2703316758525637081684445)
              ·
                refine ⟨1013743784447113905631667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703316758525637081684445 1013743784447113905631667)
                ·
                  refine ⟨1520615676670670858447501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013743784447113905631667 1520615676670670858447501)
                  ·
                    refine ⟨570230878751501571917813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520615676670670858447501 570230878751501571917813)
                    ·
                      rfl

theorem cell22_1665781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1665781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665781 prefixEnd_1665781 := by exact prefixLift 1665781
  have htrace : WordTrace (prefixWord ++ tailWord_1665781) baseStart_1665781 baseEnd_1665781 := by
    simpa [prefixWord, tailWord_1665781, baseEnd_1665781] using wordTrace_append hprefix tailTrace_1665781
  have hstable : (prefixWord ++ tailWord_1665781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665781).length < 2 ^ (prefixWord ++ tailWord_1665781).sum := by decide
  have hdescent : baseEnd_1665781 < baseStart_1665781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665784 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1665784 : Nat := 118140960795 + 1665784 * 2 ^ 59
def prefixEnd_1665784 : Nat := 4983230072969 + 3 ^ 40 * 1665784 * 2
def baseEnd_1665784 : Nat := 570231905712810564092803

theorem tailTrace_1665784 : CollatzResearch.WordTrace tailWord_1665784 prefixEnd_1665784 570231905712810564092803 := by
  unfold tailWord_1665784
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378066898578268051322203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40504089198104357401762937 30378066898578268051322203)
  ·
    refine ⟨45567100347867402076983305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30378066898578268051322203 45567100347867402076983305)
    ·
      refine ⟨34175325260900551557737479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45567100347867402076983305 34175325260900551557737479)
      ·
        refine ⟨51262987891350827336606219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34175325260900551557737479 51262987891350827336606219)
        ·
          refine ⟨76894481837026241004909329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51262987891350827336606219 76894481837026241004909329)
          ·
            refine ⟨57670861377769680753681997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76894481837026241004909329 57670861377769680753681997)
            ·
              refine ⟨21626573016663630282630749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57670861377769680753681997 21626573016663630282630749)
              ·
                refine ⟨8109964881248861355986531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21626573016663630282630749 8109964881248861355986531)
                ·
                  refine ⟨12164947321873292033979797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109964881248861355986531 12164947321873292033979797)
                  ·
                    refine ⟨570231905712810564092803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12164947321873292033979797 570231905712810564092803)
                    ·
                      rfl

theorem cell22_1665784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1665784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665784 prefixEnd_1665784 := by exact prefixLift 1665784
  have htrace : WordTrace (prefixWord ++ tailWord_1665784) baseStart_1665784 baseEnd_1665784 := by
    simpa [prefixWord, tailWord_1665784, baseEnd_1665784] using wordTrace_append hprefix tailTrace_1665784
  have hstable : (prefixWord ++ tailWord_1665784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665784).length < 2 ^ (prefixWord ++ tailWord_1665784).sum := by decide
  have hdescent : baseEnd_1665784 < baseStart_1665784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665786 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1665786 : Nat := 118140960795 + 1665786 * 2 ^ 59
def prefixEnd_1665786 : Nat := 4983230072969 + 3 ^ 40 * 1665786 * 2
def baseEnd_1665786 : Nat := 570232590353683225542797

theorem tailTrace_1665786 : CollatzResearch.WordTrace tailWord_1665786 prefixEnd_1665786 570232590353683225542797 := by
  unfold tailWord_1665786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15189051685787322611054303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40504137828766193629478141 15189051685787322611054303)
  ·
    refine ⟨22783577528680983916581455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15189051685787322611054303 22783577528680983916581455)
    ·
      refine ⟨34175366293021475874872183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22783577528680983916581455 34175366293021475874872183)
      ·
        refine ⟨51263049439532213812308275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34175366293021475874872183 51263049439532213812308275)
        ·
          refine ⟨76894574159298320718462413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51263049439532213812308275 76894574159298320718462413)
          ·
            refine ⟨28835465309736870269423405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76894574159298320718462413 28835465309736870269423405)
            ·
              refine ⟨10813299491151326351033777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28835465309736870269423405 10813299491151326351033777)
              ·
                refine ⟨8109974618363494763275333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10813299491151326351033777 8109974618363494763275333)
                ·
                  refine ⟨1520620240943155268114125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8109974618363494763275333 1520620240943155268114125)
                  ·
                    refine ⟨570232590353683225542797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520620240943155268114125 570232590353683225542797)
                    ·
                      rfl

theorem cell22_1665786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1665786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665786 prefixEnd_1665786 := by exact prefixLift 1665786
  have htrace : WordTrace (prefixWord ++ tailWord_1665786) baseStart_1665786 baseEnd_1665786 := by
    simpa [prefixWord, tailWord_1665786, baseEnd_1665786] using wordTrace_append hprefix tailTrace_1665786
  have hstable : (prefixWord ++ tailWord_1665786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665786).length < 2 ^ (prefixWord ++ tailWord_1665786).sum := by decide
  have hdescent : baseEnd_1665786 < baseStart_1665786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665788 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1665788 : Nat := 118140960795 + 1665788 * 2 ^ 59
def prefixEnd_1665788 : Nat := 4983230072969 + 3 ^ 40 * 1665788 * 2
def baseEnd_1665788 : Nat := 190077758331518628997597

theorem tailTrace_1665788 : CollatzResearch.WordTrace tailWord_1665788 prefixEnd_1665788 190077758331518628997597 := by
  unfold tailWord_1665788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378139844571022392895009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40504186459428029857193345 30378139844571022392895009)
  ·
    refine ⟨22783604883428266794671257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30378139844571022392895009 22783604883428266794671257)
    ·
      refine ⟨17087703662571200096003443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22783604883428266794671257 17087703662571200096003443)
      ·
        refine ⟨25631555493856800144005165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17087703662571200096003443 25631555493856800144005165)
        ·
          refine ⟨9611833310196300054001937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25631555493856800144005165 9611833310196300054001937)
          ·
            refine ⟨7208874982647225040501453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9611833310196300054001937 7208874982647225040501453)
            ·
              refine ⟨2703328118492709390188045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7208874982647225040501453 2703328118492709390188045)
              ·
                refine ⟨1013748044434766021320517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703328118492709390188045 1013748044434766021320517)
                ·
                  refine ⟨190077758331518628997597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013748044434766021320517 190077758331518628997597)
                  ·
                    rfl

theorem cell22_1665788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1665788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665788 prefixEnd_1665788 := by exact prefixLift 1665788
  have htrace : WordTrace (prefixWord ++ tailWord_1665788) baseStart_1665788 baseEnd_1665788 := by
    simpa [prefixWord, tailWord_1665788, baseEnd_1665788] using wordTrace_append hprefix tailTrace_1665788
  have hstable : (prefixWord ++ tailWord_1665788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665788).length < 2 ^ (prefixWord ++ tailWord_1665788).sum := by decide
  have hdescent : baseEnd_1665788 < baseStart_1665788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665820 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1665820 : Nat := 118140960795 + 1665820 * 2 ^ 59
def prefixEnd_1665820 : Nat := 4983230072969 + 3 ^ 40 * 1665820 * 2
def baseEnd_1665820 : Nat := 570244229248518470192693

theorem tailTrace_1665820 : CollatzResearch.WordTrace tailWord_1665820 prefixEnd_1665820 570244229248518470192693 := by
  unfold tailWord_1665820
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378723412513057125477457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40504964550017409500636609 30378723412513057125477457)
  ·
    refine ⟨22784042559384792844108093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30378723412513057125477457 22784042559384792844108093)
    ·
      refine ⟨8544015959769297316540535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22784042559384792844108093 8544015959769297316540535)
      ·
        refine ⟨12816023939653945974810803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8544015959769297316540535 12816023939653945974810803)
        ·
          refine ⟨19224035909480918962216205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12816023939653945974810803 19224035909480918962216205)
          ·
            refine ⟨7209013466055344610831077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19224035909480918962216205 7209013466055344610831077)
            ·
              refine ⟨1351690024885377114530827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7209013466055344610831077 1351690024885377114530827)
              ·
                refine ⟨2027535037328065671796241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351690024885377114530827 2027535037328065671796241)
                ·
                  refine ⟨1520651277996049253847181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2027535037328065671796241 1520651277996049253847181)
                  ·
                    refine ⟨570244229248518470192693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520651277996049253847181 570244229248518470192693)
                    ·
                      rfl

theorem cell22_1665820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1665820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665820 prefixEnd_1665820 := by exact prefixLift 1665820
  have htrace : WordTrace (prefixWord ++ tailWord_1665820) baseStart_1665820 baseEnd_1665820 := by
    simpa [prefixWord, tailWord_1665820, baseEnd_1665820] using wordTrace_append hprefix tailTrace_1665820
  have hstable : (prefixWord ++ tailWord_1665820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665820).length < 2 ^ (prefixWord ++ tailWord_1665820).sum := by decide
  have hdescent : baseEnd_1665820 < baseStart_1665820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665865 : List Nat := [1, 2, 1, 1, 2, 6, 1, 4, 1, 3]
def baseStart_1665865 : Nat := 118140960795 + 1665865 * 2 ^ 59
def prefixEnd_1665865 : Nat := 4983230072969 + 3 ^ 40 * 1665865 * 2
def baseEnd_1665865 : Nat := 570259633668153352817555

theorem tailTrace_1665865 : CollatzResearch.WordTrace tailWord_1665865 prefixEnd_1665865 570259633668153352817555 := by
  unfold tailWord_1665865
  simp only [CollatzResearch.WordTrace]
  refine ⟨60759088109863086936343049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40506058739908724624228699 60759088109863086936343049)
  ·
    refine ⟨45569316082397315202257287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60759088109863086936343049 45569316082397315202257287)
    ·
      refine ⟨68353974123595972803385931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45569316082397315202257287 68353974123595972803385931)
      ·
        refine ⟨102530961185393959205078897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68353974123595972803385931 102530961185393959205078897)
        ·
          refine ⟨76898220889045469403809173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102530961185393959205078897 76898220889045469403809173)
          ·
            refine ⟨3604604104174006378303555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76898220889045469403809173 3604604104174006378303555)
            ·
              refine ⟨5406906156261009567455333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604604104174006378303555 5406906156261009567455333)
              ·
                refine ⟨1013794904298939293897875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5406906156261009567455333 1013794904298939293897875)
                ·
                  refine ⟨1520692356448408940846813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013794904298939293897875 1520692356448408940846813)
                  ·
                    refine ⟨570259633668153352817555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520692356448408940846813 570259633668153352817555)
                    ·
                      rfl

theorem cell22_1665865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_1665865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665865 prefixEnd_1665865 := by exact prefixLift 1665865
  have htrace : WordTrace (prefixWord ++ tailWord_1665865) baseStart_1665865 baseEnd_1665865 := by
    simpa [prefixWord, tailWord_1665865, baseEnd_1665865] using wordTrace_append hprefix tailTrace_1665865
  have hstable : (prefixWord ++ tailWord_1665865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665865).length < 2 ^ (prefixWord ++ tailWord_1665865).sum := by decide
  have hdescent : baseEnd_1665865 < baseStart_1665865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665923 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 4]
def baseStart_1665923 : Nat := 118140960795 + 1665923 * 2 ^ 59
def prefixEnd_1665923 : Nat := 4983230072969 + 3 ^ 40 * 1665923 * 2
def baseEnd_1665923 : Nat := 190093162751153511622459

theorem tailTrace_1665923 : CollatzResearch.WordTrace tailWord_1665923 prefixEnd_1665923 190093162751153511622459 := by
  unfold tailWord_1665923
  simp only [CollatzResearch.WordTrace]
  refine ⟨60761203543652962841954423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40507469029101975227969615 60761203543652962841954423)
  ·
    refine ⟨91141805315479444262931635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60761203543652962841954423 91141805315479444262931635)
    ·
      refine ⟨136712707973219166394397453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91141805315479444262931635 136712707973219166394397453)
      ·
        refine ⟨51267265489957187397899045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136712707973219166394397453 51267265489957187397899045)
        ·
          refine ⟨9612612279366972637106071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51267265489957187397899045 9612612279366972637106071)
          ·
            refine ⟨14418918419050458955659107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612612279366972637106071 14418918419050458955659107)
            ·
              refine ⟨21628377628575688433488661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14418918419050458955659107 21628377628575688433488661)
              ·
                refine ⟨1013830201339485395319781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21628377628575688433488661 1013830201339485395319781)
                ·
                  refine ⟨190093162751153511622459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013830201339485395319781 190093162751153511622459)
                  ·
                    rfl

theorem cell22_1665923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 4].length) (baseStart_1665923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665923 prefixEnd_1665923 := by exact prefixLift 1665923
  have htrace : WordTrace (prefixWord ++ tailWord_1665923) baseStart_1665923 baseEnd_1665923 := by
    simpa [prefixWord, tailWord_1665923, baseEnd_1665923] using wordTrace_append hprefix tailTrace_1665923
  have hstable : (prefixWord ++ tailWord_1665923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665923).length < 2 ^ (prefixWord ++ tailWord_1665923).sum := by decide
  have hdescent : baseEnd_1665923 < baseStart_1665923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665953 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1665953 : Nat := 118140960795 + 1665953 * 2 ^ 59
def prefixEnd_1665953 : Nat := 4983230072969 + 3 ^ 40 * 1665953 * 2
def baseEnd_1665953 : Nat := 570289757866550456617285

theorem tailTrace_1665953 : CollatzResearch.WordTrace tailWord_1665953 prefixEnd_1665953 570289757866550456617285 := by
  unfold tailWord_1665953
  simp only [CollatzResearch.WordTrace]
  refine ⟨60762297733544277965546513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40508198489029518643697675 60762297733544277965546513)
  ·
    refine ⟨45571723300158208474159885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60762297733544277965546513 45571723300158208474159885)
    ·
      refine ⟨17089396237559328177809957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45571723300158208474159885 17089396237559328177809957)
      ·
        refine ⟨3204261794542374033339367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17089396237559328177809957 3204261794542374033339367)
        ·
          refine ⟨4806392691813561050009051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204261794542374033339367 4806392691813561050009051)
          ·
            refine ⟨7209589037720341575013577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806392691813561050009051 7209589037720341575013577)
            ·
              refine ⟨5407191778290256181260183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7209589037720341575013577 5407191778290256181260183)
              ·
                refine ⟨8110787667435384271890275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407191778290256181260183 8110787667435384271890275)
                ·
                  refine ⟨12166181501153076407835413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8110787667435384271890275 12166181501153076407835413)
                  ·
                    refine ⟨570289757866550456617285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12166181501153076407835413 570289757866550456617285)
                    ·
                      rfl

theorem cell22_1665953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1665953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665953 prefixEnd_1665953 := by exact prefixLift 1665953
  have htrace : WordTrace (prefixWord ++ tailWord_1665953) baseStart_1665953 baseEnd_1665953 := by
    simpa [prefixWord, tailWord_1665953, baseEnd_1665953] using wordTrace_append hprefix tailTrace_1665953
  have hstable : (prefixWord ++ tailWord_1665953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665953).length < 2 ^ (prefixWord ++ tailWord_1665953).sum := by decide
  have hdescent : baseEnd_1665953 < baseStart_1665953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665972 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1665972 : Nat := 118140960795 + 1665972 * 2 ^ 59
def prefixEnd_1665972 : Nat := 4983230072969 + 3 ^ 40 * 1665972 * 2
def baseEnd_1665972 : Nat := 570296261954840740392227

theorem tailTrace_1665972 : CollatzResearch.WordTrace tailWord_1665972 prefixEnd_1665972 570296261954840740392227 := by
  unfold tailWord_1665972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30381495360237722105244085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40508660480316962806992113 30381495360237722105244085)
  ·
    refine ⟨2848265190022286447366633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30381495360237722105244085 2848265190022286447366633)
    ·
      refine ⟨2136198892516714835524975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2848265190022286447366633 2136198892516714835524975)
      ·
        refine ⟨3204298338775072253287463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136198892516714835524975 3204298338775072253287463)
        ·
          refine ⟨4806447508162608379931195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204298338775072253287463 4806447508162608379931195)
          ·
            refine ⟨7209671262243912569896793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806447508162608379931195 7209671262243912569896793)
            ·
              refine ⟨5407253446682934427422595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7209671262243912569896793 5407253446682934427422595)
              ·
                refine ⟨8110880170024401641133893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407253446682934427422595 8110880170024401641133893)
                ·
                  refine ⟨1520790031879575307712605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8110880170024401641133893 1520790031879575307712605)
                  ·
                    refine ⟨570296261954840740392227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520790031879575307712605 570296261954840740392227)
                    ·
                      rfl

theorem cell22_1665972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1665972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665972 prefixEnd_1665972 := by exact prefixLift 1665972
  have htrace : WordTrace (prefixWord ++ tailWord_1665972) baseStart_1665972 baseEnd_1665972 := by
    simpa [prefixWord, tailWord_1665972, baseEnd_1665972] using wordTrace_append hprefix tailTrace_1665972
  have hstable : (prefixWord ++ tailWord_1665972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665972).length < 2 ^ (prefixWord ++ tailWord_1665972).sum := by decide
  have hdescent : baseEnd_1665972 < baseStart_1665972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665983 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 3, 3]
def baseStart_1665983 : Nat := 118140960795 + 1665983 * 2 ^ 59
def prefixEnd_1665983 : Nat := 4983230072969 + 3 ^ 40 * 1665983 * 2
def baseEnd_1665983 : Nat := 570300027479640378367193

theorem tailTrace_1665983 : CollatzResearch.WordTrace tailWord_1665983 prefixEnd_1665983 570300027479640378367193 := by
  unfold tailWord_1665983
  simp only [CollatzResearch.WordTrace]
  refine ⟨60763391923435593089138603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40508927948957062059425735 60763391923435593089138603)
  ·
    refine ⟨91145087885153389633707905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60763391923435593089138603 91145087885153389633707905)
    ·
      refine ⟨68358815913865042225280929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91145087885153389633707905 68358815913865042225280929)
      ·
        refine ⟨51269111935398781668960697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68358815913865042225280929 51269111935398781668960697)
        ·
          refine ⟨38451833951549086251720523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51269111935398781668960697 38451833951549086251720523)
          ·
            refine ⟨57677750927323629377580785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38451833951549086251720523 57677750927323629377580785)
            ·
              refine ⟨43258313195492722033185589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57677750927323629377580785 43258313195492722033185589)
              ·
                refine ⟨4055466862077442690611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43258313195492722033185589 4055466862077442690611149)
                ·
                  refine ⟨1520800073279041008979181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4055466862077442690611149 1520800073279041008979181)
                  ·
                    refine ⟨570300027479640378367193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1520800073279041008979181 570300027479640378367193)
                    ·
                      rfl

theorem cell22_1665983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_1665983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1665983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1665983 prefixEnd_1665983 := by exact prefixLift 1665983
  have htrace : WordTrace (prefixWord ++ tailWord_1665983) baseStart_1665983 baseEnd_1665983 := by
    simpa [prefixWord, tailWord_1665983, baseEnd_1665983] using wordTrace_append hprefix tailTrace_1665983
  have hstable : (prefixWord ++ tailWord_1665983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665983).length < 2 ^ (prefixWord ++ tailWord_1665983).sum := by decide
  have hdescent : baseEnd_1665983 < baseStart_1665983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666036 : List Nat := [2, 6, 2, 1, 1, 2, 1, 7]
def baseStart_1666036 : Nat := 118140960795 + 1666036 * 2 ^ 59
def prefixEnd_1666036 : Nat := 4983230072969 + 3 ^ 40 * 1666036 * 2
def baseEnd_1666036 : Nat := 63368685606973989643559

theorem tailTrace_1666036 : CollatzResearch.WordTrace tailWord_1666036 prefixEnd_1666036 63368685606973989643559 := by
  unfold tailWord_1666036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30382662496121791570408981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40510216661495722093878641 30382662496121791570408981)
  ·
    refine ⟨1424187304505708979862921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30382662496121791570408981 1424187304505708979862921)
    ·
      refine ⟨1068140478379281734897191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1424187304505708979862921 1068140478379281734897191)
      ·
        refine ⟨1602210717568922602345787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068140478379281734897191 1602210717568922602345787)
        ·
          refine ⟨2403316076353383903518681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602210717568922602345787 2403316076353383903518681)
          ·
            refine ⟨1802487057265037927639011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403316076353383903518681 1802487057265037927639011)
            ·
              refine ⟨2703730585897556891458517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802487057265037927639011 2703730585897556891458517)
              ·
                refine ⟨63368685606973989643559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2703730585897556891458517 63368685606973989643559)
                ·
                  rfl

theorem cell22_1666036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_1666036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666036 prefixEnd_1666036 := by exact prefixLift 1666036
  have htrace : WordTrace (prefixWord ++ tailWord_1666036) baseStart_1666036 baseEnd_1666036 := by
    simpa [prefixWord, tailWord_1666036, baseEnd_1666036] using wordTrace_append hprefix tailTrace_1666036
  have hstable : (prefixWord ++ tailWord_1666036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666036).length < 2 ^ (prefixWord ++ tailWord_1666036).sum := by decide
  have hdescent : baseEnd_1666036 < baseStart_1666036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666058 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_1666058 : Nat := 118140960795 + 1666058 * 2 ^ 59
def prefixEnd_1666058 : Nat := 4983230072969 + 3 ^ 40 * 1666058 * 2
def baseEnd_1666058 : Nat := 190108567170788394247321

theorem tailTrace_1666058 : CollatzResearch.WordTrace tailWord_1666058 prefixEnd_1666058 190108567170788394247321 := by
  unfold tailWord_1666058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15191531849540970224529707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40510751598775920598745885 15191531849540970224529707)
  ·
    refine ⟨22787297774311455336794561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15191531849540970224529707 22787297774311455336794561)
    ·
      refine ⟨17090473330733591502595921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22787297774311455336794561 17090473330733591502595921)
      ·
        refine ⟨12817854998050193626946941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17090473330733591502595921 12817854998050193626946941)
        ·
          refine ⟨4806695624268822610105103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12817854998050193626946941 4806695624268822610105103)
          ·
            refine ⟨7210043436403233915157655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806695624268822610105103 7210043436403233915157655)
            ·
              refine ⟨10815065154604850872736483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210043436403233915157655 10815065154604850872736483)
              ·
                refine ⟨16222597731907276309104725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10815065154604850872736483 16222597731907276309104725)
                ·
                  refine ⟨190108567170788394247321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16222597731907276309104725 190108567170788394247321)
                  ·
                    rfl

theorem cell22_1666058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_1666058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666058 prefixEnd_1666058 := by exact prefixLift 1666058
  have htrace : WordTrace (prefixWord ++ tailWord_1666058) baseStart_1666058 baseEnd_1666058 := by
    simpa [prefixWord, tailWord_1666058, baseEnd_1666058] using wordTrace_append hprefix tailTrace_1666058
  have hstable : (prefixWord ++ tailWord_1666058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666058).length < 2 ^ (prefixWord ++ tailWord_1666058).sum := by decide
  have hdescent : baseEnd_1666058 < baseStart_1666058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666073 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_1666073 : Nat := 118140960795 + 1666073 * 2 ^ 59
def prefixEnd_1666073 : Nat := 4983230072969 + 3 ^ 40 * 1666073 * 2
def baseEnd_1666073 : Nat := 570330836318910143616917

theorem tailTrace_1666073 : CollatzResearch.WordTrace tailWord_1666073 prefixEnd_1666073 570330836318910143616917 := by
  unfold tailWord_1666073
  simp only [CollatzResearch.WordTrace]
  refine ⟨60766674493109538459914873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40511116328739692306609915 60766674493109538459914873)
  ·
    refine ⟨45575005869832153844936155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60766674493109538459914873 45575005869832153844936155)
    ·
      refine ⟨68362508804748230767404233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45575005869832153844936155 68362508804748230767404233)
      ·
        refine ⟨51271881603561173075553175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68362508804748230767404233 51271881603561173075553175)
        ·
          refine ⟨76907822405341759613329763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51271881603561173075553175 76907822405341759613329763)
          ·
            refine ⟨115361733608012639419994645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76907822405341759613329763 115361733608012639419994645)
            ·
              refine ⟨5407581262875592472812249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115361733608012639419994645 5407581262875592472812249)
              ·
                refine ⟨4055685947156694354609187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407581262875592472812249 4055685947156694354609187)
                ·
                  refine ⟨6083528920735041531913781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055685947156694354609187 6083528920735041531913781)
                  ·
                    refine ⟨570330836318910143616917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6083528920735041531913781 570330836318910143616917)
                    ·
                      rfl

theorem cell22_1666073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_1666073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666073 prefixEnd_1666073 := by exact prefixLift 1666073
  have htrace : WordTrace (prefixWord ++ tailWord_1666073) baseStart_1666073 baseEnd_1666073 := by
    simpa [prefixWord, tailWord_1666073, baseEnd_1666073] using wordTrace_append hprefix tailTrace_1666073
  have hstable : (prefixWord ++ tailWord_1666073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666073).length < 2 ^ (prefixWord ++ tailWord_1666073).sum := by decide
  have hdescent : baseEnd_1666073 < baseStart_1666073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666077 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1666077 : Nat := 118140960795 + 1666077 * 2 ^ 59
def prefixEnd_1666077 : Nat := 4983230072969 + 3 ^ 40 * 1666077 * 2
def baseEnd_1666077 : Nat := 570332205600655466516905

theorem tailTrace_1666077 : CollatzResearch.WordTrace tailWord_1666077 prefixEnd_1666077 570332205600655466516905 := by
  unfold tailWord_1666077
  simp only [CollatzResearch.WordTrace]
  refine ⟨60766820385095047143060485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40511213590063364762040323 60766820385095047143060485)
  ·
    refine ⟨11393778822205321339323841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60766820385095047143060485 11393778822205321339323841)
    ·
      refine ⟨8545334116653991004492881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11393778822205321339323841 8545334116653991004492881)
      ·
        refine ⟨6409000587490493253369661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8545334116653991004492881 6409000587490493253369661)
        ·
          refine ⟨2403375220308934970013623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6409000587490493253369661 2403375220308934970013623)
          ·
            refine ⟨3605062830463402455020435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403375220308934970013623 3605062830463402455020435)
            ·
              refine ⟨5407594245695103682530653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605062830463402455020435 5407594245695103682530653)
              ·
                refine ⟨2027847842135663880948995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5407594245695103682530653 2027847842135663880948995)
                ·
                  refine ⟨3041771763203495821423493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027847842135663880948995 3041771763203495821423493)
                  ·
                    refine ⟨570332205600655466516905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3041771763203495821423493 570332205600655466516905)
                    ·
                      rfl

theorem cell22_1666077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1666077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666077 prefixEnd_1666077 := by exact prefixLift 1666077
  have htrace : WordTrace (prefixWord ++ tailWord_1666077) baseStart_1666077 baseEnd_1666077 := by
    simpa [prefixWord, tailWord_1666077, baseEnd_1666077] using wordTrace_append hprefix tailTrace_1666077
  have hstable : (prefixWord ++ tailWord_1666077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666077).length < 2 ^ (prefixWord ++ tailWord_1666077).sum := by decide
  have hdescent : baseEnd_1666077 < baseStart_1666077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666195 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 1, 4]
def baseStart_1666195 : Nat := 118140960795 + 1666195 * 2 ^ 59
def prefixEnd_1666195 : Nat := 4983230072969 + 3 ^ 40 * 1666195 * 2
def baseEnd_1666195 : Nat := 570372599412142492066543

theorem tailTrace_1666195 : CollatzResearch.WordTrace tailWord_1666195 prefixEnd_1666195 570372599412142492066543 := by
  unfold tailWord_1666195
  simp only [CollatzResearch.WordTrace]
  refine ⟨60771124198667553295856039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40514082799111702197237359 60771124198667553295856039)
  ·
    refine ⟨91156686298001329943784059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60771124198667553295856039 91156686298001329943784059)
    ·
      refine ⟨136735029447001994915676089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91156686298001329943784059 136735029447001994915676089)
      ·
        refine ⟨102551272085251496186757067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136735029447001994915676089 102551272085251496186757067)
        ·
          refine ⟨153826908127877244280135601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102551272085251496186757067 153826908127877244280135601)
          ·
            refine ⟨115370181095907933210101701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153826908127877244280135601 115370181095907933210101701)
            ·
              refine ⟨21631908955482737476894069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115370181095907933210101701 21631908955482737476894069)
              ·
                refine ⟨2027991464576506638458819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21631908955482737476894069 2027991464576506638458819)
                ·
                  refine ⟨3041987196864759957688229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027991464576506638458819 3041987196864759957688229)
                  ·
                    refine ⟨570372599412142492066543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3041987196864759957688229 570372599412142492066543)
                    ·
                      rfl

theorem cell22_1666195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4].length) (baseStart_1666195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666195 prefixEnd_1666195 := by exact prefixLift 1666195
  have htrace : WordTrace (prefixWord ++ tailWord_1666195) baseStart_1666195 baseEnd_1666195 := by
    simpa [prefixWord, tailWord_1666195, baseEnd_1666195] using wordTrace_append hprefix tailTrace_1666195
  have hstable : (prefixWord ++ tailWord_1666195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666195).length < 2 ^ (prefixWord ++ tailWord_1666195).sum := by decide
  have hdescent : baseEnd_1666195 < baseStart_1666195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666321 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 1, 3]
def baseStart_1666321 : Nat := 118140960795 + 1666321 * 2 ^ 59
def prefixEnd_1666321 : Nat := 4983230072969 + 3 ^ 40 * 1666321 * 2
def baseEnd_1666321 : Nat := 570415731787120163416157

theorem tailTrace_1666321 : CollatzResearch.WordTrace tailWord_1666321 prefixEnd_1666321 570415731787120163416157 := by
  unfold tailWord_1666321
  simp only [CollatzResearch.WordTrace]
  refine ⟨60775719796211076814942817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40517146530807384543295211 60775719796211076814942817)
  ·
    refine ⟨45581789847158307611207113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60775719796211076814942817 45581789847158307611207113)
    ·
      refine ⟨34186342385368730708405335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45581789847158307611207113 34186342385368730708405335)
      ·
        refine ⟨51279513578053096062608003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34186342385368730708405335 51279513578053096062608003)
        ·
          refine ⟨76919270367079644093912005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51279513578053096062608003 76919270367079644093912005)
          ·
            refine ⟨14422363193827433267608501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76919270367079644093912005 14422363193827433267608501)
            ·
              refine ⟨1352096549421321868838297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14422363193827433267608501 1352096549421321868838297)
              ·
                refine ⟨1014072412065991401628723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352096549421321868838297 1014072412065991401628723)
                ·
                  refine ⟨1521108618098987102443085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014072412065991401628723 1521108618098987102443085)
                  ·
                    refine ⟨570415731787120163416157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521108618098987102443085 570415731787120163416157)
                    ·
                      rfl

theorem cell22_1666321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_1666321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666321 prefixEnd_1666321 := by exact prefixLift 1666321
  have htrace : WordTrace (prefixWord ++ tailWord_1666321) baseStart_1666321 baseEnd_1666321 := by
    simpa [prefixWord, tailWord_1666321, baseEnd_1666321] using wordTrace_append hprefix tailTrace_1666321
  have hstable : (prefixWord ++ tailWord_1666321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666321).length < 2 ^ (prefixWord ++ tailWord_1666321).sum := by decide
  have hdescent : baseEnd_1666321 < baseStart_1666321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666377 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_1666377 : Nat := 118140960795 + 1666377 * 2 ^ 59
def prefixEnd_1666377 : Nat := 4983230072969 + 3 ^ 40 * 1666377 * 2
def baseEnd_1666377 : Nat := 570434901731554684015985

theorem tailTrace_1666377 : CollatzResearch.WordTrace tailWord_1666377 prefixEnd_1666377 570434901731554684015985 := by
  unfold tailWord_1666377
  simp only [CollatzResearch.WordTrace]
  refine ⟨60777762284008198378981385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40518508189338798919320923 60777762284008198378981385)
  ·
    refine ⟨45583321713006148784236039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60777762284008198378981385 45583321713006148784236039)
    ·
      refine ⟨68374982569509223176354059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45583321713006148784236039 68374982569509223176354059)
      ·
        refine ⟨102562473854263834764531089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68374982569509223176354059 102562473854263834764531089)
        ·
          refine ⟨76921855390697876073398317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102562473854263834764531089 76921855390697876073398317)
          ·
            refine ⟨28845695771511703527524369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76921855390697876073398317 28845695771511703527524369)
            ·
              refine ⟨21634271828633777645643277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28845695771511703527524369 21634271828633777645643277)
              ·
                refine ⟨8112851935737666617116229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21634271828633777645643277 8112851935737666617116229)
                ·
                  refine ⟨1521159737950812490709293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8112851935737666617116229 1521159737950812490709293)
                  ·
                    refine ⟨570434901731554684015985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521159737950812490709293 570434901731554684015985)
                    ·
                      rfl

theorem cell22_1666377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_1666377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666377 prefixEnd_1666377 := by exact prefixLift 1666377
  have htrace : WordTrace (prefixWord ++ tailWord_1666377) baseStart_1666377 baseEnd_1666377 := by
    simpa [prefixWord, tailWord_1666377, baseEnd_1666377] using wordTrace_append hprefix tailTrace_1666377
  have hstable : (prefixWord ++ tailWord_1666377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666377).length < 2 ^ (prefixWord ++ tailWord_1666377).sum := by decide
  have hdescent : baseEnd_1666377 < baseStart_1666377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666394 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_1666394 : Nat := 118140960795 + 1666394 * 2 ^ 59
def prefixEnd_1666394 : Nat := 4983230072969 + 3 ^ 40 * 1666394 * 2
def baseEnd_1666394 : Nat := 570440721178972306340933

theorem tailTrace_1666394 : CollatzResearch.WordTrace tailWord_1666394 prefixEnd_1666394 570440721178972306340933 := by
  unfold tailWord_1666394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194595581236652570587559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40518921549964406854900157 15194595581236652570587559)
  ·
    refine ⟨22791893371854978855881339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15194595581236652570587559 22791893371854978855881339)
    ·
      refine ⟨34187840057782468283822009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22791893371854978855881339 34187840057782468283822009)
      ·
        refine ⟨25640880043336851212866507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34187840057782468283822009 25640880043336851212866507)
        ·
          refine ⟨38461320065005276819299761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25640880043336851212866507 38461320065005276819299761)
          ·
            refine ⟨28845990048753957614474821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38461320065005276819299761 28845990048753957614474821)
            ·
              refine ⟨5408623134141367052714029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28845990048753957614474821 5408623134141367052714029)
              ·
                refine ⟨2028233675303012644767761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5408623134141367052714029 2028233675303012644767761)
                ·
                  refine ⟨1521175256477259483575821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028233675303012644767761 1521175256477259483575821)
                  ·
                    refine ⟨570440721178972306340933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521175256477259483575821 570440721178972306340933)
                    ·
                      rfl

theorem cell22_1666394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_1666394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666394 prefixEnd_1666394 := by exact prefixLift 1666394
  have htrace : WordTrace (prefixWord ++ tailWord_1666394) baseStart_1666394 baseEnd_1666394 := by
    simpa [prefixWord, tailWord_1666394, baseEnd_1666394] using wordTrace_append hprefix tailTrace_1666394
  have hstable : (prefixWord ++ tailWord_1666394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666394).length < 2 ^ (prefixWord ++ tailWord_1666394).sum := by decide
  have hdescent : baseEnd_1666394 < baseStart_1666394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666439 : List Nat := [1, 1, 4, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1666439 : Nat := 118140960795 + 1666439 * 2 ^ 59
def prefixEnd_1666439 : Nat := 4983230072969 + 3 ^ 40 * 1666439 * 2
def baseEnd_1666439 : Nat := 570456125598607188965795

theorem tailTrace_1666439 : CollatzResearch.WordTrace tailWord_1666439 prefixEnd_1666439 570456125598607188965795 := by
  unfold tailWord_1666439
  simp only [CollatzResearch.WordTrace]
  refine ⟨60780023609783582967738371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40520015739855721978492247 60780023609783582967738371)
  ·
    refine ⟨91170035414675374451607557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60780023609783582967738371 91170035414675374451607557)
    ·
      refine ⟨17094381640251632709676417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91170035414675374451607557 17094381640251632709676417)
      ·
        refine ⟨12820786230188724532257313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17094381640251632709676417 12820786230188724532257313)
        ·
          refine ⟨9615589672641543399192985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12820786230188724532257313 9615589672641543399192985)
          ·
            refine ⟨7211692254481157549394739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9615589672641543399192985 7211692254481157549394739)
            ·
              refine ⟨10817538381721736324092109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211692254481157549394739 10817538381721736324092109)
              ·
                refine ⟨4056576893145651121534541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10817538381721736324092109 4056576893145651121534541)
                ·
                  refine ⟨1521216334929619170575453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4056576893145651121534541 1521216334929619170575453)
                  ·
                    refine ⟨570456125598607188965795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521216334929619170575453 570456125598607188965795)
                    ·
                      rfl

theorem cell22_1666439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1666439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666439 prefixEnd_1666439 := by exact prefixLift 1666439
  have htrace : WordTrace (prefixWord ++ tailWord_1666439) baseStart_1666439 baseEnd_1666439 := by
    simpa [prefixWord, tailWord_1666439, baseEnd_1666439] using wordTrace_append hprefix tailTrace_1666439
  have hstable : (prefixWord ++ tailWord_1666439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666439).length < 2 ^ (prefixWord ++ tailWord_1666439).sum := by decide
  have hdescent : baseEnd_1666439 < baseStart_1666439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666516 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1666516 : Nat := 118140960795 + 1666516 * 2 ^ 59
def prefixEnd_1666516 : Nat := 4983230072969 + 3 ^ 40 * 1666516 * 2
def baseEnd_1666516 : Nat := 570482484272204654790559

theorem tailTrace_1666516 : CollatzResearch.WordTrace tailWord_1666516 prefixEnd_1666516 570482484272204654790559 := by
  unfold tailWord_1666516
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391416015252312559145701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40521888020336416745527601 30391416015252312559145701)
  ·
    refine ⟨5698390502859808604839819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30391416015252312559145701 5698390502859808604839819)
    ·
      refine ⟨8547585754289712907259729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698390502859808604839819 8547585754289712907259729)
      ·
        refine ⟨6410689315717284680444797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8547585754289712907259729 6410689315717284680444797)
        ·
          refine ⟨2404008493393981755166799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6410689315717284680444797 2404008493393981755166799)
          ·
            refine ⟨3606012740090972632750199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404008493393981755166799 3606012740090972632750199)
            ·
              refine ⟨5409019110136458949125299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606012740090972632750199 5409019110136458949125299)
              ·
                refine ⟨8113528665204688423687949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409019110136458949125299 8113528665204688423687949)
                ·
                  refine ⟨3042573249451758158882981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8113528665204688423687949 3042573249451758158882981)
                  ·
                    refine ⟨570482484272204654790559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042573249451758158882981 570482484272204654790559)
                    ·
                      rfl

theorem cell22_1666516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1666516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666516 prefixEnd_1666516 := by exact prefixLift 1666516
  have htrace : WordTrace (prefixWord ++ tailWord_1666516) baseStart_1666516 baseEnd_1666516 := by
    simpa [prefixWord, tailWord_1666516, baseEnd_1666516] using wordTrace_append hprefix tailTrace_1666516
  have hstable : (prefixWord ++ tailWord_1666516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666516).length < 2 ^ (prefixWord ++ tailWord_1666516).sum := by decide
  have hdescent : baseEnd_1666516 < baseStart_1666516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666529 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1666529 : Nat := 118140960795 + 1666529 * 2 ^ 59
def prefixEnd_1666529 : Nat := 4983230072969 + 3 ^ 40 * 1666529 * 2
def baseEnd_1666529 : Nat := 570486934437876954215519

theorem tailTrace_1666529 : CollatzResearch.WordTrace tailWord_1666529 prefixEnd_1666529 570486934437876954215519 := by
  unfold tailWord_1666529
  simp only [CollatzResearch.WordTrace]
  refine ⟨60783306179457528338514641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40522204119638352225676427 60783306179457528338514641)
  ·
    refine ⟨45587479634593146253885981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60783306179457528338514641 45587479634593146253885981)
    ·
      refine ⟨17095304862972429845207243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45587479634593146253885981 17095304862972429845207243)
      ·
        refine ⟨25642957294458644767810865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17095304862972429845207243 25642957294458644767810865)
        ·
          refine ⟨19232217970843983575858149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25642957294458644767810865 19232217970843983575858149)
          ·
            refine ⟨3606040869533246920473403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19232217970843983575858149 3606040869533246920473403)
            ·
              refine ⟨5409061304299870380710105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606040869533246920473403 5409061304299870380710105)
              ·
                refine ⟨4056795978224902785532579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409061304299870380710105 4056795978224902785532579)
                ·
                  refine ⟨6085193967337354178298869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056795978224902785532579 6085193967337354178298869)
                  ·
                    refine ⟨570486934437876954215519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6085193967337354178298869 570486934437876954215519)
                    ·
                      rfl

theorem cell22_1666529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1666529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666529 prefixEnd_1666529 := by exact prefixLift 1666529
  have htrace : WordTrace (prefixWord ++ tailWord_1666529) baseStart_1666529 baseEnd_1666529 := by
    simpa [prefixWord, tailWord_1666529, baseEnd_1666529] using wordTrace_append hprefix tailTrace_1666529
  have hstable : (prefixWord ++ tailWord_1666529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666529).length < 2 ^ (prefixWord ++ tailWord_1666529).sum := by decide
  have hdescent : baseEnd_1666529 < baseStart_1666529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666533 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_1666533 : Nat := 118140960795 + 1666533 * 2 ^ 59
def prefixEnd_1666533 : Nat := 4983230072969 + 3 ^ 40 * 1666533 * 2
def baseEnd_1666533 : Nat := 570488303719622277115507

theorem tailTrace_1666533 : CollatzResearch.WordTrace tailWord_1666533 prefixEnd_1666533 570488303719622277115507 := by
  unfold tailWord_1666533
  simp only [CollatzResearch.WordTrace]
  refine ⟨60783452071443037021660253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40522301380962024681106835 60783452071443037021660253)
  ·
    refine ⟨22793794526791138883122595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60783452071443037021660253 22793794526791138883122595)
    ·
      refine ⟨34190691790186708324683893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22793794526791138883122595 34190691790186708324683893)
      ·
        refine ⟨3205377355330003905439115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34190691790186708324683893 3205377355330003905439115)
        ·
          refine ⟨4808066032995005858158673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205377355330003905439115 4808066032995005858158673)
          ·
            refine ⟨3606049524746254393619005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808066032995005858158673 3606049524746254393619005)
            ·
              refine ⟨1352268571779845397607127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3606049524746254393619005 1352268571779845397607127)
              ·
                refine ⟨2028402857669768096410691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352268571779845397607127 2028402857669768096410691)
                ·
                  refine ⟨3042604286504652144616037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028402857669768096410691 3042604286504652144616037)
                  ·
                    refine ⟨570488303719622277115507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042604286504652144616037 570488303719622277115507)
                    ·
                      rfl

theorem cell22_1666533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_1666533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666533 prefixEnd_1666533 := by exact prefixLift 1666533
  have htrace : WordTrace (prefixWord ++ tailWord_1666533) baseStart_1666533 baseEnd_1666533 := by
    simpa [prefixWord, tailWord_1666533, baseEnd_1666533] using wordTrace_append hprefix tailTrace_1666533
  have hstable : (prefixWord ++ tailWord_1666533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666533).length < 2 ^ (prefixWord ++ tailWord_1666533).sum := by decide
  have hdescent : baseEnd_1666533 < baseStart_1666533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666544 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_1666544 : Nat := 118140960795 + 1666544 * 2 ^ 59
def prefixEnd_1666544 : Nat := 4983230072969 + 3 ^ 40 * 1666544 * 2
def baseEnd_1666544 : Nat := 570492069244421915090473

theorem tailTrace_1666544 : CollatzResearch.WordTrace tailWord_1666544 prefixEnd_1666544 570492069244421915090473 := by
  unfold tailWord_1666544
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391926637201592950155343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40522568849602123933540457 30391926637201592950155343)
  ·
    refine ⟨45587889955802389425233015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30391926637201592950155343 45587889955802389425233015)
    ·
      refine ⟨68381834933703584137849523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45587889955802389425233015 68381834933703584137849523)
      ·
        refine ⟨102572752400555376206774285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68381834933703584137849523 102572752400555376206774285)
        ·
          refine ⟨38464782150208266077540357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102572752400555376206774285 38464782150208266077540357)
          ·
            refine ⟨7212146653164049889538817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38464782150208266077540357 7212146653164049889538817)
            ·
              refine ⟨5409109989873037417154113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7212146653164049889538817 5409109989873037417154113)
              ·
                refine ⟨4056832492404778062865585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409109989873037417154113 4056832492404778062865585)
                ·
                  refine ⟨3042624369303583547149189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056832492404778062865585 3042624369303583547149189)
                  ·
                    refine ⟨570492069244421915090473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042624369303583547149189 570492069244421915090473)
                    ·
                      rfl

theorem cell22_1666544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_1666544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666544 prefixEnd_1666544 := by exact prefixLift 1666544
  have htrace : WordTrace (prefixWord ++ tailWord_1666544) baseStart_1666544 baseEnd_1666544 := by
    simpa [prefixWord, tailWord_1666544, baseEnd_1666544] using wordTrace_append hprefix tailTrace_1666544
  have hstable : (prefixWord ++ tailWord_1666544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666544).length < 2 ^ (prefixWord ++ tailWord_1666544).sum := by decide
  have hdescent : baseEnd_1666544 < baseStart_1666544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666666 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_1666666 : Nat := 118140960795 + 1666666 * 2 ^ 59
def prefixEnd_1666666 : Nat := 4983230072969 + 3 ^ 40 * 1666666 * 2
def baseEnd_1666666 : Nat := 190177944112551421180033

theorem tailTrace_1666666 : CollatzResearch.WordTrace tailWord_1666666 prefixEnd_1666666 190177944112551421180033 := by
  unfold tailWord_1666666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197075744990300184062963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40525535319974133824167901 15197075744990300184062963)
  ·
    refine ⟨22795613617485450276094445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15197075744990300184062963 22795613617485450276094445)
    ·
      refine ⟨8548355106557043853535417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22795613617485450276094445 8548355106557043853535417)
      ·
        refine ⟨6411266329917782890151563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8548355106557043853535417 6411266329917782890151563)
        ·
          refine ⟨9616899494876674335227345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411266329917782890151563 9616899494876674335227345)
          ·
            refine ⟨7212674621157505751420509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9616899494876674335227345 7212674621157505751420509)
            ·
              refine ⟨2704752982934064656782691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7212674621157505751420509 2704752982934064656782691)
              ·
                refine ⟨4057129474401096985174037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704752982934064656782691 4057129474401096985174037)
                ·
                  refine ⟨190177944112551421180033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4057129474401096985174037 190177944112551421180033)
                  ·
                    rfl

theorem cell22_1666666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_1666666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666666 prefixEnd_1666666 := by exact prefixLift 1666666
  have htrace : WordTrace (prefixWord ++ tailWord_1666666) baseStart_1666666 baseEnd_1666666 := by
    simpa [prefixWord, tailWord_1666666, baseEnd_1666666] using wordTrace_append hprefix tailTrace_1666666
  have hstable : (prefixWord ++ tailWord_1666666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666666).length < 2 ^ (prefixWord ++ tailWord_1666666).sum := by decide
  have hdescent : baseEnd_1666666 < baseStart_1666666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666679 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1666679 : Nat := 118140960795 + 1666679 * 2 ^ 59
def prefixEnd_1666679 : Nat := 4983230072969 + 3 ^ 40 * 1666679 * 2
def baseEnd_1666679 : Nat := 570538282503326562965059

theorem tailTrace_1666679 : CollatzResearch.WordTrace tailWord_1666679 prefixEnd_1666679 570538282503326562965059 := by
  unfold tailWord_1666679
  simp only [CollatzResearch.WordTrace]
  refine ⟨60788777128914103956475091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40525851419276069304316727 60788777128914103956475091)
  ·
    refine ⟨91183165693371155934712637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60788777128914103956475091 91183165693371155934712637)
    ·
      refine ⟨34193687135014183475517239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91183165693371155934712637 34193687135014183475517239)
      ·
        refine ⟨51290530702521275213275859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34193687135014183475517239 51290530702521275213275859)
        ·
          refine ⟨76935796053781912819913789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51290530702521275213275859 76935796053781912819913789)
          ·
            refine ⟨28850923520168217307467671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76935796053781912819913789 28850923520168217307467671)
            ·
              refine ⟨43276385280252325961201507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28850923520168217307467671 43276385280252325961201507)
              ·
                refine ⟨64914577920378488941802261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43276385280252325961201507 64914577920378488941802261)
                ·
                  refine ⟨3042870840017741669146981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64914577920378488941802261 3042870840017741669146981)
                  ·
                    refine ⟨570538282503326562965059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3042870840017741669146981 570538282503326562965059)
                    ·
                      rfl

theorem cell22_1666679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1666679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666679 prefixEnd_1666679 := by exact prefixLift 1666679
  have htrace : WordTrace (prefixWord ++ tailWord_1666679) baseStart_1666679 baseEnd_1666679 := by
    simpa [prefixWord, tailWord_1666679, baseEnd_1666679] using wordTrace_append hprefix tailTrace_1666679
  have hstable : (prefixWord ++ tailWord_1666679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666679).length < 2 ^ (prefixWord ++ tailWord_1666679).sum := by decide
  have hdescent : baseEnd_1666679 < baseStart_1666679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666743 : List Nat := [1, 1, 3, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1666743 : Nat := 118140960795 + 1666743 * 2 ^ 59
def prefixEnd_1666743 : Nat := 4983230072969 + 3 ^ 40 * 1666743 * 2
def baseEnd_1666743 : Nat := 570560191011251729364863

theorem tailTrace_1666743 : CollatzResearch.WordTrace tailWord_1666743 prefixEnd_1666743 570560191011251729364863 := by
  unfold tailWord_1666743
  simp only [CollatzResearch.WordTrace]
  refine ⟨60791111400682242886804883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40527407600454828591203255 60791111400682242886804883)
  ·
    refine ⟨91186667101023364330207325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60791111400682242886804883 91186667101023364330207325)
    ·
      refine ⟨34195000162883761623827747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91186667101023364330207325 34195000162883761623827747)
      ·
        refine ⟨51292500244325642435741621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34195000162883761623827747 51292500244325642435741621)
        ·
          refine ⟨4808671897905528978350777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51292500244325642435741621 4808671897905528978350777)
          ·
            refine ⟨3606503923429146733763083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808671897905528978350777 3606503923429146733763083)
            ·
              refine ⟨5409755885143720100644625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606503923429146733763083 5409755885143720100644625)
              ·
                refine ⟨4057316913857790075483469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409755885143720100644625 4057316913857790075483469)
                ·
                  refine ⟨1521493842696671278306301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4057316913857790075483469 1521493842696671278306301)
                  ·
                    refine ⟨570560191011251729364863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521493842696671278306301 570560191011251729364863)
                    ·
                      rfl

theorem cell22_1666743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1666743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666743 prefixEnd_1666743 := by exact prefixLift 1666743
  have htrace : WordTrace (prefixWord ++ tailWord_1666743) baseStart_1666743 baseEnd_1666743 := by
    simpa [prefixWord, tailWord_1666743, baseEnd_1666743] using wordTrace_append hprefix tailTrace_1666743
  have hstable : (prefixWord ++ tailWord_1666743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666743).length < 2 ^ (prefixWord ++ tailWord_1666743).sum := by decide
  have hdescent : baseEnd_1666743 < baseStart_1666743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666756 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1666756 : Nat := 118140960795 + 1666756 * 2 ^ 59
def prefixEnd_1666756 : Nat := 4983230072969 + 3 ^ 40 * 1666756 * 2
def baseEnd_1666756 : Nat := 190188213725641342929941

theorem tailTrace_1666756 : CollatzResearch.WordTrace tailWord_1666756 prefixEnd_1666756 190188213725641342929941 := by
  unfold tailWord_1666756
  simp only [CollatzResearch.WordTrace]
  refine ⟨30395792774817573053514061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40527723699756764071352081 30395792774817573053514061)
  ·
    refine ⟨11398422290556589895067773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30395792774817573053514061 11398422290556589895067773)
    ·
      refine ⟨4274408358958721210650415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11398422290556589895067773 4274408358958721210650415)
      ·
        refine ⟨6411612538438081815975623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274408358958721210650415 6411612538438081815975623)
        ·
          refine ⟨9617418807657122723963435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411612538438081815975623 9617418807657122723963435)
          ·
            refine ⟨14426128211485684085945153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617418807657122723963435 14426128211485684085945153)
            ·
              refine ⟨10819596158614263064458865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14426128211485684085945153 10819596158614263064458865)
              ·
                refine ⟨8114697118960697298344149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10819596158614263064458865 8114697118960697298344149)
                ·
                  refine ⟨190188213725641342929941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8114697118960697298344149 190188213725641342929941)
                  ·
                    rfl

theorem cell22_1666756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1666756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666756 prefixEnd_1666756 := by exact prefixLift 1666756
  have htrace : WordTrace (prefixWord ++ tailWord_1666756) baseStart_1666756 baseEnd_1666756 := by
    simpa [prefixWord, tailWord_1666756, baseEnd_1666756] using wordTrace_append hprefix tailTrace_1666756
  have hstable : (prefixWord ++ tailWord_1666756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666756).length < 2 ^ (prefixWord ++ tailWord_1666756).sum := by decide
  have hdescent : baseEnd_1666756 < baseStart_1666756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666760 : List Nat := [2, 1, 3, 1, 2, 2, 4, 3, 1, 3]
def baseStart_1666760 : Nat := 118140960795 + 1666760 * 2 ^ 59
def prefixEnd_1666760 : Nat := 4983230072969 + 3 ^ 40 * 1666760 * 2
def baseEnd_1666760 : Nat := 570566010458669351689811

theorem tailTrace_1666760 : CollatzResearch.WordTrace tailWord_1666760 prefixEnd_1666760 570566010458669351689811 := by
  unfold tailWord_1666760
  simp only [CollatzResearch.WordTrace]
  refine ⟨30395865720810327395086867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40527820961080436526782489 30395865720810327395086867)
  ·
    refine ⟨45593798581215491092630301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30395865720810327395086867 45593798581215491092630301)
    ·
      refine ⟨17097674467955809159736363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45593798581215491092630301 17097674467955809159736363)
      ·
        refine ⟨25646511701933713739604545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17097674467955809159736363 25646511701933713739604545)
        ·
          refine ⟨19234883776450285304703409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25646511701933713739604545 19234883776450285304703409)
          ·
            refine ⟨14426162832337713978527557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19234883776450285304703409 14426162832337713978527557)
            ·
              refine ⟨2704905531063321370973917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14426162832337713978527557 2704905531063321370973917)
              ·
                refine ⟨1014339574148745514115219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2704905531063321370973917 1014339574148745514115219)
                ·
                  refine ⟨1521509361223118271172829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014339574148745514115219 1521509361223118271172829)
                  ·
                    refine ⟨570566010458669351689811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521509361223118271172829 570566010458669351689811)
                    ·
                      rfl

theorem cell22_1666760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_1666760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666760 prefixEnd_1666760 := by exact prefixLift 1666760
  have htrace : WordTrace (prefixWord ++ tailWord_1666760) baseStart_1666760 baseEnd_1666760 := by
    simpa [prefixWord, tailWord_1666760, baseEnd_1666760] using wordTrace_append hprefix tailTrace_1666760
  have hstable : (prefixWord ++ tailWord_1666760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666760).length < 2 ^ (prefixWord ++ tailWord_1666760).sum := by decide
  have hdescent : baseEnd_1666760 < baseStart_1666760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666801 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 6]
def baseStart_1666801 : Nat := 118140960795 + 1666801 * 2 ^ 59
def prefixEnd_1666801 : Nat := 4983230072969 + 3 ^ 40 * 1666801 * 2
def baseEnd_1666801 : Nat := 190193348532186303804895

theorem tailTrace_1666801 : CollatzResearch.WordTrace tailWord_1666801 prefixEnd_1666801 190193348532186303804895 := by
  unfold tailWord_1666801
  simp only [CollatzResearch.WordTrace]
  refine ⟨60793226834472118792416257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40528817889648079194944171 60793226834472118792416257)
  ·
    refine ⟨45594920125854089094312193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60793226834472118792416257 45594920125854089094312193)
    ·
      refine ⟨34196190094390566820734145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45594920125854089094312193 34196190094390566820734145)
      ·
        refine ⟨25647142570792925115550609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34196190094390566820734145 25647142570792925115550609)
        ·
          refine ⟨19235356928094693836662957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25647142570792925115550609 19235356928094693836662957)
          ·
            refine ⟨7213258848035510188748609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19235356928094693836662957 7213258848035510188748609)
            ·
              refine ⟨5409944136026632641561457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7213258848035510188748609 5409944136026632641561457)
              ·
                refine ⟨4057458102019974481171093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409944136026632641561457 4057458102019974481171093)
                ·
                  refine ⟨190193348532186303804895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4057458102019974481171093 190193348532186303804895)
                  ·
                    rfl

theorem cell22_1666801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_1666801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666801 prefixEnd_1666801 := by exact prefixLift 1666801
  have htrace : WordTrace (prefixWord ++ tailWord_1666801) baseStart_1666801 baseEnd_1666801 := by
    simpa [prefixWord, tailWord_1666801, baseEnd_1666801] using wordTrace_append hprefix tailTrace_1666801
  have hstable : (prefixWord ++ tailWord_1666801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666801).length < 2 ^ (prefixWord ++ tailWord_1666801).sum := by decide
  have hdescent : baseEnd_1666801 < baseStart_1666801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666833 : List Nat := [1, 2, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_1666833 : Nat := 118140960795 + 1666833 * 2 ^ 59
def prefixEnd_1666833 : Nat := 4983230072969 + 3 ^ 40 * 1666833 * 2
def baseEnd_1666833 : Nat := 570590999850521494614587

theorem tailTrace_1666833 : CollatzResearch.WordTrace tailWord_1666833 prefixEnd_1666833 570590999850521494614587 := by
  unfold tailWord_1666833
  simp only [CollatzResearch.WordTrace]
  refine ⟨60794393970356188257581153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40529595980237458838387435 60794393970356188257581153)
  ·
    refine ⟨45595795477767141193185865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60794393970356188257581153 45595795477767141193185865)
    ·
      refine ⟨34196846608325355894889399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45595795477767141193185865 34196846608325355894889399)
      ·
        refine ⟨51295269912488033842334099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34196846608325355894889399 51295269912488033842334099)
        ·
          refine ⟨76942904868732050763501149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51295269912488033842334099 76942904868732050763501149)
          ·
            refine ⟨28853589325774519036312931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76942904868732050763501149 28853589325774519036312931)
            ·
              refine ⟨43280383988661778554469397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28853589325774519036312931 43280383988661778554469397)
              ·
                refine ⟨2028767999468520869740753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43280383988661778554469397 2028767999468520869740753)
                ·
                  refine ⟨1521575999601390652305565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028767999468520869740753 1521575999601390652305565)
                  ·
                    refine ⟨570590999850521494614587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521575999601390652305565 570590999850521494614587)
                    ·
                      rfl

theorem cell22_1666833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_1666833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666833 prefixEnd_1666833 := by exact prefixLift 1666833
  have htrace : WordTrace (prefixWord ++ tailWord_1666833) baseStart_1666833 baseEnd_1666833 := by
    simpa [prefixWord, tailWord_1666833, baseEnd_1666833] using wordTrace_append hprefix tailTrace_1666833
  have hstable : (prefixWord ++ tailWord_1666833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666833).length < 2 ^ (prefixWord ++ tailWord_1666833).sum := by decide
  have hdescent : baseEnd_1666833 < baseStart_1666833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666850 : List Nat := [3, 3, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1666850 : Nat := 118140960795 + 1666850 * 2 ^ 59
def prefixEnd_1666850 : Nat := 4983230072969 + 3 ^ 40 * 1666850 * 2
def baseEnd_1666850 : Nat := 570596819297939116939535

theorem tailTrace_1666850 : CollatzResearch.WordTrace tailWord_1666850 prefixEnd_1666850 570596819297939116939535 := by
  unfold tailWord_1666850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198753502823650040237501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40530009340863066773966669 15198753502823650040237501)
  ·
    refine ⟨5699532563558868765089063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15198753502823650040237501 5699532563558868765089063)
    ·
      refine ⟨8549298845338303147633595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699532563558868765089063 8549298845338303147633595)
      ·
        refine ⟨12823948268007454721450393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549298845338303147633595 12823948268007454721450393)
        ·
          refine ⟨9617961201005591041087795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12823948268007454721450393 9617961201005591041087795)
          ·
            refine ⟨14426941801508386561631693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617961201005591041087795 14426941801508386561631693)
            ·
              refine ⟨5410103175565644960611885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14426941801508386561631693 5410103175565644960611885)
              ·
                refine ⟨2028788690837116860229457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5410103175565644960611885 2028788690837116860229457)
                ·
                  refine ⟨1521591518127837645172093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028788690837116860229457 1521591518127837645172093)
                  ·
                    refine ⟨570596819297939116939535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521591518127837645172093 570596819297939116939535)
                    ·
                      rfl

theorem cell22_1666850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1666850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666850 prefixEnd_1666850 := by exact prefixLift 1666850
  have htrace : WordTrace (prefixWord ++ tailWord_1666850) baseStart_1666850 baseEnd_1666850 := by
    simpa [prefixWord, tailWord_1666850, baseEnd_1666850] using wordTrace_append hprefix tailTrace_1666850
  have hstable : (prefixWord ++ tailWord_1666850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666850).length < 2 ^ (prefixWord ++ tailWord_1666850).sum := by decide
  have hdescent : baseEnd_1666850 < baseStart_1666850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666886 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_1666886 : Nat := 118140960795 + 1666886 * 2 ^ 59
def prefixEnd_1666886 : Nat := 4983230072969 + 3 ^ 40 * 1666886 * 2
def baseEnd_1666886 : Nat := 190203047611215674346475

theorem tailTrace_1666886 : CollatzResearch.WordTrace tailWord_1666886 prefixEnd_1666886 190203047611215674346475 := by
  unfold tailWord_1666886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899885219973880572164391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40530884692776118872840341 1899885219973880572164391)
  ·
    refine ⟨2849827829960820858246587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1899885219973880572164391 2849827829960820858246587)
    ·
      refine ⟨4274741744941231287369881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849827829960820858246587 4274741744941231287369881)
      ·
        refine ⟨3206056308705923465527411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4274741744941231287369881 3206056308705923465527411)
        ·
          refine ⟨4809084463058885198291117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206056308705923465527411 4809084463058885198291117)
          ·
            refine ⟨1803406673647081949359169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4809084463058885198291117 1803406673647081949359169)
            ·
              refine ⟨1352555005235311462019377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803406673647081949359169 1352555005235311462019377)
              ·
                refine ⟨1014416253926483596514533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352555005235311462019377 1014416253926483596514533)
                ·
                  refine ⟨190203047611215674346475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014416253926483596514533 190203047611215674346475)
                  ·
                    rfl

theorem cell22_1666886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_1666886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666886 prefixEnd_1666886 := by exact prefixLift 1666886
  have htrace : WordTrace (prefixWord ++ tailWord_1666886) baseStart_1666886 baseEnd_1666886 := by
    simpa [prefixWord, tailWord_1666886, baseEnd_1666886] using wordTrace_append hprefix tailTrace_1666886
  have hstable : (prefixWord ++ tailWord_1666886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666886).length < 2 ^ (prefixWord ++ tailWord_1666886).sum := by decide
  have hdescent : baseEnd_1666886 < baseStart_1666886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666942 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1666942 : Nat := 118140960795 + 1666942 * 2 ^ 59
def prefixEnd_1666942 : Nat := 4983230072969 + 3 ^ 40 * 1666942 * 2
def baseEnd_1666942 : Nat := 190209437592693847879751

theorem tailTrace_1666942 : CollatzResearch.WordTrace tailWord_1666942 prefixEnd_1666942 190209437592693847879751 := by
  unfold tailWord_1666942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599796190870162484162385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40532246351307533248866053 7599796190870162484162385)
  ·
    refine ⟨5699847143152621863121789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7599796190870162484162385 5699847143152621863121789)
    ·
      refine ⟨2137442678682233198670671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5699847143152621863121789 2137442678682233198670671)
      ·
        refine ⟨3206164018023349798006007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137442678682233198670671 3206164018023349798006007)
        ·
          refine ⟨4809246027035024697009011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206164018023349798006007 4809246027035024697009011)
          ·
            refine ⟨7213869040552537045513517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809246027035024697009011 7213869040552537045513517)
            ·
              refine ⟨2705200890207201392067569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7213869040552537045513517 2705200890207201392067569)
              ·
                refine ⟨2028900667655401044050677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705200890207201392067569 2028900667655401044050677)
                ·
                  refine ⟨190209437592693847879751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2028900667655401044050677 190209437592693847879751)
                  ·
                    rfl

theorem cell22_1666942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1666942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666942 prefixEnd_1666942 := by exact prefixLift 1666942
  have htrace : WordTrace (prefixWord ++ tailWord_1666942) baseStart_1666942 baseEnd_1666942 := by
    simpa [prefixWord, tailWord_1666942, baseEnd_1666942] using wordTrace_append hprefix tailTrace_1666942
  have hstable : (prefixWord ++ tailWord_1666942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666942).length < 2 ^ (prefixWord ++ tailWord_1666942).sum := by decide
  have hdescent : baseEnd_1666942 < baseStart_1666942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666953 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 6]
def baseStart_1666953 : Nat := 118140960795 + 1666953 * 2 ^ 59
def prefixEnd_1666953 : Nat := 4983230072969 + 3 ^ 40 * 1666953 * 2
def baseEnd_1666953 : Nat := 190210692767627060538073

theorem tailTrace_1666953 : CollatzResearch.WordTrace tailWord_1666953 prefixEnd_1666953 190210692767627060538073 := by
  unfold tailWord_1666953
  simp only [CollatzResearch.WordTrace]
  refine ⟨60798770729921448751949513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40532513819947632501299675 60798770729921448751949513)
  ·
    refine ⟨45599078047441086563962135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60798770729921448751949513 45599078047441086563962135)
    ·
      refine ⟨68398617071161629845943203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45599078047441086563962135 68398617071161629845943203)
      ·
        refine ⟨102597925606742444768914805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68398617071161629845943203 102597925606742444768914805)
        ·
          refine ⟨9618555525632104197085763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102597925606742444768914805 9618555525632104197085763)
          ·
            refine ⟨14427833288448156295628645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618555525632104197085763 14427833288448156295628645)
            ·
              refine ⟨2705218741584029305430371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14427833288448156295628645 2705218741584029305430371)
              ·
                refine ⟨4057828112376043958145557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705218741584029305430371 4057828112376043958145557)
                ·
                  refine ⟨190210692767627060538073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4057828112376043958145557 190210692767627060538073)
                  ·
                    rfl

theorem cell22_1666953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_1666953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666953 prefixEnd_1666953 := by exact prefixLift 1666953
  have htrace : WordTrace (prefixWord ++ tailWord_1666953) baseStart_1666953 baseEnd_1666953 := by
    simpa [prefixWord, tailWord_1666953, baseEnd_1666953] using wordTrace_append hprefix tailTrace_1666953
  have hstable : (prefixWord ++ tailWord_1666953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666953).length < 2 ^ (prefixWord ++ tailWord_1666953).sum := by decide
  have hdescent : baseEnd_1666953 < baseStart_1666953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666972 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1666972 : Nat := 118140960795 + 1666972 * 2 ^ 59
def prefixEnd_1666972 : Nat := 4983230072969 + 3 ^ 40 * 1666972 * 2
def baseEnd_1666972 : Nat := 570638582391171465389161

theorem tailTrace_1666972 : CollatzResearch.WordTrace tailWord_1666972 prefixEnd_1666972 570638582391171465389161 := by
  unfold tailWord_1666972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30399731858426307498445585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40532975811235076664594113 30399731858426307498445585)
  ·
    refine ⟨22799798893819730623834189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30399731858426307498445585 22799798893819730623834189)
    ·
      refine ⟨8549924585182398983937821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22799798893819730623834189 8549924585182398983937821)
      ·
        refine ⟨3206221719443399618976683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8549924585182398983937821 3206221719443399618976683)
        ·
          refine ⟨4809332579165099428465025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206221719443399618976683 4809332579165099428465025)
          ·
            refine ⟨3606999434373824571348769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809332579165099428465025 3606999434373824571348769)
            ·
              refine ⟨2705249575780368428511577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606999434373824571348769 2705249575780368428511577)
              ·
                refine ⟨2028937181835276321383683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705249575780368428511577 2028937181835276321383683)
                ·
                  refine ⟨3043405772752914482075525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028937181835276321383683 3043405772752914482075525)
                  ·
                    refine ⟨570638582391171465389161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3043405772752914482075525 570638582391171465389161)
                    ·
                      rfl

theorem cell22_1666972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1666972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1666972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1666972 prefixEnd_1666972 := by exact prefixLift 1666972
  have htrace : WordTrace (prefixWord ++ tailWord_1666972) baseStart_1666972 baseEnd_1666972 := by
    simpa [prefixWord, tailWord_1666972, baseEnd_1666972] using wordTrace_append hprefix tailTrace_1666972
  have hstable : (prefixWord ++ tailWord_1666972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666972).length < 2 ^ (prefixWord ++ tailWord_1666972).sum := by decide
  have hdescent : baseEnd_1666972 < baseStart_1666972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667004 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_1667004 : Nat := 118140960795 + 1667004 * 2 ^ 59
def prefixEnd_1667004 : Nat := 4983230072969 + 3 ^ 40 * 1667004 * 2
def baseEnd_1667004 : Nat := 190216512215044682863021

theorem tailTrace_1667004 : CollatzResearch.WordTrace tailWord_1667004 prefixEnd_1667004 190216512215044682863021 := by
  unfold tailWord_1667004
  simp only [CollatzResearch.WordTrace]
  refine ⟨30400315426368342231028033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40533753901824456308037377 30400315426368342231028033)
  ·
    refine ⟨22800236569776256673271025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30400315426368342231028033 22800236569776256673271025)
    ·
      refine ⟨17100177427332192504953269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22800236569776256673271025 17100177427332192504953269)
      ·
        refine ⟨1603141633812393047339369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17100177427332192504953269 1603141633812393047339369)
        ·
          refine ⟨1202356225359294785504527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603141633812393047339369 1202356225359294785504527)
          ·
            refine ⟨1803534338038942178256791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202356225359294785504527 1803534338038942178256791)
            ·
              refine ⟨2705301507058413267385187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803534338038942178256791 2705301507058413267385187)
              ·
                refine ⟨4057952260587619901077781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705301507058413267385187 4057952260587619901077781)
                ·
                  refine ⟨190216512215044682863021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4057952260587619901077781 190216512215044682863021)
                  ·
                    rfl

theorem cell22_1667004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_1667004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667004 prefixEnd_1667004 := by exact prefixLift 1667004
  have htrace : WordTrace (prefixWord ++ tailWord_1667004) baseStart_1667004 baseEnd_1667004 := by
    simpa [prefixWord, tailWord_1667004, baseEnd_1667004] using wordTrace_append hprefix tailTrace_1667004
  have hstable : (prefixWord ++ tailWord_1667004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667004).length < 2 ^ (prefixWord ++ tailWord_1667004).sum := by decide
  have hdescent : baseEnd_1667004 < baseStart_1667004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667064 : List Nat := [2, 1, 2, 1, 1, 3, 6, 2, 1, 3]
def baseStart_1667064 : Nat := 118140960795 + 1667064 * 2 ^ 59
def prefixEnd_1667064 : Nat := 4983230072969 + 3 ^ 40 * 1667064 * 2
def baseEnd_1667064 : Nat := 570670075871313892088879

theorem tailTrace_1667064 : CollatzResearch.WordTrace tailWord_1667064 prefixEnd_1667064 570670075871313892088879 := by
  unfold tailWord_1667064
  simp only [CollatzResearch.WordTrace]
  refine ⟨30401409616259657354620123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40535212821679543139493497 30401409616259657354620123)
  ·
    refine ⟨45602114424389486031930185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30401409616259657354620123 45602114424389486031930185)
    ·
      refine ⟨34201585818292114523947639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45602114424389486031930185 34201585818292114523947639)
      ·
        refine ⟨51302378727438171785921459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34201585818292114523947639 51302378727438171785921459)
        ·
          refine ⟨76953568091157257678882189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51302378727438171785921459 76953568091157257678882189)
          ·
            refine ⟨28857588034183971629580821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76953568091157257678882189 28857588034183971629580821)
            ·
              refine ⟨1352699439102373670136601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28857588034183971629580821 1352699439102373670136601)
              ·
                refine ⟨1014524579326780252602451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352699439102373670136601 1014524579326780252602451)
                ·
                  refine ⟨1521786868990170378903677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014524579326780252602451 1521786868990170378903677)
                  ·
                    refine ⟨570670075871313892088879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521786868990170378903677 570670075871313892088879)
                    ·
                      rfl

theorem cell22_1667064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_1667064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667064 prefixEnd_1667064 := by exact prefixLift 1667064
  have htrace : WordTrace (prefixWord ++ tailWord_1667064) baseStart_1667064 baseEnd_1667064 := by
    simpa [prefixWord, tailWord_1667064, baseEnd_1667064] using wordTrace_append hprefix tailTrace_1667064
  have hstable : (prefixWord ++ tailWord_1667064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667064).length < 2 ^ (prefixWord ++ tailWord_1667064).sum := by decide
  have hdescent : baseEnd_1667064 < baseStart_1667064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_1667088 : Nat := 118140960795 + 1667088 * 2 ^ 59
def prefixEnd_1667088 : Nat := 4983230072969 + 3 ^ 40 * 1667088 * 2
def baseEnd_1667088 : Nat := 190226097187261943162935

theorem tailTrace_1667088 : CollatzResearch.WordTrace tailWord_1667088 prefixEnd_1667088 190226097187261943162935 := by
  unfold tailWord_1667088
  simp only [CollatzResearch.WordTrace]
  refine ⟨30401847292216183404056959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40535796389621577872075945 30401847292216183404056959)
  ·
    refine ⟨45602770938324275106085439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30401847292216183404056959 45602770938324275106085439)
    ·
      refine ⟨68404156407486412659128159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45602770938324275106085439 68404156407486412659128159)
      ·
        refine ⟨102606234611229618988692239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68404156407486412659128159 102606234611229618988692239)
        ·
          refine ⟨153909351916844428483038359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102606234611229618988692239 153909351916844428483038359)
          ·
            refine ⟨230864027875266642724557539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153909351916844428483038359 230864027875266642724557539)
            ·
              refine ⟨346296041812899964086836309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230864027875266642724557539 346296041812899964086836309)
              ·
                refine ⟨4058156739994921454142613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 346296041812899964086836309 4058156739994921454142613)
                ·
                  refine ⟨190226097187261943162935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4058156739994921454142613 190226097187261943162935)
                  ·
                    rfl

theorem cell22_1667088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_1667088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667088 prefixEnd_1667088 := by exact prefixLift 1667088
  have htrace : WordTrace (prefixWord ++ tailWord_1667088) baseStart_1667088 baseEnd_1667088 := by
    simpa [prefixWord, tailWord_1667088, baseEnd_1667088] using wordTrace_append hprefix tailTrace_1667088
  have hstable : (prefixWord ++ tailWord_1667088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667088).length < 2 ^ (prefixWord ++ tailWord_1667088).sum := by decide
  have hdescent : baseEnd_1667088 < baseStart_1667088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667111 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 5]
def baseStart_1667111 : Nat := 118140960795 + 1667111 * 2 ^ 59
def prefixEnd_1667111 : Nat := 4983230072969 + 3 ^ 40 * 1667111 * 2
def baseEnd_1667111 : Nat := 190228721643940478721245

theorem tailTrace_1667111 : CollatzResearch.WordTrace tailWord_1667111 prefixEnd_1667111 190228721643940478721245 := by
  unfold tailWord_1667111
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804533463349041736201187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40536355642232694490800791 60804533463349041736201187)
  ·
    refine ⟨91206800195023562604301781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60804533463349041736201187 91206800195023562604301781)
    ·
      refine ⟨2137659379570864748538323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91206800195023562604301781 2137659379570864748538323)
      ·
        refine ⟨3206489069356297122807485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137659379570864748538323 3206489069356297122807485)
        ·
          refine ⟨1202433401008611421052807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3206489069356297122807485 1202433401008611421052807)
          ·
            refine ⟨1803650101512917131579211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202433401008611421052807 1803650101512917131579211)
            ·
              refine ⟨2705475152269375697368817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803650101512917131579211 2705475152269375697368817)
              ·
                refine ⟨2029106364202031773026613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705475152269375697368817 2029106364202031773026613)
                ·
                  refine ⟨190228721643940478721245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029106364202031773026613 190228721643940478721245)
                  ·
                    rfl

theorem cell22_1667111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 5].length) (baseStart_1667111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667111 prefixEnd_1667111 := by exact prefixLift 1667111
  have htrace : WordTrace (prefixWord ++ tailWord_1667111) baseStart_1667111 baseEnd_1667111 := by
    simpa [prefixWord, tailWord_1667111, baseEnd_1667111] using wordTrace_append hprefix tailTrace_1667111
  have hstable : (prefixWord ++ tailWord_1667111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667111).length < 2 ^ (prefixWord ++ tailWord_1667111).sum := by decide
  have hdescent : baseEnd_1667111 < baseStart_1667111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667122 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1667122 : Nat := 118140960795 + 1667122 * 2 ^ 59
def prefixEnd_1667122 : Nat := 4983230072969 + 3 ^ 40 * 1667122 * 2
def baseEnd_1667122 : Nat := 190229976818873691379567

theorem tailTrace_1667122 : CollatzResearch.WordTrace tailWord_1667122 prefixEnd_1667122 190229976818873691379567 := by
  unfold tailWord_1667122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201233666577297653712905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40536623110872793743234413 15201233666577297653712905)
  ·
    refine ⟨11400925249932973240284679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15201233666577297653712905 11400925249932973240284679)
    ·
      refine ⟨17101387874899459860427019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11400925249932973240284679 17101387874899459860427019)
      ·
        refine ⟨25652081812349189790640529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17101387874899459860427019 25652081812349189790640529)
        ·
          refine ⟨19239061359261892342980397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25652081812349189790640529 19239061359261892342980397)
          ·
            refine ⟨7214648009723209628617649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19239061359261892342980397 7214648009723209628617649)
            ·
              refine ⟨5410986007292407221463237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7214648009723209628617649 5410986007292407221463237)
              ·
                refine ⟨1014559876367326354024357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5410986007292407221463237 1014559876367326354024357)
                ·
                  refine ⟨190229976818873691379567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014559876367326354024357 190229976818873691379567)
                  ·
                    rfl

theorem cell22_1667122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1667122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667122 prefixEnd_1667122 := by exact prefixLift 1667122
  have htrace : WordTrace (prefixWord ++ tailWord_1667122) baseStart_1667122 baseEnd_1667122 := by
    simpa [prefixWord, tailWord_1667122, baseEnd_1667122] using wordTrace_append hprefix tailTrace_1667122
  have hstable : (prefixWord ++ tailWord_1667122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667122).length < 2 ^ (prefixWord ++ tailWord_1667122).sum := by decide
  have hdescent : baseEnd_1667122 < baseStart_1667122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667137 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1667137 : Nat := 118140960795 + 1667137 * 2 ^ 59
def prefixEnd_1667137 : Nat := 4983230072969 + 3 ^ 40 * 1667137 * 2
def baseEnd_1667137 : Nat := 570695065263166035013655

theorem tailTrace_1667137 : CollatzResearch.WordTrace tailWord_1667137 prefixEnd_1667137 570695065263166035013655 := by
  unfold tailWord_1667137
  simp only [CollatzResearch.WordTrace]
  refine ⟨60805481761254848176647665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40536987840836565451098443 60805481761254848176647665)
  ·
    refine ⟨45604111320941136132485749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60805481761254848176647665 45604111320941136132485749)
    ·
      refine ⟨4275385436338231512420539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45604111320941136132485749 4275385436338231512420539)
      ·
        refine ⟨6413078154507347268630809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275385436338231512420539 6413078154507347268630809)
        ·
          refine ⟨4809808615880510451473107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413078154507347268630809 4809808615880510451473107)
          ·
            refine ⟨7214712923820765677209661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809808615880510451473107 7214712923820765677209661)
            ·
              refine ⟨2705517346432787128953623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214712923820765677209661 2705517346432787128953623)
              ·
                refine ⟨4058276019649180693430435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705517346432787128953623 4058276019649180693430435)
                ·
                  refine ⟨6087414029473771040145653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058276019649180693430435 6087414029473771040145653)
                  ·
                    refine ⟨570695065263166035013655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6087414029473771040145653 570695065263166035013655)
                    ·
                      rfl

theorem cell22_1667137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1667137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667137 prefixEnd_1667137 := by exact prefixLift 1667137
  have htrace : WordTrace (prefixWord ++ tailWord_1667137) baseStart_1667137 baseEnd_1667137 := by
    simpa [prefixWord, tailWord_1667137, baseEnd_1667137] using wordTrace_append hprefix tailTrace_1667137
  have hstable : (prefixWord ++ tailWord_1667137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667137).length < 2 ^ (prefixWord ++ tailWord_1667137).sum := by decide
  have hdescent : baseEnd_1667137 < baseStart_1667137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667150 : List Nat := [4, 1, 1, 1, 1, 5, 1, 8]
def baseStart_1667150 : Nat := 118140960795 + 1667150 * 2 ^ 59
def prefixEnd_1667150 : Nat := 4983230072969 + 3 ^ 40 * 1667150 * 2
def baseEnd_1667150 : Nat := 63411057269870926048735

theorem tailTrace_1667150 : CollatzResearch.WordTrace tailWord_1667150 prefixEnd_1667150 63411057269870926048735 := by
  unfold tailWord_1667150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600744488775968924608863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40537303940138500931247269 7600744488775968924608863)
  ·
    refine ⟨11401116733163953386913295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7600744488775968924608863 11401116733163953386913295)
    ·
      refine ⟨17101675099745930080369943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11401116733163953386913295 17101675099745930080369943)
      ·
        refine ⟨25652512649618895120554915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17101675099745930080369943 25652512649618895120554915)
        ·
          refine ⟨38478768974428342680832373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25652512649618895120554915 38478768974428342680832373)
          ·
            refine ⟨3607384591352657126328035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38478768974428342680832373 3607384591352657126328035)
            ·
              refine ⟨5411076887028985689492053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607384591352657126328035 5411076887028985689492053)
              ·
                refine ⟨63411057269870926048735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5411076887028985689492053 63411057269870926048735)
                ·
                  rfl

theorem cell22_1667150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_1667150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667150 prefixEnd_1667150 := by exact prefixLift 1667150
  have htrace : WordTrace (prefixWord ++ tailWord_1667150) baseStart_1667150 baseEnd_1667150 := by
    simpa [prefixWord, tailWord_1667150, baseEnd_1667150] using wordTrace_append hprefix tailTrace_1667150
  have hstable : (prefixWord ++ tailWord_1667150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667150).length < 2 ^ (prefixWord ++ tailWord_1667150).sum := by decide
  have hdescent : baseEnd_1667150 < baseStart_1667150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667222 : List Nat := [5, 3, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1667222 : Nat := 118140960795 + 1667222 * 2 ^ 59
def prefixEnd_1667222 : Nat := 4983230072969 + 3 ^ 40 * 1667222 * 2
def baseEnd_1667222 : Nat := 570724162500254146638395

theorem tailTrace_1667222 : CollatzResearch.WordTrace tailWord_1667222 prefixEnd_1667222 570724162500254146638395 := by
  unfold tailWord_1667222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800536372871681730843245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40539054643964605128994613 3800536372871681730843245)
  ·
    refine ⟨1425201139826880649066217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3800536372871681730843245 1425201139826880649066217)
    ·
      refine ⟨1068900854870160486799663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1425201139826880649066217 1068900854870160486799663)
      ·
        refine ⟨1603351282305240730199495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068900854870160486799663 1603351282305240730199495)
        ·
          refine ⟨2405026923457861095299243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603351282305240730199495 2405026923457861095299243)
          ·
            refine ⟨3607540385186791642948865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405026923457861095299243 3607540385186791642948865)
            ·
              refine ⟨2705655288890093732211649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3607540385186791642948865 2705655288890093732211649)
              ·
                refine ⟨2029241466667570299158737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705655288890093732211649 2029241466667570299158737)
                ·
                  refine ⟨1521931100000677724369053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2029241466667570299158737 1521931100000677724369053)
                  ·
                    refine ⟨570724162500254146638395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521931100000677724369053 570724162500254146638395)
                    ·
                      rfl

theorem cell22_1667222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1667222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667222 prefixEnd_1667222 := by exact prefixLift 1667222
  have htrace : WordTrace (prefixWord ++ tailWord_1667222) baseStart_1667222 baseEnd_1667222 := by
    simpa [prefixWord, tailWord_1667222, baseEnd_1667222] using wordTrace_append hprefix tailTrace_1667222
  have hstable : (prefixWord ++ tailWord_1667222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667222).length < 2 ^ (prefixWord ++ tailWord_1667222).sum := by decide
  have hdescent : baseEnd_1667222 < baseStart_1667222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667233 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 1, 3]
def baseStart_1667233 : Nat := 118140960795 + 1667233 * 2 ^ 59
def prefixEnd_1667233 : Nat := 4983230072969 + 3 ^ 40 * 1667233 * 2
def baseEnd_1667233 : Nat := 570727928025053784613361

theorem tailTrace_1667233 : CollatzResearch.WordTrace tailWord_1667233 prefixEnd_1667233 570727928025053784613361 := by
  unfold tailWord_1667233
  simp only [CollatzResearch.WordTrace]
  refine ⟨60808983168907056572142353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40539322112604704381428235 60808983168907056572142353)
  ·
    refine ⟨45606737376680292429106765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60808983168907056572142353 45606737376680292429106765)
    ·
      refine ⟨17102526516255109660915037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45606737376680292429106765 17102526516255109660915037)
      ·
        refine ⟨6413447443595666122843139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17102526516255109660915037 6413447443595666122843139)
        ·
          refine ⟨9620171165393499184264709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413447443595666122843139 9620171165393499184264709)
          ·
            refine ⟨1803782093511281097049633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9620171165393499184264709 1803782093511281097049633)
            ·
              refine ⟨1352836570133460822787225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803782093511281097049633 1352836570133460822787225)
              ·
                refine ⟨1014627427600095617090419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352836570133460822787225 1014627427600095617090419)
                ·
                  refine ⟨1521941141400143425635629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014627427600095617090419 1521941141400143425635629)
                  ·
                    refine ⟨570727928025053784613361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521941141400143425635629 570727928025053784613361)
                    ·
                      rfl

theorem cell22_1667233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_1667233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667233 prefixEnd_1667233 := by exact prefixLift 1667233
  have htrace : WordTrace (prefixWord ++ tailWord_1667233) baseStart_1667233 baseEnd_1667233 := by
    simpa [prefixWord, tailWord_1667233, baseEnd_1667233] using wordTrace_append hprefix tailTrace_1667233
  have hstable : (prefixWord ++ tailWord_1667233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667233).length < 2 ^ (prefixWord ++ tailWord_1667233).sum := by decide
  have hdescent : baseEnd_1667233 < baseStart_1667233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667272 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_1667272 : Nat := 118140960795 + 1667272 * 2 ^ 59
def prefixEnd_1667272 : Nat := 4983230072969 + 3 ^ 40 * 1667272 * 2
def baseEnd_1667272 : Nat := 570741278522070682888241

theorem tailTrace_1667272 : CollatzResearch.WordTrace tailWord_1667272 prefixEnd_1667272 570741278522070682888241 := by
  unfold tailWord_1667272
  simp only [CollatzResearch.WordTrace]
  refine ⟨30405202807882883116406035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40540270410510510821874713 30405202807882883116406035)
  ·
    refine ⟨45607804211824324674609053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30405202807882883116406035 45607804211824324674609053)
    ·
      refine ⟨17102926579434121752978395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45607804211824324674609053 17102926579434121752978395)
      ·
        refine ⟨25654389869151182629467593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17102926579434121752978395 25654389869151182629467593)
        ·
          refine ⟨19240792401863386972100695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25654389869151182629467593 19240792401863386972100695)
          ·
            refine ⟨28861188602795080458151043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240792401863386972100695 28861188602795080458151043)
            ·
              refine ⟨43291782904192620687226565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28861188602795080458151043 43291782904192620687226565)
              ·
                refine ⟨8117209294536116378854981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43291782904192620687226565 8117209294536116378854981)
                ·
                  refine ⟨1521976742725521821035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8117209294536116378854981 1521976742725521821035309)
                  ·
                    refine ⟨570741278522070682888241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521976742725521821035309 570741278522070682888241)
                    ·
                      rfl

theorem cell22_1667272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_1667272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667272 prefixEnd_1667272 := by exact prefixLift 1667272
  have htrace : WordTrace (prefixWord ++ tailWord_1667272) baseStart_1667272 baseEnd_1667272 := by
    simpa [prefixWord, tailWord_1667272, baseEnd_1667272] using wordTrace_append hprefix tailTrace_1667272
  have hstable : (prefixWord ++ tailWord_1667272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667272).length < 2 ^ (prefixWord ++ tailWord_1667272).sum := by decide
  have hdescent : baseEnd_1667272 < baseStart_1667272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667274 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_1667274 : Nat := 118140960795 + 1667274 * 2 ^ 59
def prefixEnd_1667274 : Nat := 4983230072969 + 3 ^ 40 * 1667274 * 2
def baseEnd_1667274 : Nat := 190247321054314448112745

theorem tailTrace_1667274 : CollatzResearch.WordTrace tailWord_1667274 prefixEnd_1667274 190247321054314448112745 := by
  unfold tailWord_1667274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202619640439630143596219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40540319041172347049589917 15202619640439630143596219)
  ·
    refine ⟨22803929460659445215394329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202619640439630143596219 22803929460659445215394329)
    ·
      refine ⟨17102947095494583911545747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22803929460659445215394329 17102947095494583911545747)
      ·
        refine ⟨25654420643241875867318621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17102947095494583911545747 25654420643241875867318621)
        ·
          refine ⟨9620407741215703450244483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25654420643241875867318621 9620407741215703450244483)
          ·
            refine ⟨14430611611823555175366725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620407741215703450244483 14430611611823555175366725)
            ·
              refine ⟨2705739677216916595381261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14430611611823555175366725 2705739677216916595381261)
              ·
                refine ⟨1014652378956343723267973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2705739677216916595381261 1014652378956343723267973)
                ·
                  refine ⟨190247321054314448112745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014652378956343723267973 190247321054314448112745)
                  ·
                    rfl

theorem cell22_1667274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_1667274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667274 prefixEnd_1667274 := by exact prefixLift 1667274
  have htrace : WordTrace (prefixWord ++ tailWord_1667274) baseStart_1667274 baseEnd_1667274 := by
    simpa [prefixWord, tailWord_1667274, baseEnd_1667274] using wordTrace_append hprefix tailTrace_1667274
  have hstable : (prefixWord ++ tailWord_1667274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667274).length < 2 ^ (prefixWord ++ tailWord_1667274).sum := by decide
  have hdescent : baseEnd_1667274 < baseStart_1667274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667276 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_1667276 : Nat := 118140960795 + 1667276 * 2 ^ 59
def prefixEnd_1667276 : Nat := 4983230072969 + 3 ^ 40 * 1667276 * 2
def baseEnd_1667276 : Nat := 570742647803816005788229

theorem tailTrace_1667276 : CollatzResearch.WordTrace tailWord_1667276 prefixEnd_1667276 570742647803816005788229 := by
  unfold tailWord_1667276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30405275753875637457978841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40540367671834183277305121 30405275753875637457978841)
  ·
    refine ⟨22803956815406728093484131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30405275753875637457978841 22803956815406728093484131)
    ·
      refine ⟨34205935223110092140226197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22803956815406728093484131 34205935223110092140226197)
      ·
        refine ⟨1603403213583285569073103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34205935223110092140226197 1603403213583285569073103)
        ·
          refine ⟨2405104820374928353609655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603403213583285569073103 2405104820374928353609655)
          ·
            refine ⟨3607657230562392530414483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405104820374928353609655 3607657230562392530414483)
            ·
              refine ⟨5411485845843588795621725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607657230562392530414483 5411485845843588795621725)
              ·
                refine ⟨2029307192191345798358147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5411485845843588795621725 2029307192191345798358147)
                ·
                  refine ⟨3043960788287018697537221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029307192191345798358147 3043960788287018697537221)
                  ·
                    refine ⟨570742647803816005788229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3043960788287018697537221 570742647803816005788229)
                    ·
                      rfl

theorem cell22_1667276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_1667276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667276 prefixEnd_1667276 := by exact prefixLift 1667276
  have htrace : WordTrace (prefixWord ++ tailWord_1667276) baseStart_1667276 baseEnd_1667276 := by
    simpa [prefixWord, tailWord_1667276, baseEnd_1667276] using wordTrace_append hprefix tailTrace_1667276
  have hstable : (prefixWord ++ tailWord_1667276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667276).length < 2 ^ (prefixWord ++ tailWord_1667276).sum := by decide
  have hdescent : baseEnd_1667276 < baseStart_1667276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667289 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_1667289 : Nat := 118140960795 + 1667289 * 2 ^ 59
def prefixEnd_1667289 : Nat := 4983230072969 + 3 ^ 40 * 1667289 * 2
def baseEnd_1667289 : Nat := 570747097969488305213189

theorem tailTrace_1667289 : CollatzResearch.WordTrace tailWord_1667289 prefixEnd_1667289 570747097969488305213189 := by
  unfold tailWord_1667289
  simp only [CollatzResearch.WordTrace]
  refine ⟨60811025656704178136180921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40540683771136118757453947 60811025656704178136180921)
  ·
    refine ⟨45608269242528133602135691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60811025656704178136180921 45608269242528133602135691)
    ·
      refine ⟨68412403863792200403203537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45608269242528133602135691 68412403863792200403203537)
      ·
        refine ⟨51309302897844150302402653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68412403863792200403203537 51309302897844150302402653)
        ·
          refine ⟨19240988586691556363400995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51309302897844150302402653 19240988586691556363400995)
          ·
            refine ⟨28861482880037334545101493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240988586691556363400995 28861482880037334545101493)
            ·
              refine ⟨2705764020003500113603265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28861482880037334545101493 2705764020003500113603265)
              ·
                refine ⟨2029323015002625085202449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705764020003500113603265 2029323015002625085202449)
                ·
                  refine ⟨1521992261251968813901837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2029323015002625085202449 1521992261251968813901837)
                  ·
                    refine ⟨570747097969488305213189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521992261251968813901837 570747097969488305213189)
                    ·
                      rfl

theorem cell22_1667289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_1667289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667289 prefixEnd_1667289 := by exact prefixLift 1667289
  have htrace : WordTrace (prefixWord ++ tailWord_1667289) baseStart_1667289 baseEnd_1667289 := by
    simpa [prefixWord, tailWord_1667289, baseEnd_1667289] using wordTrace_append hprefix tailTrace_1667289
  have hstable : (prefixWord ++ tailWord_1667289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667289).length < 2 ^ (prefixWord ++ tailWord_1667289).sum := by decide
  have hdescent : baseEnd_1667289 < baseStart_1667289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667306 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1667306 : Nat := 118140960795 + 1667306 * 2 ^ 59
def prefixEnd_1667306 : Nat := 4983230072969 + 3 ^ 40 * 1667306 * 2
def baseEnd_1667306 : Nat := 570752917416905927538137

theorem tailTrace_1667306 : CollatzResearch.WordTrace tailWord_1667306 prefixEnd_1667306 570752917416905927538137 := by
  unfold tailWord_1667306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202911424410647509887443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40541097131761726693033181 15202911424410647509887443)
  ·
    refine ⟨22804367136615971264831165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202911424410647509887443 22804367136615971264831165)
    ·
      refine ⟨8551637676230989224311687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22804367136615971264831165 8551637676230989224311687)
      ·
        refine ⟨12827456514346483836467531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551637676230989224311687 12827456514346483836467531)
        ·
          refine ⟨19241184771519725754701297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827456514346483836467531 19241184771519725754701297)
          ·
            refine ⟨14430888578639794316025973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19241184771519725754701297 14430888578639794316025973)
            ·
              refine ⟨1352895804247480717127435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14430888578639794316025973 1352895804247480717127435)
              ·
                refine ⟨2029343706371221075691153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352895804247480717127435 2029343706371221075691153)
                ·
                  refine ⟨1522007779778415806768365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2029343706371221075691153 1522007779778415806768365)
                  ·
                    refine ⟨570752917416905927538137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522007779778415806768365 570752917416905927538137)
                    ·
                      rfl

theorem cell22_1667306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1667306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667306 prefixEnd_1667306 := by exact prefixLift 1667306
  have htrace : WordTrace (prefixWord ++ tailWord_1667306) baseStart_1667306 baseEnd_1667306 := by
    simpa [prefixWord, tailWord_1667306, baseEnd_1667306] using wordTrace_append hprefix tailTrace_1667306
  have hstable : (prefixWord ++ tailWord_1667306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667306).length < 2 ^ (prefixWord ++ tailWord_1667306).sum := by decide
  have hdescent : baseEnd_1667306 < baseStart_1667306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667351 : List Nat := [1, 1, 3, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1667351 : Nat := 118140960795 + 1667351 * 2 ^ 59
def prefixEnd_1667351 : Nat := 4983230072969 + 3 ^ 40 * 1667351 * 2
def baseEnd_1667351 : Nat := 570768321836540810162999

theorem tailTrace_1667351 : CollatzResearch.WordTrace tailWord_1667351 prefixEnd_1667351 570768321836540810162999 := by
  unfold tailWord_1667351
  simp only [CollatzResearch.WordTrace]
  refine ⟨60813286982479562724937907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40542191321653041816625271 60813286982479562724937907)
  ·
    refine ⟨91219930473719344087406861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60813286982479562724937907 91219930473719344087406861)
    ·
      refine ⟨34207473927644754032777573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91219930473719344087406861 34207473927644754032777573)
      ·
        refine ⟨6413901361433391381145795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34207473927644754032777573 6413901361433391381145795)
        ·
          refine ⟨9620852042150087071718693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413901361433391381145795 9620852042150087071718693)
          ·
            refine ⟨1803909757903141325947255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9620852042150087071718693 1803909757903141325947255)
            ·
              refine ⟨2705864636854711988920883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803909757903141325947255 2705864636854711988920883)
              ·
                refine ⟨4058796955282067983381325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705864636854711988920883 4058796955282067983381325)
                ·
                  refine ⟨1522048858230775493767997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4058796955282067983381325 1522048858230775493767997)
                  ·
                    refine ⟨570768321836540810162999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522048858230775493767997 570768321836540810162999)
                    ·
                      rfl

theorem cell22_1667351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1667351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667351 prefixEnd_1667351 := by exact prefixLift 1667351
  have htrace : WordTrace (prefixWord ++ tailWord_1667351) baseStart_1667351 baseEnd_1667351 := by
    simpa [prefixWord, tailWord_1667351, baseEnd_1667351] using wordTrace_append hprefix tailTrace_1667351
  have hstable : (prefixWord ++ tailWord_1667351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667351).length < 2 ^ (prefixWord ++ tailWord_1667351).sum := by decide
  have hdescent : baseEnd_1667351 < baseStart_1667351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667364 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1667364 : Nat := 118140960795 + 1667364 * 2 ^ 59
def prefixEnd_1667364 : Nat := 4983230072969 + 3 ^ 40 * 1667364 * 2
def baseEnd_1667364 : Nat := 190257590667404369862653

theorem tailTrace_1667364 : CollatzResearch.WordTrace tailWord_1667364 prefixEnd_1667364 190257590667404369862653 := by
  unfold tailWord_1667364
  simp only [CollatzResearch.WordTrace]
  refine ⟨30406880565716232972580573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40542507420954977296774097 30406880565716232972580573)
  ·
    refine ⟨11402580212143587364717715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30406880565716232972580573 11402580212143587364717715)
    ·
      refine ⟨17103870318215381047076573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11402580212143587364717715 17103870318215381047076573)
      ·
        refine ⟨6413951369330767892653715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17103870318215381047076573 6413951369330767892653715)
        ·
          refine ⟨9620927053996151838980573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413951369330767892653715 9620927053996151838980573)
          ·
            refine ⟨3607847645248556939617715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9620927053996151838980573 3607847645248556939617715)
            ·
              refine ⟨5411771467872835409426573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607847645248556939617715 5411771467872835409426573)
              ·
                refine ⟨2029414300452313278534965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5411771467872835409426573 2029414300452313278534965)
                ·
                  refine ⟨190257590667404369862653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029414300452313278534965 190257590667404369862653)
                  ·
                    rfl

theorem cell22_1667364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1667364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667364 prefixEnd_1667364 := by exact prefixLift 1667364
  have htrace : WordTrace (prefixWord ++ tailWord_1667364) baseStart_1667364 baseEnd_1667364 := by
    simpa [prefixWord, tailWord_1667364, baseEnd_1667364] using wordTrace_append hprefix tailTrace_1667364
  have hstable : (prefixWord ++ tailWord_1667364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667364).length < 2 ^ (prefixWord ++ tailWord_1667364).sum := by decide
  have hdescent : baseEnd_1667364 < baseStart_1667364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667497 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1667497 : Nat := 118140960795 + 1667497 * 2 ^ 59
def prefixEnd_1667497 : Nat := 4983230072969 + 3 ^ 40 * 1667497 * 2
def baseEnd_1667497 : Nat := 570818300620245096012551

theorem tailTrace_1667497 : CollatzResearch.WordTrace tailWord_1667497 prefixEnd_1667497 570818300620245096012551 := by
  unfold tailWord_1667497
  simp only [CollatzResearch.WordTrace]
  refine ⟨60818612039950629659752745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40545741359967086439835163 60818612039950629659752745)
  ·
    refine ⟨45613959029962972244814559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60818612039950629659752745 45613959029962972244814559)
    ·
      refine ⟨68420938544944458367221839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45613959029962972244814559 68420938544944458367221839)
      ·
        refine ⟨102631407817416687550832759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68420938544944458367221839 102631407817416687550832759)
        ·
          refine ⟨153947111726125031326249139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102631407817416687550832759 153947111726125031326249139)
          ·
            refine ⟨230920667589187546989373709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153947111726125031326249139 230920667589187546989373709)
            ·
              refine ⟨86595250345945330121015141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230920667589187546989373709 86595250345945330121015141)
              ·
                refine ⟨16236609439864749397690339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86595250345945330121015141 16236609439864749397690339)
                ·
                  refine ⟨24354914159797124096535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16236609439864749397690339 24354914159797124096535509)
                  ·
                    refine ⟨570818300620245096012551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24354914159797124096535509 570818300620245096012551)
                    ·
                      rfl

theorem cell22_1667497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1667497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667497 prefixEnd_1667497 := by exact prefixLift 1667497
  have htrace : WordTrace (prefixWord ++ tailWord_1667497) baseStart_1667497 baseEnd_1667497 := by
    simpa [prefixWord, tailWord_1667497, baseEnd_1667497] using wordTrace_append hprefix tailTrace_1667497
  have hstable : (prefixWord ++ tailWord_1667497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667497).length < 2 ^ (prefixWord ++ tailWord_1667497).sum := by decide
  have hdescent : baseEnd_1667497 < baseStart_1667497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667589 : List Nat := [1, 3, 1, 1, 2, 2, 5, 7]
def baseStart_1667589 : Nat := 118140960795 + 1667589 * 2 ^ 59
def prefixEnd_1667589 : Nat := 4983230072969 + 3 ^ 40 * 1667589 * 2
def baseEnd_1667589 : Nat := 63427754900043058079141

theorem tailTrace_1667589 : CollatzResearch.WordTrace tailWord_1667589 prefixEnd_1667589 63427754900043058079141 := by
  unfold tailWord_1667589
  simp only [CollatzResearch.WordTrace]
  refine ⟨60821967555617329372101821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40547978370411552914734547 60821967555617329372101821)
  ·
    refine ⟨22808237833356498514538183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60821967555617329372101821 22808237833356498514538183)
    ·
      refine ⟨34212356750034747771807275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22808237833356498514538183 34212356750034747771807275)
      ·
        refine ⟨51318535125052121657710913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34212356750034747771807275 51318535125052121657710913)
        ·
          refine ⟨38488901343789091243283185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51318535125052121657710913 38488901343789091243283185)
          ·
            refine ⟨28866676007841818432462389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38488901343789091243283185 28866676007841818432462389)
            ·
              refine ⟨2706250875735170478043349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28866676007841818432462389 2706250875735170478043349)
              ·
                refine ⟨63427754900043058079141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2706250875735170478043349 63427754900043058079141)
                ·
                  rfl

theorem cell22_1667589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 7].length) (baseStart_1667589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667589 prefixEnd_1667589 := by exact prefixLift 1667589
  have htrace : WordTrace (prefixWord ++ tailWord_1667589) baseStart_1667589 baseEnd_1667589 := by
    simpa [prefixWord, tailWord_1667589, baseEnd_1667589] using wordTrace_append hprefix tailTrace_1667589
  have hstable : (prefixWord ++ tailWord_1667589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667589).length < 2 ^ (prefixWord ++ tailWord_1667589).sum := by decide
  have hdescent : baseEnd_1667589 < baseStart_1667589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667608 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_1667608 : Nat := 118140960795 + 1667608 * 2 ^ 59
def prefixEnd_1667608 : Nat := 4983230072969 + 3 ^ 40 * 1667608 * 2
def baseEnd_1667608 : Nat := 570856298188677806487211

theorem tailTrace_1667608 : CollatzResearch.WordTrace tailWord_1667608 prefixEnd_1667608 570856298188677806487211 := by
  unfold tailWord_1667608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30411330271274247808521739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40548440361698997078028985 30411330271274247808521739)
  ·
    refine ⟨45616995406911371712782609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30411330271274247808521739 45616995406911371712782609)
    ·
      refine ⟨34212746555183528784586957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45616995406911371712782609 34212746555183528784586957)
      ·
        refine ⟨12829779958193823294220109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34212746555183528784586957 12829779958193823294220109)
        ·
          refine ⟨4811167484322683735332541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12829779958193823294220109 4811167484322683735332541)
          ·
            refine ⟨1804187806621006400749703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4811167484322683735332541 1804187806621006400749703)
            ·
              refine ⟨2706281709931509601124555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804187806621006400749703 2706281709931509601124555)
              ·
                refine ⟨4059422564897264401686833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706281709931509601124555 4059422564897264401686833)
                ·
                  refine ⟨3044566923672948301265125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4059422564897264401686833 3044566923672948301265125)
                  ·
                    refine ⟨570856298188677806487211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3044566923672948301265125 570856298188677806487211)
                    ·
                      rfl

theorem cell22_1667608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_1667608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667608 prefixEnd_1667608 := by exact prefixLift 1667608
  have htrace : WordTrace (prefixWord ++ tailWord_1667608) baseStart_1667608 baseEnd_1667608 := by
    simpa [prefixWord, tailWord_1667608, baseEnd_1667608] using wordTrace_append hprefix tailTrace_1667608
  have hstable : (prefixWord ++ tailWord_1667608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667608).length < 2 ^ (prefixWord ++ tailWord_1667608).sum := by decide
  have hdescent : baseEnd_1667608 < baseStart_1667608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667623 : List Nat := [1, 1, 7, 2, 1, 1, 9]
def baseStart_1667623 : Nat := 118140960795 + 1667623 * 2 ^ 59
def prefixEnd_1667623 : Nat := 4983230072969 + 3 ^ 40 * 1667623 * 2
def baseEnd_1667623 : Nat := 21143016036860102494895

theorem tailTrace_1667623 : CollatzResearch.WordTrace tailWord_1667623 prefixEnd_1667623 21143016036860102494895 := by
  unfold tailWord_1667623
  simp only [CollatzResearch.WordTrace]
  refine ⟨60823207637494153178839523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40548805091662768785893015 60823207637494153178839523)
  ·
    refine ⟨91234811456241229768259285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60823207637494153178839523 91234811456241229768259285)
    ·
      refine ⟨2138315893505653822693577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91234811456241229768259285 2138315893505653822693577)
      ·
        refine ⟨1603736920129240367020183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138315893505653822693577 1603736920129240367020183)
        ·
          refine ⟨2405605380193860550530275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603736920129240367020183 2405605380193860550530275)
          ·
            refine ⟨3608408070290790825795413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405605380193860550530275 3608408070290790825795413)
            ·
              refine ⟨21143016036860102494895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3608408070290790825795413 21143016036860102494895)
              ·
                rfl

theorem cell22_1667623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 9].length) (baseStart_1667623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667623 prefixEnd_1667623 := by exact prefixLift 1667623
  have htrace : WordTrace (prefixWord ++ tailWord_1667623) baseStart_1667623 baseEnd_1667623 := by
    simpa [prefixWord, tailWord_1667623, baseEnd_1667623] using wordTrace_append hprefix tailTrace_1667623
  have hstable : (prefixWord ++ tailWord_1667623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667623).length < 2 ^ (prefixWord ++ tailWord_1667623).sum := by decide
  have hdescent : baseEnd_1667623 < baseStart_1667623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667679 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 8]
def baseStart_1667679 : Nat := 118140960795 + 1667679 * 2 ^ 59
def prefixEnd_1667679 : Nat := 4983230072969 + 3 ^ 40 * 1667679 * 2
def baseEnd_1667679 : Nat := 190293534313219095987331

theorem tailTrace_1667679 : CollatzResearch.WordTrace tailWord_1667679 prefixEnd_1667679 190293534313219095987331 := by
  unfold tailWord_1667679
  simp only [CollatzResearch.WordTrace]
  refine ⟨60825250125291274742878091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40550166750194183161918727 60825250125291274742878091)
  ·
    refine ⟨91237875187936912114317137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60825250125291274742878091 91237875187936912114317137)
    ·
      refine ⟨68428406390952684085737853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91237875187936912114317137 68428406390952684085737853)
      ·
        refine ⟨25660652396607256532151695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68428406390952684085737853 25660652396607256532151695)
        ·
          refine ⟨38490978594910884798227543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25660652396607256532151695 38490978594910884798227543)
          ·
            refine ⟨57736467892366327197341315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38490978594910884798227543 57736467892366327197341315)
            ·
              refine ⟨86604701838549490796011973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57736467892366327197341315 86604701838549490796011973)
              ·
                refine ⟨16238381594728029524252245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86604701838549490796011973 16238381594728029524252245)
                ·
                  refine ⟨190293534313219095987331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16238381594728029524252245 190293534313219095987331)
                  ·
                    rfl

theorem cell22_1667679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_1667679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667679 prefixEnd_1667679 := by exact prefixLift 1667679
  have htrace : WordTrace (prefixWord ++ tailWord_1667679) baseStart_1667679 baseEnd_1667679 := by
    simpa [prefixWord, tailWord_1667679, baseEnd_1667679] using wordTrace_append hprefix tailTrace_1667679
  have hstable : (prefixWord ++ tailWord_1667679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667679).length < 2 ^ (prefixWord ++ tailWord_1667679).sum := by decide
  have hdescent : baseEnd_1667679 < baseStart_1667679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667702 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1667702 : Nat := 118140960795 + 1667702 * 2 ^ 59
def prefixEnd_1667702 : Nat := 4983230072969 + 3 ^ 40 * 1667702 * 2
def baseEnd_1667702 : Nat := 190296158769897631545641

theorem tailTrace_1667702 : CollatzResearch.WordTrace tailWord_1667702 prefixEnd_1667702 190296158769897631545641 := by
  unfold tailWord_1667702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3801630562762996854435335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40550726002805299780643573 3801630562762996854435335)
  ·
    refine ⟨5702445844144495281653003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3801630562762996854435335 5702445844144495281653003)
    ·
      refine ⟨8553668766216742922479505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702445844144495281653003 8553668766216742922479505)
      ·
        refine ⟨6415251574662557191859629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8553668766216742922479505 6415251574662557191859629)
        ·
          refine ⟨2405719340498458946947361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6415251574662557191859629 2405719340498458946947361)
          ·
            refine ⟨1804289505373844210210521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2405719340498458946947361 1804289505373844210210521)
            ·
              refine ⟨1353217129030383157657891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804289505373844210210521 1353217129030383157657891)
              ·
                refine ⟨2029825693545574736486837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353217129030383157657891 2029825693545574736486837)
                ·
                  refine ⟨190296158769897631545641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029825693545574736486837 190296158769897631545641)
                  ·
                    rfl

theorem cell22_1667702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1667702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667702 prefixEnd_1667702 := by exact prefixLift 1667702
  have htrace : WordTrace (prefixWord ++ tailWord_1667702) baseStart_1667702 baseEnd_1667702 := by
    simpa [prefixWord, tailWord_1667702, baseEnd_1667702] using wordTrace_append hprefix tailTrace_1667702
  have hstable : (prefixWord ++ tailWord_1667702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667702).length < 2 ^ (prefixWord ++ tailWord_1667702).sum := by decide
  have hdescent : baseEnd_1667702 < baseStart_1667702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667711 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 6, 3]
def baseStart_1667711 : Nat := 118140960795 + 1667711 * 2 ^ 59
def prefixEnd_1667711 : Nat := 4983230072969 + 3 ^ 40 * 1667711 * 2
def baseEnd_1667711 : Nat := 570891557193619871161895

theorem tailTrace_1667711 : CollatzResearch.WordTrace tailWord_1667711 prefixEnd_1667711 570891557193619871161895 := by
  unfold tailWord_1667711
  simp only [CollatzResearch.WordTrace]
  refine ⟨60826417261175344208042987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40550944840783562805361991 60826417261175344208042987)
  ·
    refine ⟨91239625891763016312064481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60826417261175344208042987 91239625891763016312064481)
    ·
      refine ⟨68429719418822262234048361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91239625891763016312064481 68429719418822262234048361)
      ·
        refine ⟨51322289564116696675536271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68429719418822262234048361 51322289564116696675536271)
        ·
          refine ⟨76983434346175045013304407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51322289564116696675536271 76983434346175045013304407)
          ·
            refine ⟨115475151519262567519956611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76983434346175045013304407 115475151519262567519956611)
            ·
              refine ⟨173212727278893851279934917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115475151519262567519956611 173212727278893851279934917)
              ·
                refine ⟨32477386364792597114987797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173212727278893851279934917 32477386364792597114987797)
                ·
                  refine ⟨1522377485849652989765053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32477386364792597114987797 1522377485849652989765053)
                  ·
                    refine ⟨570891557193619871161895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522377485849652989765053 570891557193619871161895)
                    ·
                      rfl

theorem cell22_1667711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_1667711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667711 prefixEnd_1667711 := by exact prefixLift 1667711
  have htrace : WordTrace (prefixWord ++ tailWord_1667711) baseStart_1667711 baseEnd_1667711 := by
    simpa [prefixWord, tailWord_1667711, baseEnd_1667711] using wordTrace_append hprefix tailTrace_1667711
  have hstable : (prefixWord ++ tailWord_1667711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667711).length < 2 ^ (prefixWord ++ tailWord_1667711).sum := by decide
  have hdescent : baseEnd_1667711 < baseStart_1667711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667732 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1667732 : Nat := 118140960795 + 1667732 * 2 ^ 59
def prefixEnd_1667732 : Nat := 4983230072969 + 3 ^ 40 * 1667732 * 2
def baseEnd_1667732 : Nat := 570898745922782816386831

theorem tailTrace_1667732 : CollatzResearch.WordTrace tailWord_1667732 prefixEnd_1667732 570898745922782816386831 := by
  unfold tailWord_1667732
  simp only [CollatzResearch.WordTrace]
  refine ⟨30413591597049632397278725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40551455462732843196371633 30413591597049632397278725)
  ·
    refine ⟨5702548424446806074489761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30413591597049632397278725 5702548424446806074489761)
    ·
      refine ⟨4276911318335104555867321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5702548424446806074489761 4276911318335104555867321)
      ·
        refine ⟨3207683488751328416900491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4276911318335104555867321 3207683488751328416900491)
        ·
          refine ⟨4811525233126992625350737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207683488751328416900491 4811525233126992625350737)
          ·
            refine ⟨3608643924845244469013053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4811525233126992625350737 3608643924845244469013053)
            ·
              refine ⟨1353241471816966675879895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3608643924845244469013053 1353241471816966675879895)
              ·
                refine ⟨2029862207725450013819843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353241471816966675879895 2029862207725450013819843)
                ·
                  refine ⟨3044793311588175020729765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029862207725450013819843 3044793311588175020729765)
                  ·
                    refine ⟨570898745922782816386831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3044793311588175020729765 570898745922782816386831)
                    ·
                      rfl

theorem cell22_1667732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1667732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667732 prefixEnd_1667732 := by exact prefixLift 1667732
  have htrace : WordTrace (prefixWord ++ tailWord_1667732) baseStart_1667732 baseEnd_1667732 := by
    simpa [prefixWord, tailWord_1667732, baseEnd_1667732] using wordTrace_append hprefix tailTrace_1667732
  have hstable : (prefixWord ++ tailWord_1667732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667732).length < 2 ^ (prefixWord ++ tailWord_1667732).sum := by decide
  have hdescent : baseEnd_1667732 < baseStart_1667732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667773 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1667773 : Nat := 118140960795 + 1667773 * 2 ^ 59
def prefixEnd_1667773 : Nat := 4983230072969 + 3 ^ 40 * 1667773 * 2
def baseEnd_1667773 : Nat := 570912781060672376111705

theorem tailTrace_1667773 : CollatzResearch.WordTrace tailWord_1667773 prefixEnd_1667773 570912781060672376111705 := by
  unfold tailWord_1667773
  simp only [CollatzResearch.WordTrace]
  refine ⟨60828678586950728796799973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40552452391300485864533315 60828678586950728796799973)
  ·
    refine ⟨11405377235053261649399995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60828678586950728796799973 11405377235053261649399995)
    ·
      refine ⟨17108065852579892474099993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11405377235053261649399995 17108065852579892474099993)
      ·
        refine ⟨12831049389434919355574995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17108065852579892474099993 12831049389434919355574995)
        ·
          refine ⟨19246574084152379033362493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12831049389434919355574995 19246574084152379033362493)
          ·
            refine ⟨7217465281557142137510935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19246574084152379033362493 7217465281557142137510935)
            ·
              refine ⟨10826197922335713206266403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217465281557142137510935 10826197922335713206266403)
              ·
                refine ⟨16239296883503569809399605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826197922335713206266403 16239296883503569809399605)
                ·
                  refine ⟨1522434082828459669631213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16239296883503569809399605 1522434082828459669631213)
                  ·
                    refine ⟨570912781060672376111705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522434082828459669631213 570912781060672376111705)
                    ·
                      rfl

theorem cell22_1667773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1667773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667773 prefixEnd_1667773 := by exact prefixLift 1667773
  have htrace : WordTrace (prefixWord ++ tailWord_1667773) baseStart_1667773 baseEnd_1667773 := by
    simpa [prefixWord, tailWord_1667773, baseEnd_1667773] using wordTrace_append hprefix tailTrace_1667773
  have hstable : (prefixWord ++ tailWord_1667773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667773).length < 2 ^ (prefixWord ++ tailWord_1667773).sum := by decide
  have hdescent : baseEnd_1667773 < baseStart_1667773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667801 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_1667801 : Nat := 118140960795 + 1667801 * 2 ^ 59
def prefixEnd_1667801 : Nat := 4983230072969 + 3 ^ 40 * 1667801 * 2
def baseEnd_1667801 : Nat := 570922366032889636411619

theorem tailTrace_1667801 : CollatzResearch.WordTrace tailWord_1667801 prefixEnd_1667801 570922366032889636411619 := by
  unfold tailWord_1667801
  simp only [CollatzResearch.WordTrace]
  refine ⟨60829699830849289578819257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40553133220566193052546171 60829699830849289578819257)
  ·
    refine ⟨45622274873136967184114443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60829699830849289578819257 45622274873136967184114443)
    ·
      refine ⟨68433412309705450776171665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45622274873136967184114443 68433412309705450776171665)
      ·
        refine ⟨51325059232279088082128749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68433412309705450776171665 51325059232279088082128749)
        ·
          refine ⟨19246897212104658030798281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51325059232279088082128749 19246897212104658030798281)
          ·
            refine ⟨14435172909078493523098711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19246897212104658030798281 14435172909078493523098711)
            ·
              refine ⟨21652759363617740284648067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435172909078493523098711 21652759363617740284648067)
              ·
                refine ⟨32479139045426610426972101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21652759363617740284648067 32479139045426610426972101)
                ·
                  refine ⟨6089838571017489455057269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32479139045426610426972101 6089838571017489455057269)
                  ·
                    refine ⟨570922366032889636411619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6089838571017489455057269 570922366032889636411619)
                    ·
                      rfl

theorem cell22_1667801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_1667801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667801 prefixEnd_1667801 := by exact prefixLift 1667801
  have htrace : WordTrace (prefixWord ++ tailWord_1667801) baseStart_1667801 baseEnd_1667801 := by
    simpa [prefixWord, tailWord_1667801, baseEnd_1667801] using wordTrace_append hprefix tailTrace_1667801
  have hstable : (prefixWord ++ tailWord_1667801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667801).length < 2 ^ (prefixWord ++ tailWord_1667801).sum := by decide
  have hdescent : baseEnd_1667801 < baseStart_1667801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667893 : List Nat := [1, 3, 3, 1, 3, 1, 2, 8]
def baseStart_1667893 : Nat := 118140960795 + 1667893 * 2 ^ 59
def prefixEnd_1667893 : Nat := 4983230072969 + 3 ^ 40 * 1667893 * 2
def baseEnd_1667893 : Nat := 63439317723670229234593

theorem tailTrace_1667893 : CollatzResearch.WordTrace tailWord_1667893 prefixEnd_1667893 63439317723670229234593 := by
  unfold tailWord_1667893
  simp only [CollatzResearch.WordTrace]
  refine ⟨60833055346515989291168333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40555370231010659527445555 60833055346515989291168333)
  ·
    refine ⟨22812395754943495984188125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60833055346515989291168333 22812395754943495984188125)
    ·
      refine ⟨8554648408103810994070547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22812395754943495984188125 8554648408103810994070547)
      ·
        refine ⟨12831972612155716491105821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8554648408103810994070547 12831972612155716491105821)
        ·
          refine ⟨4811989729558393684164683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12831972612155716491105821 4811989729558393684164683)
          ·
            refine ⟨7217984594337590526247025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811989729558393684164683 7217984594337590526247025)
            ·
              refine ⟨5413488445753192894685269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7217984594337590526247025 5413488445753192894685269)
              ·
                refine ⟨63439317723670229234593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5413488445753192894685269 63439317723670229234593)
                ·
                  rfl

theorem cell22_1667893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 8].length) (baseStart_1667893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667893 prefixEnd_1667893 := by exact prefixLift 1667893
  have htrace : WordTrace (prefixWord ++ tailWord_1667893) baseStart_1667893 baseEnd_1667893 := by
    simpa [prefixWord, tailWord_1667893, baseEnd_1667893] using wordTrace_append hprefix tailTrace_1667893
  have hstable : (prefixWord ++ tailWord_1667893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667893).length < 2 ^ (prefixWord ++ tailWord_1667893).sum := by decide
  have hdescent : baseEnd_1667893 < baseStart_1667893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667910 : List Nat := [6, 1, 1, 2, 12]
def baseStart_1667910 : Nat := 118140960795 + 1667910 * 2 ^ 59
def prefixEnd_1667910 : Nat := 4983230072969 + 3 ^ 40 * 1667910 * 2
def baseEnd_1667910 : Nat := 2349628308479216812495

theorem tailTrace_1667910 : CollatzResearch.WordTrace tailWord_1667910 prefixEnd_1667910 2349628308479216812495 := by
  unfold tailWord_1667910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901052355857950037329287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40555783591636267463024789 1901052355857950037329287)
  ·
    refine ⟨2851578533786925055993931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901052355857950037329287 2851578533786925055993931)
    ·
      refine ⟨4277367800680387583990897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851578533786925055993931 4277367800680387583990897)
      ·
        refine ⟨3208025850510290687993173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277367800680387583990897 3208025850510290687993173)
        ·
          refine ⟨2349628308479216812495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3208025850510290687993173 2349628308479216812495)
          ·
            rfl

theorem cell22_1667910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 12].length) (baseStart_1667910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1667910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1667910 prefixEnd_1667910 := by exact prefixLift 1667910
  have htrace : WordTrace (prefixWord ++ tailWord_1667910) baseStart_1667910 baseEnd_1667910 := by
    simpa [prefixWord, tailWord_1667910, baseEnd_1667910] using wordTrace_append hprefix tailTrace_1667910
  have hstable : (prefixWord ++ tailWord_1667910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667910).length < 2 ^ (prefixWord ++ tailWord_1667910).sum := by decide
  have hdescent : baseEnd_1667910 < baseStart_1667910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
