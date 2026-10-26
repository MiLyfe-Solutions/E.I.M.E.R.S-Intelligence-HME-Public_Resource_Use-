import V185TrunkScan23Chunk1082

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6411853 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6411853 : Nat := 118140960795 + 6411853 * 2 ^ 59
def prefixEnd_6411853 : Nat := 4983230072969 + 3 ^ 40 * 6411853 * 2
def baseEnd_6411853 : Nat := 3292362474972807329349931

theorem tailTrace_6411853 : CollatzResearch.WordTrace tailWord_6411853 prefixEnd_6411853 3292362474972807329349931 := by
  unfold tailWord_6411853
  simp only [CollatzResearch.WordTrace]
  refine ⟨233859491239959113155544213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155906327493306075437029475 233859491239959113155544213)
  ·
    refine ⟨10962163651873083429166135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 233859491239959113155544213 10962163651873083429166135)
    ·
      refine ⟨16443245477809625143749203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10962163651873083429166135 16443245477809625143749203)
      ·
        refine ⟨24664868216714437715623805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443245477809625143749203 24664868216714437715623805)
        ·
          refine ⟨9249325581267914143358927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24664868216714437715623805 9249325581267914143358927)
          ·
            refine ⟨13873988371901871215038391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249325581267914143358927 13873988371901871215038391)
            ·
              refine ⟨20810982557852806822557587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13873988371901871215038391 20810982557852806822557587)
              ·
                refine ⟨31216473836779210233836381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20810982557852806822557587 31216473836779210233836381)
                ·
                  refine ⟨11706177688792203837688643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31216473836779210233836381 11706177688792203837688643)
                  ·
                    refine ⟨17559266533188305756532965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11706177688792203837688643 17559266533188305756532965)
                    ·
                      refine ⟨3292362474972807329349931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17559266533188305756532965 3292362474972807329349931)
                      ·
                        rfl

theorem cell23_6411853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6411853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411853 prefixEnd_6411853 := by exact prefixLift 6411853
  have htrace : WordTrace (prefixWord ++ tailWord_6411853) baseStart_6411853 baseEnd_6411853 := by
    simpa [prefixWord, tailWord_6411853, baseEnd_6411853] using wordTrace_append hprefix tailTrace_6411853
  have hstable : (prefixWord ++ tailWord_6411853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411853).length < 2 ^ (prefixWord ++ tailWord_6411853).sum := by decide
  have hdescent : baseEnd_6411853 < baseStart_6411853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411873 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_6411873 : Nat := 118140960795 + 6411873 * 2 ^ 59
def prefixEnd_6411873 : Nat := 4983230072969 + 3 ^ 40 * 6411873 * 2
def baseEnd_6411873 : Nat := 3292372744585897251099839

theorem tailTrace_6411873 : CollatzResearch.WordTrace tailWord_6411873 prefixEnd_6411873 3292372744585897251099839 := by
  unfold tailWord_6411873
  simp only [CollatzResearch.WordTrace]
  refine ⟨233860220699886656571272273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155906813799924437714181515 233860220699886656571272273)
  ·
    refine ⟨175395165524914992428454205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233860220699886656571272273 175395165524914992428454205)
    ·
      refine ⟨65773187071843122160670327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175395165524914992428454205 65773187071843122160670327)
      ·
        refine ⟨98659780607764683241005491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65773187071843122160670327 98659780607764683241005491)
        ·
          refine ⟨147989670911647024861508237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98659780607764683241005491 147989670911647024861508237)
          ·
            refine ⟨55496126591867634323065589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147989670911647024861508237 55496126591867634323065589)
            ·
              refine ⟨5202761867987590717787399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55496126591867634323065589 5202761867987590717787399)
              ·
                refine ⟨7804142801981386076681099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202761867987590717787399 7804142801981386076681099)
                ·
                  refine ⟨11706214202972079115021649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804142801981386076681099 11706214202972079115021649)
                  ·
                    refine ⟨8779660652229059336266237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11706214202972079115021649 8779660652229059336266237)
                    ·
                      refine ⟨3292372744585897251099839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8779660652229059336266237 3292372744585897251099839)
                      ·
                        rfl

theorem cell23_6411873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_6411873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411873 prefixEnd_6411873 := by exact prefixLift 6411873
  have htrace : WordTrace (prefixWord ++ tailWord_6411873) baseStart_6411873 baseEnd_6411873 := by
    simpa [prefixWord, tailWord_6411873, baseEnd_6411873] using wordTrace_append hprefix tailTrace_6411873
  have hstable : (prefixWord ++ tailWord_6411873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411873).length < 2 ^ (prefixWord ++ tailWord_6411873).sum := by decide
  have hdescent : baseEnd_6411873 < baseStart_6411873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411909 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_6411909 : Nat := 118140960795 + 6411909 * 2 ^ 59
def prefixEnd_6411909 : Nat := 4983230072969 + 3 ^ 40 * 6411909 * 2
def baseEnd_6411909 : Nat := 3292391229889459110249673

theorem tailTrace_6411909 : CollatzResearch.WordTrace tailWord_6411909 prefixEnd_6411909 3292391229889459110249673 := by
  unfold tailWord_6411909
  simp only [CollatzResearch.WordTrace]
  refine ⟨233861533727756234719582781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155907689151837489813055187 233861533727756234719582781)
  ·
    refine ⟨87698075147908588019843543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233861533727756234719582781 87698075147908588019843543)
    ·
      refine ⟨131547112721862882029765315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87698075147908588019843543 131547112721862882029765315)
      ·
        refine ⟨197320669082794323044647973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131547112721862882029765315 197320669082794323044647973)
        ·
          refine ⟨36997625453023935570871495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197320669082794323044647973 36997625453023935570871495)
          ·
            refine ⟨55496438179535903356307243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36997625453023935570871495 55496438179535903356307243)
            ·
              refine ⟨83244657269303855034460865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55496438179535903356307243 83244657269303855034460865)
              ·
                refine ⟨62433492951977891275845649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83244657269303855034460865 62433492951977891275845649)
                ·
                  refine ⟨46825119713983418456884237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62433492951977891275845649 46825119713983418456884237)
                  ·
                    refine ⟨17559419892743781921331589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46825119713983418456884237 17559419892743781921331589)
                    ·
                      refine ⟨3292391229889459110249673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17559419892743781921331589 3292391229889459110249673)
                      ·
                        rfl

theorem cell23_6411909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_6411909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411909 prefixEnd_6411909 := by exact prefixLift 6411909
  have htrace : WordTrace (prefixWord ++ tailWord_6411909) baseStart_6411909 baseEnd_6411909 := by
    simpa [prefixWord, tailWord_6411909, baseEnd_6411909] using wordTrace_append hprefix tailTrace_6411909
  have hstable : (prefixWord ++ tailWord_6411909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411909).length < 2 ^ (prefixWord ++ tailWord_6411909).sum := by decide
  have hdescent : baseEnd_6411909 < baseStart_6411909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411924 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6411924 : Nat := 118140960795 + 6411924 * 2 ^ 59
def prefixEnd_6411924 : Nat := 4983230072969 + 3 ^ 40 * 6411924 * 2
def baseEnd_6411924 : Nat := 3292398932099276551562105

theorem tailTrace_6411924 : CollatzResearch.WordTrace tailWord_6411924 prefixEnd_6411924 3292398932099276551562105 := by
  unfold tailWord_6411924
  simp only [CollatzResearch.WordTrace]
  refine ⟨116931040411350946140689413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155908053881801261520919217 116931040411350946140689413)
  ·
    refine ⟨21924570077128302401379265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116931040411350946140689413 21924570077128302401379265)
    ·
      refine ⟨16443427557846226801034449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21924570077128302401379265 16443427557846226801034449)
      ·
        refine ⟨12332570668384670100775837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16443427557846226801034449 12332570668384670100775837)
        ·
          refine ⟨4624714000644251287790939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12332570668384670100775837 4624714000644251287790939)
          ·
            refine ⟨6937071000966376931686409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624714000644251287790939 6937071000966376931686409)
            ·
              refine ⟨5202803250724782698764807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6937071000966376931686409 5202803250724782698764807)
              ·
                refine ⟨7804204876087174048147211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202803250724782698764807 7804204876087174048147211)
                ·
                  refine ⟨11706307314130761072220817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804204876087174048147211 11706307314130761072220817)
                  ·
                    refine ⟨8779730485598070804165613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11706307314130761072220817 8779730485598070804165613)
                    ·
                      refine ⟨3292398932099276551562105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8779730485598070804165613 3292398932099276551562105)
                      ·
                        rfl

theorem cell23_6411924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6411924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411924 prefixEnd_6411924 := by exact prefixLift 6411924
  have htrace : WordTrace (prefixWord ++ tailWord_6411924) baseStart_6411924 baseEnd_6411924 := by
    simpa [prefixWord, tailWord_6411924, baseEnd_6411924] using wordTrace_append hprefix tailTrace_6411924
  have hstable : (prefixWord ++ tailWord_6411924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411924).length < 2 ^ (prefixWord ++ tailWord_6411924).sum := by decide
  have hdescent : baseEnd_6411924 < baseStart_6411924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411929 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_6411929 : Nat := 118140960795 + 6411929 * 2 ^ 59
def prefixEnd_6411929 : Nat := 4983230072969 + 3 ^ 40 * 6411929 * 2
def baseEnd_6411929 : Nat := 3292401499502549031999581

theorem tailTrace_6411929 : CollatzResearch.WordTrace tailWord_6411929 prefixEnd_6411929 3292401499502549031999581 := by
  unfold tailWord_6411929
  simp only [CollatzResearch.WordTrace]
  refine ⟨233862263187683778135310841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155908175458455852090207227 233862263187683778135310841)
  ·
    refine ⟨175396697390762833601483131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233862263187683778135310841 175396697390762833601483131)
    ·
      refine ⟨263095046086144250402224697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175396697390762833601483131 263095046086144250402224697)
      ·
        refine ⟨197321284564608187801668523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263095046086144250402224697 197321284564608187801668523)
        ·
          refine ⟨295981926846912281702502785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197321284564608187801668523 295981926846912281702502785)
          ·
            refine ⟨221986445135184211276877089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295981926846912281702502785 221986445135184211276877089)
            ·
              refine ⟨166489833851388158457657817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221986445135184211276877089 166489833851388158457657817)
              ·
                refine ⟨124867375388541118843243363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166489833851388158457657817 124867375388541118843243363)
                ·
                  refine ⟨187301063082811678264865045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124867375388541118843243363 187301063082811678264865045)
                  ·
                    refine ⟨8779737332006797418665549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 187301063082811678264865045 8779737332006797418665549)
                    ·
                      refine ⟨3292401499502549031999581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8779737332006797418665549 3292401499502549031999581)
                      ·
                        rfl

theorem cell23_6411929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_6411929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411929 prefixEnd_6411929 := by exact prefixLift 6411929
  have htrace : WordTrace (prefixWord ++ tailWord_6411929) baseStart_6411929 baseEnd_6411929 := by
    simpa [prefixWord, tailWord_6411929, baseEnd_6411929] using wordTrace_append hprefix tailTrace_6411929
  have hstable : (prefixWord ++ tailWord_6411929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411929).length < 2 ^ (prefixWord ++ tailWord_6411929).sum := by decide
  have hdescent : baseEnd_6411929 < baseStart_6411929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411939 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_6411939 : Nat := 118140960795 + 6411939 * 2 ^ 59
def prefixEnd_6411939 : Nat := 4983230072969 + 3 ^ 40 * 6411939 * 2
def baseEnd_6411939 : Nat := 3292406634309093992874535

theorem tailTrace_6411939 : CollatzResearch.WordTrace tailWord_6411939 prefixEnd_6411939 3292406634309093992874535 := by
  unfold tailWord_6411939
  simp only [CollatzResearch.WordTrace]
  refine ⟨233862627917647549843174871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155908418611765033228783247 233862627917647549843174871)
  ·
    refine ⟨350793941876471324764762307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233862627917647549843174871 350793941876471324764762307)
    ·
      refine ⟨526190912814706987147143461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350793941876471324764762307 526190912814706987147143461)
      ·
        refine ⟨98660796152757560090089399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526190912814706987147143461 98660796152757560090089399)
        ·
          refine ⟨147991194229136340135134099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98660796152757560090089399 147991194229136340135134099)
          ·
            refine ⟨221986791343704510202701149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147991194229136340135134099 221986791343704510202701149)
            ·
              refine ⟨83245046753889191326012931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221986791343704510202701149 83245046753889191326012931)
              ·
                refine ⟨124867570130833786989019397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83245046753889191326012931 124867570130833786989019397)
                ·
                  refine ⟨23412669399531335060441137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124867570130833786989019397 23412669399531335060441137)
                  ·
                    refine ⟨17559502049648501295330853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23412669399531335060441137 17559502049648501295330853)
                    ·
                      refine ⟨3292406634309093992874535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17559502049648501295330853 3292406634309093992874535)
                      ·
                        rfl

theorem cell23_6411939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_6411939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411939 prefixEnd_6411939 := by exact prefixLift 6411939
  have htrace : WordTrace (prefixWord ++ tailWord_6411939) baseStart_6411939 baseEnd_6411939 := by
    simpa [prefixWord, tailWord_6411939, baseEnd_6411939] using wordTrace_append hprefix tailTrace_6411939
  have hstable : (prefixWord ++ tailWord_6411939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411939).length < 2 ^ (prefixWord ++ tailWord_6411939).sum := by decide
  have hdescent : baseEnd_6411939 < baseStart_6411939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411966 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_6411966 : Nat := 118140960795 + 6411966 * 2 ^ 59
def prefixEnd_6411966 : Nat := 4983230072969 + 3 ^ 40 * 6411966 * 2
def baseEnd_6411966 : Nat := 365824499809640598581879

theorem tailTrace_6411966 : CollatzResearch.WordTrace tailWord_6411966 prefixEnd_6411966 365824499809640598581879 := by
  unfold tailWord_6411966
  simp only [CollatzResearch.WordTrace]
  refine ⟨29232951586068716681800969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155909075125699822302938501 29232951586068716681800969)
  ·
    refine ⟨21924713689551537511350727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29232951586068716681800969 21924713689551537511350727)
    ·
      refine ⟨32887070534327306267026091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21924713689551537511350727 32887070534327306267026091)
      ·
        refine ⟨49330605801490959400539137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32887070534327306267026091 49330605801490959400539137)
        ·
          refine ⟨36997954351118219550404353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49330605801490959400539137 36997954351118219550404353)
          ·
            refine ⟨27748465763338664662803265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36997954351118219550404353 27748465763338664662803265)
            ·
              refine ⟨20811349322503998497102449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27748465763338664662803265 20811349322503998497102449)
              ·
                refine ⟨15608511991877998872826837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811349322503998497102449 15608511991877998872826837)
                ·
                  refine ⟨365824499809640598581879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15608511991877998872826837 365824499809640598581879)
                  ·
                    rfl

theorem cell23_6411966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_6411966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411966 prefixEnd_6411966 := by exact prefixLift 6411966
  have htrace : WordTrace (prefixWord ++ tailWord_6411966) baseStart_6411966 baseEnd_6411966 := by
    simpa [prefixWord, tailWord_6411966, baseEnd_6411966] using wordTrace_append hprefix tailTrace_6411966
  have hstable : (prefixWord ++ tailWord_6411966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411966).length < 2 ^ (prefixWord ++ tailWord_6411966).sum := by decide
  have hdescent : baseEnd_6411966 < baseStart_6411966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6411979 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 6, 5]
def baseStart_6411979 : Nat := 118140960795 + 6411979 * 2 ^ 59
def prefixEnd_6411979 : Nat := 4983230072969 + 3 ^ 40 * 6411979 * 2
def baseEnd_6411979 : Nat := 1097475724511757945458117

theorem tailTrace_6411979 : CollatzResearch.WordTrace tailWord_6411979 prefixEnd_6411979 1097475724511757945458117 := by
  unfold tailWord_6411979
  simp only [CollatzResearch.WordTrace]
  refine ⟨233864086837502636674630991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155909391225001757783087327 233864086837502636674630991)
  ·
    refine ⟨350796130256253955011946487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233864086837502636674630991 350796130256253955011946487)
    ·
      refine ⟨526194195384380932517919731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350796130256253955011946487 526194195384380932517919731)
      ·
        refine ⟨789291293076571398776879597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526194195384380932517919731 789291293076571398776879597)
        ·
          refine ⟨295984234903714274541329849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789291293076571398776879597 295984234903714274541329849)
          ·
            refine ⟨221988176177785705905997387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295984234903714274541329849 221988176177785705905997387)
            ·
              refine ⟨332982264266678558858996081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221988176177785705905997387 332982264266678558858996081)
              ·
                refine ⟨249736698200008919144247061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332982264266678558858996081 249736698200008919144247061)
                ·
                  refine ⟨11706407728125418084886581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249736698200008919144247061 11706407728125418084886581)
                  ·
                    refine ⟨1097475724511757945458117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11706407728125418084886581 1097475724511757945458117)
                    ·
                      rfl

theorem cell23_6411979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 5].length) (baseStart_6411979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6411979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6411979 prefixEnd_6411979 := by exact prefixLift 6411979
  have htrace : WordTrace (prefixWord ++ tailWord_6411979) baseStart_6411979 baseEnd_6411979 := by
    simpa [prefixWord, tailWord_6411979, baseEnd_6411979] using wordTrace_append hprefix tailTrace_6411979
  have hstable : (prefixWord ++ tailWord_6411979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6411979).length < 2 ^ (prefixWord ++ tailWord_6411979).sum := by decide
  have hdescent : baseEnd_6411979 < baseStart_6411979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6411979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412026 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_6412026 : Nat := 118140960795 + 6412026 * 2 ^ 59
def prefixEnd_6412026 : Nat := 4983230072969 + 3 ^ 40 * 6412026 * 2
def baseEnd_6412026 : Nat := 1097483769042011717495545

theorem tailTrace_6412026 : CollatzResearch.WordTrace tailWord_6412026 prefixEnd_6412026 1097483769042011717495545 := by
  unfold tailWord_6412026
  simp only [CollatzResearch.WordTrace]
  refine ⟨58466450267083090925397983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155910534045554909134394621 58466450267083090925397983)
  ·
    refine ⟨87699675400624636388096975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58466450267083090925397983 87699675400624636388096975)
    ·
      refine ⟨131549513100936954582145463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87699675400624636388096975 131549513100936954582145463)
      ·
        refine ⟨197324269651405431873218195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131549513100936954582145463 197324269651405431873218195)
        ·
          refine ⟨295986404477108147809827293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197324269651405431873218195 295986404477108147809827293)
          ·
            refine ⟨110994901678915555428685235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295986404477108147809827293 110994901678915555428685235)
            ·
              refine ⟨166492352518373333143027853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110994901678915555428685235 166492352518373333143027853)
              ·
                refine ⟨62434632194389999928635445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166492352518373333143027853 62434632194389999928635445)
                ·
                  refine ⟨5853246768224062493309573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62434632194389999928635445 5853246768224062493309573)
                  ·
                    refine ⟨1097483769042011717495545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853246768224062493309573 1097483769042011717495545)
                    ·
                      rfl

theorem cell23_6412026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_6412026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412026 prefixEnd_6412026 := by exact prefixLift 6412026
  have htrace : WordTrace (prefixWord ++ tailWord_6412026) baseStart_6412026 baseEnd_6412026 := by
    simpa [prefixWord, tailWord_6412026, baseEnd_6412026] using wordTrace_append hprefix tailTrace_6412026
  have hstable : (prefixWord ++ tailWord_6412026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412026).length < 2 ^ (prefixWord ++ tailWord_6412026).sum := by decide
  have hdescent : baseEnd_6412026 < baseStart_6412026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412030 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6412030 : Nat := 118140960795 + 6412030 * 2 ^ 59
def prefixEnd_6412030 : Nat := 4983230072969 + 3 ^ 40 * 6412030 * 2
def baseEnd_6412030 : Nat := 1097484453682884378945539

theorem tailTrace_6412030 : CollatzResearch.WordTrace tailWord_6412030 prefixEnd_6412030 1097484453682884378945539 := by
  unfold tailWord_6412030
  simp only [CollatzResearch.WordTrace]
  refine ⟨29233243370039734048092193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155910631306878581589825029 29233243370039734048092193)
  ·
    refine ⟨21924932527529800536069145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29233243370039734048092193 21924932527529800536069145)
    ·
      refine ⟨16443699395647350402051859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21924932527529800536069145 16443699395647350402051859)
      ·
        refine ⟨24665549093471025603077789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443699395647350402051859 24665549093471025603077789)
        ·
          refine ⟨9249580910051634601154171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24665549093471025603077789 9249580910051634601154171)
          ·
            refine ⟨13874371365077451901731257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249580910051634601154171 13874371365077451901731257)
            ·
              refine ⟨10405778523808088926298443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13874371365077451901731257 10405778523808088926298443)
              ·
                refine ⟨15608667785712133389447665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10405778523808088926298443 15608667785712133389447665)
                ·
                  refine ⟨11706500839284100042085749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15608667785712133389447665 11706500839284100042085749)
                  ·
                    refine ⟨1097484453682884378945539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11706500839284100042085749 1097484453682884378945539)
                    ·
                      rfl

theorem cell23_6412030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6412030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412030 prefixEnd_6412030 := by exact prefixLift 6412030
  have htrace : WordTrace (prefixWord ++ tailWord_6412030) baseStart_6412030 baseEnd_6412030 := by
    simpa [prefixWord, tailWord_6412030, baseEnd_6412030] using wordTrace_append hprefix tailTrace_6412030
  have hstable : (prefixWord ++ tailWord_6412030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412030).length < 2 ^ (prefixWord ++ tailWord_6412030).sum := by decide
  have hdescent : baseEnd_6412030 < baseStart_6412030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412050 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6412050 : Nat := 118140960795 + 6412050 * 2 ^ 59
def prefixEnd_6412050 : Nat := 4983230072969 + 3 ^ 40 * 6412050 * 2
def baseEnd_6412050 : Nat := 3292463630661743058586525

theorem tailTrace_6412050 : CollatzResearch.WordTrace tailWord_6412050 prefixEnd_6412050 3292463630661743058586525 := by
  unfold tailWord_6412050
  simp only [CollatzResearch.WordTrace]
  refine ⟨58466669105061353950116401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155911117613496943866977069 58466669105061353950116401)
  ·
    refine ⟨43850001828796015462587301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58466669105061353950116401 43850001828796015462587301)
    ·
      refine ⟨8221875342899252899235119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43850001828796015462587301 8221875342899252899235119)
      ·
        refine ⟨12332813014348879348852679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8221875342899252899235119 12332813014348879348852679)
        ·
          refine ⟨18499219521523319023279019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12332813014348879348852679 18499219521523319023279019)
          ·
            refine ⟨27748829282284978534918529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18499219521523319023279019 27748829282284978534918529)
            ·
              refine ⟨20811621961713733901188897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27748829282284978534918529 20811621961713733901188897)
              ·
                refine ⟨15608716471285300425891673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811621961713733901188897 15608716471285300425891673)
                ·
                  refine ⟨11706537353463975319418755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15608716471285300425891673 11706537353463975319418755)
                  ·
                    refine ⟨17559806030195962979128133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11706537353463975319418755 17559806030195962979128133)
                    ·
                      refine ⟨3292463630661743058586525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17559806030195962979128133 3292463630661743058586525)
                      ·
                        rfl

theorem cell23_6412050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6412050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412050 prefixEnd_6412050 := by exact prefixLift 6412050
  have htrace : WordTrace (prefixWord ++ tailWord_6412050) baseStart_6412050 baseEnd_6412050 := by
    simpa [prefixWord, tailWord_6412050, baseEnd_6412050] using wordTrace_append hprefix tailTrace_6412050
  have hstable : (prefixWord ++ tailWord_6412050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412050).length < 2 ^ (prefixWord ++ tailWord_6412050).sum := by decide
  have hdescent : baseEnd_6412050 < baseStart_6412050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412053 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_6412053 : Nat := 118140960795 + 6412053 * 2 ^ 59
def prefixEnd_6412053 : Nat := 4983230072969 + 3 ^ 40 * 6412053 * 2
def baseEnd_6412053 : Nat := 3292465171103706546849011

theorem tailTrace_6412053 : CollatzResearch.WordTrace tailWord_6412053 prefixEnd_6412053 3292465171103706546849011 := by
  unfold tailWord_6412053
  simp only [CollatzResearch.WordTrace]
  refine ⟨233866785839234547312824813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155911190559489698208549875 233866785839234547312824813)
  ·
    refine ⟨87700044689712955242309305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233866785839234547312824813 87700044689712955242309305)
    ·
      refine ⟨65775033517284716431731979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87700044689712955242309305 65775033517284716431731979)
      ·
        refine ⟨98662550275927074647597969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65775033517284716431731979 98662550275927074647597969)
        ·
          refine ⟨73996912706945305985698477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98662550275927074647597969 73996912706945305985698477)
          ·
            refine ⟨27748842265104489744636929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73996912706945305985698477 27748842265104489744636929)
            ·
              refine ⟨20811631698828367308477697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27748842265104489744636929 20811631698828367308477697)
              ·
                refine ⟨15608723774121275481358273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811631698828367308477697 15608723774121275481358273)
                ·
                  refine ⟨11706542830590956611018705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15608723774121275481358273 11706542830590956611018705)
                  ·
                    refine ⟨8779907122943217458264029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11706542830590956611018705 8779907122943217458264029)
                    ·
                      refine ⟨3292465171103706546849011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8779907122943217458264029 3292465171103706546849011)
                      ·
                        rfl

theorem cell23_6412053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_6412053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412053 prefixEnd_6412053 := by exact prefixLift 6412053
  have htrace : WordTrace (prefixWord ++ tailWord_6412053) baseStart_6412053 baseEnd_6412053 := by
    simpa [prefixWord, tailWord_6412053, baseEnd_6412053] using wordTrace_append hprefix tailTrace_6412053
  have hstable : (prefixWord ++ tailWord_6412053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412053).length < 2 ^ (prefixWord ++ tailWord_6412053).sum := by decide
  have hdescent : baseEnd_6412053 < baseStart_6412053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412056 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 6]
def baseStart_6412056 : Nat := 118140960795 + 6412056 * 2 ^ 59
def prefixEnd_6412056 : Nat := 4983230072969 + 3 ^ 40 * 6412056 * 2
def baseEnd_6412056 : Nat := 365829634616185559456833

theorem tailTrace_6412056 : CollatzResearch.WordTrace tailWord_6412056 prefixEnd_6412056 365829634616185559456833 := by
  unfold tailWord_6412056
  simp only [CollatzResearch.WordTrace]
  refine ⟨116933447629111839412592011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155911263505482452550122681 116933447629111839412592011)
  ·
    refine ⟨175400171443667759118888017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116933447629111839412592011 175400171443667759118888017)
    ·
      refine ⟨131550128582750819339166013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175400171443667759118888017 131550128582750819339166013)
      ·
        refine ⟨49331298218531557252187255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131550128582750819339166013 49331298218531557252187255)
        ·
          refine ⟨73996947327797335878280883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49331298218531557252187255 73996947327797335878280883)
          ·
            refine ⟨110995420991696003817421325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73996947327797335878280883 110995420991696003817421325)
            ·
              refine ⟨41623282871886001431532997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110995420991696003817421325 41623282871886001431532997)
              ·
                refine ⟨7804365538478625268412437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41623282871886001431532997 7804365538478625268412437)
                ·
                  refine ⟨365829634616185559456833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7804365538478625268412437 365829634616185559456833)
                  ·
                    rfl

theorem cell23_6412056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_6412056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412056 prefixEnd_6412056 := by exact prefixLift 6412056
  have htrace : WordTrace (prefixWord ++ tailWord_6412056) baseStart_6412056 baseEnd_6412056 := by
    simpa [prefixWord, tailWord_6412056, baseEnd_6412056] using wordTrace_append hprefix tailTrace_6412056
  have hstable : (prefixWord ++ tailWord_6412056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412056).length < 2 ^ (prefixWord ++ tailWord_6412056).sum := by decide
  have hdescent : baseEnd_6412056 < baseStart_6412056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_6412059 : Nat := 118140960795 + 6412059 * 2 ^ 59
def prefixEnd_6412059 : Nat := 4983230072969 + 3 ^ 40 * 6412059 * 2
def baseEnd_6412059 : Nat := 3292468251987633523373983

theorem tailTrace_6412059 : CollatzResearch.WordTrace tailWord_6412059 prefixEnd_6412059 3292468251987633523373983 := by
  unfold tailWord_6412059
  simp only [CollatzResearch.WordTrace]
  refine ⟨233867004677212810337543231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155911336451475206891695487 233867004677212810337543231)
  ·
    refine ⟨350800507015819215506314847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233867004677212810337543231 350800507015819215506314847)
    ·
      refine ⟨526200760523728823259472271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350800507015819215506314847 526200760523728823259472271)
      ·
        refine ⟨789301140785593234889208407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526200760523728823259472271 789301140785593234889208407)
        ·
          refine ⟨1183951711178389852333812611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789301140785593234889208407 1183951711178389852333812611)
          ·
            refine ⟨1775927566767584778500718917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183951711178389852333812611 1775927566767584778500718917)
            ·
              refine ⟨332986418768922145968884797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1775927566767584778500718917 332986418768922145968884797)
              ·
                refine ⟨124869907038345804738331799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332986418768922145968884797 124869907038345804738331799)
                ·
                  refine ⟨187304860557518707107497699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124869907038345804738331799 187304860557518707107497699)
                  ·
                    refine ⟨280957290836278060661246549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187304860557518707107497699 280957290836278060661246549)
                    ·
                      refine ⟨3292468251987633523373983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280957290836278060661246549 3292468251987633523373983)
                      ·
                        rfl

theorem cell23_6412059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_6412059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412059 prefixEnd_6412059 := by exact prefixLift 6412059
  have htrace : WordTrace (prefixWord ++ tailWord_6412059) baseStart_6412059 baseEnd_6412059 := by
    simpa [prefixWord, tailWord_6412059, baseEnd_6412059] using wordTrace_append hprefix tailTrace_6412059
  have hstable : (prefixWord ++ tailWord_6412059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412059).length < 2 ^ (prefixWord ++ tailWord_6412059).sum := by decide
  have hdescent : baseEnd_6412059 < baseStart_6412059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412060 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_6412060 : Nat := 118140960795 + 6412060 * 2 ^ 59
def prefixEnd_6412060 : Nat := 4983230072969 + 3 ^ 40 * 6412060 * 2
def baseEnd_6412060 : Nat := 1097489588489429339820493

theorem tailTrace_6412060 : CollatzResearch.WordTrace tailWord_6412060 prefixEnd_6412060 1097489588489429339820493 := by
  unfold tailWord_6412060
  simp only [CollatzResearch.WordTrace]
  refine ⟨116933520575104593754164817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155911360766806125005553089 116933520575104593754164817)
  ·
    refine ⟨87700140431328445315623613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116933520575104593754164817 87700140431328445315623613)
    ·
      refine ⟨32887552661748166993358855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87700140431328445315623613 32887552661748166993358855)
      ·
        refine ⟨49331328992622250490038283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32887552661748166993358855 49331328992622250490038283)
        ·
          refine ⟨73996993488933375735057425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49331328992622250490038283 73996993488933375735057425)
          ·
            refine ⟨55497745116700031801293069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73996993488933375735057425 55497745116700031801293069)
            ·
              refine ⟨20811654418762511925484901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55497745116700031801293069 20811654418762511925484901)
              ·
                refine ⟨3902185203517970986028419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20811654418762511925484901 3902185203517970986028419)
                ·
                  refine ⟨5853277805276956479042629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902185203517970986028419 5853277805276956479042629)
                  ·
                    refine ⟨1097489588489429339820493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853277805276956479042629 1097489588489429339820493)
                    ·
                      rfl

theorem cell23_6412060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_6412060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412060 prefixEnd_6412060 := by exact prefixLift 6412060
  have htrace : WordTrace (prefixWord ++ tailWord_6412060) baseStart_6412060 baseEnd_6412060 := by
    simpa [prefixWord, tailWord_6412060, baseEnd_6412060] using wordTrace_append hprefix tailTrace_6412060
  have hstable : (prefixWord ++ tailWord_6412060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412060).length < 2 ^ (prefixWord ++ tailWord_6412060).sum := by decide
  have hdescent : baseEnd_6412060 < baseStart_6412060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412117 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6412117 : Nat := 118140960795 + 6412117 * 2 ^ 59
def prefixEnd_6412117 : Nat := 4983230072969 + 3 ^ 40 * 6412117 * 2
def baseEnd_6412117 : Nat := 3292498033865594296448717

theorem tailTrace_6412117 : CollatzResearch.WordTrace tailWord_6412117 prefixEnd_6412117 3292498033865594296448717 := by
  unfold tailWord_6412117
  simp only [CollatzResearch.WordTrace]
  refine ⟨233869120111002686243154605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155912746740668457495436403 233869120111002686243154605)
  ·
    refine ⟨87700920041626007341182977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233869120111002686243154605 87700920041626007341182977)
    ·
      refine ⟨65775690031219505505887233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87700920041626007341182977 65775690031219505505887233)
      ·
        refine ⟨49331767523414629129415425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65775690031219505505887233 49331767523414629129415425)
        ·
          refine ⟨36998825642560971847061569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49331767523414629129415425 36998825642560971847061569)
          ·
            refine ⟨27749119231920728885296177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36998825642560971847061569 27749119231920728885296177)
            ·
              refine ⟨20811839423940546663972133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27749119231920728885296177 20811839423940546663972133)
              ·
                refine ⟨3902219891988852499494775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20811839423940546663972133 3902219891988852499494775)
                ·
                  refine ⟨5853329837983278749242163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902219891988852499494775 5853329837983278749242163)
                  ·
                    refine ⟨8779994756974918123863245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5853329837983278749242163 8779994756974918123863245)
                    ·
                      refine ⟨3292498033865594296448717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8779994756974918123863245 3292498033865594296448717)
                      ·
                        rfl

theorem cell23_6412117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6412117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412117 prefixEnd_6412117 := by exact prefixLift 6412117
  have htrace : WordTrace (prefixWord ++ tailWord_6412117) baseStart_6412117 baseEnd_6412117 := by
    simpa [prefixWord, tailWord_6412117, baseEnd_6412117] using wordTrace_append hprefix tailTrace_6412117
  have hstable : (prefixWord ++ tailWord_6412117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412117).length < 2 ^ (prefixWord ++ tailWord_6412117).sum := by decide
  have hdescent : baseEnd_6412117 < baseStart_6412117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412140 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_6412140 : Nat := 118140960795 + 6412140 * 2 ^ 59
def prefixEnd_6412140 : Nat := 4983230072969 + 3 ^ 40 * 6412140 * 2
def baseEnd_6412140 : Nat := 3292509843920647706461111

theorem tailTrace_6412140 : CollatzResearch.WordTrace tailWord_6412140 prefixEnd_6412140 3292509843920647706461111 := by
  unfold tailWord_6412140
  simp only [CollatzResearch.WordTrace]
  refine ⟨116934979494959680585620937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155913305993279574114161249 116934979494959680585620937)
  ·
    refine ⟨87701234621219760439215703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116934979494959680585620937 87701234621219760439215703)
    ·
      refine ⟨131551851931829640658823555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87701234621219760439215703 131551851931829640658823555)
      ·
        refine ⟨197327777897744460988235333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131551851931829640658823555 197327777897744460988235333)
        ·
          refine ⟨36998958355827086435294125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197327777897744460988235333 36998958355827086435294125)
          ·
            refine ⟨13874609383435157413235297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36998958355827086435294125 13874609383435157413235297)
            ·
              refine ⟨10405957037576368059926473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13874609383435157413235297 10405957037576368059926473)
              ·
                refine ⟨7804467778182276044944855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10405957037576368059926473 7804467778182276044944855)
                ·
                  refine ⟨11706701667273414067417283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804467778182276044944855 11706701667273414067417283)
                  ·
                    refine ⟨17560052500910121101125925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11706701667273414067417283 17560052500910121101125925)
                    ·
                      refine ⟨3292509843920647706461111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17560052500910121101125925 3292509843920647706461111)
                      ·
                        rfl

theorem cell23_6412140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_6412140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412140 prefixEnd_6412140 := by exact prefixLift 6412140
  have htrace : WordTrace (prefixWord ++ tailWord_6412140) baseStart_6412140 baseEnd_6412140 := by
    simpa [prefixWord, tailWord_6412140, baseEnd_6412140] using wordTrace_append hprefix tailTrace_6412140
  have hstable : (prefixWord ++ tailWord_6412140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412140).length < 2 ^ (prefixWord ++ tailWord_6412140).sum := by decide
  have hdescent : baseEnd_6412140 < baseStart_6412140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412194 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_6412194 : Nat := 118140960795 + 6412194 * 2 ^ 59
def prefixEnd_6412194 : Nat := 4983230072969 + 3 ^ 40 * 6412194 * 2
def baseEnd_6412194 : Nat := 3292537571875990495185863

theorem tailTrace_6412194 : CollatzResearch.WordTrace tailWord_6412194 prefixEnd_6412194 3292537571875990495185863 := by
  unfold tailWord_6412194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58467982132930932098426909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155914619021149152262471757 58467982132930932098426909)
  ·
    refine ⟨21925493299849099536910091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58467982132930932098426909 21925493299849099536910091)
    ·
      refine ⟨32888239949773649305365137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21925493299849099536910091 32888239949773649305365137)
      ·
        refine ⟨24666179962330236979023853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32888239949773649305365137 24666179962330236979023853)
        ·
          refine ⟨9249817485873838867133945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24666179962330236979023853 9249817485873838867133945)
          ·
            refine ⟨6937363114405379150350459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9249817485873838867133945 6937363114405379150350459)
            ·
              refine ⟨10406044671608068725525689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6937363114405379150350459 10406044671608068725525689)
              ·
                refine ⟨7804533503706051544144267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10406044671608068725525689 7804533503706051544144267)
                ·
                  refine ⟨11706800255559077316216401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804533503706051544144267 11706800255559077316216401)
                  ·
                    refine ⟨8780100191669307987162301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11706800255559077316216401 8780100191669307987162301)
                    ·
                      refine ⟨3292537571875990495185863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8780100191669307987162301 3292537571875990495185863)
                      ·
                        rfl

theorem cell23_6412194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_6412194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412194 prefixEnd_6412194 := by exact prefixLift 6412194
  have htrace : WordTrace (prefixWord ++ tailWord_6412194) baseStart_6412194 baseEnd_6412194 := by
    simpa [prefixWord, tailWord_6412194, baseEnd_6412194] using wordTrace_append hprefix tailTrace_6412194
  have hstable : (prefixWord ++ tailWord_6412194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412194).length < 2 ^ (prefixWord ++ tailWord_6412194).sum := by decide
  have hdescent : baseEnd_6412194 < baseStart_6412194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412247 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_6412247 : Nat := 118140960795 + 6412247 * 2 ^ 59
def prefixEnd_6412247 : Nat := 4983230072969 + 3 ^ 40 * 6412247 * 2
def baseEnd_6412247 : Nat := 3292564786350678787823119

theorem tailTrace_6412247 : CollatzResearch.WordTrace tailWord_6412247 prefixEnd_6412247 3292564786350678787823119 := by
  unfold tailWord_6412247
  simp only [CollatzResearch.WordTrace]
  refine ⟨233873861600531718445386995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155915907733687812296924663 233873861600531718445386995)
  ·
    refine ⟨350810792400797577668080493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233873861600531718445386995 350810792400797577668080493)
    ·
      refine ⟨131554047150299091625530185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350810792400797577668080493 131554047150299091625530185)
      ·
        refine ⟨98665535362724318719147639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131554047150299091625530185 98665535362724318719147639)
        ·
          refine ⟨147998303044086478078721459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98665535362724318719147639 147998303044086478078721459)
          ·
            refine ⟨221997454566129717118082189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147998303044086478078721459 221997454566129717118082189)
            ·
              refine ⟨83249045462298643919280821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221997454566129717118082189 83249045462298643919280821)
              ·
                refine ⟨7804598012090497867432577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83249045462298643919280821 7804598012090497867432577)
                ·
                  refine ⟨5853448509067873400574433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7804598012090497867432577 5853448509067873400574433)
                  ·
                    refine ⟨4390086381800905050430825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5853448509067873400574433 4390086381800905050430825)
                    ·
                      refine ⟨3292564786350678787823119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390086381800905050430825 3292564786350678787823119)
                      ·
                        rfl

theorem cell23_6412247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_6412247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412247 prefixEnd_6412247 := by exact prefixLift 6412247
  have htrace : WordTrace (prefixWord ++ tailWord_6412247) baseStart_6412247 baseEnd_6412247 := by
    simpa [prefixWord, tailWord_6412247, baseEnd_6412247] using wordTrace_append hprefix tailTrace_6412247
  have hstable : (prefixWord ++ tailWord_6412247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412247).length < 2 ^ (prefixWord ++ tailWord_6412247).sum := by decide
  have hdescent : baseEnd_6412247 < baseStart_6412247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412283 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 2, 5]
def baseStart_6412283 : Nat := 118140960795 + 6412283 * 2 ^ 59
def prefixEnd_6412283 : Nat := 4983230072969 + 3 ^ 40 * 6412283 * 2
def baseEnd_6412283 : Nat := 1097527757218080215657651

theorem tailTrace_6412283 : CollatzResearch.WordTrace tailWord_6412283 prefixEnd_6412283 1097527757218080215657651 := by
  unfold tailWord_6412283
  simp only [CollatzResearch.WordTrace]
  refine ⟨233875174628401296593697503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155916783085600864395798335 233875174628401296593697503)
  ·
    refine ⟨350812761942601944890546255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233875174628401296593697503 350812761942601944890546255)
    ·
      refine ⟨526219142913902917335819383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350812761942601944890546255 526219142913902917335819383)
      ·
        refine ⟨789328714370854376003729075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526219142913902917335819383 789328714370854376003729075)
        ·
          refine ⟨1183993071556281564005593613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789328714370854376003729075 1183993071556281564005593613)
          ·
            refine ⟨443997401833605586502097605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1183993071556281564005593613 443997401833605586502097605)
            ·
              refine ⟨83249512843801047469143301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443997401833605586502097605 83249512843801047469143301)
              ·
                refine ⟨15609283658212696400464369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83249512843801047469143301 15609283658212696400464369)
                ·
                  refine ⟨11706962743659522300348277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15609283658212696400464369 11706962743659522300348277)
                  ·
                    refine ⟨1097527757218080215657651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11706962743659522300348277 1097527757218080215657651)
                    ·
                      rfl

theorem cell23_6412283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 5].length) (baseStart_6412283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412283 prefixEnd_6412283 := by exact prefixLift 6412283
  have htrace : WordTrace (prefixWord ++ tailWord_6412283) baseStart_6412283 baseEnd_6412283 := by
    simpa [prefixWord, tailWord_6412283, baseEnd_6412283] using wordTrace_append hprefix tailTrace_6412283
  have hstable : (prefixWord ++ tailWord_6412283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412283).length < 2 ^ (prefixWord ++ tailWord_6412283).sum := by decide
  have hdescent : baseEnd_6412283 < baseStart_6412283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412343 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 8]
def baseStart_6412343 : Nat := 118140960795 + 6412343 * 2 ^ 59
def prefixEnd_6412343 : Nat := 4983230072969 + 3 ^ 40 * 6412343 * 2
def baseEnd_6412343 : Nat := 365846008943723379135853

theorem tailTrace_6412343 : CollatzResearch.WordTrace tailWord_6412343 prefixEnd_6412343 365846008943723379135853 := by
  unfold tailWord_6412343
  simp only [CollatzResearch.WordTrace]
  refine ⟨233877363008183926840881683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155918242005455951227254455 233877363008183926840881683)
  ·
    refine ⟨350816044512275890261322525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233877363008183926840881683 350816044512275890261322525)
    ·
      refine ⟨131556016692103458847995947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350816044512275890261322525 131556016692103458847995947)
      ·
        refine ⟨197334025038155188271993921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131556016692103458847995947 197334025038155188271993921)
        ·
          refine ⟨148000518778616391203995441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197334025038155188271993921 148000518778616391203995441)
          ·
            refine ⟨111000389083962293402996581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148000518778616391203995441 111000389083962293402996581)
            ·
              refine ⟨20812572953242930013061859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111000389083962293402996581 20812572953242930013061859)
              ·
                refine ⟨31218859429864395019592789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20812572953242930013061859 31218859429864395019592789)
                ·
                  refine ⟨365846008943723379135853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31218859429864395019592789 365846008943723379135853)
                  ·
                    rfl

theorem cell23_6412343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 8].length) (baseStart_6412343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412343 prefixEnd_6412343 := by exact prefixLift 6412343
  have htrace : WordTrace (prefixWord ++ tailWord_6412343) baseStart_6412343 baseEnd_6412343 := by
    simpa [prefixWord, tailWord_6412343, baseEnd_6412343] using wordTrace_append hprefix tailTrace_6412343
  have hstable : (prefixWord ++ tailWord_6412343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412343).length < 2 ^ (prefixWord ++ tailWord_6412343).sum := by decide
  have hdescent : baseEnd_6412343 < baseStart_6412343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412383 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_6412383 : Nat := 118140960795 + 6412383 * 2 ^ 59
def prefixEnd_6412383 : Nat := 4983230072969 + 3 ^ 40 * 6412383 * 2
def baseEnd_6412383 : Nat := 3292634619719690255722493

theorem tailTrace_6412383 : CollatzResearch.WordTrace tailWord_6412383 prefixEnd_6412383 3292634619719690255722493 := by
  unfold tailWord_6412383
  simp only [CollatzResearch.WordTrace]
  refine ⟨233878821928039013672337803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155919214618692675781558535 233878821928039013672337803)
  ·
    refine ⟨350818232892058520508506705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233878821928039013672337803 350818232892058520508506705)
    ·
      refine ⟨263113674669043890381380029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350818232892058520508506705 263113674669043890381380029)
      ·
        refine ⟨98667628000891458893017511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263113674669043890381380029 98667628000891458893017511)
        ·
          refine ⟨148001442001337188339526267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98667628000891458893017511 148001442001337188339526267)
          ·
            refine ⟨222002163002005782509289401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148001442001337188339526267 222002163002005782509289401)
            ·
              refine ⟨166501622251504336881967051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222002163002005782509289401 166501622251504336881967051)
              ·
                refine ⟨249752433377256505322950577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166501622251504336881967051 249752433377256505322950577)
                ·
                  refine ⟨187314325032942378992212933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249752433377256505322950577 187314325032942378992212933)
                  ·
                    refine ⟨35121435943676696061039925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187314325032942378992212933 35121435943676696061039925)
                    ·
                      refine ⟨3292634619719690255722493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35121435943676696061039925 3292634619719690255722493)
                      ·
                        rfl

theorem cell23_6412383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_6412383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412383 prefixEnd_6412383 := by exact prefixLift 6412383
  have htrace : WordTrace (prefixWord ++ tailWord_6412383) baseStart_6412383 baseEnd_6412383 := by
    simpa [prefixWord, tailWord_6412383, baseEnd_6412383] using wordTrace_append hprefix tailTrace_6412383
  have hstable : (prefixWord ++ tailWord_6412383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412383).length < 2 ^ (prefixWord ++ tailWord_6412383).sum := by decide
  have hdescent : baseEnd_6412383 < baseStart_6412383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412444 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6412444 : Nat := 118140960795 + 6412444 * 2 ^ 59
def prefixEnd_6412444 : Nat := 4983230072969 + 3 ^ 40 * 6412444 * 2
def baseEnd_6412444 : Nat := 3292665942039614517059713

theorem tailTrace_6412444 : CollatzResearch.WordTrace tailWord_6412444 prefixEnd_6412444 3292665942039614517059713 := by
  unfold tailWord_6412444
  simp only [CollatzResearch.WordTrace]
  refine ⟨116940523390409010545154193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155920697853878680726872257 116940523390409010545154193)
  ·
    refine ⟨87705392542806757908865645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116940523390409010545154193 87705392542806757908865645)
    ·
      refine ⟨32889522203552534215824617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87705392542806757908865645 32889522203552534215824617)
      ·
        refine ⟨24667141652664400661868463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32889522203552534215824617 24667141652664400661868463)
        ·
          refine ⟨37000712478996600992802695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24667141652664400661868463 37000712478996600992802695)
          ·
            refine ⟨55501068718494901489204043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37000712478996600992802695 55501068718494901489204043)
            ·
              refine ⟨83251603077742352233806065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55501068718494901489204043 83251603077742352233806065)
              ·
                refine ⟨62438702308306764175354549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83251603077742352233806065 62438702308306764175354549)
                ·
                  refine ⟨5853628341403759141439489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62438702308306764175354549 5853628341403759141439489)
                  ·
                    refine ⟨4390221256052819356079617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5853628341403759141439489 4390221256052819356079617)
                    ·
                      refine ⟨3292665942039614517059713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390221256052819356079617 3292665942039614517059713)
                      ·
                        rfl

theorem cell23_6412444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6412444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412444 prefixEnd_6412444 := by exact prefixLift 6412444
  have htrace : WordTrace (prefixWord ++ tailWord_6412444) baseStart_6412444 baseEnd_6412444 := by
    simpa [prefixWord, tailWord_6412444, baseEnd_6412444] using wordTrace_append hprefix tailTrace_6412444
  have hstable : (prefixWord ++ tailWord_6412444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412444).length < 2 ^ (prefixWord ++ tailWord_6412444).sum := by decide
  have hdescent : baseEnd_6412444 < baseStart_6412444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412461 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_6412461 : Nat := 118140960795 + 6412461 * 2 ^ 59
def prefixEnd_6412461 : Nat := 4983230072969 + 3 ^ 40 * 6412461 * 2
def baseEnd_6412461 : Nat := 3292674671210740950547135

theorem tailTrace_6412461 : CollatzResearch.WordTrace tailWord_6412461 prefixEnd_6412461 3292674671210740950547135 := by
  unfold tailWord_6412461
  simp only [CollatzResearch.WordTrace]
  refine ⟨233881666821756432993677237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155921111214504288662451491 233881666821756432993677237)
  ·
    refine ⟨21926406264539665593157241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233881666821756432993677237 21926406264539665593157241)
    ·
      refine ⟨16444804698404749194867931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21926406264539665593157241 16444804698404749194867931)
      ·
        refine ⟨24667207047607123792301897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444804698404749194867931 24667207047607123792301897)
        ·
          refine ⟨18500405285705342844226423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24667207047607123792301897 18500405285705342844226423)
          ·
            refine ⟨27750607928558014266339635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18500405285705342844226423 27750607928558014266339635)
            ·
              refine ⟨41625911892837021399509453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27750607928558014266339635 41625911892837021399509453)
              ·
                refine ⟨15609716959813883024816045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41625911892837021399509453 15609716959813883024816045)
                ·
                  refine ⟨5853643859930206134306017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15609716959813883024816045 5853643859930206134306017)
                  ·
                    refine ⟨4390232894947654600729513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5853643859930206134306017 4390232894947654600729513)
                    ·
                      refine ⟨3292674671210740950547135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390232894947654600729513 3292674671210740950547135)
                      ·
                        rfl

theorem cell23_6412461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_6412461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412461 prefixEnd_6412461 := by exact prefixLift 6412461
  have htrace : WordTrace (prefixWord ++ tailWord_6412461) baseStart_6412461 baseEnd_6412461 := by
    simpa [prefixWord, tailWord_6412461, baseEnd_6412461] using wordTrace_append hprefix tailTrace_6412461
  have hstable : (prefixWord ++ tailWord_6412461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412461).length < 2 ^ (prefixWord ++ tailWord_6412461).sum := by decide
  have hdescent : baseEnd_6412461 < baseStart_6412461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412484 : List Nat := [2, 3, 3, 1, 2, 3, 2, 7]
def baseStart_6412484 : Nat := 118140960795 + 6412484 * 2 ^ 59
def prefixEnd_6412484 : Nat := 4983230072969 + 3 ^ 40 * 6412484 * 2
def baseEnd_6412484 : Nat := 121951351157992383724427

theorem tailTrace_6412484 : CollatzResearch.WordTrace tailWord_6412484 prefixEnd_6412484 121951351157992383724427 := by
  unfold tailWord_6412484
  simp only [CollatzResearch.WordTrace]
  refine ⟨116941252850336553960882253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155921670467115405281176337 116941252850336553960882253)
  ·
    refine ⟨43852969818876207735330845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116941252850336553960882253 43852969818876207735330845)
    ·
      refine ⟨16444863682078577900749067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43852969818876207735330845 16444863682078577900749067)
      ·
        refine ⟨24667295523117866851123601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444863682078577900749067 24667295523117866851123601)
        ·
          refine ⟨18500471642338400138342701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24667295523117866851123601 18500471642338400138342701)
          ·
            refine ⟨6937676865876900051878513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18500471642338400138342701 6937676865876900051878513)
            ·
              refine ⟨5203257649407675038908885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6937676865876900051878513 5203257649407675038908885)
              ·
                refine ⟨121951351157992383724427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5203257649407675038908885 121951351157992383724427)
                ·
                  rfl

theorem cell23_6412484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 7].length) (baseStart_6412484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412484 prefixEnd_6412484 := by exact prefixLift 6412484
  have htrace : WordTrace (prefixWord ++ tailWord_6412484) baseStart_6412484 baseEnd_6412484 := by
    simpa [prefixWord, tailWord_6412484, baseEnd_6412484] using wordTrace_append hprefix tailTrace_6412484
  have hstable : (prefixWord ++ tailWord_6412484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412484).length < 2 ^ (prefixWord ++ tailWord_6412484).sum := by decide
  have hdescent : baseEnd_6412484 < baseStart_6412484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412490 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_6412490 : Nat := 118140960795 + 6412490 * 2 ^ 59
def prefixEnd_6412490 : Nat := 4983230072969 + 3 ^ 40 * 6412490 * 2
def baseEnd_6412490 : Nat := 3292689562149721337084501

theorem tailTrace_6412490 : CollatzResearch.WordTrace tailWord_6412490 prefixEnd_6412490 3292689562149721337084501 := by
  unfold tailWord_6412490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58470681134662842736620731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155921816359100913964321949 58470681134662842736620731)
  ·
    refine ⟨87706021701994264104931097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58470681134662842736620731 87706021701994264104931097)
    ·
      refine ⟨65779516276495698078698323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87706021701994264104931097 65779516276495698078698323)
      ·
        refine ⟨98669274414743547118047485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65779516276495698078698323 98669274414743547118047485)
        ·
          refine ⟨37000977905528830169267807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98669274414743547118047485 37000977905528830169267807)
          ·
            refine ⟨55501466858293245253901711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37000977905528830169267807 55501466858293245253901711)
            ·
              refine ⟨83252200287439867880852567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55501466858293245253901711 83252200287439867880852567)
              ·
                refine ⟨124878300431159801821278851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83252200287439867880852567 124878300431159801821278851)
                ·
                  refine ⟨187317450646739702731918277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124878300431159801821278851 187317450646739702731918277)
                  ·
                    refine ⟨35122021996263694262234677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187317450646739702731918277 35122021996263694262234677)
                    ·
                      refine ⟨3292689562149721337084501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35122021996263694262234677 3292689562149721337084501)
                      ·
                        rfl

theorem cell23_6412490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_6412490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412490 prefixEnd_6412490 := by exact prefixLift 6412490
  have htrace : WordTrace (prefixWord ++ tailWord_6412490) baseStart_6412490 baseEnd_6412490 := by
    simpa [prefixWord, tailWord_6412490, baseEnd_6412490] using wordTrace_append hprefix tailTrace_6412490
  have hstable : (prefixWord ++ tailWord_6412490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412490).length < 2 ^ (prefixWord ++ tailWord_6412490).sum := by decide
  have hdescent : baseEnd_6412490 < baseStart_6412490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412494 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_6412494 : Nat := 118140960795 + 6412494 * 2 ^ 59
def prefixEnd_6412494 : Nat := 4983230072969 + 3 ^ 40 * 6412494 * 2
def baseEnd_6412494 : Nat := 3292691616072339321434483

theorem tailTrace_6412494 : CollatzResearch.WordTrace tailWord_6412494 prefixEnd_6412494 3292691616072339321434483 := by
  unfold tailWord_6412494
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235358803829609953703567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155921913620424586419752357 29235358803829609953703567)
  ·
    refine ⟨43853038205744414930555351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29235358803829609953703567 43853038205744414930555351)
    ·
      refine ⟨65779557308616622395833027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43853038205744414930555351 65779557308616622395833027)
      ·
        refine ⟨98669335962924933593749541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65779557308616622395833027 98669335962924933593749541)
        ·
          refine ⟨18500500493048425048828039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98669335962924933593749541 18500500493048425048828039)
          ·
            refine ⟨27750750739572637573242059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18500500493048425048828039 27750750739572637573242059)
            ·
              refine ⟨41626126109358956359863089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27750750739572637573242059 41626126109358956359863089)
              ·
                refine ⟨31219594582019217269897317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41626126109358956359863089 31219594582019217269897317)
                ·
                  refine ⟨5853673984128603238105747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31219594582019217269897317 5853673984128603238105747)
                  ·
                    refine ⟨8780510976192904857158621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5853673984128603238105747 8780510976192904857158621)
                    ·
                      refine ⟨3292691616072339321434483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8780510976192904857158621 3292691616072339321434483)
                      ·
                        rfl

theorem cell23_6412494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_6412494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412494 prefixEnd_6412494 := by exact prefixLift 6412494
  have htrace : WordTrace (prefixWord ++ tailWord_6412494) baseStart_6412494 baseEnd_6412494 := by
    simpa [prefixWord, tailWord_6412494, baseEnd_6412494] using wordTrace_append hprefix tailTrace_6412494
  have hstable : (prefixWord ++ tailWord_6412494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412494).length < 2 ^ (prefixWord ++ tailWord_6412494).sum := by decide
  have hdescent : baseEnd_6412494 < baseStart_6412494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412607 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_6412607 : Nat := 118140960795 + 6412607 * 2 ^ 59
def prefixEnd_6412607 : Nat := 4983230072969 + 3 ^ 40 * 6412607 * 2
def baseEnd_6412607 : Nat := 3292749639386297379321463

theorem tailTrace_6412607 : CollatzResearch.WordTrace tailWord_6412607 prefixEnd_6412607 3292749639386297379321463 := by
  unfold tailWord_6412607
  simp only [CollatzResearch.WordTrace]
  refine ⟨233886991879227499928492075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155924661252818333285661383 233886991879227499928492075)
  ·
    refine ⟨350830487818841249892738113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233886991879227499928492075 350830487818841249892738113)
    ·
      refine ⟨263122865864130937419553585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350830487818841249892738113 263122865864130937419553585)
      ·
        refine ⟨197342149398098203064665189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263122865864130937419553585 197342149398098203064665189)
        ·
          refine ⟨37001653012143413074624723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197342149398098203064665189 37001653012143413074624723)
          ·
            refine ⟨55502479518215119611937085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37001653012143413074624723 55502479518215119611937085)
            ·
              refine ⟨20813429819330669854476407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55502479518215119611937085 20813429819330669854476407)
              ·
                refine ⟨31220144728996004781714611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20813429819330669854476407 31220144728996004781714611)
                ·
                  refine ⟨46830217093494007172571917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31220144728996004781714611 46830217093494007172571917)
                  ·
                    refine ⟨17561331410060252689714469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46830217093494007172571917 17561331410060252689714469)
                    ·
                      refine ⟨3292749639386297379321463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17561331410060252689714469 3292749639386297379321463)
                      ·
                        rfl

theorem cell23_6412607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_6412607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412607 prefixEnd_6412607 := by exact prefixLift 6412607
  have htrace : WordTrace (prefixWord ++ tailWord_6412607) baseStart_6412607 baseEnd_6412607 := by
    simpa [prefixWord, tailWord_6412607, baseEnd_6412607] using wordTrace_append hprefix tailTrace_6412607
  have hstable : (prefixWord ++ tailWord_6412607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412607).length < 2 ^ (prefixWord ++ tailWord_6412607).sum := by decide
  have hdescent : baseEnd_6412607 < baseStart_6412607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412617 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_6412617 : Nat := 118140960795 + 6412617 * 2 ^ 59
def prefixEnd_6412617 : Nat := 4983230072969 + 3 ^ 40 * 6412617 * 2
def baseEnd_6412617 : Nat := 1097584924730947446732139

theorem tailTrace_6412617 : CollatzResearch.WordTrace tailWord_6412617 prefixEnd_6412617 1097584924730947446732139 := by
  unfold tailWord_6412617
  simp only [CollatzResearch.WordTrace]
  refine ⟨233887356609191271636356105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155924904406127514424237403 233887356609191271636356105)
  ·
    refine ⟨175415517456893453727267079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233887356609191271636356105 175415517456893453727267079)
    ·
      refine ⟨263123276185340180590900619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175415517456893453727267079 263123276185340180590900619)
      ·
        refine ⟨394684914278010270886350929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263123276185340180590900619 394684914278010270886350929)
        ·
          refine ⟨296013685708507703164763197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394684914278010270886350929 296013685708507703164763197)
          ·
            refine ⟨111005132140690388686786199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296013685708507703164763197 111005132140690388686786199)
            ·
              refine ⟨166507698211035583030179299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111005132140690388686786199 166507698211035583030179299)
              ·
                refine ⟨249761547316553374545268949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166507698211035583030179299 249761547316553374545268949)
                ·
                  refine ⟨5853786265231719715904741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249761547316553374545268949 5853786265231719715904741)
                  ·
                    refine ⟨1097584924730947446732139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853786265231719715904741 1097584924730947446732139)
                    ·
                      rfl

theorem cell23_6412617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_6412617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412617 prefixEnd_6412617 := by exact prefixLift 6412617
  have htrace : WordTrace (prefixWord ++ tailWord_6412617) baseStart_6412617 baseEnd_6412617 := by
    simpa [prefixWord, tailWord_6412617, baseEnd_6412617] using wordTrace_append hprefix tailTrace_6412617
  have hstable : (prefixWord ++ tailWord_6412617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412617).length < 2 ^ (prefixWord ++ tailWord_6412617).sum := by decide
  have hdescent : baseEnd_6412617 < baseStart_6412617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412624 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2]
def baseStart_6412624 : Nat := 118140960795 + 6412624 * 2 ^ 59
def prefixEnd_6412624 : Nat := 4983230072969 + 3 ^ 40 * 6412624 * 2
def baseEnd_6412624 : Nat := 3292758368557423812808885

theorem tailTrace_6412624 : CollatzResearch.WordTrace tailWord_6412624 prefixEnd_6412624 3292758368557423812808885 := by
  unfold tailWord_6412624
  simp only [CollatzResearch.WordTrace]
  refine ⟨116943805960082955915930463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155925074613443941221240617 116943805960082955915930463)
  ·
    refine ⟨175415708940124433873895695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116943805960082955915930463 175415708940124433873895695)
    ·
      refine ⟨263123563410186650810843543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175415708940124433873895695 263123563410186650810843543)
      ·
        refine ⟨394685345115279976216265315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263123563410186650810843543 394685345115279976216265315)
        ·
          refine ⟨592028017672919964324397973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394685345115279976216265315 592028017672919964324397973)
          ·
            refine ⟨27751313328418123327706155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 592028017672919964324397973 27751313328418123327706155)
            ·
              refine ⟨41626969992627184991559233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27751313328418123327706155 41626969992627184991559233)
              ·
                refine ⟨31220227494470388743669425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41626969992627184991559233 31220227494470388743669425)
                ·
                  refine ⟨23415170620852791557752069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31220227494470388743669425 23415170620852791557752069)
                  ·
                    refine ⟨4390344491409898417078513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23415170620852791557752069 4390344491409898417078513)
                    ·
                      refine ⟨3292758368557423812808885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390344491409898417078513 3292758368557423812808885)
                      ·
                        rfl

theorem cell23_6412624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2].length) (baseStart_6412624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412624 prefixEnd_6412624 := by exact prefixLift 6412624
  have htrace : WordTrace (prefixWord ++ tailWord_6412624) baseStart_6412624 baseEnd_6412624 := by
    simpa [prefixWord, tailWord_6412624, baseEnd_6412624] using wordTrace_append hprefix tailTrace_6412624
  have hstable : (prefixWord ++ tailWord_6412624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412624).length < 2 ^ (prefixWord ++ tailWord_6412624).sum := by decide
  have hdescent : baseEnd_6412624 < baseStart_6412624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412657 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_6412657 : Nat := 118140960795 + 6412657 * 2 ^ 59
def prefixEnd_6412657 : Nat := 4983230072969 + 3 ^ 40 * 6412657 * 2
def baseEnd_6412657 : Nat := 3292775313419022183696233

theorem tailTrace_6412657 : CollatzResearch.WordTrace tailWord_6412657 prefixEnd_6412657 3292775313419022183696233 := by
  unfold tailWord_6412657
  simp only [CollatzResearch.WordTrace]
  refine ⟨233888815529046358467812225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155925877019364238978541483 233888815529046358467812225)
  ·
    refine ⟨175416611646784768850859169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233888815529046358467812225 175416611646784768850859169)
    ·
      refine ⟨131562458735088576638144377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175416611646784768850859169 131562458735088576638144377)
      ·
        refine ⟨98671844051316432478608283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131562458735088576638144377 98671844051316432478608283)
        ·
          refine ⟨148007766076974648717912425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98671844051316432478608283 148007766076974648717912425)
          ·
            refine ⟨111005824557730986538434319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148007766076974648717912425 111005824557730986538434319)
            ·
              refine ⟨166508736836596479807651479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111005824557730986538434319 166508736836596479807651479)
              ·
                refine ⟨249763105254894719711477219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166508736836596479807651479 249763105254894719711477219)
                ·
                  refine ⟨374644657882342079567215829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249763105254894719711477219 374644657882342079567215829)
                  ·
                    refine ⟨8780734169117392489856621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 374644657882342079567215829 8780734169117392489856621)
                    ·
                      refine ⟨3292775313419022183696233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8780734169117392489856621 3292775313419022183696233)
                      ·
                        rfl

theorem cell23_6412657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_6412657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412657 prefixEnd_6412657 := by exact prefixLift 6412657
  have htrace : WordTrace (prefixWord ++ tailWord_6412657) baseStart_6412657 baseEnd_6412657 := by
    simpa [prefixWord, tailWord_6412657, baseEnd_6412657] using wordTrace_append hprefix tailTrace_6412657
  have hstable : (prefixWord ++ tailWord_6412657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412657).length < 2 ^ (prefixWord ++ tailWord_6412657).sum := by decide
  have hdescent : baseEnd_6412657 < baseStart_6412657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412677 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_6412677 : Nat := 118140960795 + 6412677 * 2 ^ 59
def prefixEnd_6412677 : Nat := 4983230072969 + 3 ^ 40 * 6412677 * 2
def baseEnd_6412677 : Nat := 1097595194344037368482047

theorem tailTrace_6412677 : CollatzResearch.WordTrace tailWord_6412677 prefixEnd_6412677 1097595194344037368482047 := by
  unfold tailWord_6412677
  simp only [CollatzResearch.WordTrace]
  refine ⟨233889544988973901883540285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155926363325982601255693523 233889544988973901883540285)
  ·
    refine ⟨87708579370865213206327607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233889544988973901883540285 87708579370865213206327607)
    ·
      refine ⟨131562869056297819809491411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87708579370865213206327607 131562869056297819809491411)
      ·
        refine ⟨197344303584446729714237117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131562869056297819809491411 197344303584446729714237117)
        ·
          refine ⟨74004113844167523642838919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197344303584446729714237117 74004113844167523642838919)
          ·
            refine ⟨111006170766251285464258379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74004113844167523642838919 111006170766251285464258379)
            ·
              refine ⟨166509256149376928196387569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111006170766251285464258379 166509256149376928196387569)
              ·
                refine ⟨124881942112032696147290677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166509256149376928196387569 124881942112032696147290677)
                ·
                  refine ⟨11707682073003065263808501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124881942112032696147290677 11707682073003065263808501)
                  ·
                    refine ⟨1097595194344037368482047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11707682073003065263808501 1097595194344037368482047)
                    ·
                      rfl

theorem cell23_6412677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_6412677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412677 prefixEnd_6412677 := by exact prefixLift 6412677
  have htrace : WordTrace (prefixWord ++ tailWord_6412677) baseStart_6412677 baseEnd_6412677 := by
    simpa [prefixWord, tailWord_6412677, baseEnd_6412677] using wordTrace_append hprefix tailTrace_6412677
  have hstable : (prefixWord ++ tailWord_6412677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412677).length < 2 ^ (prefixWord ++ tailWord_6412677).sum := by decide
  have hdescent : baseEnd_6412677 < baseStart_6412677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412711 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 1, 5]
def baseStart_6412711 : Nat := 118140960795 + 6412711 * 2 ^ 59
def prefixEnd_6412711 : Nat := 4983230072969 + 3 ^ 40 * 6412711 * 2
def baseEnd_6412711 : Nat := 1097601013791454990806995

theorem tailTrace_6412711 : CollatzResearch.WordTrace tailWord_6412711 prefixEnd_6412711 1097601013791454990806995 := by
  unfold tailWord_6412711
  simp only [CollatzResearch.WordTrace]
  refine ⟨233890785070850725690277987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155927190047233817126851991 233890785070850725690277987)
  ·
    refine ⟨350836177606276088535416981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233890785070850725690277987 350836177606276088535416981)
    ·
      refine ⟨16445445825294191650097671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 350836177606276088535416981 16445445825294191650097671)
      ·
        refine ⟨24668168737941287475146507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16445445825294191650097671 24668168737941287475146507)
        ·
          refine ⟨37002253106911931212719761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24668168737941287475146507 37002253106911931212719761)
          ·
            refine ⟨27751689830183948409539821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37002253106911931212719761 27751689830183948409539821)
            ·
              refine ⟨10406883686318980653577433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27751689830183948409539821 10406883686318980653577433)
              ·
                refine ⟨7805162764739235490183075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10406883686318980653577433 7805162764739235490183075)
                ·
                  refine ⟨11707744147108853235274613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7805162764739235490183075 11707744147108853235274613)
                  ·
                    refine ⟨1097601013791454990806995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11707744147108853235274613 1097601013791454990806995)
                    ·
                      rfl

theorem cell23_6412711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_6412711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412711 prefixEnd_6412711 := by exact prefixLift 6412711
  have htrace : WordTrace (prefixWord ++ tailWord_6412711) baseStart_6412711 baseEnd_6412711 := by
    simpa [prefixWord, tailWord_6412711, baseEnd_6412711] using wordTrace_append hprefix tailTrace_6412711
  have hstable : (prefixWord ++ tailWord_6412711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412711).length < 2 ^ (prefixWord ++ tailWord_6412711).sum := by decide
  have hdescent : baseEnd_6412711 < baseStart_6412711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412758 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_6412758 : Nat := 118140960795 + 6412758 * 2 ^ 59
def prefixEnd_6412758 : Nat := 4983230072969 + 3 ^ 40 * 6412758 * 2
def baseEnd_6412758 : Nat := 1097609058321708762844423

theorem tailTrace_6412758 : CollatzResearch.WordTrace tailWord_6412758 prefixEnd_6412758 1097609058321708762844423 := by
  unfold tailWord_6412758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618281206355028294827433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155928332867786968478159285 14618281206355028294827433)
  ·
    refine ⟨10963710904766271221120575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14618281206355028294827433 10963710904766271221120575)
    ·
      refine ⟨16445566357149406831680863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963710904766271221120575 16445566357149406831680863)
      ·
        refine ⟨24668349535724110247521295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16445566357149406831680863 24668349535724110247521295)
        ·
          refine ⟨37002524303586165371281943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24668349535724110247521295 37002524303586165371281943)
          ·
            refine ⟨55503786455379248056922915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37002524303586165371281943 55503786455379248056922915)
            ·
              refine ⟨83255679683068872085384373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55503786455379248056922915 83255679683068872085384373)
              ·
                refine ⟨7805219970287706758004785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83255679683068872085384373 7805219970287706758004785)
                ·
                  refine ⟨5853914977715780068503589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7805219970287706758004785 5853914977715780068503589)
                  ·
                    refine ⟨1097609058321708762844423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853914977715780068503589 1097609058321708762844423)
                    ·
                      rfl

theorem cell23_6412758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_6412758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412758 prefixEnd_6412758 := by exact prefixLift 6412758
  have htrace : WordTrace (prefixWord ++ tailWord_6412758) baseStart_6412758 baseEnd_6412758 := by
    simpa [prefixWord, tailWord_6412758, baseEnd_6412758] using wordTrace_append hprefix tailTrace_6412758
  have hstable : (prefixWord ++ tailWord_6412758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412758).length < 2 ^ (prefixWord ++ tailWord_6412758).sum := by decide
  have hdescent : baseEnd_6412758 < baseStart_6412758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412771 : List Nat := [1, 1, 1, 6, 3, 1, 3, 7]
def baseStart_6412771 : Nat := 118140960795 + 6412771 * 2 ^ 59
def prefixEnd_6412771 : Nat := 4983230072969 + 3 ^ 40 * 6412771 * 2
def baseEnd_6412771 : Nat := 121956809267171656950767

theorem tailTrace_6412771 : CollatzResearch.WordTrace tailWord_6412771 prefixEnd_6412771 121956809267171656950767 := by
  unfold tailWord_6412771
  simp only [CollatzResearch.WordTrace]
  refine ⟨233892973450633355937462167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155928648967088903958308111 233892973450633355937462167)
  ·
    refine ⟨350839460175950033906193251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233892973450633355937462167 350839460175950033906193251)
    ·
      refine ⟨526259190263925050859289877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350839460175950033906193251 526259190263925050859289877)
      ·
        refine ⟨24668399543621486759029213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 526259190263925050859289877 24668399543621486759029213)
        ·
          refine ⟨9250649828858057534635955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24668399543621486759029213 9250649828858057534635955)
          ·
            refine ⟨13875974743287086301953933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250649828858057534635955 13875974743287086301953933)
            ·
              refine ⟨5203490528732657363232725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13875974743287086301953933 5203490528732657363232725)
              ·
                refine ⟨121956809267171656950767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5203490528732657363232725 121956809267171656950767)
                ·
                  rfl

theorem cell23_6412771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 7].length) (baseStart_6412771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412771 prefixEnd_6412771 := by exact prefixLift 6412771
  have htrace : WordTrace (prefixWord ++ tailWord_6412771) baseStart_6412771 baseEnd_6412771 := by
    simpa [prefixWord, tailWord_6412771, baseEnd_6412771] using wordTrace_append hprefix tailTrace_6412771
  have hstable : (prefixWord ++ tailWord_6412771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412771).length < 2 ^ (prefixWord ++ tailWord_6412771).sum := by decide
  have hdescent : baseEnd_6412771 < baseStart_6412771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412782 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_6412782 : Nat := 118140960795 + 6412782 * 2 ^ 59
def prefixEnd_6412782 : Nat := 4983230072969 + 3 ^ 40 * 6412782 * 2
def baseEnd_6412782 : Nat := 3292839498500834194633159

theorem tailTrace_6412782 : CollatzResearch.WordTrace tailWord_6412782 prefixEnd_6412782 3292839498500834194633159 := by
  unfold tailWord_6412782
  simp only [CollatzResearch.WordTrace]
  refine ⟨29236671831699188102014075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155928916435729003210741733 29236671831699188102014075)
  ·
    refine ⟨43855007747548782153021113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29236671831699188102014075 43855007747548782153021113)
    ·
      refine ⟨32891255810661586614765835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43855007747548782153021113 32891255810661586614765835)
      ·
        refine ⟨49336883715992379922148753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32891255810661586614765835 49336883715992379922148753)
        ·
          refine ⟨37002662786994284941611565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49336883715992379922148753 37002662786994284941611565)
          ·
            refine ⟨13875998545122856853104337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37002662786994284941611565 13875998545122856853104337)
            ·
              refine ⟨10406998908842142639828253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875998545122856853104337 10406998908842142639828253)
              ·
                refine ⟨3902624590815803489935595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10406998908842142639828253 3902624590815803489935595)
                ·
                  refine ⟨5853936886223705234903393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902624590815803489935595 5853936886223705234903393)
                  ·
                    refine ⟨4390452664667778926177545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5853936886223705234903393 4390452664667778926177545)
                    ·
                      refine ⟨3292839498500834194633159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390452664667778926177545 3292839498500834194633159)
                      ·
                        rfl

theorem cell23_6412782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_6412782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412782 prefixEnd_6412782 := by exact prefixLift 6412782
  have htrace : WordTrace (prefixWord ++ tailWord_6412782) baseStart_6412782 baseEnd_6412782 := by
    simpa [prefixWord, tailWord_6412782, baseEnd_6412782] using wordTrace_append hprefix tailTrace_6412782
  have hstable : (prefixWord ++ tailWord_6412782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412782).length < 2 ^ (prefixWord ++ tailWord_6412782).sum := by decide
  have hdescent : baseEnd_6412782 < baseStart_6412782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412861 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 7]
def baseStart_6412861 : Nat := 118140960795 + 6412861 * 2 ^ 59
def prefixEnd_6412861 : Nat := 4983230072969 + 3 ^ 40 * 6412861 * 2
def baseEnd_6412861 : Nat := 365875562608059931727255

theorem tailTrace_6412861 : CollatzResearch.WordTrace tailWord_6412861 prefixEnd_6412861 365875562608059931727255 := by
  unfold tailWord_6412861
  simp only [CollatzResearch.WordTrace]
  refine ⟨233896256020307301308238437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155930837346871534205492291 233896256020307301308238437)
  ·
    refine ⟨43855548003807618995294707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233896256020307301308238437 43855548003807618995294707)
    ·
      refine ⟨65783322005711428492942061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43855548003807618995294707 65783322005711428492942061)
      ·
        refine ⟨24668745752141785684853273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65783322005711428492942061 24668745752141785684853273)
        ·
          refine ⟨18501559314106339263639955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24668745752141785684853273 18501559314106339263639955)
          ·
            refine ⟨27752338971159508895459933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18501559314106339263639955 27752338971159508895459933)
            ·
              refine ⟨10407127114184815835797475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27752338971159508895459933 10407127114184815835797475)
              ·
                refine ⟨15610690671277223753696213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10407127114184815835797475 15610690671277223753696213)
                ·
                  refine ⟨365875562608059931727255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15610690671277223753696213 365875562608059931727255)
                  ·
                    rfl

theorem cell23_6412861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_6412861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412861 prefixEnd_6412861 := by exact prefixLift 6412861
  have htrace : WordTrace (prefixWord ++ tailWord_6412861) baseStart_6412861 baseEnd_6412861 := by
    simpa [prefixWord, tailWord_6412861, baseEnd_6412861] using wordTrace_append hprefix tailTrace_6412861
  have hstable : (prefixWord ++ tailWord_6412861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412861).length < 2 ^ (prefixWord ++ tailWord_6412861).sum := by decide
  have hdescent : baseEnd_6412861 < baseStart_6412861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412911 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_6412911 : Nat := 118140960795 + 6412911 * 2 ^ 59
def prefixEnd_6412911 : Nat := 4983230072969 + 3 ^ 40 * 6412911 * 2
def baseEnd_6412911 : Nat := 3292905737505264189920065

theorem tailTrace_6412911 : CollatzResearch.WordTrace tailWord_6412911 prefixEnd_6412911 3292905737505264189920065 := by
  unfold tailWord_6412911
  simp only [CollatzResearch.WordTrace]
  refine ⟨233898079670126159847558587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155932053113417439898372391 233898079670126159847558587)
  ·
    refine ⟨350847119505189239771337881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233898079670126159847558587 350847119505189239771337881)
    ·
      refine ⟨263135339628891929828503411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350847119505189239771337881 263135339628891929828503411)
      ·
        refine ⟨394703009443337894742755117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263135339628891929828503411 394703009443337894742755117)
        ·
          refine ⟨148013628541251710528533169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394703009443337894742755117 148013628541251710528533169)
          ·
            refine ⟨111010221405938782896399877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148013628541251710528533169 111010221405938782896399877)
            ·
              refine ⟨20814416513613521793074977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111010221405938782896399877 20814416513613521793074977)
              ·
                refine ⟨15610812385210141344806233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20814416513613521793074977 15610812385210141344806233)
                ·
                  refine ⟨11708109288907606008604675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15610812385210141344806233 11708109288907606008604675)
                  ·
                    refine ⟨17562163933361409012907013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11708109288907606008604675 17562163933361409012907013)
                    ·
                      refine ⟨3292905737505264189920065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17562163933361409012907013 3292905737505264189920065)
                      ·
                        rfl

theorem cell23_6412911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_6412911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412911 prefixEnd_6412911 := by exact prefixLift 6412911
  have htrace : WordTrace (prefixWord ++ tailWord_6412911) baseStart_6412911 baseEnd_6412911 := by
    simpa [prefixWord, tailWord_6412911, baseEnd_6412911] using wordTrace_append hprefix tailTrace_6412911
  have hstable : (prefixWord ++ tailWord_6412911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412911).length < 2 ^ (prefixWord ++ tailWord_6412911).sum := by decide
  have hdescent : baseEnd_6412911 < baseStart_6412911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412912 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 5]
def baseStart_6412912 : Nat := 118140960795 + 6412912 * 2 ^ 59
def prefixEnd_6412912 : Nat := 4983230072969 + 3 ^ 40 * 6412912 * 2
def baseEnd_6412912 : Nat := 365878472331768742889729

theorem tailTrace_6412912 : CollatzResearch.WordTrace tailWord_6412912 prefixEnd_6412912 365878472331768742889729 := by
  unfold tailWord_6412912
  simp only [CollatzResearch.WordTrace]
  refine ⟨116949058071561268509172495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155932077428748358012229993 116949058071561268509172495)
  ·
    refine ⟨175423587107341902763758743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116949058071561268509172495 175423587107341902763758743)
    ·
      refine ⟨263135380661012854145638115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175423587107341902763758743 263135380661012854145638115)
      ·
        refine ⟨394703070991519281218457173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263135380661012854145638115 394703070991519281218457173)
        ·
          refine ⟨4625426613181866576778795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 394703070991519281218457173 4625426613181866576778795)
          ·
            refine ⟨6938139919772799865168193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625426613181866576778795 6938139919772799865168193)
            ·
              refine ⟨5203604939829599898876145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6938139919772799865168193 5203604939829599898876145)
              ·
                refine ⟨3902703704872199924157109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5203604939829599898876145 3902703704872199924157109)
                ·
                  refine ⟨365878472331768742889729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902703704872199924157109 365878472331768742889729)
                  ·
                    rfl

theorem cell23_6412912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 5].length) (baseStart_6412912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412912 prefixEnd_6412912 := by exact prefixLift 6412912
  have htrace : WordTrace (prefixWord ++ tailWord_6412912) baseStart_6412912 baseEnd_6412912 := by
    simpa [prefixWord, tailWord_6412912, baseEnd_6412912] using wordTrace_append hprefix tailTrace_6412912
  have hstable : (prefixWord ++ tailWord_6412912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412912).length < 2 ^ (prefixWord ++ tailWord_6412912).sum := by decide
  have hdescent : baseEnd_6412912 < baseStart_6412912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412928 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2]
def baseStart_6412928 : Nat := 118140960795 + 6412928 * 2 ^ 59
def prefixEnd_6412928 : Nat := 4983230072969 + 3 ^ 40 * 6412928 * 2
def baseEnd_6412928 : Nat := 3292914466676390623407487

theorem tailTrace_6412928 : CollatzResearch.WordTrace tailWord_6412928 prefixEnd_6412928 3292914466676390623407487 := by
  unfold tailWord_6412928
  simp only [CollatzResearch.WordTrace]
  refine ⟨116949349855532285875463719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155932466474043047833951625 116949349855532285875463719)
  ·
    refine ⟨175424024783298428813195579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116949349855532285875463719 175424024783298428813195579)
    ·
      refine ⟨263136037174947643219793369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175424024783298428813195579 263136037174947643219793369)
      ·
        refine ⟨197352027881210732414845027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263136037174947643219793369 197352027881210732414845027)
        ·
          refine ⟨296028041821816098622267541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197352027881210732414845027 296028041821816098622267541)
          ·
            refine ⟨13876314460397629622918791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 296028041821816098622267541 13876314460397629622918791)
            ·
              refine ⟨20814471690596444434378187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13876314460397629622918791 20814471690596444434378187)
              ·
                refine ⟨31221707535894666651567281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20814471690596444434378187 31221707535894666651567281)
                ·
                  refine ⟨23416280651920999988675461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31221707535894666651567281 23416280651920999988675461)
                  ·
                    refine ⟨4390552622235187497876649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23416280651920999988675461 4390552622235187497876649)
                    ·
                      refine ⟨3292914466676390623407487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390552622235187497876649 3292914466676390623407487)
                      ·
                        rfl

theorem cell23_6412928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_6412928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412928 prefixEnd_6412928 := by exact prefixLift 6412928
  have htrace : WordTrace (prefixWord ++ tailWord_6412928) baseStart_6412928 baseEnd_6412928 := by
    simpa [prefixWord, tailWord_6412928, baseEnd_6412928] using wordTrace_append hprefix tailTrace_6412928
  have hstable : (prefixWord ++ tailWord_6412928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412928).length < 2 ^ (prefixWord ++ tailWord_6412928).sum := by decide
  have hdescent : baseEnd_6412928 < baseStart_6412928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412931 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3]
def baseStart_6412931 : Nat := 118140960795 + 6412931 * 2 ^ 59
def prefixEnd_6412931 : Nat := 4983230072969 + 3 ^ 40 * 6412931 * 2
def baseEnd_6412931 : Nat := 3292916007118354111669973

theorem tailTrace_6412931 : CollatzResearch.WordTrace tailWord_6412931 prefixEnd_6412931 3292916007118354111669973 := by
  unfold tailWord_6412931
  simp only [CollatzResearch.WordTrace]
  refine ⟨233898809130053703263286647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155932539420035802175524431 233898809130053703263286647)
  ·
    refine ⟨350848213695080554894929971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233898809130053703263286647 350848213695080554894929971)
    ·
      refine ⟨526272320542620832342394957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350848213695080554894929971 526272320542620832342394957)
      ·
        refine ⟨197352120203482812128398109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526272320542620832342394957 197352120203482812128398109)
        ·
          refine ⟨74007045076306054548149291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197352120203482812128398109 74007045076306054548149291)
          ·
            refine ⟨111010567614459081822223937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74007045076306054548149291 111010567614459081822223937)
            ·
              refine ⟨83257925710844311366667953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111010567614459081822223937 83257925710844311366667953)
              ·
                refine ⟨62443444283133233525000965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83257925710844311366667953 62443444283133233525000965)
                ·
                  refine ⟨11708145803087481285937681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62443444283133233525000965 11708145803087481285937681)
                  ·
                    refine ⟨8781109352315610964453261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11708145803087481285937681 8781109352315610964453261)
                    ·
                      refine ⟨3292916007118354111669973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8781109352315610964453261 3292916007118354111669973)
                      ·
                        rfl

theorem cell23_6412931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_6412931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412931 prefixEnd_6412931 := by exact prefixLift 6412931
  have htrace : WordTrace (prefixWord ++ tailWord_6412931) baseStart_6412931 baseEnd_6412931 := by
    simpa [prefixWord, tailWord_6412931, baseEnd_6412931] using wordTrace_append hprefix tailTrace_6412931
  have hstable : (prefixWord ++ tailWord_6412931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412931).length < 2 ^ (prefixWord ++ tailWord_6412931).sum := by decide
  have hdescent : baseEnd_6412931 < baseStart_6412931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6412988 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_6412988 : Nat := 118140960795 + 6412988 * 2 ^ 59
def prefixEnd_6412988 : Nat := 4983230072969 + 3 ^ 40 * 6412988 * 2
def baseEnd_6412988 : Nat := 3292945275515660388657211

theorem tailTrace_6412988 : CollatzResearch.WordTrace tailWord_6412988 prefixEnd_6412988 3292945275515660388657211 := by
  unfold tailWord_6412988
  simp only [CollatzResearch.WordTrace]
  refine ⟨116950444045423600999055809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155933925393898134665407745 116950444045423600999055809)
  ·
    refine ⟨87712833034067700749291857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116950444045423600999055809 87712833034067700749291857)
    ·
      refine ⟨65784624775550775561968893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87712833034067700749291857 65784624775550775561968893)
      ·
        refine ⟨24669234290831540835738335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65784624775550775561968893 24669234290831540835738335)
        ·
          refine ⟨37003851436247311253607503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24669234290831540835738335 37003851436247311253607503)
          ·
            refine ⟨55505777154370966880411255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37003851436247311253607503 55505777154370966880411255)
            ·
              refine ⟨83258665731556450320616883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55505777154370966880411255 83258665731556450320616883)
              ·
                refine ⟨124887998597334675480925325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83258665731556450320616883 124887998597334675480925325)
                ·
                  refine ⟨46832999474000503305346997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124887998597334675480925325 46832999474000503305346997)
                  ·
                    refine ⟨4390593700687547184876281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46832999474000503305346997 4390593700687547184876281)
                    ·
                      refine ⟨3292945275515660388657211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390593700687547184876281 3292945275515660388657211)
                      ·
                        rfl

theorem cell23_6412988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_6412988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6412988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6412988 prefixEnd_6412988 := by exact prefixLift 6412988
  have htrace : WordTrace (prefixWord ++ tailWord_6412988) baseStart_6412988 baseEnd_6412988 := by
    simpa [prefixWord, tailWord_6412988, baseEnd_6412988] using wordTrace_append hprefix tailTrace_6412988
  have hstable : (prefixWord ++ tailWord_6412988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6412988).length < 2 ^ (prefixWord ++ tailWord_6412988).sum := by decide
  have hdescent : baseEnd_6412988 < baseStart_6412988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6412988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413018 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_6413018 : Nat := 118140960795 + 6413018 * 2 ^ 59
def prefixEnd_6413018 : Nat := 4983230072969 + 3 ^ 40 * 6413018 * 2
def baseEnd_6413018 : Nat := 3292960679935295271282073

theorem tailTrace_6413018 : CollatzResearch.WordTrace tailWord_6413018 prefixEnd_6413018 3292960679935295271282073 := by
  unfold tailWord_6413018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58475495570184629280425927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155934654853825678081135805 58475495570184629280425927)
  ·
    refine ⟨87713243355276943920638891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58475495570184629280425927 87713243355276943920638891)
    ·
      refine ⟨131569865032915415880958337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87713243355276943920638891 131569865032915415880958337)
      ·
        refine ⟨98677398774686561910718753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131569865032915415880958337 98677398774686561910718753)
        ·
          refine ⟨74008049081014921433039065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98677398774686561910718753 74008049081014921433039065)
          ·
            refine ⟨55506036810761191074779299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74008049081014921433039065 55506036810761191074779299)
            ·
              refine ⟨83259055216141786612168949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55506036810761191074779299 83259055216141786612168949)
              ·
                refine ⟨7805536426513292494890839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83259055216141786612168949 7805536426513292494890839)
                ·
                  refine ⟨11708304639769938742336259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7805536426513292494890839 11708304639769938742336259)
                  ·
                    refine ⟨17562456959654908113504389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11708304639769938742336259 17562456959654908113504389)
                    ·
                      refine ⟨3292960679935295271282073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17562456959654908113504389 3292960679935295271282073)
                      ·
                        rfl

theorem cell23_6413018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_6413018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413018 prefixEnd_6413018 := by exact prefixLift 6413018
  have htrace : WordTrace (prefixWord ++ tailWord_6413018) baseStart_6413018 baseEnd_6413018 := by
    simpa [prefixWord, tailWord_6413018, baseEnd_6413018] using wordTrace_append hprefix tailTrace_6413018
  have hstable : (prefixWord ++ tailWord_6413018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413018).length < 2 ^ (prefixWord ++ tailWord_6413018).sum := by decide
  have hdescent : baseEnd_6413018 < baseStart_6413018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413028 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_6413028 : Nat := 118140960795 + 6413028 * 2 ^ 59
def prefixEnd_6413028 : Nat := 4983230072969 + 3 ^ 40 * 6413028 * 2
def baseEnd_6413028 : Nat := 1097655271580613410719009

theorem tailTrace_6413028 : CollatzResearch.WordTrace tailWord_6413028 prefixEnd_6413028 1097655271580613410719009 := by
  unfold tailWord_6413028
  simp only [CollatzResearch.WordTrace]
  refine ⟨116951173505351144414783869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155934898007134859219711825 116951173505351144414783869)
  ·
    refine ⟨43856690064506679155543951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116951173505351144414783869 43856690064506679155543951)
    ·
      refine ⟨65785035096760018733315927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43856690064506679155543951 65785035096760018733315927)
      ·
        refine ⟨98677552645140028099973891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65785035096760018733315927 98677552645140028099973891)
        ·
          refine ⟨148016328967710042149960837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98677552645140028099973891 148016328967710042149960837)
          ·
            refine ⟨27753061681445632903117657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148016328967710042149960837 27753061681445632903117657)
            ·
              refine ⟨20814796261084224677338243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27753061681445632903117657 20814796261084224677338243)
              ·
                refine ⟨31222194391626337016007365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20814796261084224677338243 31222194391626337016007365)
                ·
                  refine ⟨5854161448429938190501381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31222194391626337016007365 5854161448429938190501381)
                  ·
                    refine ⟨1097655271580613410719009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854161448429938190501381 1097655271580613410719009)
                    ·
                      rfl

theorem cell23_6413028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_6413028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413028 prefixEnd_6413028 := by exact prefixLift 6413028
  have htrace : WordTrace (prefixWord ++ tailWord_6413028) baseStart_6413028 baseEnd_6413028 := by
    simpa [prefixWord, tailWord_6413028, baseEnd_6413028] using wordTrace_append hprefix tailTrace_6413028
  have hstable : (prefixWord ++ tailWord_6413028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413028).length < 2 ^ (prefixWord ++ tailWord_6413028).sum := by decide
  have hdescent : baseEnd_6413028 < baseStart_6413028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413029 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6413029 : Nat := 118140960795 + 6413029 * 2 ^ 59
def prefixEnd_6413029 : Nat := 4983230072969 + 3 ^ 40 * 6413029 * 2
def baseEnd_6413029 : Nat := 3292966328222494728244523

theorem tailTrace_6413029 : CollatzResearch.WordTrace tailWord_6413029 prefixEnd_6413029 3292966328222494728244523 := by
  unfold tailWord_6413029
  simp only [CollatzResearch.WordTrace]
  refine ⟨233902383483698666000354141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155934922322465777333569427 233902383483698666000354141)
  ·
    refine ⟨87713393806386999750132803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233902383483698666000354141 87713393806386999750132803)
    ·
      refine ⟨131570090709580499625199205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87713393806386999750132803 131570090709580499625199205)
      ·
        refine ⟨24669392008046343679724851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131570090709580499625199205 24669392008046343679724851)
        ·
          refine ⟨37004088012069515519587277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24669392008046343679724851 37004088012069515519587277)
          ·
            refine ⟨13876533004526068319845229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37004088012069515519587277 13876533004526068319845229)
            ·
              refine ⟨5203699876697275619941961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13876533004526068319845229 5203699876697275619941961)
              ·
                refine ⟨3902774907522956714956471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5203699876697275619941961 3902774907522956714956471)
                ·
                  refine ⟨5854162361284435072434707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902774907522956714956471 5854162361284435072434707)
                  ·
                    refine ⟨8781243541926652608652061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854162361284435072434707 8781243541926652608652061)
                    ·
                      refine ⟨3292966328222494728244523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8781243541926652608652061 3292966328222494728244523)
                      ·
                        rfl

theorem cell23_6413029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6413029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413029 prefixEnd_6413029 := by exact prefixLift 6413029
  have htrace : WordTrace (prefixWord ++ tailWord_6413029) baseStart_6413029 baseEnd_6413029 := by
    simpa [prefixWord, tailWord_6413029, baseEnd_6413029] using wordTrace_append hprefix tailTrace_6413029
  have hstable : (prefixWord ++ tailWord_6413029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413029).length < 2 ^ (prefixWord ++ tailWord_6413029).sum := by decide
  have hdescent : baseEnd_6413029 < baseStart_6413029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413038 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6413038 : Nat := 118140960795 + 6413038 * 2 ^ 59
def prefixEnd_6413038 : Nat := 4983230072969 + 3 ^ 40 * 6413038 * 2
def baseEnd_6413038 : Nat := 3292970949548385193031981

theorem tailTrace_6413038 : CollatzResearch.WordTrace tailWord_6413038 prefixEnd_6413038 3292970949548385193031981 := by
  unfold tailWord_6413038
  simp only [CollatzResearch.WordTrace]
  refine ⟨29237838967583257567178971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155935141160444040358287845 29237838967583257567178971)
  ·
    refine ⟨43856758451374886350768457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29237838967583257567178971 43856758451374886350768457)
    ·
      refine ⟨32892568838531164763076343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43856758451374886350768457 32892568838531164763076343)
      ·
        refine ⟨49338853257796747144614515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32892568838531164763076343 49338853257796747144614515)
        ·
          refine ⟨74008279886695120716921773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49338853257796747144614515 74008279886695120716921773)
          ·
            refine ⟨27753104957510670268845665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74008279886695120716921773 27753104957510670268845665)
            ·
              refine ⟨20814828718133002701634249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27753104957510670268845665 20814828718133002701634249)
              ·
                refine ⟨15611121538599752026225687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20814828718133002701634249 15611121538599752026225687)
                ·
                  refine ⟨23416682307899628039338531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15611121538599752026225687 23416682307899628039338531)
                  ·
                    refine ⟨35125023461849442059007797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23416682307899628039338531 35125023461849442059007797)
                    ·
                      refine ⟨3292970949548385193031981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35125023461849442059007797 3292970949548385193031981)
                      ·
                        rfl

theorem cell23_6413038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6413038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413038 prefixEnd_6413038 := by exact prefixLift 6413038
  have htrace : WordTrace (prefixWord ++ tailWord_6413038) baseStart_6413038 baseEnd_6413038 := by
    simpa [prefixWord, tailWord_6413038, baseEnd_6413038] using wordTrace_append hprefix tailTrace_6413038
  have hstable : (prefixWord ++ tailWord_6413038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413038).length < 2 ^ (prefixWord ++ tailWord_6413038).sum := by decide
  have hdescent : baseEnd_6413038 < baseStart_6413038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413041 : List Nat := [1, 2, 2, 2, 2, 2, 4, 8]
def baseStart_6413041 : Nat := 118140960795 + 6413041 * 2 ^ 59
def prefixEnd_6413041 : Nat := 4983230072969 + 3 ^ 40 * 6413041 * 2
def baseEnd_6413041 : Nat := 121961944073716617825721

theorem tailTrace_6413041 : CollatzResearch.WordTrace tailWord_6413041 prefixEnd_6413041 121961944073716617825721 := by
  unfold tailWord_6413041
  simp only [CollatzResearch.WordTrace]
  refine ⟨233902821159655192049790977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155935214106436794699860651 233902821159655192049790977)
  ·
    refine ⟨175427115869741394037343233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233902821159655192049790977 175427115869741394037343233)
    ·
      refine ⟨131570336902306045528007425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175427115869741394037343233 131570336902306045528007425)
      ·
        refine ⟨98677752676729534146005569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131570336902306045528007425 98677752676729534146005569)
        ·
          refine ⟨74008314507547150609504177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98677752676729534146005569 74008314507547150609504177)
          ·
            refine ⟨55506235880660362957128133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74008314507547150609504177 55506235880660362957128133)
            ·
              refine ⟨10407419227623818054461525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55506235880660362957128133 10407419227623818054461525)
              ·
                refine ⟨121961944073716617825721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10407419227623818054461525 121961944073716617825721)
                ·
                  rfl

theorem cell23_6413041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 8].length) (baseStart_6413041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413041 prefixEnd_6413041 := by exact prefixLift 6413041
  have htrace : WordTrace (prefixWord ++ tailWord_6413041) baseStart_6413041 baseEnd_6413041 := by
    simpa [prefixWord, tailWord_6413041, baseEnd_6413041] using wordTrace_append hprefix tailTrace_6413041
  have hstable : (prefixWord ++ tailWord_6413041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413041).length < 2 ^ (prefixWord ++ tailWord_6413041).sum := by decide
  have hdescent : baseEnd_6413041 < baseStart_6413041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413058 : List Nat := [3, 4, 1, 1, 1, 2, 2, 9]
def baseStart_6413058 : Nat := 118140960795 + 6413058 * 2 ^ 59
def prefixEnd_6413058 : Nat := 4983230072969 + 3 ^ 40 * 6413058 * 2
def baseEnd_6413058 : Nat := 121962267376350930177107

theorem tailTrace_6413058 : CollatzResearch.WordTrace tailWord_6413058 prefixEnd_6413058 121962267376350930177107 := by
  unfold tailWord_6413058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58475860300148400988289957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155935627467062402635439885 58475860300148400988289957)
  ·
    refine ⟨10964223806277825185304367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58475860300148400988289957 10964223806277825185304367)
    ·
      refine ⟨16446335709416737777956551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10964223806277825185304367 16446335709416737777956551)
      ·
        refine ⟨24669503564125106666934827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16446335709416737777956551 24669503564125106666934827)
        ·
          refine ⟨37004255346187660000402241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24669503564125106666934827 37004255346187660000402241)
          ·
            refine ⟨27753191509640745000301681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37004255346187660000402241 27753191509640745000301681)
            ·
              refine ⟨20814893632230558750226261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27753191509640745000301681 20814893632230558750226261)
              ·
                refine ⟨121962267376350930177107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20814893632230558750226261 121962267376350930177107)
                ·
                  rfl

theorem cell23_6413058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_6413058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413058 prefixEnd_6413058 := by exact prefixLift 6413058
  have htrace : WordTrace (prefixWord ++ tailWord_6413058) baseStart_6413058 baseEnd_6413058 := by
    simpa [prefixWord, tailWord_6413058, baseEnd_6413058] using wordTrace_append hprefix tailTrace_6413058
  have hstable : (prefixWord ++ tailWord_6413058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413058).length < 2 ^ (prefixWord ++ tailWord_6413058).sum := by decide
  have hdescent : baseEnd_6413058 < baseStart_6413058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413102 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6413102 : Nat := 118140960795 + 6413102 * 2 ^ 59
def prefixEnd_6413102 : Nat := 4983230072969 + 3 ^ 40 * 6413102 * 2
def baseEnd_6413102 : Nat := 3293003812310272942631687

theorem tailTrace_6413102 : CollatzResearch.WordTrace tailWord_6413102 prefixEnd_6413102 3293003812310272942631687 := by
  unfold tailWord_6413102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29238130751554274933470195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155936697341622799645174373 29238130751554274933470195)
  ·
    refine ⟨43857196127331412400205293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29238130751554274933470195 43857196127331412400205293)
    ·
      refine ⟨16446448547749279650076985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43857196127331412400205293 16446448547749279650076985)
      ·
        refine ⟨12334836410811959737557739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16446448547749279650076985 12334836410811959737557739)
        ·
          refine ⟨18502254616217939606336609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12334836410811959737557739 18502254616217939606336609)
          ·
            refine ⟨13876690962163454704752457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18502254616217939606336609 13876690962163454704752457)
            ·
              refine ⟨10407518221622591028564343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13876690962163454704752457 10407518221622591028564343)
              ·
                refine ⟨15611277332433886542846515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10407518221622591028564343 15611277332433886542846515)
                ·
                  refine ⟨23416915998650829814269773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15611277332433886542846515 23416915998650829814269773)
                  ·
                    refine ⟨8781343499494061180351165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23416915998650829814269773 8781343499494061180351165)
                    ·
                      refine ⟨3293003812310272942631687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8781343499494061180351165 3293003812310272942631687)
                      ·
                        rfl

theorem cell23_6413102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6413102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413102 prefixEnd_6413102 := by exact prefixLift 6413102
  have htrace : WordTrace (prefixWord ++ tailWord_6413102) baseStart_6413102 baseEnd_6413102 := by
    simpa [prefixWord, tailWord_6413102, baseEnd_6413102] using wordTrace_append hprefix tailTrace_6413102
  have hstable : (prefixWord ++ tailWord_6413102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413102).length < 2 ^ (prefixWord ++ tailWord_6413102).sum := by decide
  have hdescent : baseEnd_6413102 < baseStart_6413102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413129 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 1, 3, 2]
def baseStart_6413129 : Nat := 118140960795 + 6413129 * 2 ^ 59
def prefixEnd_6413129 : Nat := 4983230072969 + 3 ^ 40 * 6413129 * 2
def baseEnd_6413129 : Nat := 3293017676287944336994063

theorem tailTrace_6413129 : CollatzResearch.WordTrace tailWord_6413129 prefixEnd_6413129 3293017676287944336994063 := by
  unfold tailWord_6413129
  simp only [CollatzResearch.WordTrace]
  refine ⟨233906030783336383078994441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155937353855557588719329627 233906030783336383078994441)
  ·
    refine ⟨175429523087502287309245831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233906030783336383078994441 175429523087502287309245831)
    ·
      refine ⟨263144284631253430963868747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175429523087502287309245831 263144284631253430963868747)
      ·
        refine ⟨394716426946880146445803121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263144284631253430963868747 394716426946880146445803121)
        ·
          refine ⟨296037320210160109834352341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394716426946880146445803121 296037320210160109834352341)
          ·
            refine ⟨6938374692425627574242633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296037320210160109834352341 6938374692425627574242633)
            ·
              refine ⟨5203781019319220680681975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6938374692425627574242633 5203781019319220680681975)
              ·
                refine ⟨7805671528978831021022963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5203781019319220680681975 7805671528978831021022963)
                ·
                  refine ⟨11708507293468246531534445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7805671528978831021022963 11708507293468246531534445)
                  ·
                    refine ⟨4390690235050592449325417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11708507293468246531534445 4390690235050592449325417)
                    ·
                      refine ⟨3293017676287944336994063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4390690235050592449325417 3293017676287944336994063)
                      ·
                        rfl

theorem cell23_6413129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 3, 2].length) (baseStart_6413129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413129 prefixEnd_6413129 := by exact prefixLift 6413129
  have htrace : WordTrace (prefixWord ++ tailWord_6413129) baseStart_6413129 baseEnd_6413129 := by
    simpa [prefixWord, tailWord_6413129, baseEnd_6413129] using wordTrace_append hprefix tailTrace_6413129
  have hstable : (prefixWord ++ tailWord_6413129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413129).length < 2 ^ (prefixWord ++ tailWord_6413129).sum := by decide
  have hdescent : baseEnd_6413129 < baseStart_6413129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413138 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6413138 : Nat := 118140960795 + 6413138 * 2 ^ 59
def prefixEnd_6413138 : Nat := 4983230072969 + 3 ^ 40 * 6413138 * 2
def baseEnd_6413138 : Nat := 3293022297613834801781521

theorem tailTrace_6413138 : CollatzResearch.WordTrace tailWord_6413138 prefixEnd_6413138 3293022297613834801781521 := by
  unfold tailWord_6413138
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476589760075944404018017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155937572693535851744048045 58476589760075944404018017)
  ·
    refine ⟨43857442320056958303013513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58476589760075944404018017 43857442320056958303013513)
    ·
      refine ⟨32893081740042718727260135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43857442320056958303013513 32893081740042718727260135)
      ·
        refine ⟨49339622610064078090890203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32893081740042718727260135 49339622610064078090890203)
        ·
          refine ⟨74009433915096117136335305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49339622610064078090890203 74009433915096117136335305)
          ·
            refine ⟨55507075436322087852251479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74009433915096117136335305 55507075436322087852251479)
            ·
              refine ⟨83260613154483131778377219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55507075436322087852251479 83260613154483131778377219)
              ·
                refine ⟨124890919731724697667565829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83260613154483131778377219 124890919731724697667565829)
                ·
                  refine ⟨23417047449698380812668593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124890919731724697667565829 23417047449698380812668593)
                  ·
                    refine ⟨17562785587273785609501445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23417047449698380812668593 17562785587273785609501445)
                    ·
                      refine ⟨3293022297613834801781521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17562785587273785609501445 3293022297613834801781521)
                      ·
                        rfl

theorem cell23_6413138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6413138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413138 prefixEnd_6413138 := by exact prefixLift 6413138
  have htrace : WordTrace (prefixWord ++ tailWord_6413138) baseStart_6413138 baseEnd_6413138 := by
    simpa [prefixWord, tailWord_6413138, baseEnd_6413138] using wordTrace_append hprefix tailTrace_6413138
  have hstable : (prefixWord ++ tailWord_6413138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413138).length < 2 ^ (prefixWord ++ tailWord_6413138).sum := by decide
  have hdescent : baseEnd_6413138 < baseStart_6413138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413178 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_6413178 : Nat := 118140960795 + 6413178 * 2 ^ 59
def prefixEnd_6413178 : Nat := 4983230072969 + 3 ^ 40 * 6413178 * 2
def baseEnd_6413178 : Nat := 1097680945613338215093779

theorem tailTrace_6413178 : CollatzResearch.WordTrace tailWord_6413178 prefixEnd_6413178 1097680945613338215093779 := by
  unfold tailWord_6413178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476954490039716111882047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155938545306772576298352125 58476954490039716111882047)
  ·
    refine ⟨87715431735059574167823071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58476954490039716111882047 87715431735059574167823071)
    ·
      refine ⟨131573147602589361251734607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87715431735059574167823071 131573147602589361251734607)
      ·
        refine ⟨197359721403884041877601911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131573147602589361251734607 197359721403884041877601911)
        ·
          refine ⟨296039582105826062816402867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197359721403884041877601911 296039582105826062816402867)
          ·
            refine ⟨444059373158739094224604301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296039582105826062816402867 444059373158739094224604301)
            ·
              refine ⟨166522264934527160334226613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444059373158739094224604301 166522264934527160334226613)
              ·
                refine ⟨15611462337611921281333745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166522264934527160334226613 15611462337611921281333745)
                ·
                  refine ⟨11708596753208940961000309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15611462337611921281333745 11708596753208940961000309)
                  ·
                    refine ⟨1097680945613338215093779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11708596753208940961000309 1097680945613338215093779)
                    ·
                      rfl

theorem cell23_6413178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_6413178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413178 prefixEnd_6413178 := by exact prefixLift 6413178
  have htrace : WordTrace (prefixWord ++ tailWord_6413178) baseStart_6413178 baseEnd_6413178 := by
    simpa [prefixWord, tailWord_6413178, baseEnd_6413178] using wordTrace_append hprefix tailTrace_6413178
  have hstable : (prefixWord ++ tailWord_6413178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413178).length < 2 ^ (prefixWord ++ tailWord_6413178).sum := by decide
  have hdescent : baseEnd_6413178 < baseStart_6413178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413188 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_6413188 : Nat := 118140960795 + 6413188 * 2 ^ 59
def prefixEnd_6413188 : Nat := 4983230072969 + 3 ^ 40 * 6413188 * 2
def baseEnd_6413188 : Nat := 3293047971646559606156291

theorem tailTrace_6413188 : CollatzResearch.WordTrace tailWord_6413188 prefixEnd_6413188 3293047971646559606156291 := by
  unfold tailWord_6413188
  simp only [CollatzResearch.WordTrace]
  refine ⟨116954091345061318077696109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155938788460081757436928145 116954091345061318077696109)
  ·
    refine ⟨43857784254397994279136041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116954091345061318077696109 43857784254397994279136041)
    ·
      refine ⟨32893338190798495709352031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43857784254397994279136041 32893338190798495709352031)
      ·
        refine ⟨49340007286197743564028047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32893338190798495709352031 49340007286197743564028047)
        ·
          refine ⟨74010010929296615346042071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49340007286197743564028047 74010010929296615346042071)
          ·
            refine ⟨111015016393944923019063107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74010010929296615346042071 111015016393944923019063107)
            ·
              refine ⟨166522524590917384528594661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111015016393944923019063107 166522524590917384528594661)
              ·
                refine ⟨31222973360797009599111499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166522524590917384528594661 31222973360797009599111499)
                ·
                  refine ⟨46834460041195514398667249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31222973360797009599111499 46834460041195514398667249)
                  ·
                    refine ⟨35125845030896635799000437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46834460041195514398667249 35125845030896635799000437)
                    ·
                      refine ⟨3293047971646559606156291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35125845030896635799000437 3293047971646559606156291)
                      ·
                        rfl

theorem cell23_6413188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_6413188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413188 prefixEnd_6413188 := by exact prefixLift 6413188
  have htrace : WordTrace (prefixWord ++ tailWord_6413188) baseStart_6413188 baseEnd_6413188 := by
    simpa [prefixWord, tailWord_6413188, baseEnd_6413188] using wordTrace_append hprefix tailTrace_6413188
  have hstable : (prefixWord ++ tailWord_6413188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413188).length < 2 ^ (prefixWord ++ tailWord_6413188).sum := by decide
  have hdescent : baseEnd_6413188 < baseStart_6413188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413229 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_6413229 : Nat := 118140960795 + 6413229 * 2 ^ 59
def prefixEnd_6413229 : Nat := 4983230072969 + 3 ^ 40 * 6413229 * 2
def baseEnd_6413229 : Nat := 1097689674784464648581201

theorem tailTrace_6413229 : CollatzResearch.WordTrace tailWord_6413229 prefixEnd_6413229 1097689674784464648581201 := by
  unfold tailWord_6413229
  simp only [CollatzResearch.WordTrace]
  refine ⟨233909678082974100157634741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155939785388649400105089827 233909678082974100157634741)
  ·
    refine ⟨21929032320278821889778257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233909678082974100157634741 21929032320278821889778257)
    ·
      refine ⟨16446774240209116417333693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21929032320278821889778257 16446774240209116417333693)
      ·
        refine ⟨6167540340078418656500135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16446774240209116417333693 6167540340078418656500135)
        ·
          refine ⟨9251310510117627984750203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6167540340078418656500135 9251310510117627984750203)
          ·
            refine ⟨13876965765176441977125305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9251310510117627984750203 13876965765176441977125305)
            ·
              refine ⟨10407724323882331482843979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13876965765176441977125305 10407724323882331482843979)
              ·
                refine ⟨15611586485823497224265969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10407724323882331482843979 15611586485823497224265969)
                ·
                  refine ⟨11708689864367622918199477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15611586485823497224265969 11708689864367622918199477)
                  ·
                    refine ⟨1097689674784464648581201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11708689864367622918199477 1097689674784464648581201)
                    ·
                      rfl

theorem cell23_6413229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_6413229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413229 prefixEnd_6413229 := by exact prefixLift 6413229
  have htrace : WordTrace (prefixWord ++ tailWord_6413229) baseStart_6413229 baseEnd_6413229 := by
    simpa [prefixWord, tailWord_6413229, baseEnd_6413229] using wordTrace_append hprefix tailTrace_6413229
  have hstable : (prefixWord ++ tailWord_6413229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413229).length < 2 ^ (prefixWord ++ tailWord_6413229).sum := by decide
  have hdescent : baseEnd_6413229 < baseStart_6413229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413242 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_6413242 : Nat := 118140960795 + 6413242 * 2 ^ 59
def prefixEnd_6413242 : Nat := 4983230072969 + 3 ^ 40 * 6413242 * 2
def baseEnd_6413242 : Nat := 1097691899867300798293681

theorem tailTrace_6413242 : CollatzResearch.WordTrace tailWord_6413242 prefixEnd_6413242 1097691899867300798293681 := by
  unfold tailWord_6413242
  simp only [CollatzResearch.WordTrace]
  refine ⟨58477538057981750844464495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155940101487951335585238653 58477538057981750844464495)
  ·
    refine ⟨87716307086972626266696743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58477538057981750844464495 87716307086972626266696743)
    ·
      refine ⟨131574460630458939400045115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87716307086972626266696743 131574460630458939400045115)
      ·
        refine ⟨197361690945688409100067673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131574460630458939400045115 197361690945688409100067673)
        ·
          refine ⟨148021268209266306825050755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197361690945688409100067673 148021268209266306825050755)
          ·
            refine ⟨222031902313899460237576133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148021268209266306825050755 222031902313899460237576133)
            ·
              refine ⟨41630981683856148794545525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222031902313899460237576133 41630981683856148794545525)
              ·
                refine ⟨3902904532861513949488643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41630981683856148794545525 3902904532861513949488643)
                ·
                  refine ⟨5854356799292270924232965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902904532861513949488643 5854356799292270924232965)
                  ·
                    refine ⟨1097691899867300798293681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854356799292270924232965 1097691899867300798293681)
                    ·
                      rfl

theorem cell23_6413242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_6413242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413242 prefixEnd_6413242 := by exact prefixLift 6413242
  have htrace : WordTrace (prefixWord ++ tailWord_6413242) baseStart_6413242 baseEnd_6413242 := by
    simpa [prefixWord, tailWord_6413242, baseEnd_6413242] using wordTrace_append hprefix tailTrace_6413242
  have hstable : (prefixWord ++ tailWord_6413242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413242).length < 2 ^ (prefixWord ++ tailWord_6413242).sum := by decide
  have hdescent : baseEnd_6413242 < baseStart_6413242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413258 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_6413258 : Nat := 118140960795 + 6413258 * 2 ^ 59
def prefixEnd_6413258 : Nat := 4983230072969 + 3 ^ 40 * 6413258 * 2
def baseEnd_6413258 : Nat := 3293083915292374332280969

theorem tailTrace_6413258 : CollatzResearch.WordTrace tailWord_6413258 prefixEnd_6413258 3293083915292374332280969 := by
  unfold tailWord_6413258
  simp only [CollatzResearch.WordTrace]
  refine ⟨58477683949967259527610107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155940490533246025406960285 58477683949967259527610107)
  ·
    refine ⟨87716525924950889291415161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58477683949967259527610107 87716525924950889291415161)
    ·
      refine ⟨65787394443713166968561371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87716525924950889291415161 65787394443713166968561371)
      ·
        refine ⟨98681091665569750452842057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65787394443713166968561371 98681091665569750452842057)
        ·
          refine ⟨74010818749177312839631543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98681091665569750452842057 74010818749177312839631543)
          ·
            refine ⟨111016228123765969259447315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74010818749177312839631543 111016228123765969259447315)
            ·
              refine ⟨166524342185648953889170973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111016228123765969259447315 166524342185648953889170973)
              ·
                refine ⟨62446628319618357708439115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166524342185648953889170973 62446628319618357708439115)
                ·
                  refine ⟨93669942479427536562658673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62446628319618357708439115 93669942479427536562658673)
                  ·
                    refine ⟨70252456859570652421994005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93669942479427536562658673 70252456859570652421994005)
                    ·
                      refine ⟨3293083915292374332280969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70252456859570652421994005 3293083915292374332280969)
                      ·
                        rfl

theorem cell23_6413258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_6413258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413258 prefixEnd_6413258 := by exact prefixLift 6413258
  have htrace : WordTrace (prefixWord ++ tailWord_6413258) baseStart_6413258 baseEnd_6413258 := by
    simpa [prefixWord, tailWord_6413258, baseEnd_6413258] using wordTrace_append hprefix tailTrace_6413258
  have hstable : (prefixWord ++ tailWord_6413258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413258).length < 2 ^ (prefixWord ++ tailWord_6413258).sum := by decide
  have hdescent : baseEnd_6413258 < baseStart_6413258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413259 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 1, 4]
def baseStart_6413259 : Nat := 118140960795 + 6413259 * 2 ^ 59
def prefixEnd_6413259 : Nat := 4983230072969 + 3 ^ 40 * 6413259 * 2
def baseEnd_6413259 : Nat := 1097694809591009609456155

theorem tailTrace_6413259 : CollatzResearch.WordTrace tailWord_6413259 prefixEnd_6413259 1097694809591009609456155 := by
  unfold tailWord_6413259
  simp only [CollatzResearch.WordTrace]
  refine ⟨233910772272865415281226831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155940514848576943520817887 233910772272865415281226831)
  ·
    refine ⟨350866158409298122921840247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233910772272865415281226831 350866158409298122921840247)
    ·
      refine ⟨526299237613947184382760371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350866158409298122921840247 526299237613947184382760371)
      ·
        refine ⟨789448856420920776574140557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526299237613947184382760371 789448856420920776574140557)
        ·
          refine ⟨296043321157845291215302709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789448856420920776574140557 296043321157845291215302709)
          ·
            refine ⟨27754061358547996051434629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296043321157845291215302709 27754061358547996051434629)
            ·
              refine ⟨5203886504727749259643993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27754061358547996051434629 5203886504727749259643993)
              ·
                refine ⟨3902914878545811944732995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5203886504727749259643993 3902914878545811944732995)
                ·
                  refine ⟨5854372317818717917099493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902914878545811944732995 5854372317818717917099493)
                  ·
                    refine ⟨1097694809591009609456155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854372317818717917099493 1097694809591009609456155)
                    ·
                      rfl

theorem cell23_6413259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 4].length) (baseStart_6413259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413259 prefixEnd_6413259 := by exact prefixLift 6413259
  have htrace : WordTrace (prefixWord ++ tailWord_6413259) baseStart_6413259 baseEnd_6413259 := by
    simpa [prefixWord, tailWord_6413259, baseEnd_6413259] using wordTrace_append hprefix tailTrace_6413259
  have hstable : (prefixWord ++ tailWord_6413259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413259).length < 2 ^ (prefixWord ++ tailWord_6413259).sum := by decide
  have hdescent : baseEnd_6413259 < baseStart_6413259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413345 : List Nat := [1, 2, 3, 2, 3, 2, 1, 9]
def baseStart_6413345 : Nat := 118140960795 + 6413345 * 2 ^ 59
def prefixEnd_6413345 : Nat := 4983230072969 + 3 ^ 40 * 6413345 * 2
def baseEnd_6413345 : Nat := 121967725485530203403447

theorem tailTrace_6413345 : CollatzResearch.WordTrace tailWord_6413345 prefixEnd_6413345 121967725485530203403447 := by
  unfold tailWord_6413345
  simp only [CollatzResearch.WordTrace]
  refine ⟨233913908950553851968857489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155942605967035901312571659 233913908950553851968857489)
  ·
    refine ⟨175435431712915388976643117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233913908950553851968857489 175435431712915388976643117)
    ·
      refine ⟨65788286892343270866241169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175435431712915388976643117 65788286892343270866241169)
      ·
        refine ⟨49341215169257453149680877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65788286892343270866241169 49341215169257453149680877)
        ·
          refine ⟨18502955688471544931130329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49341215169257453149680877 18502955688471544931130329)
          ·
            refine ⟨13877216766353658698347747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18502955688471544931130329 13877216766353658698347747)
            ·
              refine ⟨20815825149530488047521621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13877216766353658698347747 20815825149530488047521621)
              ·
                refine ⟨121967725485530203403447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20815825149530488047521621 121967725485530203403447)
                ·
                  rfl

theorem cell23_6413345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 9].length) (baseStart_6413345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413345 prefixEnd_6413345 := by exact prefixLift 6413345
  have htrace : WordTrace (prefixWord ++ tailWord_6413345) baseStart_6413345 baseEnd_6413345 := by
    simpa [prefixWord, tailWord_6413345, baseEnd_6413345] using wordTrace_append hprefix tailTrace_6413345
  have hstable : (prefixWord ++ tailWord_6413345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413345).length < 2 ^ (prefixWord ++ tailWord_6413345).sum := by decide
  have hdescent : baseEnd_6413345 < baseStart_6413345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413355 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3]
def baseStart_6413355 : Nat := 118140960795 + 6413355 * 2 ^ 59
def prefixEnd_6413355 : Nat := 4983230072969 + 3 ^ 40 * 6413355 * 2
def baseEnd_6413355 : Nat := 3293133722915860452768023

theorem tailTrace_6413355 : CollatzResearch.WordTrace tailWord_6413355 prefixEnd_6413355 3293133722915860452768023 := by
  unfold tailWord_6413355
  simp only [CollatzResearch.WordTrace]
  refine ⟨233914273680517623676721519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155942849120345082451147679 233914273680517623676721519)
  ·
    refine ⟨350871410520776435515082279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233914273680517623676721519 350871410520776435515082279)
    ·
      refine ⟨526307115781164653272623419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350871410520776435515082279 526307115781164653272623419)
      ·
        refine ⟨789460673671746979908935129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526307115781164653272623419 789460673671746979908935129)
        ·
          refine ⟨592095505253810234931701347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789460673671746979908935129 592095505253810234931701347)
          ·
            refine ⟨888143257880715352397552021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592095505253810234931701347 888143257880715352397552021)
            ·
              refine ⟨41631715213158532143635251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 888143257880715352397552021 41631715213158532143635251)
              ·
                refine ⟨62447572819737798215452877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41631715213158532143635251 62447572819737798215452877)
                ·
                  refine ⟨23417839807401674330794829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62447572819737798215452877 23417839807401674330794829)
                  ·
                    refine ⟨8781689927775627874048061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23417839807401674330794829 8781689927775627874048061)
                    ·
                      refine ⟨3293133722915860452768023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8781689927775627874048061 3293133722915860452768023)
                      ·
                        rfl

theorem cell23_6413355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3].length) (baseStart_6413355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413355 prefixEnd_6413355 := by exact prefixLift 6413355
  have htrace : WordTrace (prefixWord ++ tailWord_6413355) baseStart_6413355 baseEnd_6413355 := by
    simpa [prefixWord, tailWord_6413355, baseEnd_6413355] using wordTrace_append hprefix tailTrace_6413355
  have hstable : (prefixWord ++ tailWord_6413355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413355).length < 2 ^ (prefixWord ++ tailWord_6413355).sum := by decide
  have hdescent : baseEnd_6413355 < baseStart_6413355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413406 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6413406 : Nat := 118140960795 + 6413406 * 2 ^ 59
def prefixEnd_6413406 : Nat := 4983230072969 + 3 ^ 40 * 6413406 * 2
def baseEnd_6413406 : Nat := 3293159910429239753230289

theorem tailTrace_6413406 : CollatzResearch.WordTrace tailWord_6413406 prefixEnd_6413406 3293159910429239753230289 := by
  unfold tailWord_6413406
  simp only [CollatzResearch.WordTrace]
  refine ⟨29239516725416607423353509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155944089202221906257885381 29239516725416607423353509)
  ·
    refine ⟨5482409386015613891878783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29239516725416607423353509 5482409386015613891878783)
    ·
      refine ⟨8223614079023420837818175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5482409386015613891878783 8223614079023420837818175)
      ·
        refine ⟨12335421118535131256727263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223614079023420837818175 12335421118535131256727263)
        ·
          refine ⟨18503131677802696885090895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335421118535131256727263 18503131677802696885090895)
          ·
            refine ⟨27754697516704045327636343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18503131677802696885090895 27754697516704045327636343)
            ·
              refine ⟨41632046275056067991454515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27754697516704045327636343 41632046275056067991454515)
              ·
                refine ⟨62448069412584101987181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41632046275056067991454515 62448069412584101987181773)
                ·
                  refine ⟨23418026029719038245193165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62448069412584101987181773 23418026029719038245193165)
                  ·
                    refine ⟨8781759761144639341947437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23418026029719038245193165 8781759761144639341947437)
                    ·
                      refine ⟨3293159910429239753230289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8781759761144639341947437 3293159910429239753230289)
                      ·
                        rfl

theorem cell23_6413406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6413406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413406 prefixEnd_6413406 := by exact prefixLift 6413406
  have htrace : WordTrace (prefixWord ++ tailWord_6413406) baseStart_6413406 baseEnd_6413406 := by
    simpa [prefixWord, tailWord_6413406, baseEnd_6413406] using wordTrace_append hprefix tailTrace_6413406
  have hstable : (prefixWord ++ tailWord_6413406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413406).length < 2 ^ (prefixWord ++ tailWord_6413406).sum := by decide
  have hdescent : baseEnd_6413406 < baseStart_6413406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413469 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 5]
def baseStart_6413469 : Nat := 118140960795 + 6413469 * 2 ^ 59
def prefixEnd_6413469 : Nat := 4983230072969 + 3 ^ 40 * 6413469 * 2
def baseEnd_6413469 : Nat := 365910251078941445193611

theorem tailTrace_6413469 : CollatzResearch.WordTrace tailWord_6413469 prefixEnd_6413469 365910251078941445193611 := by
  unfold tailWord_6413469
  simp only [CollatzResearch.WordTrace]
  refine ⟨233918431602104621146371461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155945621068069747430914307 233918431602104621146371461)
  ·
    refine ⟨43859705925394616464944649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233918431602104621146371461 43859705925394616464944649)
    ·
      refine ⟨32894779444045962348708487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43859705925394616464944649 32894779444045962348708487)
      ·
        refine ⟨49342169166068943523062731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32894779444045962348708487 49342169166068943523062731)
        ·
          refine ⟨74013253749103415284594097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49342169166068943523062731 74013253749103415284594097)
          ·
            refine ⟨55509940311827561463445573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74013253749103415284594097 55509940311827561463445573)
            ·
              refine ⟨10408113808467667774396045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55509940311827561463445573 10408113808467667774396045)
              ·
                refine ⟨3903042678175375415398517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10408113808467667774396045 3903042678175375415398517)
                ·
                  refine ⟨365910251078941445193611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3903042678175375415398517 365910251078941445193611)
                  ·
                    rfl

theorem cell23_6413469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_6413469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413469 prefixEnd_6413469 := by exact prefixLift 6413469
  have htrace : WordTrace (prefixWord ++ tailWord_6413469) baseStart_6413469 baseEnd_6413469 := by
    simpa [prefixWord, tailWord_6413469, baseEnd_6413469] using wordTrace_append hprefix tailTrace_6413469
  have hstable : (prefixWord ++ tailWord_6413469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413469).length < 2 ^ (prefixWord ++ tailWord_6413469).sum := by decide
  have hdescent : baseEnd_6413469 < baseStart_6413469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413475 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_6413475 : Nat := 118140960795 + 6413475 * 2 ^ 59
def prefixEnd_6413475 : Nat := 4983230072969 + 3 ^ 40 * 6413475 * 2
def baseEnd_6413475 : Nat := 3293195340594399983267471

theorem tailTrace_6413475 : CollatzResearch.WordTrace tailWord_6413475 prefixEnd_6413475 3293195340594399983267471 := by
  unfold tailWord_6413475
  simp only [CollatzResearch.WordTrace]
  refine ⟨233918650440082884171089879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155945766960055256114059919 233918650440082884171089879)
  ·
    refine ⟨350877975660124326256634819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233918650440082884171089879 350877975660124326256634819)
    ·
      refine ⟨526316963490186489384952229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350877975660124326256634819 526316963490186489384952229)
      ·
        refine ⟨98684430654409966759678543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526316963490186489384952229 98684430654409966759678543)
        ·
          refine ⟨148026645981614950139517815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98684430654409966759678543 148026645981614950139517815)
          ·
            refine ⟨222039968972422425209276723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148026645981614950139517815 222039968972422425209276723)
            ·
              refine ⟨333059953458633637813915085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222039968972422425209276723 333059953458633637813915085)
              ·
                refine ⟨124897482546987614180218157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333059953458633637813915085 124897482546987614180218157)
                ·
                  refine ⟨46836555955120355317581809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124897482546987614180218157 46836555955120355317581809)
                  ·
                    refine ⟨35127416966340266488186357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46836555955120355317581809 35127416966340266488186357)
                    ·
                      refine ⟨3293195340594399983267471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35127416966340266488186357 3293195340594399983267471)
                      ·
                        rfl

theorem cell23_6413475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_6413475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413475 prefixEnd_6413475 := by exact prefixLift 6413475
  have htrace : WordTrace (prefixWord ++ tailWord_6413475) baseStart_6413475 baseEnd_6413475 := by
    simpa [prefixWord, tailWord_6413475, baseEnd_6413475] using wordTrace_append hprefix tailTrace_6413475
  have hstable : (prefixWord ++ tailWord_6413475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413475).length < 2 ^ (prefixWord ++ tailWord_6413475).sum := by decide
  have hdescent : baseEnd_6413475 < baseStart_6413475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413479 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6413479 : Nat := 118140960795 + 6413479 * 2 ^ 59
def prefixEnd_6413479 : Nat := 4983230072969 + 3 ^ 40 * 6413479 * 2
def baseEnd_6413479 : Nat := 3293197394517017967617453

theorem tailTrace_6413479 : CollatzResearch.WordTrace tailWord_6413479 prefixEnd_6413479 3293197394517017967617453 := by
  unfold tailWord_6413479
  simp only [CollatzResearch.WordTrace]
  refine ⟨233918796332068392854235491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155945864221378928569490327 233918796332068392854235491)
  ·
    refine ⟨350878194498102589281353237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233918796332068392854235491 350878194498102589281353237)
    ·
      refine ⟨16447415367098558872563433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 350878194498102589281353237 16447415367098558872563433)
      ·
        refine ⟨12335561525323919154422575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16447415367098558872563433 12335561525323919154422575)
        ·
          refine ⟨18503342287985878731633863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335561525323919154422575 18503342287985878731633863)
          ·
            refine ⟨27755013431978818097450795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18503342287985878731633863 27755013431978818097450795)
            ·
              refine ⟨41632520147968227146176193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27755013431978818097450795 41632520147968227146176193)
              ·
                refine ⟨31224390110976170359632145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41632520147968227146176193 31224390110976170359632145)
                ·
                  refine ⟨23418292583232127769724109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31224390110976170359632145 23418292583232127769724109)
                  ·
                    refine ⟨8781859718712047913646541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23418292583232127769724109 8781859718712047913646541)
                    ·
                      refine ⟨3293197394517017967617453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8781859718712047913646541 3293197394517017967617453)
                      ·
                        rfl

theorem cell23_6413479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6413479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413479 prefixEnd_6413479 := by exact prefixLift 6413479
  have htrace : WordTrace (prefixWord ++ tailWord_6413479) baseStart_6413479 baseEnd_6413479 := by
    simpa [prefixWord, tailWord_6413479, baseEnd_6413479] using wordTrace_append hprefix tailTrace_6413479
  have hstable : (prefixWord ++ tailWord_6413479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413479).length < 2 ^ (prefixWord ++ tailWord_6413479).sum := by decide
  have hdescent : baseEnd_6413479 < baseStart_6413479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413515 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_6413515 : Nat := 118140960795 + 6413515 * 2 ^ 59
def prefixEnd_6413515 : Nat := 4983230072969 + 3 ^ 40 * 6413515 * 2
def baseEnd_6413515 : Nat := 3293215879820579826767287

theorem tailTrace_6413515 : CollatzResearch.WordTrace tailWord_6413515 prefixEnd_6413515 3293215879820579826767287 := by
  unfold tailWord_6413515
  simp only [CollatzResearch.WordTrace]
  refine ⟨233920109359937971002545999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155946739573291980668363999 233920109359937971002545999)
  ·
    refine ⟨350880164039906956503818999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233920109359937971002545999 350880164039906956503818999)
    ·
      refine ⟨526320246059860434755728499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350880164039906956503818999 526320246059860434755728499)
      ·
        refine ⟨789480369089790652133592749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526320246059860434755728499 789480369089790652133592749)
        ·
          refine ⟨296055138408671494550097281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789480369089790652133592749 296055138408671494550097281)
          ·
            refine ⟨222041353806503620912572961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296055138408671494550097281 222041353806503620912572961)
            ·
              refine ⟨166531015354877715684429721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222041353806503620912572961 166531015354877715684429721)
              ·
                refine ⟨124898261516158286763322291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166531015354877715684429721 124898261516158286763322291)
                ·
                  refine ⟨187347392274237430144983437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124898261516158286763322291 187347392274237430144983437)
                  ·
                    refine ⟨70255272102839036304368789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187347392274237430144983437 70255272102839036304368789)
                    ·
                      refine ⟨3293215879820579826767287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70255272102839036304368789 3293215879820579826767287)
                      ·
                        rfl

theorem cell23_6413515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_6413515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413515 prefixEnd_6413515 := by exact prefixLift 6413515
  have htrace : WordTrace (prefixWord ++ tailWord_6413515) baseStart_6413515 baseEnd_6413515 := by
    simpa [prefixWord, tailWord_6413515, baseEnd_6413515] using wordTrace_append hprefix tailTrace_6413515
  have hstable : (prefixWord ++ tailWord_6413515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413515).length < 2 ^ (prefixWord ++ tailWord_6413515).sum := by decide
  have hdescent : baseEnd_6413515 < baseStart_6413515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413546 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_6413546 : Nat := 118140960795 + 6413546 * 2 ^ 59
def prefixEnd_6413546 : Nat := 4983230072969 + 3 ^ 40 * 6413546 * 2
def baseEnd_6413546 : Nat := 1097743932573623068493215

theorem tailTrace_6413546 : CollatzResearch.WordTrace tailWord_6413546 prefixEnd_6413546 1097743932573623068493215 := by
  unfold tailWord_6413546
  simp only [CollatzResearch.WordTrace]
  refine ⟨58480310005706415824231123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155947493348550442197949661 58480310005706415824231123)
  ·
    refine ⟨87720465008559623736346685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58480310005706415824231123 87720465008559623736346685)
    ·
      refine ⟨32895174378209858901130007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87720465008559623736346685 32895174378209858901130007)
      ·
        refine ⟨49342761567314788351695011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32895174378209858901130007 49342761567314788351695011)
        ·
          refine ⟨74014142350972182527542517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49342761567314788351695011 74014142350972182527542517)
          ·
            refine ⟨6938825845403642111957111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74014142350972182527542517 6938825845403642111957111)
            ·
              refine ⟨10408238768105463167935667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938825845403642111957111 10408238768105463167935667)
              ·
                refine ⟨15612358152158194751903501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408238768105463167935667 15612358152158194751903501)
                ·
                  refine ⟨5854634307059323031963813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15612358152158194751903501 5854634307059323031963813)
                  ·
                    refine ⟨1097743932573623068493215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854634307059323031963813 1097743932573623068493215)
                    ·
                      rfl

theorem cell23_6413546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_6413546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413546 prefixEnd_6413546 := by exact prefixLift 6413546
  have htrace : WordTrace (prefixWord ++ tailWord_6413546) baseStart_6413546 baseEnd_6413546 := by
    simpa [prefixWord, tailWord_6413546, baseEnd_6413546] using wordTrace_append hprefix tailTrace_6413546
  have hstable : (prefixWord ++ tailWord_6413546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413546).length < 2 ^ (prefixWord ++ tailWord_6413546).sum := by decide
  have hdescent : baseEnd_6413546 < baseStart_6413546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413596 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_6413596 : Nat := 118140960795 + 6413596 * 2 ^ 59
def prefixEnd_6413596 : Nat := 4983230072969 + 3 ^ 40 * 6413596 * 2
def baseEnd_6413596 : Nat := 3293257471753594009854415

theorem tailTrace_6413596 : CollatzResearch.WordTrace tailWord_6413596 prefixEnd_6413596 3293257471753594009854415 := by
  unfold tailWord_6413596
  simp only [CollatzResearch.WordTrace]
  refine ⟨116961531836322260918122321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155948709115096347890829761 116961531836322260918122321)
  ·
    refine ⟨87721148877241695688591741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116961531836322260918122321 87721148877241695688591741)
    ·
      refine ⟨32895430828965635883221903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87721148877241695688591741 32895430828965635883221903)
      ·
        refine ⟨49343146243448453824832855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32895430828965635883221903 49343146243448453824832855)
        ·
          refine ⟨74014719365172680737249283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49343146243448453824832855 74014719365172680737249283)
          ·
            refine ⟨111022079047759021105873925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74014719365172680737249283 111022079047759021105873925)
            ·
              refine ⟨20816639821454816457351361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111022079047759021105873925 20816639821454816457351361)
              ·
                refine ⟨15612479866091112343013521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20816639821454816457351361 15612479866091112343013521)
                ·
                  refine ⟨11709359899568334257260141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15612479866091112343013521 11709359899568334257260141)
                  ·
                    refine ⟨4391009962338125346472553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11709359899568334257260141 4391009962338125346472553)
                    ·
                      refine ⟨3293257471753594009854415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391009962338125346472553 3293257471753594009854415)
                      ·
                        rfl

theorem cell23_6413596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_6413596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413596 prefixEnd_6413596 := by exact prefixLift 6413596
  have htrace : WordTrace (prefixWord ++ tailWord_6413596) baseStart_6413596 baseEnd_6413596 := by
    simpa [prefixWord, tailWord_6413596, baseEnd_6413596] using wordTrace_append hprefix tailTrace_6413596
  have hstable : (prefixWord ++ tailWord_6413596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413596).length < 2 ^ (prefixWord ++ tailWord_6413596).sum := by decide
  have hdescent : baseEnd_6413596 < baseStart_6413596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413603 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 1, 1, 3]
def baseStart_6413603 : Nat := 118140960795 + 6413603 * 2 ^ 59
def prefixEnd_6413603 : Nat := 4983230072969 + 3 ^ 40 * 6413603 * 2
def baseEnd_6413603 : Nat := 3293261066118175482466883

theorem tailTrace_6413603 : CollatzResearch.WordTrace tailWord_6413603 prefixEnd_6413603 3293261066118175482466883 := by
  unfold tailWord_6413603
  simp only [CollatzResearch.WordTrace]
  refine ⟨233923318983619162031749463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155948879322412774687832975 233923318983619162031749463)
  ·
    refine ⟨350884978475428743047624195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233923318983619162031749463 350884978475428743047624195)
    ·
      refine ⟨526327467713143114571436293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350884978475428743047624195 526327467713143114571436293)
      ·
        refine ⟨98686400196214333982144305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526327467713143114571436293 98686400196214333982144305)
        ·
          refine ⟨74014800147160750486608229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98686400196214333982144305 74014800147160750486608229)
          ·
            refine ⟨13877775027592640716239043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74014800147160750486608229 13877775027592640716239043)
            ·
              refine ⟨20816662541388961074358565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13877775027592640716239043 20816662541388961074358565)
              ·
                refine ⟨3903124226510430201442231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20816662541388961074358565 3903124226510430201442231)
                ·
                  refine ⟨5854686339765645302163347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903124226510430201442231 5854686339765645302163347)
                  ·
                    refine ⟨8782029509648467953245021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854686339765645302163347 8782029509648467953245021)
                    ·
                      refine ⟨3293261066118175482466883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782029509648467953245021 3293261066118175482466883)
                      ·
                        rfl

theorem cell23_6413603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_6413603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413603 prefixEnd_6413603 := by exact prefixLift 6413603
  have htrace : WordTrace (prefixWord ++ tailWord_6413603) baseStart_6413603 baseEnd_6413603 := by
    simpa [prefixWord, tailWord_6413603, baseEnd_6413603] using wordTrace_append hprefix tailTrace_6413603
  have hstable : (prefixWord ++ tailWord_6413603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413603).length < 2 ^ (prefixWord ++ tailWord_6413603).sum := by decide
  have hdescent : baseEnd_6413603 < baseStart_6413603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413612 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_6413612 : Nat := 118140960795 + 6413612 * 2 ^ 59
def prefixEnd_6413612 : Nat := 4983230072969 + 3 ^ 40 * 6413612 * 2
def baseEnd_6413612 : Nat := 3293265687444065947254341

theorem tailTrace_6413612 : CollatzResearch.WordTrace tailWord_6413612 prefixEnd_6413612 3293265687444065947254341 := by
  unfold tailWord_6413612
  simp only [CollatzResearch.WordTrace]
  refine ⟨116961823620293278284413545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155949098160391037712551393 116961823620293278284413545)
  ·
    refine ⟨87721367715219958713310159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116961823620293278284413545 87721367715219958713310159)
    ·
      refine ⟨131582051572829938069965239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87721367715219958713310159 131582051572829938069965239)
      ·
        refine ⟨197373077359244907104947859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131582051572829938069965239 197373077359244907104947859)
        ·
          refine ⟨296059616038867360657421789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197373077359244907104947859 296059616038867360657421789)
          ·
            refine ⟨111022356014575260246533171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296059616038867360657421789 111022356014575260246533171)
            ·
              refine ⟨166533534021862890369799757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111022356014575260246533171 166533534021862890369799757)
              ·
                refine ⟨62450075258198583888674909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166533534021862890369799757 62450075258198583888674909)
                ·
                  refine ⟨23418778221824468958253091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62450075258198583888674909 23418778221824468958253091)
                  ·
                    refine ⟨35128167332736703437379637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23418778221824468958253091 35128167332736703437379637)
                    ·
                      refine ⟨3293265687444065947254341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35128167332736703437379637 3293265687444065947254341)
                      ·
                        rfl

theorem cell23_6413612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_6413612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413612 prefixEnd_6413612 := by exact prefixLift 6413612
  have htrace : WordTrace (prefixWord ++ tailWord_6413612) baseStart_6413612 baseEnd_6413612 := by
    simpa [prefixWord, tailWord_6413612, baseEnd_6413612] using wordTrace_append hprefix tailTrace_6413612
  have hstable : (prefixWord ++ tailWord_6413612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413612).length < 2 ^ (prefixWord ++ tailWord_6413612).sum := by decide
  have hdescent : baseEnd_6413612 < baseStart_6413612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413619 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 1, 6]
def baseStart_6413619 : Nat := 118140960795 + 6413619 * 2 ^ 59
def prefixEnd_6413619 : Nat := 4983230072969 + 3 ^ 40 * 6413619 * 2
def baseEnd_6413619 : Nat := 1097756427269549139955603

theorem tailTrace_6413619 : CollatzResearch.WordTrace tailWord_6413619 prefixEnd_6413619 1097756427269549139955603 := by
  unfold tailWord_6413619
  simp only [CollatzResearch.WordTrace]
  refine ⟨233923902551561196764331911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155949268367707464509554607 233923902551561196764331911)
  ·
    refine ⟨350885853827341795146497867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233923902551561196764331911 350885853827341795146497867)
    ·
      refine ⟨526328780741012692719746801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350885853827341795146497867 526328780741012692719746801)
      ·
        refine ⟨394746585555759519539810101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526328780741012692719746801 394746585555759519539810101)
        ·
          refine ⟨37007492395852454956857197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394746585555759519539810101 37007492395852454956857197)
          ·
            refine ⟨13877809648444670608821449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37007492395852454956857197 13877809648444670608821449)
            ·
              refine ⟨10408357236333502956616087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13877809648444670608821449 10408357236333502956616087)
              ·
                refine ⟨15612535854500254434924131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408357236333502956616087 15612535854500254434924131)
                ·
                  refine ⟨23418803781750381652386197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15612535854500254434924131 23418803781750381652386197)
                  ·
                    refine ⟨1097756427269549139955603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23418803781750381652386197 1097756427269549139955603)
                    ·
                      rfl

theorem cell23_6413619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 6].length) (baseStart_6413619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413619 prefixEnd_6413619 := by exact prefixLift 6413619
  have htrace : WordTrace (prefixWord ++ tailWord_6413619) baseStart_6413619 baseEnd_6413619 := by
    simpa [prefixWord, tailWord_6413619, baseEnd_6413619] using wordTrace_append hprefix tailTrace_6413619
  have hstable : (prefixWord ++ tailWord_6413619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413619).length < 2 ^ (prefixWord ++ tailWord_6413619).sum := by decide
  have hdescent : baseEnd_6413619 < baseStart_6413619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413636 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6413636 : Nat := 118140960795 + 6413636 * 2 ^ 59
def prefixEnd_6413636 : Nat := 4983230072969 + 3 ^ 40 * 6413636 * 2
def baseEnd_6413636 : Nat := 1097759336993257951118077

theorem tailTrace_6413636 : CollatzResearch.WordTrace tailWord_6413636 prefixEnd_6413636 1097759336993257951118077 := by
  unfold tailWord_6413636
  simp only [CollatzResearch.WordTrace]
  refine ⟨116962261296249804333850381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155949681728333072445133841 116962261296249804333850381)
  ·
    refine ⟨43860847986093676625193893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116962261296249804333850381 43860847986093676625193893)
    ·
      refine ⟨8223908997392564367223855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43860847986093676625193893 8223908997392564367223855)
      ·
        refine ⟨12335863496088846550835783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223908997392564367223855 12335863496088846550835783)
        ·
          refine ⟨18503795244133269826253675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335863496088846550835783 18503795244133269826253675)
          ·
            refine ⟨27755692866199904739380513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18503795244133269826253675 27755692866199904739380513)
            ·
              refine ⟨20816769649649928554535385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27755692866199904739380513 20816769649649928554535385)
              ·
                refine ⟨15612577237237446415901539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20816769649649928554535385 15612577237237446415901539)
                ·
                  refine ⟨23418865855856169623852309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15612577237237446415901539 23418865855856169623852309)
                  ·
                    refine ⟨1097759336993257951118077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23418865855856169623852309 1097759336993257951118077)
                    ·
                      rfl

theorem cell23_6413636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6413636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413636 prefixEnd_6413636 := by exact prefixLift 6413636
  have htrace : WordTrace (prefixWord ++ tailWord_6413636) baseStart_6413636 baseEnd_6413636 := by
    simpa [prefixWord, tailWord_6413636, baseEnd_6413636] using wordTrace_append hprefix tailTrace_6413636
  have hstable : (prefixWord ++ tailWord_6413636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413636).length < 2 ^ (prefixWord ++ tailWord_6413636).sum := by decide
  have hdescent : baseEnd_6413636 < baseStart_6413636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413639 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_6413639 : Nat := 118140960795 + 6413639 * 2 ^ 59
def prefixEnd_6413639 : Nat := 4983230072969 + 3 ^ 40 * 6413639 * 2
def baseEnd_6413639 : Nat := 3293279551421737341616717

theorem tailTrace_6413639 : CollatzResearch.WordTrace tailWord_6413639 prefixEnd_6413639 3293279551421737341616717 := by
  unfold tailWord_6413639
  simp only [CollatzResearch.WordTrace]
  refine ⟨233924632011488740180059971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155949754674325826786706647 233924632011488740180059971)
  ·
    refine ⟨350886948017233110270089957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233924632011488740180059971 350886948017233110270089957)
    ·
      refine ⟨65791302753231208175641867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350886948017233110270089957 65791302753231208175641867)
      ·
        refine ⟨98686954129846812263462801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65791302753231208175641867 98686954129846812263462801)
        ·
          refine ⟨74015215597385109197597101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98686954129846812263462801 74015215597385109197597101)
          ·
            refine ⟨27755705849019415949098913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74015215597385109197597101 27755705849019415949098913)
            ·
              refine ⟨20816779386764561961824185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27755705849019415949098913 20816779386764561961824185)
              ·
                refine ⟨15612584540073421471368139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20816779386764561961824185 15612584540073421471368139)
                ·
                  refine ⟨23418876810110132207052209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15612584540073421471368139 23418876810110132207052209)
                  ·
                    refine ⟨17564157607582599155289157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23418876810110132207052209 17564157607582599155289157)
                    ·
                      refine ⟨3293279551421737341616717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17564157607582599155289157 3293279551421737341616717)
                      ·
                        rfl

theorem cell23_6413639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_6413639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413639 prefixEnd_6413639 := by exact prefixLift 6413639
  have htrace : WordTrace (prefixWord ++ tailWord_6413639) baseStart_6413639 baseEnd_6413639 := by
    simpa [prefixWord, tailWord_6413639, baseEnd_6413639] using wordTrace_append hprefix tailTrace_6413639
  have hstable : (prefixWord ++ tailWord_6413639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413639).length < 2 ^ (prefixWord ++ tailWord_6413639).sum := by decide
  have hdescent : baseEnd_6413639 < baseStart_6413639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413646 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_6413646 : Nat := 118140960795 + 6413646 * 2 ^ 59
def prefixEnd_6413646 : Nat := 4983230072969 + 3 ^ 40 * 6413646 * 2
def baseEnd_6413646 : Nat := 3293283145786318814229185

theorem tailTrace_6413646 : CollatzResearch.WordTrace tailWord_6413646 prefixEnd_6413646 3293283145786318814229185 := by
  unfold tailWord_6413646
  simp only [CollatzResearch.WordTrace]
  refine ⟨29240610915307922546945599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155949924881642253583709861 29240610915307922546945599)
  ·
    refine ⟨43860916372961883820418399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29240610915307922546945599 43860916372961883820418399)
    ·
      refine ⟨65791374559442825730627599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43860916372961883820418399 65791374559442825730627599)
      ·
        refine ⟨98687061839164238595941399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65791374559442825730627599 98687061839164238595941399)
        ·
          refine ⟨148030592758746357893912099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98687061839164238595941399 148030592758746357893912099)
          ·
            refine ⟨222045889138119536840868149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148030592758746357893912099 222045889138119536840868149)
            ·
              refine ⟨20816802106698706578831389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222045889138119536840868149 20816802106698706578831389)
              ·
                refine ⟨7806300790012014967061771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20816802106698706578831389 7806300790012014967061771)
                ·
                  refine ⟨11709451185018022450592657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7806300790012014967061771 11709451185018022450592657)
                  ·
                    refine ⟨8782088388763516837944493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11709451185018022450592657 8782088388763516837944493)
                    ·
                      refine ⟨3293283145786318814229185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782088388763516837944493 3293283145786318814229185)
                      ·
                        rfl

theorem cell23_6413646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_6413646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413646 prefixEnd_6413646 := by exact prefixLift 6413646
  have htrace : WordTrace (prefixWord ++ tailWord_6413646) baseStart_6413646 baseEnd_6413646 := by
    simpa [prefixWord, tailWord_6413646, baseEnd_6413646] using wordTrace_append hprefix tailTrace_6413646
  have hstable : (prefixWord ++ tailWord_6413646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413646).length < 2 ^ (prefixWord ++ tailWord_6413646).sum := by decide
  have hdescent : baseEnd_6413646 < baseStart_6413646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413653 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_6413653 : Nat := 118140960795 + 6413653 * 2 ^ 59
def prefixEnd_6413653 : Nat := 4983230072969 + 3 ^ 40 * 6413653 * 2
def baseEnd_6413653 : Nat := 1097762246716966762280551

theorem tailTrace_6413653 : CollatzResearch.WordTrace tailWord_6413653 prefixEnd_6413653 1097762246716966762280551 := by
  unfold tailWord_6413653
  simp only [CollatzResearch.WordTrace]
  refine ⟨233925142633438020571069613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155950095088958680380713075 233925142633438020571069613)
  ·
    refine ⟨87721928487539257714151105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233925142633438020571069613 87721928487539257714151105)
    ·
      refine ⟨65791446365654443285613329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87721928487539257714151105 65791446365654443285613329)
      ·
        refine ⟨49343584774240832464209997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65791446365654443285613329 49343584774240832464209997)
        ·
          refine ⟨18503844290340312174078749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49343584774240832464209997 18503844290340312174078749)
          ·
            refine ⟨6938941608877617065279531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18503844290340312174078749 6938941608877617065279531)
            ·
              refine ⟨10408412413316425597919297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938941608877617065279531 10408412413316425597919297)
              ·
                refine ⟨7806309309987319198439473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10408412413316425597919297 7806309309987319198439473)
                ·
                  refine ⟨5854731982490489398829605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806309309987319198439473 5854731982490489398829605)
                  ·
                    refine ⟨1097762246716966762280551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854731982490489398829605 1097762246716966762280551)
                    ·
                      rfl

theorem cell23_6413653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_6413653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413653 prefixEnd_6413653 := by exact prefixLift 6413653
  have htrace : WordTrace (prefixWord ++ tailWord_6413653) baseStart_6413653 baseEnd_6413653 := by
    simpa [prefixWord, tailWord_6413653, baseEnd_6413653] using wordTrace_append hprefix tailTrace_6413653
  have hstable : (prefixWord ++ tailWord_6413653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413653).length < 2 ^ (prefixWord ++ tailWord_6413653).sum := by decide
  have hdescent : baseEnd_6413653 < baseStart_6413653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413654 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6413654 : Nat := 118140960795 + 6413654 * 2 ^ 59
def prefixEnd_6413654 : Nat := 4983230072969 + 3 ^ 40 * 6413654 * 2
def baseEnd_6413654 : Nat := 3293287253631554782929149

theorem tailTrace_6413654 : CollatzResearch.WordTrace tailWord_6413654 prefixEnd_6413654 3293287253631554782929149 := by
  unfold tailWord_6413654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14620323694152149858866001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155950119404289598494570677 14620323694152149858866001)
  ·
    refine ⟨10965242770614112394149501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14620323694152149858866001 10965242770614112394149501)
    ·
      refine ⟨4111966038980292147806063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10965242770614112394149501 4111966038980292147806063)
      ·
        refine ⟨6167949058470438221709095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111966038980292147806063 6167949058470438221709095)
        ·
          refine ⟨9251923587705657332563643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6167949058470438221709095 9251923587705657332563643)
          ·
            refine ⟨13877885381558485998845465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9251923587705657332563643 13877885381558485998845465)
            ·
              refine ⟨10408414036168864499134099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13877885381558485998845465 10408414036168864499134099)
              ·
                refine ⟨15612621054253296748701149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408414036168864499134099 15612621054253296748701149)
                ·
                  refine ⟨5854732895344986280762931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15612621054253296748701149 5854732895344986280762931)
                  ·
                    refine ⟨8782099343017479421144397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854732895344986280762931 8782099343017479421144397)
                    ·
                      refine ⟨3293287253631554782929149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782099343017479421144397 3293287253631554782929149)
                      ·
                        rfl

theorem cell23_6413654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6413654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413654 prefixEnd_6413654 := by exact prefixLift 6413654
  have htrace : WordTrace (prefixWord ++ tailWord_6413654) baseStart_6413654 baseEnd_6413654 := by
    simpa [prefixWord, tailWord_6413654, baseEnd_6413654] using wordTrace_append hprefix tailTrace_6413654
  have hstable : (prefixWord ++ tailWord_6413654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413654).length < 2 ^ (prefixWord ++ tailWord_6413654).sum := by decide
  have hdescent : baseEnd_6413654 < baseStart_6413654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413676 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_6413676 : Nat := 118140960795 + 6413676 * 2 ^ 59
def prefixEnd_6413676 : Nat := 4983230072969 + 3 ^ 40 * 6413676 * 2
def baseEnd_6413676 : Nat := 3293298550205953696854047

theorem tailTrace_6413676 : CollatzResearch.WordTrace tailWord_6413676 prefixEnd_6413676 3293298550205953696854047 := by
  unfold tailWord_6413676
  simp only [CollatzResearch.WordTrace]
  refine ⟨116962990756177347749578441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155950654341569796999437921 116962990756177347749578441)
  ·
    refine ⟨87722243067133010812183831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116962990756177347749578441 87722243067133010812183831)
    ·
      refine ⟨131583364600699516218275747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87722243067133010812183831 131583364600699516218275747)
      ·
        refine ⟨197375046901049274327413621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131583364600699516218275747 197375046901049274327413621)
        ·
          refine ⟨18503910646973369468195027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197375046901049274327413621 18503910646973369468195027)
          ·
            refine ⟨27755865970460054202292541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18503910646973369468195027 27755865970460054202292541)
            ·
              refine ⟨10408449738922520325859703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27755865970460054202292541 10408449738922520325859703)
              ·
                refine ⟨15612674608383780488789555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408449738922520325859703 15612674608383780488789555)
                ·
                  refine ⟨23419011912575670733184333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15612674608383780488789555 23419011912575670733184333)
                  ·
                    refine ⟨8782129467215876524944125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23419011912575670733184333 8782129467215876524944125)
                    ·
                      refine ⟨3293298550205953696854047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782129467215876524944125 3293298550205953696854047)
                      ·
                        rfl

theorem cell23_6413676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_6413676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413676 prefixEnd_6413676 := by exact prefixLift 6413676
  have htrace : WordTrace (prefixWord ++ tailWord_6413676) baseStart_6413676 baseEnd_6413676 := by
    simpa [prefixWord, tailWord_6413676, baseEnd_6413676] using wordTrace_append hprefix tailTrace_6413676
  have hstable : (prefixWord ++ tailWord_6413676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413676).length < 2 ^ (prefixWord ++ tailWord_6413676).sum := by decide
  have hdescent : baseEnd_6413676 < baseStart_6413676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413703 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_6413703 : Nat := 118140960795 + 6413703 * 2 ^ 59
def prefixEnd_6413703 : Nat := 4983230072969 + 3 ^ 40 * 6413703 * 2
def baseEnd_6413703 : Nat := 3293312414183625091216423

theorem tailTrace_6413703 : CollatzResearch.WordTrace tailWord_6413703 prefixEnd_6413703 3293312414183625091216423 := by
  unfold tailWord_6413703
  simp only [CollatzResearch.WordTrace]
  refine ⟨233926966283256879110389763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155951310855504586073593175 233926966283256879110389763)
  ·
    refine ⟨350890449424885318665584645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233926966283256879110389763 350890449424885318665584645)
    ·
      refine ⟨65791959267165997249797121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350890449424885318665584645 65791959267165997249797121)
      ·
        refine ⟨49343969450374497937347841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65791959267165997249797121 49343969450374497937347841)
        ·
          refine ⟨37007977087780873453010881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49343969450374497937347841 37007977087780873453010881)
          ·
            refine ⟨27755982815835655089758161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37007977087780873453010881 27755982815835655089758161)
            ·
              refine ⟨20816987111876741317318621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27755982815835655089758161 20816987111876741317318621)
              ·
                refine ⟨7806370166953777993994483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20816987111876741317318621 7806370166953777993994483)
                ·
                  refine ⟨11709555250430666990991725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7806370166953777993994483 11709555250430666990991725)
                  ·
                    refine ⟨4391083218911500121621897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11709555250430666990991725 4391083218911500121621897)
                    ·
                      refine ⟨3293312414183625091216423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391083218911500121621897 3293312414183625091216423)
                      ·
                        rfl

theorem cell23_6413703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_6413703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413703 prefixEnd_6413703 := by exact prefixLift 6413703
  have htrace : WordTrace (prefixWord ++ tailWord_6413703) baseStart_6413703 baseEnd_6413703 := by
    simpa [prefixWord, tailWord_6413703, baseEnd_6413703] using wordTrace_append hprefix tailTrace_6413703
  have hstable : (prefixWord ++ tailWord_6413703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413703).length < 2 ^ (prefixWord ++ tailWord_6413703).sum := by decide
  have hdescent : baseEnd_6413703 < baseStart_6413703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413719 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_6413719 : Nat := 118140960795 + 6413719 * 2 ^ 59
def prefixEnd_6413719 : Nat := 4983230072969 + 3 ^ 40 * 6413719 * 2
def baseEnd_6413719 : Nat := 3293320629874097028616349

theorem tailTrace_6413719 : CollatzResearch.WordTrace tailWord_6413719 prefixEnd_6413719 3293320629874097028616349 := by
  unfold tailWord_6413719
  simp only [CollatzResearch.WordTrace]
  refine ⟨233927549851198913842972211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155951699900799275895314807 233927549851198913842972211)
  ·
    refine ⟨350891324776798370764458317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233927549851198913842972211 350891324776798370764458317)
    ·
      refine ⟨131584246791299389036671869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350891324776798370764458317 131584246791299389036671869)
      ·
        refine ⟨49344092546737270888751951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131584246791299389036671869 49344092546737270888751951)
        ·
          refine ⟨74016138820105906333127927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49344092546737270888751951 74016138820105906333127927)
          ·
            refine ⟨111024208230158859499691891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74016138820105906333127927 111024208230158859499691891)
            ·
              refine ⟨166536312345238289249537837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111024208230158859499691891 166536312345238289249537837)
              ·
                refine ⟨62451117129464358468576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166536312345238289249537837 62451117129464358468576689)
                ·
                  refine ⟨46838337847098268851432517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62451117129464358468576689 46838337847098268851432517)
                  ·
                    refine ⟨8782188346330925409643597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46838337847098268851432517 8782188346330925409643597)
                    ·
                      refine ⟨3293320629874097028616349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782188346330925409643597 3293320629874097028616349)
                      ·
                        rfl

theorem cell23_6413719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_6413719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413719 prefixEnd_6413719 := by exact prefixLift 6413719
  have htrace : WordTrace (prefixWord ++ tailWord_6413719) baseStart_6413719 baseEnd_6413719 := by
    simpa [prefixWord, tailWord_6413719, baseEnd_6413719] using wordTrace_append hprefix tailTrace_6413719
  have hstable : (prefixWord ++ tailWord_6413719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413719).length < 2 ^ (prefixWord ++ tailWord_6413719).sum := by decide
  have hdescent : baseEnd_6413719 < baseStart_6413719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413762 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6413762 : Nat := 118140960795 + 6413762 * 2 ^ 59
def prefixEnd_6413762 : Nat := 4983230072969 + 3 ^ 40 * 6413762 * 2
def baseEnd_6413762 : Nat := 3293342709542240360378653

theorem tailTrace_6413762 : CollatzResearch.WordTrace tailWord_6413762 prefixEnd_6413762 3293342709542240360378653 := by
  unfold tailWord_6413762
  simp only [CollatzResearch.WordTrace]
  refine ⟨58482279547510783046696885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155952745460028754791191693 58482279547510783046696885)
  ·
    refine ⟨5482713707579135910627833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58482279547510783046696885 5482713707579135910627833)
    ·
      refine ⟨4112035280684351932970875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5482713707579135910627833 4112035280684351932970875)
      ·
        refine ⟨6168052921026527899456313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112035280684351932970875 6168052921026527899456313)
        ·
          refine ⟨4626039690769895924592235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168052921026527899456313 4626039690769895924592235)
          ·
            refine ⟨6939059536154843886888353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626039690769895924592235 6939059536154843886888353)
            ·
              refine ⟨5204294652116132915166265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6939059536154843886888353 5204294652116132915166265)
              ·
                refine ⟨3903220989087099686374699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5204294652116132915166265 3903220989087099686374699)
                ·
                  refine ⟨5854831483630649529562049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903220989087099686374699 5854831483630649529562049)
                  ·
                    refine ⟨4391123612722987147171537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5854831483630649529562049 4391123612722987147171537)
                    ·
                      refine ⟨3293342709542240360378653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391123612722987147171537 3293342709542240360378653)
                      ·
                        rfl

theorem cell23_6413762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6413762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413762 prefixEnd_6413762 := by exact prefixLift 6413762
  have htrace : WordTrace (prefixWord ++ tailWord_6413762) baseStart_6413762 baseEnd_6413762 := by
    simpa [prefixWord, tailWord_6413762, baseEnd_6413762] using wordTrace_append hprefix tailTrace_6413762
  have hstable : (prefixWord ++ tailWord_6413762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413762).length < 2 ^ (prefixWord ++ tailWord_6413762).sum := by decide
  have hdescent : baseEnd_6413762 < baseStart_6413762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413806 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6413806 : Nat := 118140960795 + 6413806 * 2 ^ 59
def prefixEnd_6413806 : Nat := 4983230072969 + 3 ^ 40 * 6413806 * 2
def baseEnd_6413806 : Nat := 3293365302691038188228449

theorem tailTrace_6413806 : CollatzResearch.WordTrace tailWord_6413806 prefixEnd_6413806 3293365302691038188228449 := by
  unfold tailWord_6413806
  simp only [CollatzResearch.WordTrace]
  refine ⟨29241340375235465962673659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155953815334589151800926181 29241340375235465962673659)
  ·
    refine ⟨43862010562853198944010489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29241340375235465962673659 43862010562853198944010489)
    ·
      refine ⟨32896507922139899208007867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43862010562853198944010489 32896507922139899208007867)
      ·
        refine ⟨49344761883209848812011801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32896507922139899208007867 49344761883209848812011801)
        ·
          refine ⟨37008571412407386609008851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49344761883209848812011801 37008571412407386609008851)
          ·
            refine ⟨55512857118611079913513277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37008571412407386609008851 55512857118611079913513277)
            ·
              refine ⟨20817321419479154967567479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55512857118611079913513277 20817321419479154967567479)
              ·
                refine ⟨31225982129218732451351219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20817321419479154967567479 31225982129218732451351219)
                ·
                  refine ⟨46838973193828098677026829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31225982129218732451351219 46838973193828098677026829)
                  ·
                    refine ⟨17564614947685537003885061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46838973193828098677026829 17564614947685537003885061)
                    ·
                      refine ⟨3293365302691038188228449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17564614947685537003885061 3293365302691038188228449)
                      ·
                        rfl

theorem cell23_6413806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6413806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413806 prefixEnd_6413806 := by exact prefixLift 6413806
  have htrace : WordTrace (prefixWord ++ tailWord_6413806) baseStart_6413806 baseEnd_6413806 := by
    simpa [prefixWord, tailWord_6413806, baseEnd_6413806] using wordTrace_append hprefix tailTrace_6413806
  have hstable : (prefixWord ++ tailWord_6413806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413806).length < 2 ^ (prefixWord ++ tailWord_6413806).sum := by decide
  have hdescent : baseEnd_6413806 < baseStart_6413806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413833 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 1, 4]
def baseStart_6413833 : Nat := 118140960795 + 6413833 * 2 ^ 59
def prefixEnd_6413833 : Nat := 4983230072969 + 3 ^ 40 * 6413833 * 2
def baseEnd_6413833 : Nat := 1097793055556236527530275

theorem tailTrace_6413833 : CollatzResearch.WordTrace tailWord_6413833 prefixEnd_6413833 1097793055556236527530275 := by
  unfold tailWord_6413833
  simp only [CollatzResearch.WordTrace]
  refine ⟨233931707772785911312622153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155954471848523940875081435 233931707772785911312622153)
  ·
    refine ⟨175448780829589433484466615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233931707772785911312622153 175448780829589433484466615)
    ·
      refine ⟨263173171244384150226699923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175448780829589433484466615 263173171244384150226699923)
      ·
        refine ⟨394759756866576225340049885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263173171244384150226699923 394759756866576225340049885)
        ·
          refine ⟨148034908824966084502518707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394759756866576225340049885 148034908824966084502518707)
          ·
            refine ⟨222052363237449126753778061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148034908824966084502518707 222052363237449126753778061)
            ·
              refine ⟨83269636214043422532666773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222052363237449126753778061 83269636214043422532666773)
              ·
                refine ⟨3903264197533285431218755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83269636214043422532666773 3903264197533285431218755)
                ·
                  refine ⟨5854896296299928146828133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903264197533285431218755 5854896296299928146828133)
                  ·
                    refine ⟨1097793055556236527530275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854896296299928146828133 1097793055556236527530275)
                    ·
                      rfl

theorem cell23_6413833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 4].length) (baseStart_6413833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413833 prefixEnd_6413833 := by exact prefixLift 6413833
  have htrace : WordTrace (prefixWord ++ tailWord_6413833) baseStart_6413833 baseEnd_6413833 := by
    simpa [prefixWord, tailWord_6413833, baseEnd_6413833] using wordTrace_append hprefix tailTrace_6413833
  have hstable : (prefixWord ++ tailWord_6413833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413833).length < 2 ^ (prefixWord ++ tailWord_6413833).sum := by decide
  have hdescent : baseEnd_6413833 < baseStart_6413833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413941 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6413941 : Nat := 118140960795 + 6413941 * 2 ^ 59
def prefixEnd_6413941 : Nat := 4983230072969 + 3 ^ 40 * 6413941 * 2
def baseEnd_6413941 : Nat := 3293434622579395160040329

theorem tailTrace_6413941 : CollatzResearch.WordTrace tailWord_6413941 prefixEnd_6413941 3293434622579395160040329 := by
  unfold tailWord_6413941
  simp only [CollatzResearch.WordTrace]
  refine ⟨233935646856394645757553677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155957097904263097171702451 233935646856394645757553677)
  ·
    refine ⟨87725867571147992159082629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233935646856394645757553677 87725867571147992159082629)
    ·
      refine ⟨16448600169590248529827993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87725867571147992159082629 16448600169590248529827993)
      ·
        refine ⟨12336450127192686397370995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16448600169590248529827993 12336450127192686397370995)
        ·
          refine ⟨18504675190789029596056493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12336450127192686397370995 18504675190789029596056493)
          ·
            refine ⟨6939253196545886098521185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18504675190789029596056493 6939253196545886098521185)
            ·
              refine ⟨5204439897409414573890889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6939253196545886098521185 5204439897409414573890889)
              ·
                refine ⟨3903329923057060930418167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5204439897409414573890889 3903329923057060930418167)
                ·
                  refine ⟨5854994884585591395627251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903329923057060930418167 5854994884585591395627251)
                  ·
                    refine ⟨8782492326878387093440877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854994884585591395627251 8782492326878387093440877)
                    ·
                      refine ⟨3293434622579395160040329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782492326878387093440877 3293434622579395160040329)
                      ·
                        rfl

theorem cell23_6413941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6413941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413941 prefixEnd_6413941 := by exact prefixLift 6413941
  have htrace : WordTrace (prefixWord ++ tailWord_6413941) baseStart_6413941 baseEnd_6413941 := by
    simpa [prefixWord, tailWord_6413941, baseEnd_6413941] using wordTrace_append hprefix tailTrace_6413941
  have hstable : (prefixWord ++ tailWord_6413941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413941).length < 2 ^ (prefixWord ++ tailWord_6413941).sum := by decide
  have hdescent : baseEnd_6413941 < baseStart_6413941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413947 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 1, 2, 2]
def baseStart_6413947 : Nat := 118140960795 + 6413947 * 2 ^ 59
def prefixEnd_6413947 : Nat := 4983230072969 + 3 ^ 40 * 6413947 * 2
def baseEnd_6413947 : Nat := 3293437703463322136565301

theorem tailTrace_6413947 : CollatzResearch.WordTrace tailWord_6413947 prefixEnd_6413947 3293437703463322136565301 := by
  unfold tailWord_6413947
  simp only [CollatzResearch.WordTrace]
  refine ⟨233935865694372908782272095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155957243796248605854848063 233935865694372908782272095)
  ·
    refine ⟨350903798541559363173408143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233935865694372908782272095 350903798541559363173408143)
    ·
      refine ⟨526355697812339044760112215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350903798541559363173408143 526355697812339044760112215)
      ·
        refine ⟨789533546718508567140168323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526355697812339044760112215 789533546718508567140168323)
        ·
          refine ⟨1184300320077762850710252485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789533546718508567140168323 1184300320077762850710252485)
          ·
            refine ⟨222056310014580534508172341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1184300320077762850710252485 222056310014580534508172341)
            ·
              refine ⟨20817779063866925110141157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222056310014580534508172341 20817779063866925110141157)
              ·
                refine ⟨3903333574475048458151467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20817779063866925110141157 3903333574475048458151467)
                ·
                  refine ⟨5855000361712572687227201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903333574475048458151467 5855000361712572687227201)
                  ·
                    refine ⟨4391250271284429515420401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855000361712572687227201 4391250271284429515420401)
                    ·
                      refine ⟨3293437703463322136565301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391250271284429515420401 3293437703463322136565301)
                      ·
                        rfl

theorem cell23_6413947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 2, 2].length) (baseStart_6413947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413947 prefixEnd_6413947 := by exact prefixLift 6413947
  have htrace : WordTrace (prefixWord ++ tailWord_6413947) baseStart_6413947 baseEnd_6413947 := by
    simpa [prefixWord, tailWord_6413947, baseEnd_6413947] using wordTrace_append hprefix tailTrace_6413947
  have hstable : (prefixWord ++ tailWord_6413947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413947).length < 2 ^ (prefixWord ++ tailWord_6413947).sum := by decide
  have hdescent : baseEnd_6413947 < baseStart_6413947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413953 : List Nat := [1, 2, 4, 2, 1, 4, 1, 8]
def baseStart_6413953 : Nat := 118140960795 + 6413953 * 2 ^ 59
def prefixEnd_6413953 : Nat := 4983230072969 + 3 ^ 40 * 6413953 * 2
def baseEnd_6413953 : Nat := 121979288309157374558899

theorem tailTrace_6413953 : CollatzResearch.WordTrace tailWord_6413953 prefixEnd_6413953 121979288309157374558899 := by
  unfold tailWord_6413953
  simp only [CollatzResearch.WordTrace]
  refine ⟨233936084532351171806990513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155957389688234114537993675 233936084532351171806990513)
  ·
    refine ⟨175452063399263378855242885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233936084532351171806990513 175452063399263378855242885)
    ·
      refine ⟨32897261887361883535358041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175452063399263378855242885 32897261887361883535358041)
      ·
        refine ⟨24672946415521412651518531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32897261887361883535358041 24672946415521412651518531)
        ·
          refine ⟨37009419623282118977277797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24672946415521412651518531 37009419623282118977277797)
          ·
            refine ⟨6939266179365397308239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37009419623282118977277797 6939266179365397308239587)
            ·
              refine ⟨10408899269048095962359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939266179365397308239587 10408899269048095962359381)
              ·
                refine ⟨121979288309157374558899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10408899269048095962359381 121979288309157374558899)
                ·
                  rfl

theorem cell23_6413953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 8].length) (baseStart_6413953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413953 prefixEnd_6413953 := by exact prefixLift 6413953
  have htrace : WordTrace (prefixWord ++ tailWord_6413953) baseStart_6413953 baseEnd_6413953 := by
    simpa [prefixWord, tailWord_6413953, baseEnd_6413953] using wordTrace_append hprefix tailTrace_6413953
  have hstable : (prefixWord ++ tailWord_6413953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413953).length < 2 ^ (prefixWord ++ tailWord_6413953).sum := by decide
  have hdescent : baseEnd_6413953 < baseStart_6413953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413963 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3]
def baseStart_6413963 : Nat := 118140960795 + 6413963 * 2 ^ 59
def prefixEnd_6413963 : Nat := 4983230072969 + 3 ^ 40 * 6413963 * 2
def baseEnd_6413963 : Nat := 3293445919153794073965227

theorem tailTrace_6413963 : CollatzResearch.WordTrace tailWord_6413963 prefixEnd_6413963 3293445919153794073965227 := by
  unfold tailWord_6413963
  simp only [CollatzResearch.WordTrace]
  refine ⟨233936449262314943514854543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155957632841543295676569695 233936449262314943514854543)
  ·
    refine ⟨350904673893472415272281815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233936449262314943514854543 350904673893472415272281815)
    ·
      refine ⟨526357010840208622908422723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350904673893472415272281815 526357010840208622908422723)
      ·
        refine ⟨789535516260312934362634085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526357010840208622908422723 789535516260312934362634085)
        ·
          refine ⟨148037909298808675192993891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 789535516260312934362634085 148037909298808675192993891)
          ·
            refine ⟨222056863948213012789490837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148037909298808675192993891 222056863948213012789490837)
            ·
              refine ⟨10408915497572484974507383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222056863948213012789490837 10408915497572484974507383)
              ·
                refine ⟨15613373246358727461761075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408915497572484974507383 15613373246358727461761075)
                ·
                  refine ⟨23420059869538091192641613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15613373246358727461761075 23420059869538091192641613)
                  ·
                    refine ⟨8782522451076784197240605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23420059869538091192641613 8782522451076784197240605)
                    ·
                      refine ⟨3293445919153794073965227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782522451076784197240605 3293445919153794073965227)
                      ·
                        rfl

theorem cell23_6413963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3].length) (baseStart_6413963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413963 prefixEnd_6413963 := by exact prefixLift 6413963
  have htrace : WordTrace (prefixWord ++ tailWord_6413963) baseStart_6413963 baseEnd_6413963 := by
    simpa [prefixWord, tailWord_6413963, baseEnd_6413963] using wordTrace_append hprefix tailTrace_6413963
  have hstable : (prefixWord ++ tailWord_6413963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413963).length < 2 ^ (prefixWord ++ tailWord_6413963).sum := by decide
  have hdescent : baseEnd_6413963 < baseStart_6413963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6413970 : List Nat := [3, 2, 3, 1, 3, 1, 3, 7]
def baseStart_6413970 : Nat := 118140960795 + 6413970 * 2 ^ 59
def prefixEnd_6413970 : Nat := 4983230072969 + 3 ^ 40 * 6413970 * 2
def baseEnd_6413970 : Nat := 121979611611791686910285

theorem tailTrace_6413970 : CollatzResearch.WordTrace tailWord_6413970 prefixEnd_6413970 121979611611791686910285 := by
  unfold tailWord_6413970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58484176143322395927589841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155957803048859722473572909 58484176143322395927589841)
  ·
    refine ⟨43863132107491796945692381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58484176143322395927589841 43863132107491796945692381)
    ·
      refine ⟨16448674540309423854634643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43863132107491796945692381 16448674540309423854634643)
      ·
        refine ⟨24673011810464135781951965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16448674540309423854634643 24673011810464135781951965)
        ·
          refine ⟨9252379428924050918231987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24673011810464135781951965 9252379428924050918231987)
          ·
            refine ⟨13878569143386076377347981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252379428924050918231987 13878569143386076377347981)
            ·
              refine ⟨5204463428769778641505493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13878569143386076377347981 5204463428769778641505493)
              ·
                refine ⟨121979611611791686910285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5204463428769778641505493 121979611611791686910285)
                ·
                  rfl

theorem cell23_6413970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_6413970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6413970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6413970 prefixEnd_6413970 := by exact prefixLift 6413970
  have htrace : WordTrace (prefixWord ++ tailWord_6413970) baseStart_6413970 baseEnd_6413970 := by
    simpa [prefixWord, tailWord_6413970, baseEnd_6413970] using wordTrace_append hprefix tailTrace_6413970
  have hstable : (prefixWord ++ tailWord_6413970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6413970).length < 2 ^ (prefixWord ++ tailWord_6413970).sum := by decide
  have hdescent : baseEnd_6413970 < baseStart_6413970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6413970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414014 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_6414014 : Nat := 118140960795 + 6414014 * 2 ^ 59
def prefixEnd_6414014 : Nat := 4983230072969 + 3 ^ 40 * 6414014 * 2
def baseEnd_6414014 : Nat := 3293472106667173374427493

theorem tailTrace_6414014 : CollatzResearch.WordTrace tailWord_6414014 prefixEnd_6414014 3293472106667173374427493 := by
  unfold tailWord_6414014
  simp only [CollatzResearch.WordTrace]
  refine ⟨29242288673141272403120137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155958872923420119483307397 29242288673141272403120137)
  ·
    refine ⟨21931716504855954302340103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29242288673141272403120137 21931716504855954302340103)
    ·
      refine ⟨32897574757283931453510155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21931716504855954302340103 32897574757283931453510155)
      ·
        refine ⟨49346362135925897180265233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32897574757283931453510155 49346362135925897180265233)
        ·
          refine ⟨37009771601944422885198925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49346362135925897180265233 37009771601944422885198925)
          ·
            refine ⟨13878664350729158581949597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37009771601944422885198925 13878664350729158581949597)
            ·
              refine ⟨5204499131523434468231099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13878664350729158581949597 5204499131523434468231099)
              ·
                refine ⟨7806748697285151702346649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204499131523434468231099 7806748697285151702346649)
                ·
                  refine ⟨5855061522963863776759987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806748697285151702346649 5855061522963863776759987)
                  ·
                    refine ⟨8782592284445795665139981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855061522963863776759987 8782592284445795665139981)
                    ·
                      refine ⟨3293472106667173374427493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782592284445795665139981 3293472106667173374427493)
                      ·
                        rfl

theorem cell23_6414014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_6414014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414014 prefixEnd_6414014 := by exact prefixLift 6414014
  have htrace : WordTrace (prefixWord ++ tailWord_6414014) baseStart_6414014 baseEnd_6414014 := by
    simpa [prefixWord, tailWord_6414014, baseEnd_6414014] using wordTrace_append hprefix tailTrace_6414014
  have hstable : (prefixWord ++ tailWord_6414014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414014).length < 2 ^ (prefixWord ++ tailWord_6414014).sum := by decide
  have hdescent : baseEnd_6414014 < baseStart_6414014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414090 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_6414090 : Nat := 118140960795 + 6414090 * 2 ^ 59
def prefixEnd_6414090 : Nat := 4983230072969 + 3 ^ 40 * 6414090 * 2
def baseEnd_6414090 : Nat := 1097837043732305025692381

theorem tailTrace_6414090 : CollatzResearch.WordTrace tailWord_6414090 prefixEnd_6414090 1097837043732305025692381 := by
  unfold tailWord_6414090
  simp only [CollatzResearch.WordTrace]
  refine ⟨58485270333213711051181931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155960720888569896136485149 58485270333213711051181931)
  ·
    refine ⟨87727905499820566576772897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58485270333213711051181931 87727905499820566576772897)
    ·
      refine ⟨65795929124865424932579673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87727905499820566576772897 65795929124865424932579673)
      ·
        refine ⟨49346946843649068699434755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65795929124865424932579673 49346946843649068699434755)
        ·
          refine ⟨74020420265473603049152133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49346946843649068699434755 74020420265473603049152133)
          ·
            refine ⟨13878828799776300571716025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74020420265473603049152133 13878828799776300571716025)
            ·
              refine ⟨10409121599832225428787019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13878828799776300571716025 10409121599832225428787019)
              ·
                refine ⟨15613682399748338143180529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10409121599832225428787019 15613682399748338143180529)
                ·
                  refine ⟨11710261799811253607385397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15613682399748338143180529 11710261799811253607385397)
                  ·
                    refine ⟨1097837043732305025692381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710261799811253607385397 1097837043732305025692381)
                    ·
                      rfl

theorem cell23_6414090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_6414090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414090 prefixEnd_6414090 := by exact prefixLift 6414090
  have htrace : WordTrace (prefixWord ++ tailWord_6414090) baseStart_6414090 baseEnd_6414090 := by
    simpa [prefixWord, tailWord_6414090, baseEnd_6414090] using wordTrace_append hprefix tailTrace_6414090
  have hstable : (prefixWord ++ tailWord_6414090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414090).length < 2 ^ (prefixWord ++ tailWord_6414090).sum := by decide
  have hdescent : baseEnd_6414090 < baseStart_6414090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414147 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 3]
def baseStart_6414147 : Nat := 118140960795 + 6414147 * 2 ^ 59
def prefixEnd_6414147 : Nat := 4983230072969 + 3 ^ 40 * 6414147 * 2
def baseEnd_6414147 : Nat := 3293540399594221354064381

theorem tailTrace_6414147 : CollatzResearch.WordTrace tailWord_6414147 prefixEnd_6414147 3293540399594221354064381 := by
  unfold tailWord_6414147
  simp only [CollatzResearch.WordTrace]
  refine ⟨233943160293648342939552695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155962106862432228626368463 233943160293648342939552695)
  ·
    refine ⟨350914740440472514409329043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233943160293648342939552695 350914740440472514409329043)
    ·
      refine ⟨526372110660708771613993565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350914740440472514409329043 526372110660708771613993565)
      ·
        refine ⟨197389541497765789355247587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526372110660708771613993565 197389541497765789355247587)
        ·
          refine ⟨296084312246648684032871381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197389541497765789355247587 296084312246648684032871381)
          ·
            refine ⟨6939476068280828532020423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296084312246648684032871381 6939476068280828532020423)
            ·
              refine ⟨10409214102421242798030635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939476068280828532020423 10409214102421242798030635)
              ·
                refine ⟨15613821153631864197045953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10409214102421242798030635 15613821153631864197045953)
                ·
                  refine ⟨11710365865223898147784465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15613821153631864197045953 11710365865223898147784465)
                  ·
                    refine ⟨8782774398917923610838349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11710365865223898147784465 8782774398917923610838349)
                    ·
                      refine ⟨3293540399594221354064381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782774398917923610838349 3293540399594221354064381)
                      ·
                        rfl

theorem cell23_6414147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_6414147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414147 prefixEnd_6414147 := by exact prefixLift 6414147
  have htrace : WordTrace (prefixWord ++ tailWord_6414147) baseStart_6414147 baseEnd_6414147 := by
    simpa [prefixWord, tailWord_6414147, baseEnd_6414147] using wordTrace_append hprefix tailTrace_6414147
  have hstable : (prefixWord ++ tailWord_6414147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414147).length < 2 ^ (prefixWord ++ tailWord_6414147).sum := by decide
  have hdescent : baseEnd_6414147 < baseStart_6414147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414160 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3]
def baseStart_6414160 : Nat := 118140960795 + 6414160 * 2 ^ 59
def prefixEnd_6414160 : Nat := 4983230072969 + 3 ^ 40 * 6414160 * 2
def baseEnd_6414160 : Nat := 3293547074842729803201821

theorem tailTrace_6414160 : CollatzResearch.WordTrace tailWord_6414160 prefixEnd_6414160 3293547074842729803201821 := by
  unfold tailWord_6414160
  simp only [CollatzResearch.WordTrace]
  refine ⟨116971817221300623079887967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155962422961734164106517289 116971817221300623079887967)
  ·
    refine ⟨175457725831950934619831951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116971817221300623079887967 175457725831950934619831951)
    ·
      refine ⟨263186588747926401929747927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175457725831950934619831951 263186588747926401929747927)
      ·
        refine ⟨394779883121889602894621891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263186588747926401929747927 394779883121889602894621891)
        ·
          refine ⟨592169824682834404341932837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394779883121889602894621891 592169824682834404341932837)
          ·
            refine ⟨111031842128031450814112407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 592169824682834404341932837 111031842128031450814112407)
            ·
              refine ⟨166547763192047176221168611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111031842128031450814112407 166547763192047176221168611)
              ·
                refine ⟨249821644788070764331752917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166547763192047176221168611 249821644788070764331752917)
                ·
                  refine ⟨5855194799720408539025459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249821644788070764331752917 5855194799720408539025459)
                  ·
                    refine ⟨8782792199580612808538189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855194799720408539025459 8782792199580612808538189)
                    ·
                      refine ⟨3293547074842729803201821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782792199580612808538189 3293547074842729803201821)
                      ·
                        rfl

theorem cell23_6414160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_6414160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414160 prefixEnd_6414160 := by exact prefixLift 6414160
  have htrace : WordTrace (prefixWord ++ tailWord_6414160) baseStart_6414160 baseEnd_6414160 := by
    simpa [prefixWord, tailWord_6414160, baseEnd_6414160] using wordTrace_append hprefix tailTrace_6414160
  have hstable : (prefixWord ++ tailWord_6414160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414160).length < 2 ^ (prefixWord ++ tailWord_6414160).sum := by decide
  have hdescent : baseEnd_6414160 < baseStart_6414160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414167 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 6]
def baseStart_6414167 : Nat := 118140960795 + 6414167 * 2 ^ 59
def prefixEnd_6414167 : Nat := 4983230072969 + 3 ^ 40 * 6414167 * 2
def baseEnd_6414167 : Nat := 365950074356367919534921

theorem tailTrace_6414167 : CollatzResearch.WordTrace tailWord_6414167 prefixEnd_6414167 365950074356367919534921 := by
  unfold tailWord_6414167
  simp only [CollatzResearch.WordTrace]
  refine ⟨233943889753575886355280755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155962593169050590903520503 233943889753575886355280755)
  ·
    refine ⟨350915834630363829532921133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233943889753575886355280755 350915834630363829532921133)
    ·
      refine ⟨131593437986386436074845425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350915834630363829532921133 131593437986386436074845425)
      ·
        refine ⟨98695078489789827056134069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131593437986386436074845425 98695078489789827056134069)
        ·
          refine ⟨9252663608417796286512569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98695078489789827056134069 9252663608417796286512569)
          ·
            refine ⟨6939497706313347214884427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9252663608417796286512569 6939497706313347214884427)
            ·
              refine ⟨10409246559470020822326641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939497706313347214884427 10409246559470020822326641)
              ·
                refine ⟨7806934919602515616744981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409246559470020822326641 7806934919602515616744981)
                ·
                  refine ⟨365950074356367919534921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7806934919602515616744981 365950074356367919534921)
                  ·
                    rfl

theorem cell23_6414167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 6].length) (baseStart_6414167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414167 prefixEnd_6414167 := by exact prefixLift 6414167
  have htrace : WordTrace (prefixWord ++ tailWord_6414167) baseStart_6414167 baseEnd_6414167 := by
    simpa [prefixWord, tailWord_6414167, baseEnd_6414167] using wordTrace_append hprefix tailTrace_6414167
  have hstable : (prefixWord ++ tailWord_6414167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414167).length < 2 ^ (prefixWord ++ tailWord_6414167).sum := by decide
  have hdescent : baseEnd_6414167 < baseStart_6414167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414177 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_6414177 : Nat := 118140960795 + 6414177 * 2 ^ 59
def prefixEnd_6414177 : Nat := 4983230072969 + 3 ^ 40 * 6414177 * 2
def baseEnd_6414177 : Nat := 3293555804013856236689243

theorem tailTrace_6414177 : CollatzResearch.WordTrace tailWord_6414177 prefixEnd_6414177 3293555804013856236689243 := by
  unfold tailWord_6414177
  simp only [CollatzResearch.WordTrace]
  refine ⟨233944254483539658063144785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155962836322359772042096523 233944254483539658063144785)
  ·
    refine ⟨175458190862654743547358589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233944254483539658063144785 175458190862654743547358589)
    ·
      refine ⟨65796821573495528830259471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175458190862654743547358589 65796821573495528830259471)
      ·
        refine ⟨98695232360243293245389207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65796821573495528830259471 98695232360243293245389207)
        ·
          refine ⟨148042848540364939868083811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98695232360243293245389207 148042848540364939868083811)
          ·
            refine ⟨222064272810547409802125717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148042848540364939868083811 222064272810547409802125717)
            ·
              refine ⟨10409262787994409834474643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222064272810547409802125717 10409262787994409834474643)
              ·
                refine ⟨15613894181991614751711965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10409262787994409834474643 15613894181991614751711965)
                ·
                  refine ⟨5855210318246855531891987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15613894181991614751711965 5855210318246855531891987)
                  ·
                    refine ⟨8782815477370283297837981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855210318246855531891987 8782815477370283297837981)
                    ·
                      refine ⟨3293555804013856236689243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782815477370283297837981 3293555804013856236689243)
                      ·
                        rfl

theorem cell23_6414177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_6414177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414177 prefixEnd_6414177 := by exact prefixLift 6414177
  have htrace : WordTrace (prefixWord ++ tailWord_6414177) baseStart_6414177 baseEnd_6414177 := by
    simpa [prefixWord, tailWord_6414177, baseEnd_6414177] using wordTrace_append hprefix tailTrace_6414177
  have hstable : (prefixWord ++ tailWord_6414177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414177).length < 2 ^ (prefixWord ++ tailWord_6414177).sum := by decide
  have hdescent : baseEnd_6414177 < baseStart_6414177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414197 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6414197 : Nat := 118140960795 + 6414197 * 2 ^ 59
def prefixEnd_6414197 : Nat := 4983230072969 + 3 ^ 40 * 6414197 * 2
def baseEnd_6414197 : Nat := 1097855357875648719479717

theorem tailTrace_6414197 : CollatzResearch.WordTrace tailWord_6414197 prefixEnd_6414197 1097855357875648719479717 := by
  unfold tailWord_6414197
  simp only [CollatzResearch.WordTrace]
  refine ⟨233944983943467201478872845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155963322628978134319248563 233944983943467201478872845)
  ·
    refine ⟨87729368978800200554577317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233944983943467201478872845 87729368978800200554577317)
    ·
      refine ⟨16449256683525037603983247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87729368978800200554577317 16449256683525037603983247)
      ·
        refine ⟨24673885025287556405974871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16449256683525037603983247 24673885025287556405974871)
        ·
          refine ⟨37010827537931334608962307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24673885025287556405974871 37010827537931334608962307)
          ·
            refine ⟨55516241306897001913443461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37010827537931334608962307 55516241306897001913443461)
            ·
              refine ⟨10409295245043187858770649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55516241306897001913443461 10409295245043187858770649)
              ·
                refine ⟨7806971433782390894077987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409295245043187858770649 7806971433782390894077987)
                ·
                  refine ⟨11710457150673586341116981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7806971433782390894077987 11710457150673586341116981)
                  ·
                    refine ⟨1097855357875648719479717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710457150673586341116981 1097855357875648719479717)
                    ·
                      rfl

theorem cell23_6414197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6414197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414197 prefixEnd_6414197 := by exact prefixLift 6414197
  have htrace : WordTrace (prefixWord ++ tailWord_6414197) baseStart_6414197 baseEnd_6414197 := by
    simpa [prefixWord, tailWord_6414197, baseEnd_6414197] using wordTrace_append hprefix tailTrace_6414197
  have hstable : (prefixWord ++ tailWord_6414197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414197).length < 2 ^ (prefixWord ++ tailWord_6414197).sum := by decide
  have hdescent : baseEnd_6414197 < baseStart_6414197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414203 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_6414203 : Nat := 118140960795 + 6414203 * 2 ^ 59
def prefixEnd_6414203 : Nat := 4983230072969 + 3 ^ 40 * 6414203 * 2
def baseEnd_6414203 : Nat := 3293569154510873134964123

theorem tailTrace_6414203 : CollatzResearch.WordTrace tailWord_6414203 prefixEnd_6414203 3293569154510873134964123 := by
  unfold tailWord_6414203
  simp only [CollatzResearch.WordTrace]
  refine ⟨233945202781445464503591263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155963468520963643002394175 233945202781445464503591263)
  ·
    refine ⟨350917804172168196755386895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233945202781445464503591263 350917804172168196755386895)
    ·
      refine ⟨526376706258252295133080343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350917804172168196755386895 526376706258252295133080343)
      ·
        refine ⟨789565059387378442699620515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526376706258252295133080343 789565059387378442699620515)
        ·
          refine ⟨1184347589081067664049430773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789565059387378442699620515 1184347589081067664049430773)
          ·
            refine ⟨111032586476350093504634135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1184347589081067664049430773 111032586476350093504634135)
            ·
              refine ⟨166548879714525140256951203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111032586476350093504634135 166548879714525140256951203)
              ·
                refine ⟨249823319571787710385426805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166548879714525140256951203 249823319571787710385426805)
                ·
                  refine ⟨23420936209855097848633763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249823319571787710385426805 23420936209855097848633763)
                  ·
                    refine ⟨35131404314782646772950645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23420936209855097848633763 35131404314782646772950645)
                    ·
                      refine ⟨3293569154510873134964123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35131404314782646772950645 3293569154510873134964123)
                      ·
                        rfl

theorem cell23_6414203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_6414203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414203 prefixEnd_6414203 := by exact prefixLift 6414203
  have htrace : WordTrace (prefixWord ++ tailWord_6414203) baseStart_6414203 baseEnd_6414203 := by
    simpa [prefixWord, tailWord_6414203, baseEnd_6414203] using wordTrace_append hprefix tailTrace_6414203
  have hstable : (prefixWord ++ tailWord_6414203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414203).length < 2 ^ (prefixWord ++ tailWord_6414203).sum := by decide
  have hdescent : baseEnd_6414203 < baseStart_6414203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414211 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 1, 1, 3]
def baseStart_6414211 : Nat := 118140960795 + 6414211 * 2 ^ 59
def prefixEnd_6414211 : Nat := 4983230072969 + 3 ^ 40 * 6414211 * 2
def baseEnd_6414211 : Nat := 3293573262356109103664087

theorem tailTrace_6414211 : CollatzResearch.WordTrace tailWord_6414211 prefixEnd_6414211 3293573262356109103664087 := by
  unfold tailWord_6414211
  simp only [CollatzResearch.WordTrace]
  refine ⟨233945494565416481869882487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155963663043610987913254991 233945494565416481869882487)
  ·
    refine ⟨350918241848124722804823731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233945494565416481869882487 350918241848124722804823731)
    ·
      refine ⟨526377362772187084207235597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350918241848124722804823731 526377362772187084207235597)
      ·
        refine ⟨197391511039570156577713349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526377362772187084207235597 197391511039570156577713349)
        ·
          refine ⟨37010908319919404358321253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197391511039570156577713349 37010908319919404358321253)
          ·
            refine ⟨6939545309984888317185235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37010908319919404358321253 6939545309984888317185235)
            ·
              refine ⟨10409317964977332475777853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939545309984888317185235 10409317964977332475777853)
              ·
                refine ⟨3903494236866499678416695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10409317964977332475777853 3903494236866499678416695)
                ·
                  refine ⟨5855241355299749517625043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903494236866499678416695 5855241355299749517625043)
                  ·
                    refine ⟨8782862032949624276437565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855241355299749517625043 8782862032949624276437565)
                    ·
                      refine ⟨3293573262356109103664087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782862032949624276437565 3293573262356109103664087)
                      ·
                        rfl

theorem cell23_6414211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_6414211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414211 prefixEnd_6414211 := by exact prefixLift 6414211
  have htrace : WordTrace (prefixWord ++ tailWord_6414211) baseStart_6414211 baseEnd_6414211 := by
    simpa [prefixWord, tailWord_6414211, baseEnd_6414211] using wordTrace_append hprefix tailTrace_6414211
  have hstable : (prefixWord ++ tailWord_6414211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414211).length < 2 ^ (prefixWord ++ tailWord_6414211).sum := by decide
  have hdescent : baseEnd_6414211 < baseStart_6414211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414220 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_6414220 : Nat := 118140960795 + 6414220 * 2 ^ 59
def prefixEnd_6414220 : Nat := 4983230072969 + 3 ^ 40 * 6414220 * 2
def baseEnd_6414220 : Nat := 3293577883681999568451545

theorem tailTrace_6414220 : CollatzResearch.WordTrace tailWord_6414220 prefixEnd_6414220 3293577883681999568451545 := by
  unfold tailWord_6414220
  simp only [CollatzResearch.WordTrace]
  refine ⟨116972911411191938203480057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155963881881589250937973409 116972911411191938203480057)
  ·
    refine ⟨87729683558393953652610043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116972911411191938203480057 87729683558393953652610043)
    ·
      refine ⟨131594525337590930478915065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87729683558393953652610043 131594525337590930478915065)
      ·
        refine ⟨98695894003193197859186299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131594525337590930478915065 98695894003193197859186299)
        ·
          refine ⟨148043841004789796788779449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98695894003193197859186299 148043841004789796788779449)
          ·
            refine ⟨111032880753592347591584587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148043841004789796788779449 111032880753592347591584587)
            ·
              refine ⟨166549321130388521387376881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111032880753592347591584587 166549321130388521387376881)
              ·
                refine ⟨124911990847791391040532661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166549321130388521387376881 124911990847791391040532661)
                ·
                  refine ⟨11710499141980442910049937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124911990847791391040532661 11710499141980442910049937)
                  ·
                    refine ⟨8782874356485332182537453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11710499141980442910049937 8782874356485332182537453)
                    ·
                      refine ⟨3293577883681999568451545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782874356485332182537453 3293577883681999568451545)
                      ·
                        rfl

theorem cell23_6414220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_6414220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414220 prefixEnd_6414220 := by exact prefixLift 6414220
  have htrace : WordTrace (prefixWord ++ tailWord_6414220) baseStart_6414220 baseEnd_6414220 := by
    simpa [prefixWord, tailWord_6414220, baseEnd_6414220] using wordTrace_append hprefix tailTrace_6414220
  have hstable : (prefixWord ++ tailWord_6414220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414220).length < 2 ^ (prefixWord ++ tailWord_6414220).sum := by decide
  have hdescent : baseEnd_6414220 < baseStart_6414220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414228 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6414228 : Nat := 118140960795 + 6414228 * 2 ^ 59
def prefixEnd_6414228 : Nat := 4983230072969 + 3 ^ 40 * 6414228 * 2
def baseEnd_6414228 : Nat := 3293581991527235537151509

theorem tailTrace_6414228 : CollatzResearch.WordTrace tailWord_6414228 prefixEnd_6414228 3293581991527235537151509 := by
  unfold tailWord_6414228
  simp only [CollatzResearch.WordTrace]
  refine ⟨116973057303177446886625669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155964076404236595848834225 116973057303177446886625669)
  ·
    refine ⟨21932448244345771291242313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116973057303177446886625669 21932448244345771291242313)
    ·
      refine ⟨16449336183259328468431735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21932448244345771291242313 16449336183259328468431735)
      ·
        refine ⟨24674004274888992702647603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16449336183259328468431735 24674004274888992702647603)
        ·
          refine ⟨37011006412333489053971405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24674004274888992702647603 37011006412333489053971405)
          ·
            refine ⟨13879127404625058395239277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37011006412333489053971405 13879127404625058395239277)
            ·
              refine ⟨5204672776734396898214729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13879127404625058395239277 5204672776734396898214729)
              ·
                refine ⟨3903504582550797673661047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5204672776734396898214729 3903504582550797673661047)
                ·
                  refine ⟨5855256873826196510491571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903504582550797673661047 5855256873826196510491571)
                  ·
                    refine ⟨8782885310739294765737357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855256873826196510491571 8782885310739294765737357)
                    ·
                      refine ⟨3293581991527235537151509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782885310739294765737357 3293581991527235537151509)
                      ·
                        rfl

theorem cell23_6414228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6414228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414228 prefixEnd_6414228 := by exact prefixLift 6414228
  have htrace : WordTrace (prefixWord ++ tailWord_6414228) baseStart_6414228 baseEnd_6414228 := by
    simpa [prefixWord, tailWord_6414228, baseEnd_6414228] using wordTrace_append hprefix tailTrace_6414228
  have hstable : (prefixWord ++ tailWord_6414228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414228).length < 2 ^ (prefixWord ++ tailWord_6414228).sum := by decide
  have hdescent : baseEnd_6414228 < baseStart_6414228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414243 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_6414243 : Nat := 118140960795 + 6414243 * 2 ^ 59
def prefixEnd_6414243 : Nat := 4983230072969 + 3 ^ 40 * 6414243 * 2
def baseEnd_6414243 : Nat := 3293589693737052978463939

theorem tailTrace_6414243 : CollatzResearch.WordTrace tailWord_6414243 prefixEnd_6414243 3293589693737052978463939 := by
  unfold tailWord_6414243
  simp only [CollatzResearch.WordTrace]
  refine ⟨233946661701300551335047383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155964441134200367556698255 233946661701300551335047383)
  ·
    refine ⟨350919992551950827002571075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233946661701300551335047383 350919992551950827002571075)
    ·
      refine ⟨526379988827926240503856613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350919992551950827002571075 526379988827926240503856613)
      ·
        refine ⟨98696247905236170094473115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526379988827926240503856613 98696247905236170094473115)
        ·
          refine ⟨148044371857854255141709673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98696247905236170094473115 148044371857854255141709673)
          ·
            refine ⟨111033278893390691356282255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148044371857854255141709673 111033278893390691356282255)
            ·
              refine ⟨166549918340086037034423383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111033278893390691356282255 166549918340086037034423383)
              ·
                refine ⟨249824877510129055551635075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166549918340086037034423383 249824877510129055551635075)
                ·
                  refine ⟨374737316265193583327452613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249824877510129055551635075 374737316265193583327452613)
                  ·
                    refine ⟨70263246799723796873897365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374737316265193583327452613 70263246799723796873897365)
                    ·
                      refine ⟨3293589693737052978463939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70263246799723796873897365 3293589693737052978463939)
                      ·
                        rfl

theorem cell23_6414243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_6414243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414243 prefixEnd_6414243 := by exact prefixLift 6414243
  have htrace : WordTrace (prefixWord ++ tailWord_6414243) baseStart_6414243 baseEnd_6414243 := by
    simpa [prefixWord, tailWord_6414243, baseEnd_6414243] using wordTrace_append hprefix tailTrace_6414243
  have hstable : (prefixWord ++ tailWord_6414243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414243).length < 2 ^ (prefixWord ++ tailWord_6414243).sum := by decide
  have hdescent : baseEnd_6414243 < baseStart_6414243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414244 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_6414244 : Nat := 118140960795 + 6414244 * 2 ^ 59
def prefixEnd_6414244 : Nat := 4983230072969 + 3 ^ 40 * 6414244 * 2
def baseEnd_6414244 : Nat := 1097863402405902491517145

theorem tailTrace_6414244 : CollatzResearch.WordTrace tailWord_6414244 prefixEnd_6414244 1097863402405902491517145 := by
  unfold tailWord_6414244
  simp only [CollatzResearch.WordTrace]
  refine ⟨116973349087148464252916893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155964465449531285670555857 116973349087148464252916893)
  ·
    refine ⟨43865005907680674094843835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116973349087148464252916893 43865005907680674094843835)
    ·
      refine ⟨65797508861521011142265753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43865005907680674094843835 65797508861521011142265753)
      ·
        refine ⟨49348131646140758356699315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65797508861521011142265753 49348131646140758356699315)
        ·
          refine ⟨74022197469211137535048973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49348131646140758356699315 74022197469211137535048973)
          ·
            refine ⟨27758324050954176575643365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74022197469211137535048973 27758324050954176575643365)
            ·
              refine ⟨5204685759553908107933131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27758324050954176575643365 5204685759553908107933131)
              ·
                refine ⟨7807028639330862161899697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204685759553908107933131 7807028639330862161899697)
                ·
                  refine ⟨5855271479498146621424773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807028639330862161899697 5855271479498146621424773)
                  ·
                    refine ⟨1097863402405902491517145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5855271479498146621424773 1097863402405902491517145)
                    ·
                      rfl

theorem cell23_6414244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_6414244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414244 prefixEnd_6414244 := by exact prefixLift 6414244
  have htrace : WordTrace (prefixWord ++ tailWord_6414244) baseStart_6414244 baseEnd_6414244 := by
    simpa [prefixWord, tailWord_6414244, baseEnd_6414244] using wordTrace_append hprefix tailTrace_6414244
  have hstable : (prefixWord ++ tailWord_6414244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414244).length < 2 ^ (prefixWord ++ tailWord_6414244).sum := by decide
  have hdescent : baseEnd_6414244 < baseStart_6414244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414248 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6414248 : Nat := 118140960795 + 6414248 * 2 ^ 59
def prefixEnd_6414248 : Nat := 4983230072969 + 3 ^ 40 * 6414248 * 2
def baseEnd_6414248 : Nat := 1097864087046775152967139

theorem tailTrace_6414248 : CollatzResearch.WordTrace tailWord_6414248 prefixEnd_6414248 1097864087046775152967139 := by
  unfold tailWord_6414248
  simp only [CollatzResearch.WordTrace]
  refine ⟨116973422033141218594489699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155964562710854958125986265 116973422033141218594489699)
  ·
    refine ⟨175460133049711827891734549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116973422033141218594489699 175460133049711827891734549)
    ·
      refine ⟨8224693736705241932425057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175460133049711827891734549 8224693736705241932425057)
      ·
        refine ⟨6168520302528931449318793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8224693736705241932425057 6168520302528931449318793)
        ·
          refine ⟨4626390226896698586989095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168520302528931449318793 4626390226896698586989095)
          ·
            refine ⟨6939585340345047880483643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626390226896698586989095 6939585340345047880483643)
            ·
              refine ⟨10409378010517571820725465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939585340345047880483643 10409378010517571820725465)
              ·
                refine ⟨7807033507888178865544099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409378010517571820725465 7807033507888178865544099)
                ·
                  refine ⟨11710550261832268298316149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807033507888178865544099 11710550261832268298316149)
                  ·
                    refine ⟨1097864087046775152967139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710550261832268298316149 1097864087046775152967139)
                    ·
                      rfl

theorem cell23_6414248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6414248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414248 prefixEnd_6414248 := by exact prefixLift 6414248
  have htrace : WordTrace (prefixWord ++ tailWord_6414248) baseStart_6414248 baseEnd_6414248 := by
    simpa [prefixWord, tailWord_6414248, baseEnd_6414248] using wordTrace_append hprefix tailTrace_6414248
  have hstable : (prefixWord ++ tailWord_6414248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414248).length < 2 ^ (prefixWord ++ tailWord_6414248).sum := by decide
  have hdescent : baseEnd_6414248 < baseStart_6414248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414284 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6414284 : Nat := 118140960795 + 6414284 * 2 ^ 59
def prefixEnd_6414284 : Nat := 4983230072969 + 3 ^ 40 * 6414284 * 2
def baseEnd_6414284 : Nat := 3293610746443887318051251

theorem tailTrace_6414284 : CollatzResearch.WordTrace tailWord_6414284 prefixEnd_6414284 3293610746443887318051251 := by
  unfold tailWord_6414284
  simp only [CollatzResearch.WordTrace]
  refine ⟨116974078547076007668644953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155965438062768010224859937 116974078547076007668644953)
  ·
    refine ⟨87730558910307005751483715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116974078547076007668644953 87730558910307005751483715)
    ·
      refine ⟨131595838365460508627225573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87730558910307005751483715 131595838365460508627225573)
      ·
        refine ⟨24674219693523845367604795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131595838365460508627225573 24674219693523845367604795)
        ·
          refine ⟨37011329540285768051407193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24674219693523845367604795 37011329540285768051407193)
          ·
            refine ⟨27758497155214326038555395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37011329540285768051407193 27758497155214326038555395)
            ·
              refine ⟨41637745732821489057833093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27758497155214326038555395 41637745732821489057833093)
              ·
                refine ⟨7807077324904029198343705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41637745732821489057833093 7807077324904029198343705)
                ·
                  refine ⟨5855307993678021898757779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807077324904029198343705 5855307993678021898757779)
                  ·
                    refine ⟨8782961990517032848136669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855307993678021898757779 8782961990517032848136669)
                    ·
                      refine ⟨3293610746443887318051251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8782961990517032848136669 3293610746443887318051251)
                      ·
                        rfl

theorem cell23_6414284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6414284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414284 prefixEnd_6414284 := by exact prefixLift 6414284
  have htrace : WordTrace (prefixWord ++ tailWord_6414284) baseStart_6414284 baseEnd_6414284 := by
    simpa [prefixWord, tailWord_6414284, baseEnd_6414284] using wordTrace_append hprefix tailTrace_6414284
  have hstable : (prefixWord ++ tailWord_6414284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414284).length < 2 ^ (prefixWord ++ tailWord_6414284).sum := by decide
  have hdescent : baseEnd_6414284 < baseStart_6414284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414341 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_6414341 : Nat := 118140960795 + 6414341 * 2 ^ 59
def prefixEnd_6414341 : Nat := 4983230072969 + 3 ^ 40 * 6414341 * 2
def baseEnd_6414341 : Nat := 3293640014841193595038489

theorem tailTrace_6414341 : CollatzResearch.WordTrace tailWord_6414341 prefixEnd_6414341 3293640014841193595038489 := by
  unfold tailWord_6414341
  simp only [CollatzResearch.WordTrace]
  refine ⟨233950236054945514072114877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155966824036630342714743251 233950236054945514072114877)
  ·
    refine ⟨87731338520604567777043079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233950236054945514072114877 87731338520604567777043079)
    ·
      refine ⟨131597007780906851665564619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87731338520604567777043079 131597007780906851665564619)
      ·
        refine ⟨197395511671360277498346929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131597007780906851665564619 197395511671360277498346929)
        ·
          refine ⟨148046633753520208123760197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197395511671360277498346929 148046633753520208123760197)
          ·
            refine ⟨27758743828785039023205037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148046633753520208123760197 27758743828785039023205037)
            ·
              refine ⟨10409528935794389633701889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27758743828785039023205037 10409528935794389633701889)
              ·
                refine ⟨7807146701845792225276417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409528935794389633701889 7807146701845792225276417)
                ·
                  refine ⟨5855360026384344168957313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807146701845792225276417 5855360026384344168957313)
                  ·
                    refine ⟨4391520019788258126717985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855360026384344168957313 4391520019788258126717985)
                    ·
                      refine ⟨3293640014841193595038489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391520019788258126717985 3293640014841193595038489)
                      ·
                        rfl

theorem cell23_6414341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_6414341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414341 prefixEnd_6414341 := by exact prefixLift 6414341
  have htrace : WordTrace (prefixWord ++ tailWord_6414341) baseStart_6414341 baseEnd_6414341 := by
    simpa [prefixWord, tailWord_6414341, baseEnd_6414341] using wordTrace_append hprefix tailTrace_6414341
  have hstable : (prefixWord ++ tailWord_6414341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414341).length < 2 ^ (prefixWord ++ tailWord_6414341).sum := by decide
  have hdescent : baseEnd_6414341 < baseStart_6414341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414347 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 5]
def baseStart_6414347 : Nat := 118140960795 + 6414347 * 2 ^ 59
def prefixEnd_6414347 : Nat := 4983230072969 + 3 ^ 40 * 6414347 * 2
def baseEnd_6414347 : Nat := 365960343969457841284829

theorem tailTrace_6414347 : CollatzResearch.WordTrace tailWord_6414347 prefixEnd_6414347 365960343969457841284829 := by
  unfold tailWord_6414347
  simp only [CollatzResearch.WordTrace]
  refine ⟨233950454892923777096833295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155966969928615851397888863 233950454892923777096833295)
  ·
    refine ⟨350925682339385665645249943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233950454892923777096833295 350925682339385665645249943)
    ·
      refine ⟨526388523509078498467874915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350925682339385665645249943 526388523509078498467874915)
      ·
        refine ⟨789582785263617747701812373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526388523509078498467874915 789582785263617747701812373)
        ·
          refine ⟨37011693059232081923522455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 789582785263617747701812373 37011693059232081923522455)
          ·
            refine ⟨55517539588848122885283683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37011693059232081923522455 55517539588848122885283683)
            ·
              refine ⟨83276309383272184327925525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55517539588848122885283683 83276309383272184327925525)
              ·
                refine ⟨3903577002340883640371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83276309383272184327925525 3903577002340883640371509)
                ·
                  refine ⟨365960343969457841284829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3903577002340883640371509 365960343969457841284829)
                  ·
                    rfl

theorem cell23_6414347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 5].length) (baseStart_6414347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414347 prefixEnd_6414347 := by exact prefixLift 6414347
  have htrace : WordTrace (prefixWord ++ tailWord_6414347) baseStart_6414347 baseEnd_6414347 := by
    simpa [prefixWord, tailWord_6414347, baseEnd_6414347] using wordTrace_append hprefix tailTrace_6414347
  have hstable : (prefixWord ++ tailWord_6414347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414347).length < 2 ^ (prefixWord ++ tailWord_6414347).sum := by decide
  have hdescent : baseEnd_6414347 < baseStart_6414347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414360 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_6414360 : Nat := 118140960795 + 6414360 * 2 ^ 59
def prefixEnd_6414360 : Nat := 4983230072969 + 3 ^ 40 * 6414360 * 2
def baseEnd_6414360 : Nat := 1097883256991209673566967

theorem tailTrace_6414360 : CollatzResearch.WordTrace tailWord_6414360 prefixEnd_6414360 1097883256991209673566967 := by
  unfold tailWord_6414360
  simp only [CollatzResearch.WordTrace]
  refine ⟨116975464520938340158528267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155967286027917786878037689 116975464520938340158528267)
  ·
    refine ⟨175463196781407510237792401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116975464520938340158528267 175463196781407510237792401)
    ·
      refine ⟨131597397586055632678344301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175463196781407510237792401 131597397586055632678344301)
      ·
        refine ⟨49349024094770862254379113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131597397586055632678344301 49349024094770862254379113)
        ·
          refine ⟨37011768071078146690784335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49349024094770862254379113 37011768071078146690784335)
          ·
            refine ⟨55517652106617220036176503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37011768071078146690784335 55517652106617220036176503)
            ·
              refine ⟨83276478159925830054264755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55517652106617220036176503 83276478159925830054264755)
              ·
                refine ⟨124914717239888745081397133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83276478159925830054264755 124914717239888745081397133)
                ·
                  refine ⟨46843018964958279405523925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124914717239888745081397133 46843018964958279405523925)
                  ·
                    refine ⟨1097883256991209673566967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46843018964958279405523925 1097883256991209673566967)
                    ·
                      rfl

theorem cell23_6414360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_6414360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414360 prefixEnd_6414360 := by exact prefixLift 6414360
  have htrace : WordTrace (prefixWord ++ tailWord_6414360) baseStart_6414360 baseEnd_6414360 := by
    simpa [prefixWord, tailWord_6414360, baseEnd_6414360] using wordTrace_append hprefix tailTrace_6414360
  have hstable : (prefixWord ++ tailWord_6414360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414360).length < 2 ^ (prefixWord ++ tailWord_6414360).sum := by decide
  have hdescent : baseEnd_6414360 < baseStart_6414360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414398 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_6414398 : Nat := 118140960795 + 6414398 * 2 ^ 59
def prefixEnd_6414398 : Nat := 4983230072969 + 3 ^ 40 * 6414398 * 2
def baseEnd_6414398 : Nat := 365963253693166652447303

theorem tailTrace_6414398 : CollatzResearch.WordTrace tailWord_6414398 prefixEnd_6414398 365963253693166652447303 := by
  unfold tailWord_6414398
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244039376967376600867481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155968210010492675204626565 29244039376967376600867481)
  ·
    refine ⟨21933029532725532450650611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29244039376967376600867481 21933029532725532450650611)
    ·
      refine ⟨32899544299088298675975917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21933029532725532450650611 32899544299088298675975917)
      ·
        refine ⟨12337329112158112003490969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32899544299088298675975917 12337329112158112003490969)
        ·
          refine ⟨9252996834118584002618227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12337329112158112003490969 9252996834118584002618227)
          ·
            refine ⟨13879495251177876003927341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252996834118584002618227 13879495251177876003927341)
            ·
              refine ⟨5204810719191703501472753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13879495251177876003927341 5204810719191703501472753)
              ·
                refine ⟨3903608039393777626104565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5204810719191703501472753 3903608039393777626104565)
                ·
                  refine ⟨365963253693166652447303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3903608039393777626104565 365963253693166652447303)
                  ·
                    rfl

theorem cell23_6414398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_6414398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414398 prefixEnd_6414398 := by exact prefixLift 6414398
  have htrace : WordTrace (prefixWord ++ tailWord_6414398) baseStart_6414398 baseEnd_6414398 := by
    simpa [prefixWord, tailWord_6414398, baseEnd_6414398] using wordTrace_append hprefix tailTrace_6414398
  have hstable : (prefixWord ++ tailWord_6414398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414398).length < 2 ^ (prefixWord ++ tailWord_6414398).sum := by decide
  have hdescent : baseEnd_6414398 < baseStart_6414398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414417 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_6414417 : Nat := 118140960795 + 6414417 * 2 ^ 59
def prefixEnd_6414417 : Nat := 4983230072969 + 3 ^ 40 * 6414417 * 2
def baseEnd_6414417 : Nat := 3293679039370935297688139

theorem tailTrace_6414417 : CollatzResearch.WordTrace tailWord_6414417 prefixEnd_6414417 3293679039370935297688139 := by
  unfold tailWord_6414417
  simp only [CollatzResearch.WordTrace]
  refine ⟨233953008002670179051881505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155968672001780119367921003 233953008002670179051881505)
  ·
    refine ⟨175464756002002634288911129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233953008002670179051881505 175464756002002634288911129)
    ·
      refine ⟨131598567001501975716683347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175464756002002634288911129 131598567001501975716683347)
      ·
        refine ⟨197397850502252963575025021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131598567001501975716683347 197397850502252963575025021)
        ·
          refine ⟨74024193938344861340634383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197397850502252963575025021 74024193938344861340634383)
          ·
            refine ⟨111036290907517292010951575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74024193938344861340634383 111036290907517292010951575)
            ·
              refine ⟨166554436361275938016427363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111036290907517292010951575 166554436361275938016427363)
              ·
                refine ⟨249831654541913907024641045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166554436361275938016427363 249831654541913907024641045)
                ·
                  refine ⟨11710858806652214391780049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249831654541913907024641045 11710858806652214391780049)
                  ·
                    refine ⟨8783144104989160793835037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11710858806652214391780049 8783144104989160793835037)
                    ·
                      refine ⟨3293679039370935297688139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783144104989160793835037 3293679039370935297688139)
                      ·
                        rfl

theorem cell23_6414417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_6414417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414417 prefixEnd_6414417 := by exact prefixLift 6414417
  have htrace : WordTrace (prefixWord ++ tailWord_6414417) baseStart_6414417 baseEnd_6414417 := by
    simpa [prefixWord, tailWord_6414417, baseEnd_6414417] using wordTrace_append hprefix tailTrace_6414417
  have hstable : (prefixWord ++ tailWord_6414417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414417).length < 2 ^ (prefixWord ++ tailWord_6414417).sum := by decide
  have hdescent : baseEnd_6414417 < baseStart_6414417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414454 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6414454 : Nat := 118140960795 + 6414454 * 2 ^ 59
def prefixEnd_6414454 : Nat := 4983230072969 + 3 ^ 40 * 6414454 * 2
def baseEnd_6414454 : Nat := 365966448683905739213941

theorem tailTrace_6414454 : CollatzResearch.WordTrace tailWord_6414454 prefixEnd_6414454 365966448683905739213941 := by
  unfold tailWord_6414454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622147343971008398186151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155969571669024089580652277 14622147343971008398186151)
  ·
    refine ⟨21933221015956512597279227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14622147343971008398186151 21933221015956512597279227)
    ·
      refine ⟨32899831523934768895918841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21933221015956512597279227 32899831523934768895918841)
      ·
        refine ⟨24674873642951076671939131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32899831523934768895918841 24674873642951076671939131)
        ·
          refine ⟨37012310464426615007908697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24674873642951076671939131 37012310464426615007908697)
          ·
            refine ⟨27759232848319961255931523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37012310464426615007908697 27759232848319961255931523)
            ·
              refine ⟨41638849272479941883897285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27759232848319961255931523 41638849272479941883897285)
              ·
                refine ⟨7807284238589989103230741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41638849272479941883897285 7807284238589989103230741)
                ·
                  refine ⟨365966448683905739213941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7807284238589989103230741 365966448683905739213941)
                  ·
                    rfl

theorem cell23_6414454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6414454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414454 prefixEnd_6414454 := by exact prefixLift 6414454
  have htrace : WordTrace (prefixWord ++ tailWord_6414454) baseStart_6414454 baseEnd_6414454 := by
    simpa [prefixWord, tailWord_6414454, baseEnd_6414454] using wordTrace_append hprefix tailTrace_6414454
  have hstable : (prefixWord ++ tailWord_6414454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414454).length < 2 ^ (prefixWord ++ tailWord_6414454).sum := by decide
  have hdescent : baseEnd_6414454 < baseStart_6414454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414464 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3]
def baseStart_6414464 : Nat := 118140960795 + 6414464 * 2 ^ 59
def prefixEnd_6414464 : Nat := 4983230072969 + 3 ^ 40 * 6414464 * 2
def baseEnd_6414464 : Nat := 3293703172961696613800423

theorem tailTrace_6414464 : CollatzResearch.WordTrace tailWord_6414464 prefixEnd_6414464 3293703172961696613800423 := by
  unfold tailWord_6414464
  simp only [CollatzResearch.WordTrace]
  refine ⟨116977361116749953039421223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155969814822333270719228297 116977361116749953039421223)
  ·
    refine ⟨175466041675124929559131835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116977361116749953039421223 175466041675124929559131835)
    ·
      refine ⟨263199062512687394338697753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175466041675124929559131835 263199062512687394338697753)
      ·
        refine ⟨197399296884515545754023315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263199062512687394338697753 197399296884515545754023315)
        ·
          refine ⟨296098945326773318631034973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197399296884515545754023315 296098945326773318631034973)
          ·
            refine ⟨111037104497539994486638115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296098945326773318631034973 111037104497539994486638115)
            ·
              refine ⟨166555656746309991729957173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111037104497539994486638115 166555656746309991729957173)
              ·
                refine ⟨15614592819966561724683485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166555656746309991729957173 15614592819966561724683485)
                ·
                  refine ⟨5855472307487460646756307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15614592819966561724683485 5855472307487460646756307)
                  ·
                    refine ⟨8783208461231190970134461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855472307487460646756307 8783208461231190970134461)
                    ·
                      refine ⟨3293703172961696613800423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783208461231190970134461 3293703172961696613800423)
                      ·
                        rfl

theorem cell23_6414464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_6414464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414464 prefixEnd_6414464 := by exact prefixLift 6414464
  have htrace : WordTrace (prefixWord ++ tailWord_6414464) baseStart_6414464 baseEnd_6414464 := by
    simpa [prefixWord, tailWord_6414464, baseEnd_6414464] using wordTrace_append hprefix tailTrace_6414464
  have hstable : (prefixWord ++ tailWord_6414464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414464).length < 2 ^ (prefixWord ++ tailWord_6414464).sum := by decide
  have hdescent : baseEnd_6414464 < baseStart_6414464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414467 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 3, 5]
def baseStart_6414467 : Nat := 118140960795 + 6414467 * 2 ^ 59
def prefixEnd_6414467 : Nat := 4983230072969 + 3 ^ 40 * 6414467 * 2
def baseEnd_6414467 : Nat := 1097901571134553367354303

theorem tailTrace_6414467 : CollatzResearch.WordTrace tailWord_6414467 prefixEnd_6414467 1097901571134553367354303 := by
  unfold tailWord_6414467
  simp only [CollatzResearch.WordTrace]
  refine ⟨233954831652489037591201655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155969887768326025060801103 233954831652489037591201655)
  ·
    refine ⟨350932247478733556386802483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233954831652489037591201655 350932247478733556386802483)
    ·
      refine ⟨526398371218100334580203725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350932247478733556386802483 526398371218100334580203725)
      ·
        refine ⟨197399389206787625467576397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526398371218100334580203725 197399389206787625467576397)
        ·
          refine ⟨74024770952545359550341149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197399389206787625467576397 74024770952545359550341149)
          ·
            refine ⟨27759289107204509831377931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74024770952545359550341149 27759289107204509831377931)
            ·
              refine ⟨41638933660806764747066897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27759289107204509831377931 41638933660806764747066897)
              ·
                refine ⟨31229200245605073560300173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41638933660806764747066897 31229200245605073560300173)
                ·
                  refine ⟨11710950092101902585112565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31229200245605073560300173 11710950092101902585112565)
                  ·
                    refine ⟨1097901571134553367354303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710950092101902585112565 1097901571134553367354303)
                    ·
                      rfl

theorem cell23_6414467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 5].length) (baseStart_6414467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414467 prefixEnd_6414467 := by exact prefixLift 6414467
  have htrace : WordTrace (prefixWord ++ tailWord_6414467) baseStart_6414467 baseEnd_6414467 := by
    simpa [prefixWord, tailWord_6414467, baseEnd_6414467] using wordTrace_append hprefix tailTrace_6414467
  have hstable : (prefixWord ++ tailWord_6414467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414467).length < 2 ^ (prefixWord ++ tailWord_6414467).sum := by decide
  have hdescent : baseEnd_6414467 < baseStart_6414467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414514 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_6414514 : Nat := 118140960795 + 6414514 * 2 ^ 59
def prefixEnd_6414514 : Nat := 4983230072969 + 3 ^ 40 * 6414514 * 2
def baseEnd_6414514 : Nat := 1097909615664807139391731

theorem tailTrace_6414514 : CollatzResearch.WordTrace tailWord_6414514 prefixEnd_6414514 1097909615664807139391731 := by
  unfold tailWord_6414514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58489136470829691154540649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155971030588879176412108397 58489136470829691154540649)
  ·
    refine ⟨43866852353122268365905487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58489136470829691154540649 43866852353122268365905487)
    ·
      refine ⟨65800278529683402548858231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43866852353122268365905487 65800278529683402548858231)
      ·
        refine ⟨98700417794525103823287347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65800278529683402548858231 98700417794525103823287347)
        ·
          refine ⟨148050626691787655734931021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98700417794525103823287347 148050626691787655734931021)
          ·
            refine ⟨55518985009420370900599133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148050626691787655734931021 55518985009420370900599133)
            ·
              refine ⟨20819619378532639087724675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55518985009420370900599133 20819619378532639087724675)
              ·
                refine ⟨31229429067798958631587013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20819619378532639087724675 31229429067798958631587013)
                ·
                  refine ⟨5855517950212304743422565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31229429067798958631587013 5855517950212304743422565)
                  ·
                    refine ⟨1097909615664807139391731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5855517950212304743422565 1097909615664807139391731)
                    ·
                      rfl

theorem cell23_6414514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_6414514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414514 prefixEnd_6414514 := by exact prefixLift 6414514
  have htrace : WordTrace (prefixWord ++ tailWord_6414514) baseStart_6414514 baseEnd_6414514 := by
    simpa [prefixWord, tailWord_6414514, baseEnd_6414514] using wordTrace_append hprefix tailTrace_6414514
  have hstable : (prefixWord ++ tailWord_6414514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414514).length < 2 ^ (prefixWord ++ tailWord_6414514).sum := by decide
  have hdescent : baseEnd_6414514 < baseStart_6414514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414554 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_6414554 : Nat := 118140960795 + 6414554 * 2 ^ 59
def prefixEnd_6414554 : Nat := 4983230072969 + 3 ^ 40 * 6414554 * 2
def baseEnd_6414554 : Nat := 3293749386220601261675009

theorem tailTrace_6414554 : CollatzResearch.WordTrace tailWord_6414554 prefixEnd_6414554 3293749386220601261675009 := by
  unfold tailWord_6414554
  simp only [CollatzResearch.WordTrace]
  refine ⟨58489501200793462862404679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155972003202115900966412477 58489501200793462862404679)
  ·
    refine ⟨87734251801190194293607019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58489501200793462862404679 87734251801190194293607019)
    ·
      refine ⟨131601377701785291440410529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87734251801190194293607019 131601377701785291440410529)
      ·
        refine ⟨98701033276338968580307897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131601377701785291440410529 98701033276338968580307897)
        ·
          refine ⟨74025774957254226435230923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98701033276338968580307897 74025774957254226435230923)
          ·
            refine ⟨111038662435881339652846385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74025774957254226435230923 111038662435881339652846385)
            ·
              refine ⟨83278996826911004739634789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111038662435881339652846385 83278996826911004739634789)
              ·
                refine ⟨15614811905045813388681523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83278996826911004739634789 15614811905045813388681523)
                ·
                  refine ⟨23422217857568720083022285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15614811905045813388681523 23422217857568720083022285)
                  ·
                    refine ⟨8783331696588270031133357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23422217857568720083022285 8783331696588270031133357)
                    ·
                      refine ⟨3293749386220601261675009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783331696588270031133357 3293749386220601261675009)
                      ·
                        rfl

theorem cell23_6414554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_6414554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414554 prefixEnd_6414554 := by exact prefixLift 6414554
  have htrace : WordTrace (prefixWord ++ tailWord_6414554) baseStart_6414554 baseEnd_6414554 := by
    simpa [prefixWord, tailWord_6414554, baseEnd_6414554] using wordTrace_append hprefix tailTrace_6414554
  have hstable : (prefixWord ++ tailWord_6414554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414554).length < 2 ^ (prefixWord ++ tailWord_6414554).sum := by decide
  have hdescent : baseEnd_6414554 < baseStart_6414554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414571 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 3]
def baseStart_6414571 : Nat := 118140960795 + 6414571 * 2 ^ 59
def prefixEnd_6414571 : Nat := 4983230072969 + 3 ^ 40 * 6414571 * 2
def baseEnd_6414571 : Nat := 3293758115391727695162431

theorem tailTrace_6414571 : CollatzResearch.WordTrace tailWord_6414571 prefixEnd_6414571 3293758115391727695162431 := by
  unfold tailWord_6414571
  simp only [CollatzResearch.WordTrace]
  refine ⟨233958624844112263352987567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155972416562741508901991711 233958624844112263352987567)
  ·
    refine ⟨350937937266168395029481351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233958624844112263352987567 350937937266168395029481351)
    ·
      refine ⟨526406905899252592544222027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350937937266168395029481351 526406905899252592544222027)
      ·
        refine ⟨789610358848878888816333041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526406905899252592544222027 789610358848878888816333041)
        ·
          refine ⟨592207769136659166612249781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789610358848878888816333041 592207769136659166612249781)
          ·
            refine ⟨55519478356561796869898417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 592207769136659166612249781 55519478356561796869898417)
            ·
              refine ⟨41639608767421347652423813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55519478356561796869898417 41639608767421347652423813)
              ·
                refine ⟨7807426643891502684829465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41639608767421347652423813 7807426643891502684829465)
                ·
                  refine ⟨5855569982918627013622099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807426643891502684829465 5855569982918627013622099)
                  ·
                    refine ⟨8783354974377940520433149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855569982918627013622099 8783354974377940520433149)
                    ·
                      refine ⟨3293758115391727695162431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783354974377940520433149 3293758115391727695162431)
                      ·
                        rfl

theorem cell23_6414571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 3].length) (baseStart_6414571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414571 prefixEnd_6414571 := by exact prefixLift 6414571
  have htrace : WordTrace (prefixWord ++ tailWord_6414571) baseStart_6414571 baseEnd_6414571 := by
    simpa [prefixWord, tailWord_6414571, baseEnd_6414571] using wordTrace_append hprefix tailTrace_6414571
  have hstable : (prefixWord ++ tailWord_6414571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414571).length < 2 ^ (prefixWord ++ tailWord_6414571).sum := by decide
  have hdescent : baseEnd_6414571 < baseStart_6414571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414588 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_6414588 : Nat := 118140960795 + 6414588 * 2 ^ 59
def prefixEnd_6414588 : Nat := 4983230072969 + 3 ^ 40 * 6414588 * 2
def baseEnd_6414588 : Nat := 3293766844562854128649853

theorem tailTrace_6414588 : CollatzResearch.WordTrace tailWord_6414588 prefixEnd_6414588 3293766844562854128649853 := by
  unfold tailWord_6414588
  simp only [CollatzResearch.WordTrace]
  refine ⟨116979622442525337628178209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155972829923367116837570945 116979622442525337628178209)
  ·
    refine ⟨87734716831894003221133657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116979622442525337628178209 87734716831894003221133657)
    ·
      refine ⟨65801037623920502415850243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87734716831894003221133657 65801037623920502415850243)
      ·
        refine ⟨98701556435880753623775365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65801037623920502415850243 98701556435880753623775365)
        ·
          refine ⟨18506541831727641304457881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98701556435880753623775365 18506541831727641304457881)
          ·
            refine ⟨13879906373795730978343411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18506541831727641304457881 13879906373795730978343411)
            ·
              refine ⟨20819859560693596467515117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13879906373795730978343411 20819859560693596467515117)
              ·
                refine ⟨7807447335260098675318169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20819859560693596467515117 7807447335260098675318169)
                ·
                  refine ⟨5855585501445074006488627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807447335260098675318169 5855585501445074006488627)
                  ·
                    refine ⟨8783378252167611009732941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855585501445074006488627 8783378252167611009732941)
                    ·
                      refine ⟨3293766844562854128649853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783378252167611009732941 3293766844562854128649853)
                      ·
                        rfl

theorem cell23_6414588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_6414588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414588 prefixEnd_6414588 := by exact prefixLift 6414588
  have htrace : WordTrace (prefixWord ++ tailWord_6414588) baseStart_6414588 baseEnd_6414588 := by
    simpa [prefixWord, tailWord_6414588, baseEnd_6414588] using wordTrace_append hprefix tailTrace_6414588
  have hstable : (prefixWord ++ tailWord_6414588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414588).length < 2 ^ (prefixWord ++ tailWord_6414588).sum := by decide
  have hdescent : baseEnd_6414588 < baseStart_6414588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414611 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 6, 2, 2]
def baseStart_6414611 : Nat := 118140960795 + 6414611 * 2 ^ 59
def prefixEnd_6414611 : Nat := 4983230072969 + 3 ^ 40 * 6414611 * 2
def baseEnd_6414611 : Nat := 3293778654617907538662247

theorem tailTrace_6414611 : CollatzResearch.WordTrace tailWord_6414611 prefixEnd_6414611 3293778654617907538662247 := by
  unfold tailWord_6414611
  simp only [CollatzResearch.WordTrace]
  refine ⟨233960083763967350184443687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155973389175978233456295791 233960083763967350184443687)
  ·
    refine ⟨350940125645951025276665531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233960083763967350184443687 350940125645951025276665531)
    ·
      refine ⟨526410188468926537914998297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350940125645951025276665531 526410188468926537914998297)
      ·
        refine ⟨394807641351694903436248723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526410188468926537914998297 394807641351694903436248723)
        ·
          refine ⟨592211462027542355154373085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394807641351694903436248723 592211462027542355154373085)
          ·
            refine ⟨222079298260328383182889907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592211462027542355154373085 222079298260328383182889907)
            ·
              refine ⟨333118947390492574774334861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222079298260328383182889907 333118947390492574774334861)
              ·
                refine ⟨124919605271434715540375573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333118947390492574774334861 124919605271434715540375573)
                ·
                  refine ⟨5855606497098502290955105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124919605271434715540375573 5855606497098502290955105)
                  ·
                    refine ⟨4391704872823876718216329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855606497098502290955105 4391704872823876718216329)
                    ·
                      refine ⟨3293778654617907538662247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391704872823876718216329 3293778654617907538662247)
                      ·
                        rfl

theorem cell23_6414611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 2, 2].length) (baseStart_6414611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414611 prefixEnd_6414611 := by exact prefixLift 6414611
  have htrace : WordTrace (prefixWord ++ tailWord_6414611) baseStart_6414611 baseEnd_6414611 := by
    simpa [prefixWord, tailWord_6414611, baseEnd_6414611] using wordTrace_append hprefix tailTrace_6414611
  have hstable : (prefixWord ++ tailWord_6414611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414611).length < 2 ^ (prefixWord ++ tailWord_6414611).sum := by decide
  have hdescent : baseEnd_6414611 < baseStart_6414611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414615 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6414615 : Nat := 118140960795 + 6414615 * 2 ^ 59
def prefixEnd_6414615 : Nat := 4983230072969 + 3 ^ 40 * 6414615 * 2
def baseEnd_6414615 : Nat := 3293780708540525523012229

theorem tailTrace_6414615 : CollatzResearch.WordTrace tailWord_6414615 prefixEnd_6414615 3293780708540525523012229 := by
  unfold tailWord_6414615
  simp only [CollatzResearch.WordTrace]
  refine ⟨233960229655952858867589299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155973486437301905911726199 233960229655952858867589299)
  ·
    refine ⟨350940344483929288301383949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233960229655952858867589299 350940344483929288301383949)
    ·
      refine ⟨131602629181473483113018981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350940344483929288301383949 131602629181473483113018981)
      ·
        refine ⟨24675492971526278083691059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131602629181473483113018981 24675492971526278083691059)
        ·
          refine ⟨37013239457289417125536589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24675492971526278083691059 37013239457289417125536589)
          ·
            refine ⟨13879964796483531422076221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37013239457289417125536589 13879964796483531422076221)
            ·
              refine ⟨5204986798681324283278583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13879964796483531422076221 5204986798681324283278583)
              ·
                refine ⟨7807480198021986424917875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204986798681324283278583 7807480198021986424917875)
                ·
                  refine ⟨11711220297032979637376813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807480198021986424917875 11711220297032979637376813)
                  ·
                    refine ⟨4391707611387367364016305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11711220297032979637376813 4391707611387367364016305)
                    ·
                      refine ⟨3293780708540525523012229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391707611387367364016305 3293780708540525523012229)
                      ·
                        rfl

theorem cell23_6414615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6414615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414615 prefixEnd_6414615 := by exact prefixLift 6414615
  have htrace : WordTrace (prefixWord ++ tailWord_6414615) baseStart_6414615 baseEnd_6414615 := by
    simpa [prefixWord, tailWord_6414615, baseEnd_6414615] using wordTrace_append hprefix tailTrace_6414615
  have hstable : (prefixWord ++ tailWord_6414615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414615).length < 2 ^ (prefixWord ++ tailWord_6414615).sum := by decide
  have hdescent : baseEnd_6414615 < baseStart_6414615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414622 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6414622 : Nat := 118140960795 + 6414622 * 2 ^ 59
def prefixEnd_6414622 : Nat := 4983230072969 + 3 ^ 40 * 6414622 * 2
def baseEnd_6414622 : Nat := 3293784302905106995624697

theorem tailTrace_6414622 : CollatzResearch.WordTrace tailWord_6414622 prefixEnd_6414622 3293784302905106995624697 := by
  unfold tailWord_6414622
  simp only [CollatzResearch.WordTrace]
  refine ⟨29245060620865937382886765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155973656644618332708729413 29245060620865937382886765)
  ·
    refine ⟨10966897732824726518582537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29245060620865937382886765 10966897732824726518582537)
    ·
      refine ⟨8225173299618544888936903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10966897732824726518582537 8225173299618544888936903)
      ·
        refine ⟨12337759949427817333405355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8225173299618544888936903 12337759949427817333405355)
        ·
          refine ⟨18506639924141726000108033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12337759949427817333405355 18506639924141726000108033)
          ·
            refine ⟨13879979943106294500081025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18506639924141726000108033 13879979943106294500081025)
            ·
              refine ⟨10409984957329720875060769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13879979943106294500081025 10409984957329720875060769)
              ·
                refine ⟨7807488717997290656295577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409984957329720875060769 7807488717997290656295577)
                ·
                  refine ⟨5855616538497967992221683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807488717997290656295577 5855616538497967992221683)
                  ·
                    refine ⟨8783424807746951988332525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855616538497967992221683 8783424807746951988332525)
                    ·
                      refine ⟨3293784302905106995624697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783424807746951988332525 3293784302905106995624697)
                      ·
                        rfl

theorem cell23_6414622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6414622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414622 prefixEnd_6414622 := by exact prefixLift 6414622
  have htrace : WordTrace (prefixWord ++ tailWord_6414622) baseStart_6414622 baseEnd_6414622 := by
    simpa [prefixWord, tailWord_6414622, baseEnd_6414622] using wordTrace_append hprefix tailTrace_6414622
  have hstable : (prefixWord ++ tailWord_6414622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414622).length < 2 ^ (prefixWord ++ tailWord_6414622).sum := by decide
  have hdescent : baseEnd_6414622 < baseStart_6414622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414638 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_6414638 : Nat := 118140960795 + 6414638 * 2 ^ 59
def prefixEnd_6414638 : Nat := 4983230072969 + 3 ^ 40 * 6414638 * 2
def baseEnd_6414638 : Nat := 1097930839531859644341541

theorem tailTrace_6414638 : CollatzResearch.WordTrace tailWord_6414638 prefixEnd_6414638 1097930839531859644341541 := by
  unfold tailWord_6414638
  simp only [CollatzResearch.WordTrace]
  refine ⟨29245133566858691724459571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155974045689913022530451045 29245133566858691724459571)
  ·
    refine ⟨43867700350288037586689357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29245133566858691724459571 43867700350288037586689357)
    ·
      refine ⟨16450387631358014095008509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43867700350288037586689357 16450387631358014095008509)
      ·
        refine ⟨6168895361759255285628191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16450387631358014095008509 6168895361759255285628191)
        ·
          refine ⟨9253343042638882928442287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168895361759255285628191 9253343042638882928442287)
          ·
            refine ⟨13880014563958324392663431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253343042638882928442287 13880014563958324392663431)
            ·
              refine ⟨20820021845937486588995147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13880014563958324392663431 20820021845937486588995147)
              ·
                refine ⟨31230032768906229883492721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20820021845937486588995147 31230032768906229883492721)
                ·
                  refine ⟨23422524576679672412619541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31230032768906229883492721 23422524576679672412619541)
                  ·
                    refine ⟨1097930839531859644341541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23422524576679672412619541 1097930839531859644341541)
                    ·
                      rfl

theorem cell23_6414638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_6414638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414638 prefixEnd_6414638 := by exact prefixLift 6414638
  have htrace : WordTrace (prefixWord ++ tailWord_6414638) baseStart_6414638 baseEnd_6414638 := by
    simpa [prefixWord, tailWord_6414638, baseEnd_6414638] using wordTrace_append hprefix tailTrace_6414638
  have hstable : (prefixWord ++ tailWord_6414638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414638).length < 2 ^ (prefixWord ++ tailWord_6414638).sum := by decide
  have hdescent : baseEnd_6414638 < baseStart_6414638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414641 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_6414641 : Nat := 118140960795 + 6414641 * 2 ^ 59
def prefixEnd_6414641 : Nat := 4983230072969 + 3 ^ 40 * 6414641 * 2
def baseEnd_6414641 : Nat := 3293794059037542421287109

theorem tailTrace_6414641 : CollatzResearch.WordTrace tailWord_6414641 prefixEnd_6414641 3293794059037542421287109 := by
  unfold tailWord_6414641
  simp only [CollatzResearch.WordTrace]
  refine ⟨233961177953858665308035777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155974118635905776872023851 233961177953858665308035777)
  ·
    refine ⟨175470883465393998981026833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233961177953858665308035777 175470883465393998981026833)
    ·
      refine ⟨131603162599045499235770125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175470883465393998981026833 131603162599045499235770125)
      ·
        refine ⟨49351185974642062213413797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131603162599045499235770125 49351185974642062213413797)
        ·
          refine ⟨9253347370245386665015087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49351185974642062213413797 9253347370245386665015087)
          ·
            refine ⟨13880021055368079997522631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253347370245386665015087 13880021055368079997522631)
            ·
              refine ⟨20820031583052119996283947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13880021055368079997522631 20820031583052119996283947)
              ·
                refine ⟨31230047374578179994425921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20820031583052119996283947 31230047374578179994425921)
                ·
                  refine ⟨23422535530933634995819441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31230047374578179994425921 23422535530933634995819441)
                  ·
                    refine ⟨17566901648200226246864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23422535530933634995819441 17566901648200226246864581)
                    ·
                      refine ⟨3293794059037542421287109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17566901648200226246864581 3293794059037542421287109)
                      ·
                        rfl

theorem cell23_6414641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_6414641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414641 prefixEnd_6414641 := by exact prefixLift 6414641
  have htrace : WordTrace (prefixWord ++ tailWord_6414641) baseStart_6414641 baseEnd_6414641 := by
    simpa [prefixWord, tailWord_6414641, baseEnd_6414641] using wordTrace_append hprefix tailTrace_6414641
  have hstable : (prefixWord ++ tailWord_6414641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414641).length < 2 ^ (prefixWord ++ tailWord_6414641).sum := by decide
  have hdescent : baseEnd_6414641 < baseStart_6414641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414674 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6414674 : Nat := 118140960795 + 6414674 * 2 ^ 59
def prefixEnd_6414674 : Nat := 4983230072969 + 3 ^ 40 * 6414674 * 2
def baseEnd_6414674 : Nat := 3293811003899140792174457

theorem tailTrace_6414674 : CollatzResearch.WordTrace tailWord_6414674 prefixEnd_6414674 3293811003899140792174457 := by
  unfold tailWord_6414674
  simp only [CollatzResearch.WordTrace]
  refine ⟨58490595390684777985996769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155974921041826074629324717 58490595390684777985996769)
  ·
    refine ⟨43867946543013583489497577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58490595390684777985996769 43867946543013583489497577)
    ·
      refine ⟨32900959907260187617123183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43867946543013583489497577 32900959907260187617123183)
      ·
        refine ⟨49351439860890281425684775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32900959907260187617123183 49351439860890281425684775)
        ·
          refine ⟨74027159791335422138527163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49351439860890281425684775 74027159791335422138527163)
          ·
            refine ⟨111040739687003133207790745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74027159791335422138527163 111040739687003133207790745)
            ·
              refine ⟨83280554765252349905843059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111040739687003133207790745 83280554765252349905843059)
              ·
                refine ⟨124920832147878524858764589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83280554765252349905843059 124920832147878524858764589)
                ·
                  refine ⟨46845312055454446822036721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124920832147878524858764589 46845312055454446822036721)
                  ·
                    refine ⟨35133984041590835116527541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46845312055454446822036721 35133984041590835116527541)
                    ·
                      refine ⟨3293811003899140792174457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35133984041590835116527541 3293811003899140792174457)
                      ·
                        rfl

theorem cell23_6414674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6414674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414674 prefixEnd_6414674 := by exact prefixLift 6414674
  have htrace : WordTrace (prefixWord ++ tailWord_6414674) baseStart_6414674 baseEnd_6414674 := by
    simpa [prefixWord, tailWord_6414674, baseEnd_6414674] using wordTrace_append hprefix tailTrace_6414674
  have hstable : (prefixWord ++ tailWord_6414674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414674).length < 2 ^ (prefixWord ++ tailWord_6414674).sum := by decide
  have hdescent : baseEnd_6414674 < baseStart_6414674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414724 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 10]
def baseStart_6414724 : Nat := 118140960795 + 6414724 * 2 ^ 59
def prefixEnd_6414724 : Nat := 4983230072969 + 3 ^ 40 * 6414724 * 2
def baseEnd_6414724 : Nat := 365981853103540621838803

theorem tailTrace_6414724 : CollatzResearch.WordTrace tailWord_6414724 prefixEnd_6414724 365981853103540621838803 := by
  unfold tailWord_6414724
  simp only [CollatzResearch.WordTrace]
  refine ⟨116982102606278985241653613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155976136808371980322204817 116982102606278985241653613)
  ·
    refine ⟨43868288477354619465620105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116982102606278985241653613 43868288477354619465620105)
    ·
      refine ⟨32901216358015964599215079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43868288477354619465620105 32901216358015964599215079)
      ·
        refine ⟨49351824537023946898822619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32901216358015964599215079 49351824537023946898822619)
        ·
          refine ⟨74027736805535920348233929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49351824537023946898822619 74027736805535920348233929)
          ·
            refine ⟨55520802604151940261175447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74027736805535920348233929 55520802604151940261175447)
            ·
              refine ⟨83281203906227910391763171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55520802604151940261175447 83281203906227910391763171)
              ·
                refine ⟨124921805859341865587644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83281203906227910391763171 124921805859341865587644757)
                ·
                  refine ⟨365981853103540621838803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124921805859341865587644757 365981853103540621838803)
                  ·
                    rfl

theorem cell23_6414724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_6414724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414724 prefixEnd_6414724 := by exact prefixLift 6414724
  have htrace : WordTrace (prefixWord ++ tailWord_6414724) baseStart_6414724 baseEnd_6414724 := by
    simpa [prefixWord, tailWord_6414724, baseEnd_6414724] using wordTrace_append hprefix tailTrace_6414724
  have hstable : (prefixWord ++ tailWord_6414724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414724).length < 2 ^ (prefixWord ++ tailWord_6414724).sum := by decide
  have hdescent : baseEnd_6414724 < baseStart_6414724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414742 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6414742 : Nat := 118140960795 + 6414742 * 2 ^ 59
def prefixEnd_6414742 : Nat := 4983230072969 + 3 ^ 40 * 6414742 * 2
def baseEnd_6414742 : Nat := 3293845920583646526124145

theorem tailTrace_6414742 : CollatzResearch.WordTrace tailWord_6414742 prefixEnd_6414742 3293845920583646526124145 := by
  unfold tailWord_6414742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622803857905797472341405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155976574484328506371641653 14622803857905797472341405)
  ·
    refine ⟨5483551446714674052128027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14622803857905797472341405 5483551446714674052128027)
    ·
      refine ⟨8225327170072011078192041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5483551446714674052128027 8225327170072011078192041)
      ·
        refine ⟨6168995377554008308644031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8225327170072011078192041 6168995377554008308644031)
        ·
          refine ⟨9253493066331012462966047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168995377554008308644031 9253493066331012462966047)
          ·
            refine ⟨13880239599496518694449071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253493066331012462966047 13880239599496518694449071)
            ·
              refine ⟨20820359399244778041673607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13880239599496518694449071 20820359399244778041673607)
              ·
                refine ⟨31230539098867167062510411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20820359399244778041673607 31230539098867167062510411)
                ·
                  refine ⟨46845808648300750593765617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31230539098867167062510411 46845808648300750593765617)
                  ·
                    refine ⟨35134356486225562945324213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46845808648300750593765617 35134356486225562945324213)
                    ·
                      refine ⟨3293845920583646526124145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35134356486225562945324213 3293845920583646526124145)
                      ·
                        rfl

theorem cell23_6414742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6414742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414742 prefixEnd_6414742 := by exact prefixLift 6414742
  have htrace : WordTrace (prefixWord ++ tailWord_6414742) baseStart_6414742 baseEnd_6414742 := by
    simpa [prefixWord, tailWord_6414742, baseEnd_6414742] using wordTrace_append hprefix tailTrace_6414742
  have hstable : (prefixWord ++ tailWord_6414742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414742).length < 2 ^ (prefixWord ++ tailWord_6414742).sum := by decide
  have hdescent : baseEnd_6414742 < baseStart_6414742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414745 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 1, 4]
def baseStart_6414745 : Nat := 118140960795 + 6414745 * 2 ^ 59
def prefixEnd_6414745 : Nat := 4983230072969 + 3 ^ 40 * 6414745 * 2
def baseEnd_6414745 : Nat := 1097949153675203338128877

theorem tailTrace_6414745 : CollatzResearch.WordTrace tailWord_6414745 prefixEnd_6414745 1097949153675203338128877 := by
  unfold tailWord_6414745
  simp only [CollatzResearch.WordTrace]
  refine ⟨233964971145481891069821689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155976647430321260713214459 233964971145481891069821689)
  ·
    refine ⟨175473728359111418302366267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233964971145481891069821689 175473728359111418302366267)
    ·
      refine ⟨263210592538667127453549401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175473728359111418302366267 263210592538667127453549401)
      ·
        refine ⟨197407944404000345590162051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263210592538667127453549401 197407944404000345590162051)
        ·
          refine ⟨296111916606000518385243077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197407944404000345590162051 296111916606000518385243077)
          ·
            refine ⟨55520984363625097197233077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296111916606000518385243077 55520984363625097197233077)
            ·
              refine ⟨5205092284089852862240601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55520984363625097197233077 5205092284089852862240601)
              ·
                refine ⟨3903819213067389646680451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205092284089852862240601 3903819213067389646680451)
                ·
                  refine ⟨5855728819601084470020677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903819213067389646680451 5855728819601084470020677)
                  ·
                    refine ⟨1097949153675203338128877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5855728819601084470020677 1097949153675203338128877)
                    ·
                      rfl

theorem cell23_6414745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 4].length) (baseStart_6414745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414745 prefixEnd_6414745 := by exact prefixLift 6414745
  have htrace : WordTrace (prefixWord ++ tailWord_6414745) baseStart_6414745 baseEnd_6414745 := by
    simpa [prefixWord, tailWord_6414745, baseEnd_6414745] using wordTrace_append hprefix tailTrace_6414745
  have hstable : (prefixWord ++ tailWord_6414745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414745).length < 2 ^ (prefixWord ++ tailWord_6414745).sum := by decide
  have hdescent : baseEnd_6414745 < baseStart_6414745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414761 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 5, 2]
def baseStart_6414761 : Nat := 118140960795 + 6414761 * 2 ^ 59
def prefixEnd_6414761 : Nat := 4983230072969 + 3 ^ 40 * 6414761 * 2
def baseEnd_6414761 : Nat := 3293855676716081951786557

theorem tailTrace_6414761 : CollatzResearch.WordTrace tailWord_6414761 prefixEnd_6414761 3293855676716081951786557 := by
  unfold tailWord_6414761
  simp only [CollatzResearch.WordTrace]
  refine ⟨233965554713423925802404137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155977036475615950534936091 233965554713423925802404137)
  ·
    refine ⟨175474166035067944351803103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233965554713423925802404137 175474166035067944351803103)
    ·
      refine ⟨263211249052601916527704655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175474166035067944351803103 263211249052601916527704655)
      ·
        refine ⟨394816873578902874791556983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263211249052601916527704655 394816873578902874791556983)
        ·
          refine ⟨592225310368354312187335475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394816873578902874791556983 592225310368354312187335475)
          ·
            refine ⟨888337965552531468281003213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592225310368354312187335475 888337965552531468281003213)
            ·
              refine ⟨333126737082199300605376205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 888337965552531468281003213 333126737082199300605376205)
              ·
                refine ⟨124922526405824737727016077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333126737082199300605376205 124922526405824737727016077)
                ·
                  refine ⟨46845947402184276647631029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124922526405824737727016077 46845947402184276647631029)
                  ·
                    refine ⟨4391807568954775935715409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46845947402184276647631029 4391807568954775935715409)
                    ·
                      refine ⟨3293855676716081951786557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391807568954775935715409 3293855676716081951786557)
                      ·
                        rfl

theorem cell23_6414761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 5, 2].length) (baseStart_6414761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414761 prefixEnd_6414761 := by exact prefixLift 6414761
  have htrace : WordTrace (prefixWord ++ tailWord_6414761) baseStart_6414761 baseEnd_6414761 := by
    simpa [prefixWord, tailWord_6414761, baseEnd_6414761] using wordTrace_append hprefix tailTrace_6414761
  have hstable : (prefixWord ++ tailWord_6414761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414761).length < 2 ^ (prefixWord ++ tailWord_6414761).sum := by decide
  have hdescent : baseEnd_6414761 < baseStart_6414761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414801 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_6414801 : Nat := 118140960795 + 6414801 * 2 ^ 59
def prefixEnd_6414801 : Nat := 4983230072969 + 3 ^ 40 * 6414801 * 2
def baseEnd_6414801 : Nat := 1097958738647420598428791

theorem tailTrace_6414801 : CollatzResearch.WordTrace tailWord_6414801 prefixEnd_6414801 1097958738647420598428791 := by
  unfold tailWord_6414801
  simp only [CollatzResearch.WordTrace]
  refine ⟨233967013633279012633860257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155978009088852675089240171 233967013633279012633860257)
  ·
    refine ⟨175475260224959259475395193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233967013633279012633860257 175475260224959259475395193)
    ·
      refine ⟨131606445168719444606546395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175475260224959259475395193 131606445168719444606546395)
      ·
        refine ⟨197409667753079166909819593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131606445168719444606546395 197409667753079166909819593)
        ·
          refine ⟨148057250814809375182364695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197409667753079166909819593 148057250814809375182364695)
          ·
            refine ⟨222085876222214062773547043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148057250814809375182364695 222085876222214062773547043)
            ·
              refine ⟨333128814333321094160320565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222085876222214062773547043 333128814333321094160320565)
              ·
                refine ⟨31230826343748852577530053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 333128814333321094160320565 31230826343748852577530053)
                ·
                  refine ⟨5855779939452909858286885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31230826343748852577530053 5855779939452909858286885)
                  ·
                    refine ⟨1097958738647420598428791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5855779939452909858286885 1097958738647420598428791)
                    ·
                      rfl

theorem cell23_6414801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_6414801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414801 prefixEnd_6414801 := by exact prefixLift 6414801
  have htrace : WordTrace (prefixWord ++ tailWord_6414801) baseStart_6414801 baseEnd_6414801 := by
    simpa [prefixWord, tailWord_6414801, baseEnd_6414801] using wordTrace_append hprefix tailTrace_6414801
  have hstable : (prefixWord ++ tailWord_6414801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414801).length < 2 ^ (prefixWord ++ tailWord_6414801).sum := by decide
  have hdescent : baseEnd_6414801 < baseStart_6414801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414828 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_6414828 : Nat := 118140960795 + 6414828 * 2 ^ 59
def prefixEnd_6414828 : Nat := 4983230072969 + 3 ^ 40 * 6414828 * 2
def baseEnd_6414828 : Nat := 3293890079919933189648749

theorem tailTrace_6414828 : CollatzResearch.WordTrace tailWord_6414828 prefixEnd_6414828 3293890079919933189648749 := by
  unfold tailWord_6414828
  simp only [CollatzResearch.WordTrace]
  refine ⟨116983999202090598122546569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155978665602787464163395425 116983999202090598122546569)
  ·
    refine ⟨87737999401567948591909927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116983999202090598122546569 87737999401567948591909927)
    ·
      refine ⟨131606999102351922887864891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87737999401567948591909927 131606999102351922887864891)
      ·
        refine ⟨197410498653527884331797337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131606999102351922887864891 197410498653527884331797337)
        ·
          refine ⟨148057873990145913248848003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197410498653527884331797337 148057873990145913248848003)
          ·
            refine ⟨222086810985218869873272005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148057873990145913248848003 222086810985218869873272005)
            ·
              refine ⟨41641277059728538101238501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222086810985218869873272005 41641277059728538101238501)
              ·
                refine ⟨7807739448699100893982219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41641277059728538101238501 7807739448699100893982219)
                ·
                  refine ⟨11711609173048651340973329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807739448699100893982219 11711609173048651340973329)
                  ·
                    refine ⟨8783706879786488505729997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11711609173048651340973329 8783706879786488505729997)
                    ·
                      refine ⟨3293890079919933189648749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8783706879786488505729997 3293890079919933189648749)
                      ·
                        rfl

theorem cell23_6414828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_6414828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414828 prefixEnd_6414828 := by exact prefixLift 6414828
  have htrace : WordTrace (prefixWord ++ tailWord_6414828) baseStart_6414828 baseEnd_6414828 := by
    simpa [prefixWord, tailWord_6414828, baseEnd_6414828] using wordTrace_append hprefix tailTrace_6414828
  have hstable : (prefixWord ++ tailWord_6414828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414828).length < 2 ^ (prefixWord ++ tailWord_6414828).sum := by decide
  have hdescent : baseEnd_6414828 < baseStart_6414828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414838 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6414838 : Nat := 118140960795 + 6414838 * 2 ^ 59
def prefixEnd_6414838 : Nat := 4983230072969 + 3 ^ 40 * 6414838 * 2
def baseEnd_6414838 : Nat := 3293895214726478150523703

theorem tailTrace_6414838 : CollatzResearch.WordTrace tailWord_6414838 prefixEnd_6414838 3293895214726478150523703 := by
  unfold tailWord_6414838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623022695884060497059823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155978908756096645301971445 14623022695884060497059823)
  ·
    refine ⟨21934534043826090745589735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14623022695884060497059823 21934534043826090745589735)
    ·
      refine ⟨32901801065739136118384603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21934534043826090745589735 32901801065739136118384603)
      ·
        refine ⟨49352701598608704177576905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32901801065739136118384603 49352701598608704177576905)
        ·
          refine ⟨37014526198956528133182679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49352701598608704177576905 37014526198956528133182679)
          ·
            refine ⟨55521789298434792199774019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37014526198956528133182679 55521789298434792199774019)
            ·
              refine ⟨83282683947652188299661029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55521789298434792199774019 83282683947652188299661029)
              ·
                refine ⟨15615503240184785306186443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83282683947652188299661029 15615503240184785306186443)
                ·
                  refine ⟨23423254860277177959279665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15615503240184785306186443 23423254860277177959279665)
                  ·
                    refine ⟨17567441145207883469459749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23423254860277177959279665 17567441145207883469459749)
                    ·
                      refine ⟨3293895214726478150523703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17567441145207883469459749 3293895214726478150523703)
                      ·
                        rfl

theorem cell23_6414838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6414838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414838 prefixEnd_6414838 := by exact prefixLift 6414838
  have htrace : WordTrace (prefixWord ++ tailWord_6414838) baseStart_6414838 baseEnd_6414838 := by
    simpa [prefixWord, tailWord_6414838, baseEnd_6414838] using wordTrace_append hprefix tailTrace_6414838
  have hstable : (prefixWord ++ tailWord_6414838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414838).length < 2 ^ (prefixWord ++ tailWord_6414838).sum := by decide
  have hdescent : baseEnd_6414838 < baseStart_6414838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414852 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_6414852 : Nat := 118140960795 + 6414852 * 2 ^ 59
def prefixEnd_6414852 : Nat := 4983230072969 + 3 ^ 40 * 6414852 * 2
def baseEnd_6414852 : Nat := 1097967467818547031916213

theorem tailTrace_6414852 : CollatzResearch.WordTrace tailWord_6414852 prefixEnd_6414852 1097967467818547031916213 := by
  unfold tailWord_6414852
  simp only [CollatzResearch.WordTrace]
  refine ⟨116984436878047124171983405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155979249170729498895977873 116984436878047124171983405)
  ·
    refine ⟨43869163829267671564493777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116984436878047124171983405 43869163829267671564493777)
    ·
      refine ⟨32901872871950753673370333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43869163829267671564493777 32901872871950753673370333)
      ·
        refine ⟨12338202326981532627513875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32901872871950753673370333 12338202326981532627513875)
        ·
          refine ⟨18507303490472298941270813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12338202326981532627513875 18507303490472298941270813)
          ·
            refine ⟨6940238808927112102976555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18507303490472298941270813 6940238808927112102976555)
            ·
              refine ⟨10410358213390668154464833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6940238808927112102976555 10410358213390668154464833)
              ·
                refine ⟨7807768660043001115848625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10410358213390668154464833 7807768660043001115848625)
                ·
                  refine ⟨5855826495032250836886469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807768660043001115848625 5855826495032250836886469)
                  ·
                    refine ⟨1097967467818547031916213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5855826495032250836886469 1097967467818547031916213)
                    ·
                      rfl

theorem cell23_6414852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_6414852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414852 prefixEnd_6414852 := by exact prefixLift 6414852
  have htrace : WordTrace (prefixWord ++ tailWord_6414852) baseStart_6414852 baseEnd_6414852 := by
    simpa [prefixWord, tailWord_6414852, baseEnd_6414852] using wordTrace_append hprefix tailTrace_6414852
  have hstable : (prefixWord ++ tailWord_6414852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414852).length < 2 ^ (prefixWord ++ tailWord_6414852).sum := by decide
  have hdescent : baseEnd_6414852 < baseStart_6414852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414885 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_6414885 : Nat := 118140960795 + 6414885 * 2 ^ 59
def prefixEnd_6414885 : Nat := 4983230072969 + 3 ^ 40 * 6414885 * 2
def baseEnd_6414885 : Nat := 3293919348317239466635987

theorem tailTrace_6414885 : CollatzResearch.WordTrace tailWord_6414885 prefixEnd_6414885 3293919348317239466635987 := by
  unfold tailWord_6414885
  simp only [CollatzResearch.WordTrace]
  refine ⟨233970077364974694979918109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155980051576649796653278739 233970077364974694979918109)
  ·
    refine ⟨87738779011865510617469291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233970077364974694979918109 87738779011865510617469291)
    ·
      refine ⟨131608168517798265926203937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87738779011865510617469291 131608168517798265926203937)
      ·
        refine ⟨98706126388348699444652953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131608168517798265926203937 98706126388348699444652953)
        ·
          refine ⟨74029594791261524583489715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98706126388348699444652953 74029594791261524583489715)
          ·
            refine ⟨111044392186892286875234573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74029594791261524583489715 111044392186892286875234573)
            ·
              refine ⟨41641647070084607578212965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111044392186892286875234573 41641647070084607578212965)
              ·
                refine ⟨7807808825640863920914931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41641647070084607578212965 7807808825640863920914931)
                ·
                  refine ⟨11711713238461295881372397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807808825640863920914931 11711713238461295881372397)
                  ·
                    refine ⟨4391892464422985955514649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11711713238461295881372397 4391892464422985955514649)
                    ·
                      refine ⟨3293919348317239466635987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391892464422985955514649 3293919348317239466635987)
                      ·
                        rfl

theorem cell23_6414885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_6414885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414885 prefixEnd_6414885 := by exact prefixLift 6414885
  have htrace : WordTrace (prefixWord ++ tailWord_6414885) baseStart_6414885 baseEnd_6414885 := by
    simpa [prefixWord, tailWord_6414885, baseEnd_6414885] using wordTrace_append hprefix tailTrace_6414885
  have hstable : (prefixWord ++ tailWord_6414885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414885).length < 2 ^ (prefixWord ++ tailWord_6414885).sum := by decide
  have hdescent : baseEnd_6414885 < baseStart_6414885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414888 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6414888 : Nat := 118140960795 + 6414888 * 2 ^ 59
def prefixEnd_6414888 : Nat := 4983230072969 + 3 ^ 40 * 6414888 * 2
def baseEnd_6414888 : Nat := 3293920888759202954898473

theorem tailTrace_6414888 : CollatzResearch.WordTrace tailWord_6414888 prefixEnd_6414888 3293920888759202954898473 := by
  unfold tailWord_6414888
  simp only [CollatzResearch.WordTrace]
  refine ⟨116985093391981913246138659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155980124522642550994851545 116985093391981913246138659)
  ·
    refine ⟨175477640087972869869207989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116985093391981913246138659 175477640087972869869207989)
    ·
      refine ⟨16451028758247456550238249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175477640087972869869207989 16451028758247456550238249)
      ·
        refine ⟨12338271568685592412678687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16451028758247456550238249 12338271568685592412678687)
        ·
          refine ⟨18507407353028388619018031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12338271568685592412678687 18507407353028388619018031)
          ·
            refine ⟨27761111029542582928527047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18507407353028388619018031 27761111029542582928527047)
            ·
              refine ⟨41641666544313874392790571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27761111029542582928527047 41641666544313874392790571)
              ·
                refine ⟨62462499816470811589185857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41641666544313874392790571 62462499816470811589185857)
                ·
                  refine ⟨46846874862353108691889393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62462499816470811589185857 46846874862353108691889393)
                  ·
                    refine ⟨35135156146764831518917045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46846874862353108691889393 35135156146764831518917045)
                    ·
                      refine ⟨3293920888759202954898473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35135156146764831518917045 3293920888759202954898473)
                      ·
                        rfl

theorem cell23_6414888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6414888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414888 prefixEnd_6414888 := by exact prefixLift 6414888
  have htrace : WordTrace (prefixWord ++ tailWord_6414888) baseStart_6414888 baseEnd_6414888 := by
    simpa [prefixWord, tailWord_6414888, baseEnd_6414888] using wordTrace_append hprefix tailTrace_6414888
  have hstable : (prefixWord ++ tailWord_6414888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414888).length < 2 ^ (prefixWord ++ tailWord_6414888).sum := by decide
  have hdescent : baseEnd_6414888 < baseStart_6414888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414966 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6414966 : Nat := 118140960795 + 6414966 * 2 ^ 59
def prefixEnd_6414966 : Nat := 4983230072969 + 3 ^ 40 * 6414966 * 2
def baseEnd_6414966 : Nat := 3293960940250253649723115

theorem tailTrace_6414966 : CollatzResearch.WordTrace tailWord_6414966 prefixEnd_6414966 3293960940250253649723115 := by
  unfold tailWord_6414966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623314479855077863351047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155982021118454163875744501 14623314479855077863351047)
  ·
    refine ⟨21934971719782616795026571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14623314479855077863351047 21934971719782616795026571)
    ·
      refine ⟨32902457579673925192539857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21934971719782616795026571 32902457579673925192539857)
      ·
        refine ⟨24676843184755443894404893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32902457579673925192539857 24676843184755443894404893)
        ·
          refine ⟨9253816194283291460401835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24676843184755443894404893 9253816194283291460401835)
          ·
            refine ⟨13880724291424937190602753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253816194283291460401835 13880724291424937190602753)
            ·
              refine ⟨10410543218568702892952065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13880724291424937190602753 10410543218568702892952065)
              ·
                refine ⟨7807907413926527169714049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10410543218568702892952065 7807907413926527169714049)
                ·
                  refine ⟨5855930560444895377285537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807907413926527169714049 5855930560444895377285537)
                  ·
                    refine ⟨4391947920333671532964153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855930560444895377285537 4391947920333671532964153)
                    ·
                      refine ⟨3293960940250253649723115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4391947920333671532964153 3293960940250253649723115)
                      ·
                        rfl

theorem cell23_6414966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6414966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414966 prefixEnd_6414966 := by exact prefixLift 6414966
  have htrace : WordTrace (prefixWord ++ tailWord_6414966) baseStart_6414966 baseEnd_6414966 := by
    simpa [prefixWord, tailWord_6414966, baseEnd_6414966] using wordTrace_append hprefix tailTrace_6414966
  have hstable : (prefixWord ++ tailWord_6414966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414966).length < 2 ^ (prefixWord ++ tailWord_6414966).sum := by decide
  have hdescent : baseEnd_6414966 < baseStart_6414966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6414991 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_6414991 : Nat := 118140960795 + 6414991 * 2 ^ 59
def prefixEnd_6414991 : Nat := 4983230072969 + 3 ^ 40 * 6414991 * 2
def baseEnd_6414991 : Nat := 3293973777266616051910499

theorem tailTrace_6414991 : CollatzResearch.WordTrace tailWord_6414991 prefixEnd_6414991 3293973777266616051910499 := by
  unfold tailWord_6414991
  simp only [CollatzResearch.WordTrace]
  refine ⟨233973943502590675083276827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155982629001727116722184551 233973943502590675083276827)
  ·
    refine ⟨350960915253886012624915241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233973943502590675083276827 350960915253886012624915241)
    ·
      refine ⟨263220686440414509468686431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350960915253886012624915241 263220686440414509468686431)
      ·
        refine ⟨394831029660621764203029647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263220686440414509468686431 394831029660621764203029647)
        ·
          refine ⟨592246544490932646304544471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394831029660621764203029647 592246544490932646304544471)
          ·
            refine ⟨888369816736398969456816707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592246544490932646304544471 888369816736398969456816707)
            ·
              refine ⟨1332554725104598454185225061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888369816736398969456816707 1332554725104598454185225061)
              ·
                refine ⟨249854010957112210159729699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1332554725104598454185225061 249854010957112210159729699)
                ·
                  refine ⟨374781016435668315239594549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249854010957112210159729699 374781016435668315239594549)
                  ·
                    refine ⟨35135720290843904553711989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 374781016435668315239594549 35135720290843904553711989)
                    ·
                      refine ⟨3293973777266616051910499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35135720290843904553711989 3293973777266616051910499)
                      ·
                        rfl

theorem cell23_6414991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_6414991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6414991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6414991 prefixEnd_6414991 := by exact prefixLift 6414991
  have htrace : WordTrace (prefixWord ++ tailWord_6414991) baseStart_6414991 baseEnd_6414991 := by
    simpa [prefixWord, tailWord_6414991, baseEnd_6414991] using wordTrace_append hprefix tailTrace_6414991
  have hstable : (prefixWord ++ tailWord_6414991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6414991).length < 2 ^ (prefixWord ++ tailWord_6414991).sum := by decide
  have hdescent : baseEnd_6414991 < baseStart_6414991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6414991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415005 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_6415005 : Nat := 118140960795 + 6415005 * 2 ^ 59
def prefixEnd_6415005 : Nat := 4983230072969 + 3 ^ 40 * 6415005 * 2
def baseEnd_6415005 : Nat := 3293980965995778997135435

theorem tailTrace_6415005 : CollatzResearch.WordTrace tailWord_6415005 prefixEnd_6415005 3293980965995778997135435 := by
  unfold tailWord_6415005
  simp only [CollatzResearch.WordTrace]
  refine ⟨233974454124539955474286469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155982969416359970316190979 233974454124539955474286469)
  ·
    refine ⟨43870210148351241651428713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233974454124539955474286469 43870210148351241651428713)
    ·
      refine ⟨32902657611263431238571535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43870210148351241651428713 32902657611263431238571535)
      ·
        refine ⟨49353986416895146857857303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32902657611263431238571535 49353986416895146857857303)
        ·
          refine ⟨74030979625342720286785955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49353986416895146857857303 74030979625342720286785955)
          ·
            refine ⟨111046469438014080430178933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74030979625342720286785955 111046469438014080430178933)
            ·
              refine ⟨10410606509813820040329275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111046469438014080430178933 10410606509813820040329275)
              ·
                refine ⟨15615909764720730060493913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10410606509813820040329275 15615909764720730060493913)
                ·
                  refine ⟨11711932323540547545370435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15615909764720730060493913 11711932323540547545370435)
                  ·
                    refine ⟨17567898485310821318055653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11711932323540547545370435 17567898485310821318055653)
                    ·
                      refine ⟨3293980965995778997135435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17567898485310821318055653 3293980965995778997135435)
                      ·
                        rfl

theorem cell23_6415005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_6415005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415005 prefixEnd_6415005 := by exact prefixLift 6415005
  have htrace : WordTrace (prefixWord ++ tailWord_6415005) baseStart_6415005 baseEnd_6415005 := by
    simpa [prefixWord, tailWord_6415005, baseEnd_6415005] using wordTrace_append hprefix tailTrace_6415005
  have hstable : (prefixWord ++ tailWord_6415005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415005).length < 2 ^ (prefixWord ++ tailWord_6415005).sum := by decide
  have hdescent : baseEnd_6415005 < baseStart_6415005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415065 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 5, 2]
def baseStart_6415065 : Nat := 118140960795 + 6415065 * 2 ^ 59
def prefixEnd_6415065 : Nat := 4983230072969 + 3 ^ 40 * 6415065 * 2
def baseEnd_6415065 : Nat := 3294011774835048762385159

theorem tailTrace_6415065 : CollatzResearch.WordTrace tailWord_6415065 prefixEnd_6415065 3294011774835048762385159 := by
  unfold tailWord_6415065
  simp only [CollatzResearch.WordTrace]
  refine ⟨233976642504322585721470649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155984428336215057147647099 233976642504322585721470649)
  ·
    refine ⟨175482481878241939291102987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233976642504322585721470649 175482481878241939291102987)
    ·
      refine ⟨263223722817362908936654481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175482481878241939291102987 263223722817362908936654481)
      ·
        refine ⟨197417792113022181702490861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263223722817362908936654481 197417792113022181702490861)
        ·
          refine ⟨74031672042383318138434073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197417792113022181702490861 74031672042383318138434073)
          ·
            refine ⟨55523754031787488603825555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74031672042383318138434073 55523754031787488603825555)
            ·
              refine ⟨83285631047681232905738333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55523754031787488603825555 83285631047681232905738333)
              ·
                refine ⟨31232111642880462339651875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83285631047681232905738333 31232111642880462339651875)
                ·
                  refine ⟨46848167464320693509477813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31232111642880462339651875 46848167464320693509477813)
                  ·
                    refine ⟨4392015699780065016513545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46848167464320693509477813 4392015699780065016513545)
                    ·
                      refine ⟨3294011774835048762385159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392015699780065016513545 3294011774835048762385159)
                      ·
                        rfl

theorem cell23_6415065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_6415065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415065 prefixEnd_6415065 := by exact prefixLift 6415065
  have htrace : WordTrace (prefixWord ++ tailWord_6415065) baseStart_6415065 baseEnd_6415065 := by
    simpa [prefixWord, tailWord_6415065, baseEnd_6415065] using wordTrace_append hprefix tailTrace_6415065
  have hstable : (prefixWord ++ tailWord_6415065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415065).length < 2 ^ (prefixWord ++ tailWord_6415065).sum := by decide
  have hdescent : baseEnd_6415065 < baseStart_6415065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415112 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_6415112 : Nat := 118140960795 + 6415112 * 2 ^ 59
def prefixEnd_6415112 : Nat := 4983230072969 + 3 ^ 40 * 6415112 * 2
def baseEnd_6415112 : Nat := 3294035908425810078497443

theorem tailTrace_6415112 : CollatzResearch.WordTrace tailWord_6415112 prefixEnd_6415112 3294035908425810078497443 := by
  unfold tailWord_6415112
  simp only [CollatzResearch.WordTrace]
  refine ⟨116989178367576156374215795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155985571156768208498954393 116989178367576156374215795)
  ·
    refine ⟨175483767551364234561323693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116989178367576156374215795 175483767551364234561323693)
    ·
      refine ⟨65806412831761587960496385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175483767551364234561323693 65806412831761587960496385)
      ·
        refine ⟨49354809623821190970372289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65806412831761587960496385 49354809623821190970372289)
        ·
          refine ⟨37016107217865893227779217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49354809623821190970372289 37016107217865893227779217)
          ·
            refine ⟨27762080413399419920834413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37016107217865893227779217 27762080413399419920834413)
            ·
              refine ⟨10410780155024782470312905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27762080413399419920834413 10410780155024782470312905)
              ·
                refine ⟨7808085116268586852734679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10410780155024782470312905 7808085116268586852734679)
                ·
                  refine ⟨11712127674402880279102019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808085116268586852734679 11712127674402880279102019)
                  ·
                    refine ⟨17568191511604320418653029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11712127674402880279102019 17568191511604320418653029)
                    ·
                      refine ⟨3294035908425810078497443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17568191511604320418653029 3294035908425810078497443)
                      ·
                        rfl

theorem cell23_6415112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_6415112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415112 prefixEnd_6415112 := by exact prefixLift 6415112
  have htrace : WordTrace (prefixWord ++ tailWord_6415112) baseStart_6415112 baseEnd_6415112 := by
    simpa [prefixWord, tailWord_6415112, baseEnd_6415112] using wordTrace_append hprefix tailTrace_6415112
  have hstable : (prefixWord ++ tailWord_6415112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415112).length < 2 ^ (prefixWord ++ tailWord_6415112).sum := by decide
  have hdescent : baseEnd_6415112 < baseStart_6415112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415125 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_6415125 : Nat := 118140960795 + 6415125 * 2 ^ 59
def prefixEnd_6415125 : Nat := 4983230072969 + 3 ^ 40 * 6415125 * 2
def baseEnd_6415125 : Nat := 3294042583674318527634883

theorem tailTrace_6415125 : CollatzResearch.WordTrace tailWord_6415125 prefixEnd_6415125 3294042583674318527634883 := by
  unfold tailWord_6415125
  simp only [CollatzResearch.WordTrace]
  refine ⟨233978830884105215968654829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155985887256070143979103219 233978830884105215968654829)
  ·
    refine ⟨87742061581539455988245561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233978830884105215968654829 87742061581539455988245561)
    ·
      refine ⟨65806546186154591991184171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87742061581539455988245561 65806546186154591991184171)
      ·
        refine ⟨98709819279231887986776257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65806546186154591991184171 98709819279231887986776257)
        ·
          refine ⟨74032364459423915990082193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98709819279231887986776257 74032364459423915990082193)
          ·
            refine ⟨55524273344567936992561645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74032364459423915990082193 55524273344567936992561645)
            ·
              refine ⟨20821602504212976372210617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55524273344567936992561645 20821602504212976372210617)
              ·
                refine ⟨15616201878159732279157963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20821602504212976372210617 15616201878159732279157963)
                ·
                  refine ⟨23424302817239598418736945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15616201878159732279157963 23424302817239598418736945)
                  ·
                    refine ⟨17568227112929698814052709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23424302817239598418736945 17568227112929698814052709)
                    ·
                      refine ⟨3294042583674318527634883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17568227112929698814052709 3294042583674318527634883)
                      ·
                        rfl

theorem cell23_6415125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_6415125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415125 prefixEnd_6415125 := by exact prefixLift 6415125
  have htrace : WordTrace (prefixWord ++ tailWord_6415125) baseStart_6415125 baseEnd_6415125 := by
    simpa [prefixWord, tailWord_6415125, baseEnd_6415125] using wordTrace_append hprefix tailTrace_6415125
  have hstable : (prefixWord ++ tailWord_6415125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415125).length < 2 ^ (prefixWord ++ tailWord_6415125).sum := by decide
  have hdescent : baseEnd_6415125 < baseStart_6415125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415132 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_6415132 : Nat := 118140960795 + 6415132 * 2 ^ 59
def prefixEnd_6415132 : Nat := 4983230072969 + 3 ^ 40 * 6415132 * 2
def baseEnd_6415132 : Nat := 3294046178038900000247351

theorem tailTrace_6415132 : CollatzResearch.WordTrace tailWord_6415132 prefixEnd_6415132 3294046178038900000247351 := by
  unfold tailWord_6415132
  simp only [CollatzResearch.WordTrace]
  refine ⟨116989543097539928082079825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155986057463386570776106433 116989543097539928082079825)
  ·
    refine ⟨87742157323154946061559869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116989543097539928082079825 87742157323154946061559869)
    ·
      refine ⟨32903308996183104773084951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87742157323154946061559869 32903308996183104773084951)
      ·
        refine ⟨49354963494274657159627427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32903308996183104773084951 49354963494274657159627427)
        ·
          refine ⟨74032445241411985739441141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49354963494274657159627427 74032445241411985739441141)
          ·
            refine ⟨6940541741382373663072607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74032445241411985739441141 6940541741382373663072607)
            ·
              refine ⟨10410812612073560494608911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6940541741382373663072607 10410812612073560494608911)
              ·
                refine ⟨15616218918110340741913367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10410812612073560494608911 15616218918110340741913367)
                ·
                  refine ⟨23424328377165511112870051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15616218918110340741913367 23424328377165511112870051)
                  ·
                    refine ⟨35136492565748266669305077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23424328377165511112870051 35136492565748266669305077)
                    ·
                      refine ⟨3294046178038900000247351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35136492565748266669305077 3294046178038900000247351)
                      ·
                        rfl

theorem cell23_6415132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_6415132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415132 prefixEnd_6415132 := by exact prefixLift 6415132
  have htrace : WordTrace (prefixWord ++ tailWord_6415132) baseStart_6415132 baseEnd_6415132 := by
    simpa [prefixWord, tailWord_6415132, baseEnd_6415132] using wordTrace_append hprefix tailTrace_6415132
  have hstable : (prefixWord ++ tailWord_6415132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415132).length < 2 ^ (prefixWord ++ tailWord_6415132).sum := by decide
  have hdescent : baseEnd_6415132 < baseStart_6415132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415140 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_6415140 : Nat := 118140960795 + 6415140 * 2 ^ 59
def prefixEnd_6415140 : Nat := 4983230072969 + 3 ^ 40 * 6415140 * 2
def baseEnd_6415140 : Nat := 3294050285884135968947315

theorem tailTrace_6415140 : CollatzResearch.WordTrace tailWord_6415140 prefixEnd_6415140 3294050285884135968947315 := by
  unfold tailWord_6415140
  simp only [CollatzResearch.WordTrace]
  refine ⟨116989688989525436765225437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155986251986033915686967249 116989688989525436765225437)
  ·
    refine ⟨43871133371072038786959539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116989688989525436765225437 43871133371072038786959539)
    ·
      refine ⟨65806700056608058180439309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43871133371072038786959539 65806700056608058180439309)
      ·
        refine ⟨24677512521228021817664741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65806700056608058180439309 24677512521228021817664741)
        ·
          refine ⟨4627033597730254090812139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24677512521228021817664741 4627033597730254090812139)
          ·
            refine ⟨6940550396595381136218209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627033597730254090812139 6940550396595381136218209)
            ·
              refine ⟨5205412797446535852163657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940550396595381136218209 5205412797446535852163657)
              ·
                refine ⟨3904059598084901889122743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205412797446535852163657 3904059598084901889122743)
                ·
                  refine ⟨5856089397127352833684115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904059598084901889122743 5856089397127352833684115)
                  ·
                    refine ⟨8784134095691029250526173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856089397127352833684115 8784134095691029250526173)
                    ·
                      refine ⟨3294050285884135968947315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784134095691029250526173 3294050285884135968947315)
                      ·
                        rfl

theorem cell23_6415140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_6415140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415140 prefixEnd_6415140 := by exact prefixLift 6415140
  have htrace : WordTrace (prefixWord ++ tailWord_6415140) baseStart_6415140 baseEnd_6415140 := by
    simpa [prefixWord, tailWord_6415140, baseEnd_6415140] using wordTrace_append hprefix tailTrace_6415140
  have hstable : (prefixWord ++ tailWord_6415140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415140).length < 2 ^ (prefixWord ++ tailWord_6415140).sum := by decide
  have hdescent : baseEnd_6415140 < baseStart_6415140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415148 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_6415148 : Nat := 118140960795 + 6415148 * 2 ^ 59
def prefixEnd_6415148 : Nat := 4983230072969 + 3 ^ 40 * 6415148 * 2
def baseEnd_6415148 : Nat := 1098018131243123979215759

theorem tailTrace_6415148 : CollatzResearch.WordTrace tailWord_6415148 prefixEnd_6415148 1098018131243123979215759 := by
  unfold tailWord_6415148
  simp only [CollatzResearch.WordTrace]
  refine ⟨116989834881510945448371049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155986446508681260597828065 116989834881510945448371049)
  ·
    refine ⟨87742376161133209086278287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116989834881510945448371049 87742376161133209086278287)
    ·
      refine ⟨131613564241699813629417431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87742376161133209086278287 131613564241699813629417431)
      ·
        refine ⟨197420346362549720444126147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131613564241699813629417431 197420346362549720444126147)
        ·
          refine ⟨296130519543824580666189221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197420346362549720444126147 296130519543824580666189221)
          ·
            refine ⟨55524472414467108874910479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296130519543824580666189221 55524472414467108874910479)
            ·
              refine ⟨83286708621700663312365719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55524472414467108874910479 83286708621700663312365719)
              ·
                refine ⟨124930062932550994968548579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83286708621700663312365719 124930062932550994968548579)
                ·
                  refine ⟨187395094398826492452822869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124930062932550994968548579 187395094398826492452822869)
                  ·
                    refine ⟨1098018131243123979215759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187395094398826492452822869 1098018131243123979215759)
                    ·
                      rfl

theorem cell23_6415148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_6415148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415148 prefixEnd_6415148 := by exact prefixLift 6415148
  have htrace : WordTrace (prefixWord ++ tailWord_6415148) baseStart_6415148 baseEnd_6415148 := by
    simpa [prefixWord, tailWord_6415148, baseEnd_6415148] using wordTrace_append hprefix tailTrace_6415148
  have hstable : (prefixWord ++ tailWord_6415148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415148).length < 2 ^ (prefixWord ++ tailWord_6415148).sum := by decide
  have hdescent : baseEnd_6415148 < baseStart_6415148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415169 : List Nat := [1, 2, 5, 3, 1, 1, 3, 7]
def baseStart_6415169 : Nat := 118140960795 + 6415169 * 2 ^ 59
def prefixEnd_6415169 : Nat := 4983230072969 + 3 ^ 40 * 6415169 * 2
def baseEnd_6415169 : Nat := 122002413956411716869803

theorem tailTrace_6415169 : CollatzResearch.WordTrace tailWord_6415169 prefixEnd_6415169 122002413956411716869803 := by
  unfold tailWord_6415169
  simp only [CollatzResearch.WordTrace]
  refine ⟨233980435695945811483256561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155986957130630540988837707 233980435695945811483256561)
  ·
    refine ⟨175485326771959358612442421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233980435695945811483256561 175485326771959358612442421)
    ·
      refine ⟨16451749384871189869916477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175485326771959358612442421 16451749384871189869916477)
      ·
        refine ⟨6169406019326696201218679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16451749384871189869916477 6169406019326696201218679)
        ·
          refine ⟨9254109028990044301828019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169406019326696201218679 9254109028990044301828019)
          ·
            refine ⟨13881163543485066452742029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254109028990044301828019 13881163543485066452742029)
            ·
              refine ⟨5205436328806899919778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13881163543485066452742029 5205436328806899919778261)
              ·
                refine ⟨122002413956411716869803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5205436328806899919778261 122002413956411716869803)
                ·
                  rfl

theorem cell23_6415169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 7].length) (baseStart_6415169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415169 prefixEnd_6415169 := by exact prefixLift 6415169
  have htrace : WordTrace (prefixWord ++ tailWord_6415169) baseStart_6415169 baseEnd_6415169 := by
    simpa [prefixWord, tailWord_6415169, baseEnd_6415169] using wordTrace_append hprefix tailTrace_6415169
  have hstable : (prefixWord ++ tailWord_6415169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415169).length < 2 ^ (prefixWord ++ tailWord_6415169).sum := by decide
  have hdescent : baseEnd_6415169 < baseStart_6415169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415189 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6415189 : Nat := 118140960795 + 6415189 * 2 ^ 59
def prefixEnd_6415189 : Nat := 4983230072969 + 3 ^ 40 * 6415189 * 2
def baseEnd_6415189 : Nat := 3294075446436206277234589

theorem tailTrace_6415189 : CollatzResearch.WordTrace tailWord_6415189 prefixEnd_6415189 3294075446436206277234589 := by
  unfold tailWord_6415189
  simp only [CollatzResearch.WordTrace]
  refine ⟨233981165155873354898984621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155987443437248903265989747 233981165155873354898984621)
  ·
    refine ⟨87742936933452508087119233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233981165155873354898984621 87742936933452508087119233)
    ·
      refine ⟨65807202700089381065339425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87742936933452508087119233 65807202700089381065339425)
      ·
        refine ⟨49355402025067035799004569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65807202700089381065339425 49355402025067035799004569)
        ·
          refine ⟨37016551518800276849253427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49355402025067035799004569 37016551518800276849253427)
          ·
            refine ⟨55524827278200415273880141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37016551518800276849253427 55524827278200415273880141)
            ·
              refine ⟨20821810229325155727705053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55524827278200415273880141 20821810229325155727705053)
              ·
                refine ⟨7808178835996933397889395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20821810229325155727705053 7808178835996933397889395)
                ·
                  refine ⟨11712268253995400096834093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808178835996933397889395 11712268253995400096834093)
                  ·
                    refine ⟨4392100595248275036312785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11712268253995400096834093 4392100595248275036312785)
                    ·
                      refine ⟨3294075446436206277234589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392100595248275036312785 3294075446436206277234589)
                      ·
                        rfl

theorem cell23_6415189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6415189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415189 prefixEnd_6415189 := by exact prefixLift 6415189
  have htrace : WordTrace (prefixWord ++ tailWord_6415189) baseStart_6415189 baseEnd_6415189 := by
    simpa [prefixWord, tailWord_6415189, baseEnd_6415189] using wordTrace_append hprefix tailTrace_6415189
  have hstable : (prefixWord ++ tailWord_6415189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415189).length < 2 ^ (prefixWord ++ tailWord_6415189).sum := by decide
  have hdescent : baseEnd_6415189 < baseStart_6415189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415196 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6415196 : Nat := 118140960795 + 6415196 * 2 ^ 59
def prefixEnd_6415196 : Nat := 4983230072969 + 3 ^ 40 * 6415196 * 2
def baseEnd_6415196 : Nat := 3294079040800787749847057

theorem tailTrace_6415196 : CollatzResearch.WordTrace tailWord_6415196 prefixEnd_6415196 3294079040800787749847057 := by
  unfold tailWord_6415196
  simp only [CollatzResearch.WordTrace]
  refine ⟨116990710233423997547244721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155987613644565330062992961 116990710233423997547244721)
  ·
    refine ⟨87743032675067998160433541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116990710233423997547244721 87743032675067998160433541)
    ·
      refine ⟨16451818626575249655081289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87743032675067998160433541 16451818626575249655081289)
      ·
        refine ⟨12338863969931437241310967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16451818626575249655081289 12338863969931437241310967)
        ·
          refine ⟨18508295954897155861966451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12338863969931437241310967 18508295954897155861966451)
          ·
            refine ⟨27762443932345733792949677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18508295954897155861966451 27762443932345733792949677)
            ·
              refine ⟨10410916474629650172356129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27762443932345733792949677 10410916474629650172356129)
              ·
                refine ⟨7808187355972237629267097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10410916474629650172356129 7808187355972237629267097)
                ·
                  refine ⟨5856140516979178221950323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7808187355972237629267097 5856140516979178221950323)
                  ·
                    refine ⟨8784210775468767332925485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856140516979178221950323 8784210775468767332925485)
                    ·
                      refine ⟨3294079040800787749847057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784210775468767332925485 3294079040800787749847057)
                      ·
                        rfl

theorem cell23_6415196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6415196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415196 prefixEnd_6415196 := by exact prefixLift 6415196
  have htrace : WordTrace (prefixWord ++ tailWord_6415196) baseStart_6415196 baseEnd_6415196 := by
    simpa [prefixWord, tailWord_6415196, baseEnd_6415196] using wordTrace_append hprefix tailTrace_6415196
  have hstable : (prefixWord ++ tailWord_6415196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415196).length < 2 ^ (prefixWord ++ tailWord_6415196).sum := by decide
  have hdescent : baseEnd_6415196 < baseStart_6415196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415205 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_6415205 : Nat := 118140960795 + 6415205 * 2 ^ 59
def prefixEnd_6415205 : Nat := 4983230072969 + 3 ^ 40 * 6415205 * 2
def baseEnd_6415205 : Nat := 3294083662126678214634515

theorem tailTrace_6415205 : CollatzResearch.WordTrace tailWord_6415205 prefixEnd_6415205 3294083662126678214634515 := by
  unfold tailWord_6415205
  simp only [CollatzResearch.WordTrace]
  refine ⟨233981748723815389631567069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155987832482543593087711379 233981748723815389631567069)
  ·
    refine ⟨87743155771430771111837651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233981748723815389631567069 87743155771430771111837651)
    ·
      refine ⟨131614733657146156667756477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87743155771430771111837651 131614733657146156667756477)
      ·
        refine ⟨49355525121429808750408679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131614733657146156667756477 49355525121429808750408679)
        ·
          refine ⟨74033287682144713125613019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49355525121429808750408679 74033287682144713125613019)
          ·
            refine ⟨111049931523217069688419529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74033287682144713125613019 111049931523217069688419529)
            ·
              refine ⟨83287448642412802266314647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111049931523217069688419529 83287448642412802266314647)
              ·
                refine ⟨124931172963619203399471971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83287448642412802266314647 124931172963619203399471971)
                ·
                  refine ⟨187396759445428805099207957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124931172963619203399471971 187396759445428805099207957)
                  ·
                    refine ⟨8784223099004475239025373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 187396759445428805099207957 8784223099004475239025373)
                    ·
                      refine ⟨3294083662126678214634515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784223099004475239025373 3294083662126678214634515)
                      ·
                        rfl

theorem cell23_6415205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_6415205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415205 prefixEnd_6415205 := by exact prefixLift 6415205
  have htrace : WordTrace (prefixWord ++ tailWord_6415205) baseStart_6415205 baseEnd_6415205 := by
    simpa [prefixWord, tailWord_6415205, baseEnd_6415205] using wordTrace_append hprefix tailTrace_6415205
  have hstable : (prefixWord ++ tailWord_6415205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415205).length < 2 ^ (prefixWord ++ tailWord_6415205).sum := by decide
  have hdescent : baseEnd_6415205 < baseStart_6415205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415219 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 2, 2, 2]
def baseStart_6415219 : Nat := 118140960795 + 6415219 * 2 ^ 59
def prefixEnd_6415219 : Nat := 4983230072969 + 3 ^ 40 * 6415219 * 2
def baseEnd_6415219 : Nat := 3294090850855841159859451

theorem tailTrace_6415219 : CollatzResearch.WordTrace tailWord_6415219 prefixEnd_6415219 3294090850855841159859451 := by
  unfold tailWord_6415219
  simp only [CollatzResearch.WordTrace]
  refine ⟨233982259345764670022576711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155988172897176446681717807 233982259345764670022576711)
  ·
    refine ⟨350973389018647005033865067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233982259345764670022576711 350973389018647005033865067)
    ·
      refine ⟨526460083527970507550797601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350973389018647005033865067 526460083527970507550797601)
      ·
        refine ⟨394845062645977880663098201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526460083527970507550797601 394845062645977880663098201)
        ·
          refine ⟨296133796984483410497323651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394845062645977880663098201 296133796984483410497323651)
          ·
            refine ⟨444200695476725115745985477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296133796984483410497323651 444200695476725115745985477)
            ·
              refine ⟨83287630401885959202372277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 444200695476725115745985477 83287630401885959202372277)
              ·
                refine ⟨7808215350176808675222401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83287630401885959202372277 7808215350176808675222401)
                ·
                  refine ⟨5856161512632606506416801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7808215350176808675222401 5856161512632606506416801)
                  ·
                    refine ⟨4392121134474454879812601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5856161512632606506416801 4392121134474454879812601)
                    ·
                      refine ⟨3294090850855841159859451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392121134474454879812601 3294090850855841159859451)
                      ·
                        rfl

theorem cell23_6415219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 2, 2].length) (baseStart_6415219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415219 prefixEnd_6415219 := by exact prefixLift 6415219
  have htrace : WordTrace (prefixWord ++ tailWord_6415219) baseStart_6415219 baseEnd_6415219 := by
    simpa [prefixWord, tailWord_6415219, baseEnd_6415219] using wordTrace_append hprefix tailTrace_6415219
  have hstable : (prefixWord ++ tailWord_6415219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415219).length < 2 ^ (prefixWord ++ tailWord_6415219).sum := by decide
  have hdescent : baseEnd_6415219 < baseStart_6415219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415225 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 7]
def baseStart_6415225 : Nat := 118140960795 + 6415225 * 2 ^ 59
def prefixEnd_6415225 : Nat := 4983230072969 + 3 ^ 40 * 6415225 * 2
def baseEnd_6415225 : Nat := 366010436859974237376047

theorem tailTrace_6415225 : CollatzResearch.WordTrace tailWord_6415225 prefixEnd_6415225 366010436859974237376047 := by
  unfold tailWord_6415225
  simp only [CollatzResearch.WordTrace]
  refine ⟨233982478183742933047295129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155988318789161955364863419 233982478183742933047295129)
  ·
    refine ⟨175486858637807199785471347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233982478183742933047295129 175486858637807199785471347)
    ·
      refine ⟨263230287956710799678207021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175486858637807199785471347 263230287956710799678207021)
      ·
        refine ⟨98711357983766549879327633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263230287956710799678207021 98711357983766549879327633)
        ·
          refine ⟨74033518487824912409495725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98711357983766549879327633 74033518487824912409495725)
          ·
            refine ⟨27762569432934342153560897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74033518487824912409495725 27762569432934342153560897)
            ·
              refine ⟨20821927074700756615170673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27762569432934342153560897 20821927074700756615170673)
              ·
                refine ⟨15616445306025567461378005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20821927074700756615170673 15616445306025567461378005)
                ·
                  refine ⟨366010436859974237376047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15616445306025567461378005 366010436859974237376047)
                  ·
                    rfl

theorem cell23_6415225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_6415225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415225 prefixEnd_6415225 := by exact prefixLift 6415225
  have htrace : WordTrace (prefixWord ++ tailWord_6415225) baseStart_6415225 baseEnd_6415225 := by
    simpa [prefixWord, tailWord_6415225, baseEnd_6415225] using wordTrace_append hprefix tailTrace_6415225
  have hstable : (prefixWord ++ tailWord_6415225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415225).length < 2 ^ (prefixWord ++ tailWord_6415225).sum := by decide
  have hdescent : baseEnd_6415225 < baseStart_6415225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415346 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6415346 : Nat := 118140960795 + 6415346 * 2 ^ 59
def prefixEnd_6415346 : Nat := 4983230072969 + 3 ^ 40 * 6415346 * 2
def baseEnd_6415346 : Nat := 3294156062898962162971367

theorem tailTrace_6415346 : CollatzResearch.WordTrace tailWord_6415346 prefixEnd_6415346 3294156062898962162971367 := by
  unfold tailWord_6415346
  simp only [CollatzResearch.WordTrace]
  refine ⟨58496722854076142678112473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155991260944203047141633261 58496722854076142678112473)
  ·
    refine ⟨43872542140557107008584355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58496722854076142678112473 43872542140557107008584355)
    ·
      refine ⟨65808813210835660512876533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43872542140557107008584355 65808813210835660512876533)
      ·
        refine ⟨6169576238515843173082175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65808813210835660512876533 6169576238515843173082175)
        ·
          refine ⟨9254364357773764759623263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169576238515843173082175 9254364357773764759623263)
          ·
            refine ⟨13881546536660647139434895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254364357773764759623263 13881546536660647139434895)
            ·
              refine ⟨20822319804990970709152343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13881546536660647139434895 20822319804990970709152343)
              ·
                refine ⟨31233479707486456063728515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20822319804990970709152343 31233479707486456063728515)
                ·
                  refine ⟨46850219561229684095592773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31233479707486456063728515 46850219561229684095592773)
                  ·
                    refine ⟨8784416167730565767923645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46850219561229684095592773 8784416167730565767923645)
                    ·
                      refine ⟨3294156062898962162971367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784416167730565767923645 3294156062898962162971367)
                      ·
                        rfl

theorem cell23_6415346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6415346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415346 prefixEnd_6415346 := by exact prefixLift 6415346
  have htrace : WordTrace (prefixWord ++ tailWord_6415346) baseStart_6415346 baseEnd_6415346 := by
    simpa [prefixWord, tailWord_6415346, baseEnd_6415346] using wordTrace_append hprefix tailTrace_6415346
  have hstable : (prefixWord ++ tailWord_6415346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415346).length < 2 ^ (prefixWord ++ tailWord_6415346).sum := by decide
  have hdescent : baseEnd_6415346 < baseStart_6415346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415355 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_6415355 : Nat := 118140960795 + 6415355 * 2 ^ 59
def prefixEnd_6415355 : Nat := 4983230072969 + 3 ^ 40 * 6415355 * 2
def baseEnd_6415355 : Nat := 3294160684224852627758825

theorem tailTrace_6415355 : CollatzResearch.WordTrace tailWord_6415355 prefixEnd_6415355 3294160684224852627758825 := by
  unfold tailWord_6415355
  simp only [CollatzResearch.WordTrace]
  refine ⟨233987219673271965249527519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155991479782181310166351679 233987219673271965249527519)
  ·
    refine ⟨350980829509907947874291279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233987219673271965249527519 350980829509907947874291279)
    ·
      refine ⟨526471244264861921811436919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350980829509907947874291279 526471244264861921811436919)
      ·
        refine ⟨789706866397292882717155379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526471244264861921811436919 789706866397292882717155379)
        ·
          refine ⟨1184560299595939324075733069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789706866397292882717155379 1184560299595939324075733069)
          ·
            refine ⟨444210112348477246528399901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184560299595939324075733069 444210112348477246528399901)
            ·
              refine ⟨166578792130678967448149963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444210112348477246528399901 166578792130678967448149963)
              ·
                refine ⟨249868188196018451172224945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166578792130678967448149963 249868188196018451172224945)
                ·
                  refine ⟨187401141147013838379168709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249868188196018451172224945 187401141147013838379168709)
                  ·
                    refine ⟨35137713965065094696094133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187401141147013838379168709 35137713965065094696094133)
                    ·
                      refine ⟨3294160684224852627758825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35137713965065094696094133 3294160684224852627758825)
                      ·
                        rfl

theorem cell23_6415355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_6415355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415355 prefixEnd_6415355 := by exact prefixLift 6415355
  have htrace : WordTrace (prefixWord ++ tailWord_6415355) baseStart_6415355 baseEnd_6415355 := by
    simpa [prefixWord, tailWord_6415355, baseEnd_6415355] using wordTrace_append hprefix tailTrace_6415355
  have hstable : (prefixWord ++ tailWord_6415355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415355).length < 2 ^ (prefixWord ++ tailWord_6415355).sum := by decide
  have hdescent : baseEnd_6415355 < baseStart_6415355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415369 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 2, 3, 2]
def baseStart_6415369 : Nat := 118140960795 + 6415369 * 2 ^ 59
def prefixEnd_6415369 : Nat := 4983230072969 + 3 ^ 40 * 6415369 * 2
def baseEnd_6415369 : Nat := 3294167872954015572983761

theorem tailTrace_6415369 : CollatzResearch.WordTrace tailWord_6415369 prefixEnd_6415369 3294167872954015572983761 := by
  unfold tailWord_6415369
  simp only [CollatzResearch.WordTrace]
  refine ⟨233987730295221245640537161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155991820196814163760358107 233987730295221245640537161)
  ·
    refine ⟨175490797721415934230402871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233987730295221245640537161 175490797721415934230402871)
    ·
      refine ⟨263236196582123901345604307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175490797721415934230402871 263236196582123901345604307)
      ·
        refine ⟨394854294873185852018406461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263236196582123901345604307 394854294873185852018406461)
        ·
          refine ⟨148070360577444694506902423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394854294873185852018406461 148070360577444694506902423)
          ·
            refine ⟨222105540866167041760353635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148070360577444694506902423 222105540866167041760353635)
            ·
              refine ⟨333158311299250562640530453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222105540866167041760353635 333158311299250562640530453)
              ·
                refine ⟨15616795842152370123774865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333158311299250562640530453 15616795842152370123774865)
                ·
                  refine ⟨11712596881614277592831149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15616795842152370123774865 11712596881614277592831149)
                  ·
                    refine ⟨4392223830605354097311681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11712596881614277592831149 4392223830605354097311681)
                    ·
                      refine ⟨3294167872954015572983761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392223830605354097311681 3294167872954015572983761)
                      ·
                        rfl

theorem cell23_6415369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 3, 2].length) (baseStart_6415369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415369 prefixEnd_6415369 := by exact prefixLift 6415369
  have htrace : WordTrace (prefixWord ++ tailWord_6415369) baseStart_6415369 baseEnd_6415369 := by
    simpa [prefixWord, tailWord_6415369, baseEnd_6415369] using wordTrace_append hprefix tailTrace_6415369
  have hstable : (prefixWord ++ tailWord_6415369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415369).length < 2 ^ (prefixWord ++ tailWord_6415369).sum := by decide
  have hdescent : baseEnd_6415369 < baseStart_6415369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415396 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_6415396 : Nat := 118140960795 + 6415396 * 2 ^ 59
def prefixEnd_6415396 : Nat := 4983230072969 + 3 ^ 40 * 6415396 * 2
def baseEnd_6415396 : Nat := 1098060578977228989115379

theorem tailTrace_6415396 : CollatzResearch.WordTrace tailWord_6415396 prefixEnd_6415396 1098060578977228989115379 := by
  unfold tailWord_6415396
  simp only [CollatzResearch.WordTrace]
  refine ⟨116994357533061714625885021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155992476710748952834513361 116994357533061714625885021)
  ·
    refine ⟨43872884074898142984706883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116994357533061714625885021 43872884074898142984706883)
    ·
      refine ⟨65809326112347214477060325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43872884074898142984706883 65809326112347214477060325)
      ·
        refine ⟨12339248646065102714448811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65809326112347214477060325 12339248646065102714448811)
        ·
          refine ⟨18508872969097654071673217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339248646065102714448811 18508872969097654071673217)
          ·
            refine ⟨13881654726823240553754913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18508872969097654071673217 13881654726823240553754913)
            ·
              refine ⟨10411241045117430415316185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13881654726823240553754913 10411241045117430415316185)
              ·
                refine ⟨7808430783838072811487139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10411241045117430415316185 7808430783838072811487139)
                ·
                  refine ⟨11712646175757109217230709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808430783838072811487139 11712646175757109217230709)
                  ·
                    refine ⟨1098060578977228989115379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11712646175757109217230709 1098060578977228989115379)
                    ·
                      rfl

theorem cell23_6415396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_6415396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415396 prefixEnd_6415396 := by exact prefixLift 6415396
  have htrace : WordTrace (prefixWord ++ tailWord_6415396) baseStart_6415396 baseEnd_6415396 := by
    simpa [prefixWord, tailWord_6415396, baseEnd_6415396] using wordTrace_append hprefix tailTrace_6415396
  have hstable : (prefixWord ++ tailWord_6415396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415396).length < 2 ^ (prefixWord ++ tailWord_6415396).sum := by decide
  have hdescent : baseEnd_6415396 < baseStart_6415396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415449 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 3]
def baseStart_6415449 : Nat := 118140960795 + 6415449 * 2 ^ 59
def prefixEnd_6415449 : Nat := 4983230072969 + 3 ^ 40 * 6415449 * 2
def baseEnd_6415449 : Nat := 3294208951406375259983393

theorem tailTrace_6415449 : CollatzResearch.WordTrace tailWord_6415449 prefixEnd_6415449 3294208951406375259983393 := by
  unfold tailWord_6415449
  simp only [CollatzResearch.WordTrace]
  refine ⟨233990648134931419303449401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155993765423287612868966267 233990648134931419303449401)
  ·
    refine ⟨175492986101198564477587051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233990648134931419303449401 175492986101198564477587051)
    ·
      refine ⟨263239479151797846716380577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175492986101198564477587051 263239479151797846716380577)
      ·
        refine ⟨197429609363848385037285433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263239479151797846716380577 197429609363848385037285433)
        ·
          refine ⟨148072207022886288777964075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197429609363848385037285433 148072207022886288777964075)
          ·
            refine ⟨222108310534329433166946113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148072207022886288777964075 222108310534329433166946113)
            ·
              refine ⟨166581232900747074875209585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222108310534329433166946113 166581232900747074875209585)
              ·
                refine ⟨124935924675560306156407189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166581232900747074875209585 124935924675560306156407189)
                ·
                  refine ⟨5856371469166889351081587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124935924675560306156407189 5856371469166889351081587)
                  ·
                    refine ⟨8784557203750334026622381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856371469166889351081587 8784557203750334026622381)
                    ·
                      refine ⟨3294208951406375259983393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784557203750334026622381 3294208951406375259983393)
                      ·
                        rfl

theorem cell23_6415449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_6415449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415449 prefixEnd_6415449 := by exact prefixLift 6415449
  have htrace : WordTrace (prefixWord ++ tailWord_6415449) baseStart_6415449 baseEnd_6415449 := by
    simpa [prefixWord, tailWord_6415449, baseEnd_6415449] using wordTrace_append hprefix tailTrace_6415449
  have hstable : (prefixWord ++ tailWord_6415449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415449).length < 2 ^ (prefixWord ++ tailWord_6415449).sum := by decide
  have hdescent : baseEnd_6415449 < baseStart_6415449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415453 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6415453 : Nat := 118140960795 + 6415453 * 2 ^ 59
def prefixEnd_6415453 : Nat := 4983230072969 + 3 ^ 40 * 6415453 * 2
def baseEnd_6415453 : Nat := 3294211005328993244333375

theorem tailTrace_6415453 : CollatzResearch.WordTrace tailWord_6415453 prefixEnd_6415453 3294211005328993244333375 := by
  unfold tailWord_6415453
  simp only [CollatzResearch.WordTrace]
  refine ⟨233990794026916927986595013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155993862684611285324396675 233990794026916927986595013)
  ·
    refine ⟨43873273880046923997486565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233990794026916927986595013 43873273880046923997486565)
    ·
      refine ⟨8226238852508798249528731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43873273880046923997486565 8226238852508798249528731)
      ·
        refine ⟨12339358278763197374293097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8226238852508798249528731 12339358278763197374293097)
        ·
          refine ⟨9254518709072398030719823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12339358278763197374293097 9254518709072398030719823)
          ·
            refine ⟨13881778063608597046079735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254518709072398030719823 13881778063608597046079735)
            ·
              refine ⟨20822667095412895569119603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13881778063608597046079735 20822667095412895569119603)
              ·
                refine ⟨31234000643119343353679405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20822667095412895569119603 31234000643119343353679405)
                ·
                  refine ⟨11712750241169753757629777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31234000643119343353679405 11712750241169753757629777)
                  ·
                    refine ⟨8784562680877315318222333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11712750241169753757629777 8784562680877315318222333)
                    ·
                      refine ⟨3294211005328993244333375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784562680877315318222333 3294211005328993244333375)
                      ·
                        rfl

theorem cell23_6415453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6415453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415453 prefixEnd_6415453 := by exact prefixLift 6415453
  have htrace : WordTrace (prefixWord ++ tailWord_6415453) baseStart_6415453 baseEnd_6415453 := by
    simpa [prefixWord, tailWord_6415453, baseEnd_6415453] using wordTrace_append hprefix tailTrace_6415453
  have hstable : (prefixWord ++ tailWord_6415453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415453).length < 2 ^ (prefixWord ++ tailWord_6415453).sum := by decide
  have hdescent : baseEnd_6415453 < baseStart_6415453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415466 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_6415466 : Nat := 118140960795 + 6415466 * 2 ^ 59
def prefixEnd_6415466 : Nat := 4983230072969 + 3 ^ 40 * 6415466 * 2
def baseEnd_6415466 : Nat := 3294217680577501693470815

theorem tailTrace_6415466 : CollatzResearch.WordTrace tailWord_6415466 prefixEnd_6415466 3294217680577501693470815 := by
  unfold tailWord_6415466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58497817043967457801704563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155994178783913220804545501 58497817043967457801704563)
  ·
    refine ⟨87746725565951186702556845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58497817043967457801704563 87746725565951186702556845)
    ·
      refine ⟨32905022087231695013458817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87746725565951186702556845 32905022087231695013458817)
      ·
        refine ⟨24678766565423771260094113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32905022087231695013458817 24678766565423771260094113)
        ·
          refine ⟨18509074924067828445070585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24678766565423771260094113 18509074924067828445070585)
          ·
            refine ⟨13881806193050871333802939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18509074924067828445070585 13881806193050871333802939)
            ·
              refine ⟨20822709289576307000704409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13881806193050871333802939 20822709289576307000704409)
              ·
                refine ⟨15617031967182230250528307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20822709289576307000704409 15617031967182230250528307)
                ·
                  refine ⟨23425547950773345375792461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15617031967182230250528307 23425547950773345375792461)
                  ·
                    refine ⟨8784580481540004515922173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23425547950773345375792461 8784580481540004515922173)
                    ·
                      refine ⟨3294217680577501693470815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784580481540004515922173 3294217680577501693470815)
                      ·
                        rfl

theorem cell23_6415466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_6415466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415466 prefixEnd_6415466 := by exact prefixLift 6415466
  have htrace : WordTrace (prefixWord ++ tailWord_6415466) baseStart_6415466 baseEnd_6415466 := by
    simpa [prefixWord, tailWord_6415466, baseEnd_6415466] using wordTrace_append hprefix tailTrace_6415466
  have hstable : (prefixWord ++ tailWord_6415466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415466).length < 2 ^ (prefixWord ++ tailWord_6415466).sum := by decide
  have hdescent : baseEnd_6415466 < baseStart_6415466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415489 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6415489 : Nat := 118140960795 + 6415489 * 2 ^ 59
def prefixEnd_6415489 : Nat := 4983230072969 + 3 ^ 40 * 6415489 * 2
def baseEnd_6415489 : Nat := 3294229490632555103483209

theorem tailTrace_6415489 : CollatzResearch.WordTrace tailWord_6415489 prefixEnd_6415489 3294229490632555103483209 := by
  unfold tailWord_6415489
  simp only [CollatzResearch.WordTrace]
  refine ⟨233992107054786506134905521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155994738036524337423270347 233992107054786506134905521)
  ·
    refine ⟨175494080291089879601179141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233992107054786506134905521 175494080291089879601179141)
    ·
      refine ⟨32905140054579352425221089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175494080291089879601179141 32905140054579352425221089)
      ·
        refine ⟨24678855040934514318915817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32905140054579352425221089 24678855040934514318915817)
        ·
          refine ⟨18509141280700885739186863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24678855040934514318915817 18509141280700885739186863)
          ·
            refine ⟨27763711921051328608780295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509141280700885739186863 27763711921051328608780295)
            ·
              refine ⟨41645567881576992913170443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27763711921051328608780295 41645567881576992913170443)
              ·
                refine ⟨62468351822365489369755665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41645567881576992913170443 62468351822365489369755665)
                ·
                  refine ⟨46851263866774117027316749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62468351822365489369755665 46851263866774117027316749)
                  ·
                    refine ⟨17569223950040293885243781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46851263866774117027316749 17569223950040293885243781)
                    ·
                      refine ⟨3294229490632555103483209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17569223950040293885243781 3294229490632555103483209)
                      ·
                        rfl

theorem cell23_6415489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6415489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415489 prefixEnd_6415489 := by exact prefixLift 6415489
  have htrace : WordTrace (prefixWord ++ tailWord_6415489) baseStart_6415489 baseEnd_6415489 := by
    simpa [prefixWord, tailWord_6415489, baseEnd_6415489] using wordTrace_append hprefix tailTrace_6415489
  have hstable : (prefixWord ++ tailWord_6415489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415489).length < 2 ^ (prefixWord ++ tailWord_6415489).sum := by decide
  have hdescent : baseEnd_6415489 < baseStart_6415489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415527 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6415527 : Nat := 118140960795 + 6415527 * 2 ^ 59
def prefixEnd_6415527 : Nat := 4983230072969 + 3 ^ 40 * 6415527 * 2
def baseEnd_6415527 : Nat := 3294249002897425954808035

theorem tailTrace_6415527 : CollatzResearch.WordTrace tailWord_6415527 prefixEnd_6415527 3294249002897425954808035 := by
  unfold tailWord_6415527
  simp only [CollatzResearch.WordTrace]
  refine ⟨233993493028648838624788835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155995662019099225749859223 233993493028648838624788835)
  ·
    refine ⟨350990239542973257937183253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233993493028648838624788835 350990239542973257937183253)
    ·
      refine ⟨16452667478576871465805465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 350990239542973257937183253 16452667478576871465805465)
      ·
        refine ⟨12339500608932653599354099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16452667478576871465805465 12339500608932653599354099)
        ·
          refine ⟨18509250913398980399031149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339500608932653599354099 18509250913398980399031149)
          ·
            refine ⟨6940969092524617649636681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18509250913398980399031149 6940969092524617649636681)
            ·
              refine ⟨5205726819393463237227511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940969092524617649636681 5205726819393463237227511)
              ·
                refine ⟨7808590229090194855841267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205726819393463237227511 7808590229090194855841267)
                ·
                  refine ⟨11712885343635292283761901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808590229090194855841267 11712885343635292283761901)
                  ·
                    refine ⟨4392332003863234606410713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11712885343635292283761901 4392332003863234606410713)
                    ·
                      refine ⟨3294249002897425954808035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392332003863234606410713 3294249002897425954808035)
                      ·
                        rfl

theorem cell23_6415527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6415527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415527 prefixEnd_6415527 := by exact prefixLift 6415527
  have htrace : WordTrace (prefixWord ++ tailWord_6415527) baseStart_6415527 baseEnd_6415527 := by
    simpa [prefixWord, tailWord_6415527, baseEnd_6415527] using wordTrace_append hprefix tailTrace_6415527
  have hstable : (prefixWord ++ tailWord_6415527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415527).length < 2 ^ (prefixWord ++ tailWord_6415527).sum := by decide
  have hdescent : baseEnd_6415527 < baseStart_6415527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415539 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3]
def baseStart_6415539 : Nat := 118140960795 + 6415539 * 2 ^ 59
def prefixEnd_6415539 : Nat := 4983230072969 + 3 ^ 40 * 6415539 * 2
def baseEnd_6415539 : Nat := 3294255164665279907857979

theorem tailTrace_6415539 : CollatzResearch.WordTrace tailWord_6415539 prefixEnd_6415539 3294255164665279907857979 := by
  unfold tailWord_6415539
  simp only [CollatzResearch.WordTrace]
  refine ⟨233993930704605364674225671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155995953803070243116150447 233993930704605364674225671)
  ·
    refine ⟨350990896056908047011338507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233993930704605364674225671 350990896056908047011338507)
    ·
      refine ⟨526486344085362070517007761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350990896056908047011338507 526486344085362070517007761)
      ·
        refine ⟨394864758064021552887755821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526486344085362070517007761 394864758064021552887755821)
        ·
          refine ⟨148074284274008082332908433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394864758064021552887755821 148074284274008082332908433)
          ·
            refine ⟨111055713205506061749681325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148074284274008082332908433 111055713205506061749681325)
            ·
              refine ⟨41645892452064773156130497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111055713205506061749681325 41645892452064773156130497)
              ·
                refine ⟨31234419339048579867097873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41645892452064773156130497 31234419339048579867097873)
                ·
                  refine ⟨23425814504286434900323405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31234419339048579867097873 23425814504286434900323405)
                  ·
                    refine ⟨8784680439107413087621277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23425814504286434900323405 8784680439107413087621277)
                    ·
                      refine ⟨3294255164665279907857979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784680439107413087621277 3294255164665279907857979)
                      ·
                        rfl

theorem cell23_6415539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_6415539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415539 prefixEnd_6415539 := by exact prefixLift 6415539
  have htrace : WordTrace (prefixWord ++ tailWord_6415539) baseStart_6415539 baseEnd_6415539 := by
    simpa [prefixWord, tailWord_6415539, baseEnd_6415539] using wordTrace_append hprefix tailTrace_6415539
  have hstable : (prefixWord ++ tailWord_6415539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415539).length < 2 ^ (prefixWord ++ tailWord_6415539).sum := by decide
  have hdescent : baseEnd_6415539 < baseStart_6415539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415596 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_6415596 : Nat := 118140960795 + 6415596 * 2 ^ 59
def prefixEnd_6415596 : Nat := 4983230072969 + 3 ^ 40 * 6415596 * 2
def baseEnd_6415596 : Nat := 3294284433062586184845217

theorem tailTrace_6415596 : CollatzResearch.WordTrace tailWord_6415596 prefixEnd_6415596 3294284433062586184845217 := by
  unfold tailWord_6415596
  simp only [CollatzResearch.WordTrace]
  refine ⟨116998004832699431704525321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155997339776932575606033761 116998004832699431704525321)
  ·
    refine ⟨87748503624524573778393991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116998004832699431704525321 87748503624524573778393991)
    ·
      refine ⟨131622755436786860667590987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87748503624524573778393991 131622755436786860667590987)
      ·
        refine ⟨197434133155180291001386481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131622755436786860667590987 197434133155180291001386481)
        ·
          refine ⟨148075599866385218251039861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197434133155180291001386481 148075599866385218251039861)
          ·
            refine ⟨13882087487473614211034987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148075599866385218251039861 13882087487473614211034987)
            ·
              refine ⟨20823131231210421316552481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882087487473614211034987 20823131231210421316552481)
              ·
                refine ⟨15617348423407815987414361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20823131231210421316552481 15617348423407815987414361)
                ·
                  refine ⟨11713011317555861990560771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15617348423407815987414361 11713011317555861990560771)
                  ·
                    refine ⟨17569516976333792985841157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11713011317555861990560771 17569516976333792985841157)
                    ·
                      refine ⟨3294284433062586184845217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17569516976333792985841157 3294284433062586184845217)
                      ·
                        rfl

theorem cell23_6415596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_6415596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415596 prefixEnd_6415596 := by exact prefixLift 6415596
  have htrace : WordTrace (prefixWord ++ tailWord_6415596) baseStart_6415596 baseEnd_6415596 := by
    simpa [prefixWord, tailWord_6415596, baseEnd_6415596] using wordTrace_append hprefix tailTrace_6415596
  have hstable : (prefixWord ++ tailWord_6415596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415596).length < 2 ^ (prefixWord ++ tailWord_6415596).sum := by decide
  have hdescent : baseEnd_6415596 < baseStart_6415596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415666 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_6415666 : Nat := 118140960795 + 6415666 * 2 ^ 59
def prefixEnd_6415666 : Nat := 4983230072969 + 3 ^ 40 * 6415666 * 2
def baseEnd_6415666 : Nat := 1098106792236133636989965

theorem tailTrace_6415666 : CollatzResearch.WordTrace tailWord_6415666 prefixEnd_6415666 1098106792236133636989965 := by
  unfold tailWord_6415666
  simp only [CollatzResearch.WordTrace]
  refine ⟨58499640693786316341024713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155999041850096843576065901 58499640693786316341024713)
  ·
    refine ⟨43874730520339737255768535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58499640693786316341024713 43874730520339737255768535)
    ·
      refine ⟨65812095780509605883652803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43874730520339737255768535 65812095780509605883652803)
      ·
        refine ⟨98718143670764408825479205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65812095780509605883652803 98718143670764408825479205)
        ·
          refine ⟨18509651938268326654777351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98718143670764408825479205 18509651938268326654777351)
          ·
            refine ⟨27764477907402489982166027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509651938268326654777351 27764477907402489982166027)
            ·
              refine ⟨41646716861103734973249041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27764477907402489982166027 41646716861103734973249041)
              ·
                refine ⟨31235037645827801229936781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41646716861103734973249041 31235037645827801229936781)
                ·
                  refine ⟨11713139117185425461226293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31235037645827801229936781 11713139117185425461226293)
                  ·
                    refine ⟨1098106792236133636989965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11713139117185425461226293 1098106792236133636989965)
                    ·
                      rfl

theorem cell23_6415666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_6415666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415666 prefixEnd_6415666 := by exact prefixLift 6415666
  have htrace : WordTrace (prefixWord ++ tailWord_6415666) baseStart_6415666 baseEnd_6415666 := by
    simpa [prefixWord, tailWord_6415666, baseEnd_6415666] using wordTrace_append hprefix tailTrace_6415666
  have hstable : (prefixWord ++ tailWord_6415666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415666).length < 2 ^ (prefixWord ++ tailWord_6415666).sum := by decide
  have hdescent : baseEnd_6415666 < baseStart_6415666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415696 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_6415696 : Nat := 118140960795 + 6415696 * 2 ^ 59
def prefixEnd_6415696 : Nat := 4983230072969 + 3 ^ 40 * 6415696 * 2
def baseEnd_6415696 : Nat := 1098111927042678597864919

theorem tailTrace_6415696 : CollatzResearch.WordTrace tailWord_6415696 prefixEnd_6415696 1098111927042678597864919 := by
  unfold tailWord_6415696
  simp only [CollatzResearch.WordTrace]
  refine ⟨116999828482518290243845471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155999771310024386991793961 116999828482518290243845471)
  ·
    refine ⟨175499742723777435365768207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116999828482518290243845471 175499742723777435365768207)
    ·
      refine ⟨263249614085666153048652311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175499742723777435365768207 263249614085666153048652311)
      ·
        refine ⟨394874421128499229572978467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263249614085666153048652311 394874421128499229572978467)
        ·
          refine ⟨592311631692748844359467701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394874421128499229572978467 592311631692748844359467701)
          ·
            refine ⟨55529215471195204158700097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 592311631692748844359467701 55529215471195204158700097)
            ·
              refine ⟨41646911603396403119025073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55529215471195204158700097 41646911603396403119025073)
              ·
                refine ⟨31235183702547302339268805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41646911603396403119025073 31235183702547302339268805)
                ·
                  refine ⟨5856596944227619188612901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31235183702547302339268805 5856596944227619188612901)
                  ·
                    refine ⟨1098111927042678597864919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5856596944227619188612901 1098111927042678597864919)
                    ·
                      rfl

theorem cell23_6415696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_6415696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415696 prefixEnd_6415696 := by exact prefixLift 6415696
  have htrace : WordTrace (prefixWord ++ tailWord_6415696) baseStart_6415696 baseEnd_6415696 := by
    simpa [prefixWord, tailWord_6415696, baseEnd_6415696] using wordTrace_append hprefix tailTrace_6415696
  have hstable : (prefixWord ++ tailWord_6415696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415696).length < 2 ^ (prefixWord ++ tailWord_6415696).sum := by decide
  have hdescent : baseEnd_6415696 < baseStart_6415696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415703 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_6415703 : Nat := 118140960795 + 6415703 * 2 ^ 59
def prefixEnd_6415703 : Nat := 4983230072969 + 3 ^ 40 * 6415703 * 2
def baseEnd_6415703 : Nat := 3294339375492617266207225

theorem tailTrace_6415703 : CollatzResearch.WordTrace tailWord_6415703 prefixEnd_6415703 3294339375492617266207225 := by
  unfold tailWord_6415703
  simp only [CollatzResearch.WordTrace]
  refine ⟨233999912276011220683195763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155999941517340813788797175 233999912276011220683195763)
  ·
    refine ⟨350999868414016831024793645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233999912276011220683195763 350999868414016831024793645)
    ·
      refine ⟨131624950655256311634297617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350999868414016831024793645 131624950655256311634297617)
      ·
        refine ⟨98718712991442233725723213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131624950655256311634297617 98718712991442233725723213)
        ·
          refine ⟨37019517371790837647146205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98718712991442233725723213 37019517371790837647146205)
          ·
            refine ⟨13882319014421564117679827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37019517371790837647146205 13882319014421564117679827)
            ·
              refine ⟨20823478521632346176519741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882319014421564117679827 20823478521632346176519741)
              ·
                refine ⟨7808804445612129816194903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20823478521632346176519741 7808804445612129816194903)
                ·
                  refine ⟨11713206668418194724292355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808804445612129816194903 11713206668418194724292355)
                  ·
                    refine ⟨17569810002627292086438533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11713206668418194724292355 17569810002627292086438533)
                    ·
                      refine ⟨3294339375492617266207225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17569810002627292086438533 3294339375492617266207225)
                      ·
                        rfl

theorem cell23_6415703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_6415703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415703 prefixEnd_6415703 := by exact prefixLift 6415703
  have htrace : WordTrace (prefixWord ++ tailWord_6415703) baseStart_6415703 baseEnd_6415703 := by
    simpa [prefixWord, tailWord_6415703, baseEnd_6415703] using wordTrace_append hprefix tailTrace_6415703
  have hstable : (prefixWord ++ tailWord_6415703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415703).length < 2 ^ (prefixWord ++ tailWord_6415703).sum := by decide
  have hdescent : baseEnd_6415703 < baseStart_6415703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415730 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_6415730 : Nat := 118140960795 + 6415730 * 2 ^ 59
def prefixEnd_6415730 : Nat := 4983230072969 + 3 ^ 40 * 6415730 * 2
def baseEnd_6415730 : Nat := 1098117746490096220189867

theorem tailTrace_6415730 : CollatzResearch.WordTrace tailWord_6415730 prefixEnd_6415730 1098117746490096220189867 := by
  unfold tailWord_6415730
  simp only [CollatzResearch.WordTrace]
  refine ⟨58500224261728351073607161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156000598031275602862952429 58500224261728351073607161)
  ·
    refine ⟨43875168196296263305205371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58500224261728351073607161 43875168196296263305205371)
    ·
      refine ⟨65812752294444394957808057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43875168196296263305205371 65812752294444394957808057)
      ·
        refine ⟨49359564220833296218356043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65812752294444394957808057 49359564220833296218356043)
        ·
          refine ⟨74039346331249944327534065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49359564220833296218356043 74039346331249944327534065)
          ·
            refine ⟨55529509748437458245650549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74039346331249944327534065 55529509748437458245650549)
            ·
              refine ⟨5205891538916011710529739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55529509748437458245650549 5205891538916011710529739)
              ·
                refine ⟨7808837308374017565794609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205891538916011710529739 7808837308374017565794609)
                ·
                  refine ⟨5856627981280513174345957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7808837308374017565794609 5856627981280513174345957)
                  ·
                    refine ⟨1098117746490096220189867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5856627981280513174345957 1098117746490096220189867)
                    ·
                      rfl

theorem cell23_6415730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_6415730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415730 prefixEnd_6415730 := by exact prefixLift 6415730
  have htrace : WordTrace (prefixWord ++ tailWord_6415730) baseStart_6415730 baseEnd_6415730 := by
    simpa [prefixWord, tailWord_6415730, baseEnd_6415730] using wordTrace_append hprefix tailTrace_6415730
  have hstable : (prefixWord ++ tailWord_6415730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415730).length < 2 ^ (prefixWord ++ tailWord_6415730).sum := by decide
  have hdescent : baseEnd_6415730 < baseStart_6415730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415733 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_6415733 : Nat := 118140960795 + 6415733 * 2 ^ 59
def prefixEnd_6415733 : Nat := 4983230072969 + 3 ^ 40 * 6415733 * 2
def baseEnd_6415733 : Nat := 3294354779912252148832087

theorem tailTrace_6415733 : CollatzResearch.WordTrace tailWord_6415733 prefixEnd_6415733 3294354779912252148832087 := by
  unfold tailWord_6415733
  simp only [CollatzResearch.WordTrace]
  refine ⟨234001006465902535806787853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156000670977268357204525235 234001006465902535806787853)
  ·
    refine ⟨87750377424713450927545445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234001006465902535806787853 87750377424713450927545445)
    ·
      refine ⟨16453195767133772048914771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87750377424713450927545445 16453195767133772048914771)
      ·
        refine ⟨24679793650700658073372157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16453195767133772048914771 24679793650700658073372157)
        ·
          refine ⟨9254922619012746777514559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24679793650700658073372157 9254922619012746777514559)
          ·
            refine ⟨13882383928519120166271839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254922619012746777514559 13882383928519120166271839)
            ·
              refine ⟨20823575892778680249407759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882383928519120166271839 20823575892778680249407759)
              ·
                refine ⟨31235363839168020374111639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20823575892778680249407759 31235363839168020374111639)
                ·
                  refine ⟨46853045758752030561167459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31235363839168020374111639 46853045758752030561167459)
                  ·
                    refine ⟨70279568638128045841751189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46853045758752030561167459 70279568638128045841751189)
                    ·
                      refine ⟨3294354779912252148832087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70279568638128045841751189 3294354779912252148832087)
                      ·
                        rfl

theorem cell23_6415733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_6415733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415733 prefixEnd_6415733 := by exact prefixLift 6415733
  have htrace : WordTrace (prefixWord ++ tailWord_6415733) baseStart_6415733 baseEnd_6415733 := by
    simpa [prefixWord, tailWord_6415733, baseEnd_6415733] using wordTrace_append hprefix tailTrace_6415733
  have hstable : (prefixWord ++ tailWord_6415733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415733).length < 2 ^ (prefixWord ++ tailWord_6415733).sum := by decide
  have hdescent : baseEnd_6415733 < baseStart_6415733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415770 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_6415770 : Nat := 118140960795 + 6415770 * 2 ^ 59
def prefixEnd_6415770 : Nat := 4983230072969 + 3 ^ 40 * 6415770 * 2
def baseEnd_6415770 : Nat := 3294373778696468504069417

theorem tailTrace_6415770 : CollatzResearch.WordTrace tailWord_6415770 prefixEnd_6415770 3294373778696468504069417 := by
  unfold tailWord_6415770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58500588991692122781471191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156001570644512327417256509 58500588991692122781471191)
  ·
    refine ⟨87750883487538184172206787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58500588991692122781471191 87750883487538184172206787)
    ·
      refine ⟨131626325231307276258310181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87750883487538184172206787 131626325231307276258310181)
      ·
        refine ⟨24679935980870114298433159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131626325231307276258310181 24679935980870114298433159)
        ·
          refine ⟨37019903971305171447649739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24679935980870114298433159 37019903971305171447649739)
          ·
            refine ⟨55529855956957757171474609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37019903971305171447649739 55529855956957757171474609)
            ·
              refine ⟨41647391967718317878605957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55529855956957757171474609 41647391967718317878605957)
              ·
                refine ⟨7808885993947184602238617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41647391967718317878605957 7808885993947184602238617)
                ·
                  refine ⟨5856664495460388451678963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7808885993947184602238617 5856664495460388451678963)
                  ·
                    refine ⟨8784996743190582677518445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856664495460388451678963 8784996743190582677518445)
                    ·
                      refine ⟨3294373778696468504069417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8784996743190582677518445 3294373778696468504069417)
                      ·
                        rfl

theorem cell23_6415770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_6415770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415770 prefixEnd_6415770 := by exact prefixLift 6415770
  have htrace : WordTrace (prefixWord ++ tailWord_6415770) baseStart_6415770 baseEnd_6415770 := by
    simpa [prefixWord, tailWord_6415770, baseEnd_6415770] using wordTrace_append hprefix tailTrace_6415770
  have hstable : (prefixWord ++ tailWord_6415770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415770).length < 2 ^ (prefixWord ++ tailWord_6415770).sum := by decide
  have hdescent : baseEnd_6415770 < baseStart_6415770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415776 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6415776 : Nat := 118140960795 + 6415776 * 2 ^ 59
def prefixEnd_6415776 : Nat := 4983230072969 + 3 ^ 40 * 6415776 * 2
def baseEnd_6415776 : Nat := 3294376859580395480594389

theorem tailTrace_6415776 : CollatzResearch.WordTrace tailWord_6415776 prefixEnd_6415776 3294376859580395480594389 := by
  unfold tailWord_6415776
  simp only [CollatzResearch.WordTrace]
  refine ⟨117001287402373377075301591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156001716536497836100402121 117001287402373377075301591)
  ·
    refine ⟨175501931103560065612952387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117001287402373377075301591 175501931103560065612952387)
    ·
      refine ⟨263252896655340098419428581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175501931103560065612952387 263252896655340098419428581)
      ·
        refine ⟨49359918122876268453642859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263252896655340098419428581 49359918122876268453642859)
        ·
          refine ⟨74039877184314402680464289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49359918122876268453642859 74039877184314402680464289)
          ·
            refine ⟨55529907888235802010348217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74039877184314402680464289 55529907888235802010348217)
            ·
              refine ⟨41647430916176851507761163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55529907888235802010348217 41647430916176851507761163)
              ·
                refine ⟨62471146374265277261641745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41647430916176851507761163 62471146374265277261641745)
                ·
                  refine ⟨46853359780698957946231309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62471146374265277261641745 46853359780698957946231309)
                  ·
                    refine ⟨17570009917762109229836741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46853359780698957946231309 17570009917762109229836741)
                    ·
                      refine ⟨3294376859580395480594389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17570009917762109229836741 3294376859580395480594389)
                      ·
                        rfl

theorem cell23_6415776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6415776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415776 prefixEnd_6415776 := by exact prefixLift 6415776
  have htrace : WordTrace (prefixWord ++ tailWord_6415776) baseStart_6415776 baseEnd_6415776 := by
    simpa [prefixWord, tailWord_6415776, baseEnd_6415776] using wordTrace_append hprefix tailTrace_6415776
  have hstable : (prefixWord ++ tailWord_6415776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415776).length < 2 ^ (prefixWord ++ tailWord_6415776).sum := by decide
  have hdescent : baseEnd_6415776 < baseStart_6415776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415797 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_6415797 : Nat := 118140960795 + 6415797 * 2 ^ 59
def prefixEnd_6415797 : Nat := 4983230072969 + 3 ^ 40 * 6415797 * 2
def baseEnd_6415797 : Nat := 3294387642674139898431793

theorem tailTrace_6415797 : CollatzResearch.WordTrace tailWord_6415797 prefixEnd_6415797 3294387642674139898431793 := by
  unfold tailWord_6415797
  simp only [CollatzResearch.WordTrace]
  refine ⟨234003340737670674737117645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156002227158447116491411763 234003340737670674737117645)
  ·
    refine ⟨87751252776626503026419117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234003340737670674737117645 87751252776626503026419117)
    ·
      refine ⟨32906719791234938634907169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87751252776626503026419117 32906719791234938634907169)
      ·
        refine ⟨24680039843426203976180377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32906719791234938634907169 24680039843426203976180377)
        ·
          refine ⟨18510029882569652982135283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24680039843426203976180377 18510029882569652982135283)
          ·
            refine ⟨27765044823854479473202925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18510029882569652982135283 27765044823854479473202925)
            ·
              refine ⟨10411891808945429802451097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27765044823854479473202925 10411891808945429802451097)
              ·
                refine ⟨7808918856709072351838323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10411891808945429802451097 7808918856709072351838323)
                ·
                  refine ⟨11713378285063608527757485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808918856709072351838323 11713378285063608527757485)
                  ·
                    refine ⟨4392516856898853197909057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11713378285063608527757485 4392516856898853197909057)
                    ·
                      refine ⟨3294387642674139898431793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392516856898853197909057 3294387642674139898431793)
                      ·
                        rfl

theorem cell23_6415797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_6415797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415797 prefixEnd_6415797 := by exact prefixLift 6415797
  have htrace : WordTrace (prefixWord ++ tailWord_6415797) baseStart_6415797 baseEnd_6415797 := by
    simpa [prefixWord, tailWord_6415797, baseEnd_6415797] using wordTrace_append hprefix tailTrace_6415797
  have hstable : (prefixWord ++ tailWord_6415797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415797).length < 2 ^ (prefixWord ++ tailWord_6415797).sum := by decide
  have hdescent : baseEnd_6415797 < baseStart_6415797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415830 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_6415830 : Nat := 118140960795 + 6415830 * 2 ^ 59
def prefixEnd_6415830 : Nat := 4983230072969 + 3 ^ 40 * 6415830 * 2
def baseEnd_6415830 : Nat := 3294404587535738269319141

theorem tailTrace_6415830 : CollatzResearch.WordTrace tailWord_6415830 prefixEnd_6415830 3294404587535738269319141 := by
  unfold tailWord_6415830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14625284021659445085816809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156003029564367414248712629 14625284021659445085816809)
  ·
    refine ⟨10968963016244583814362607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14625284021659445085816809 10968963016244583814362607)
    ·
      refine ⟨16453444524366875721543911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10968963016244583814362607 16453444524366875721543911)
      ·
        refine ⟨24680166786550313582315867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16453444524366875721543911 24680166786550313582315867)
        ·
          refine ⟨37020250179825470373473801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680166786550313582315867 37020250179825470373473801)
          ·
            refine ⟨27765187634869102780105351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37020250179825470373473801 27765187634869102780105351)
            ·
              refine ⟨41647781452303654170158027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27765187634869102780105351 41647781452303654170158027)
              ·
                refine ⟨62471672178455481255237041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41647781452303654170158027 62471672178455481255237041)
                ·
                  refine ⟨46853754133841610941427781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62471672178455481255237041 46853754133841610941427781)
                  ·
                    refine ⟨8785078900095302051517709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46853754133841610941427781 8785078900095302051517709)
                    ·
                      refine ⟨3294404587535738269319141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785078900095302051517709 3294404587535738269319141)
                      ·
                        rfl

theorem cell23_6415830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_6415830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415830 prefixEnd_6415830 := by exact prefixLift 6415830
  have htrace : WordTrace (prefixWord ++ tailWord_6415830) baseStart_6415830 baseEnd_6415830 := by
    simpa [prefixWord, tailWord_6415830, baseEnd_6415830] using wordTrace_append hprefix tailTrace_6415830
  have hstable : (prefixWord ++ tailWord_6415830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415830).length < 2 ^ (prefixWord ++ tailWord_6415830).sum := by decide
  have hdescent : baseEnd_6415830 < baseStart_6415830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415843 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3]
def baseStart_6415843 : Nat := 118140960795 + 6415843 * 2 ^ 59
def prefixEnd_6415843 : Nat := 4983230072969 + 3 ^ 40 * 6415843 * 2
def baseEnd_6415843 : Nat := 3294411262784246718456581

theorem tailTrace_6415843 : CollatzResearch.WordTrace tailWord_6415843 prefixEnd_6415843 3294411262784246718456581 := by
  unfold tailWord_6415843
  simp only [CollatzResearch.WordTrace]
  refine ⟨234005018495504024593292183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156003345663669349728861455 234005018495504024593292183)
  ·
    refine ⟨351007527743256036889938275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234005018495504024593292183 351007527743256036889938275)
    ·
      refine ⟨526511291614884055334907413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351007527743256036889938275 526511291614884055334907413)
      ·
        refine ⟨24680216794447690093823785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 526511291614884055334907413 24680216794447690093823785)
        ·
          refine ⟨18510162595835767570367839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24680216794447690093823785 18510162595835767570367839)
          ·
            refine ⟨27765243893753651355551759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18510162595835767570367839 27765243893753651355551759)
            ·
              refine ⟨41647865840630477033327639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27765243893753651355551759 41647865840630477033327639)
              ·
                refine ⟨62471798760945715549991459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41647865840630477033327639 62471798760945715549991459)
                ·
                  refine ⟨93707698141418573324987189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62471798760945715549991459 93707698141418573324987189)
                  ·
                    refine ⟨8785096700757991249217549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93707698141418573324987189 8785096700757991249217549)
                    ·
                      refine ⟨3294411262784246718456581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785096700757991249217549 3294411262784246718456581)
                      ·
                        rfl

theorem cell23_6415843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_6415843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415843 prefixEnd_6415843 := by exact prefixLift 6415843
  have htrace : WordTrace (prefixWord ++ tailWord_6415843) baseStart_6415843 baseEnd_6415843 := by
    simpa [prefixWord, tailWord_6415843, baseEnd_6415843] using wordTrace_append hprefix tailTrace_6415843
  have hstable : (prefixWord ++ tailWord_6415843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415843).length < 2 ^ (prefixWord ++ tailWord_6415843).sum := by decide
  have hdescent : baseEnd_6415843 < baseStart_6415843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415878 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6415878 : Nat := 118140960795 + 6415878 * 2 ^ 59
def prefixEnd_6415878 : Nat := 4983230072969 + 3 ^ 40 * 6415878 * 2
def baseEnd_6415878 : Nat := 3294429234607154081518921

theorem tailTrace_6415878 : CollatzResearch.WordTrace tailWord_6415878 prefixEnd_6415878 3294429234607154081518921 := by
  unfold tailWord_6415878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312696720324288299088009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156004196700251483713877525 7312696720324288299088009)
  ·
    refine ⟨5484522540243216224316007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7312696720324288299088009 5484522540243216224316007)
    ·
      refine ⟨8226783810364824336474011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5484522540243216224316007 8226783810364824336474011)
      ·
        refine ⟨12340175715547236504711017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8226783810364824336474011 12340175715547236504711017)
        ·
          refine ⟨9255131786660427378533263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12340175715547236504711017 9255131786660427378533263)
          ·
            refine ⟨13882697679990641067799895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255131786660427378533263 13882697679990641067799895)
            ·
              refine ⟨20824046519985961601699843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882697679990641067799895 20824046519985961601699843)
              ·
                refine ⟨31236069779978942402549765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20824046519985961601699843 31236069779978942402549765)
                ·
                  refine ⟨5856763083746051700478081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31236069779978942402549765 5856763083746051700478081)
                  ·
                    refine ⟨4392572312809538775358561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5856763083746051700478081 4392572312809538775358561)
                    ·
                      refine ⟨3294429234607154081518921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392572312809538775358561 3294429234607154081518921)
                      ·
                        rfl

theorem cell23_6415878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6415878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415878 prefixEnd_6415878 := by exact prefixLift 6415878
  have htrace : WordTrace (prefixWord ++ tailWord_6415878) baseStart_6415878 baseEnd_6415878 := by
    simpa [prefixWord, tailWord_6415878, baseEnd_6415878] using wordTrace_append hprefix tailTrace_6415878
  have hstable : (prefixWord ++ tailWord_6415878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415878).length < 2 ^ (prefixWord ++ tailWord_6415878).sum := by decide
  have hdescent : baseEnd_6415878 < baseStart_6415878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415900 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_6415900 : Nat := 118140960795 + 6415900 * 2 ^ 59
def prefixEnd_6415900 : Nat := 4983230072969 + 3 ^ 40 * 6415900 * 2
def baseEnd_6415900 : Nat := 3294440531181552995443819

theorem tailTrace_6415900 : CollatzResearch.WordTrace tailWord_6415900 prefixEnd_6415900 3294440531181552995443819 := by
  unfold tailWord_6415900
  simp only [CollatzResearch.WordTrace]
  refine ⟨117003548728148761664058577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156004731637531682218744769 117003548728148761664058577)
  ·
    refine ⟨87752661546111571248043933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117003548728148761664058577 87752661546111571248043933)
    ·
      refine ⟨32907248079791839218016475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87752661546111571248043933 32907248079791839218016475)
      ·
        refine ⟨49360872119687758827024713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32907248079791839218016475 49360872119687758827024713)
        ·
          refine ⟨37020654089765819120268535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49360872119687758827024713 37020654089765819120268535)
          ·
            refine ⟨55530981134648728680402803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37020654089765819120268535 55530981134648728680402803)
            ·
              refine ⟨83296471701973093020604205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55530981134648728680402803 83296471701973093020604205)
              ·
                refine ⟨31236176888239909882726577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83296471701973093020604205 31236176888239909882726577)
                ·
                  refine ⟨23427132666179932412044933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31236176888239909882726577 23427132666179932412044933)
                  ·
                    refine ⟨4392587374908737327258425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23427132666179932412044933 4392587374908737327258425)
                    ·
                      refine ⟨3294440531181552995443819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392587374908737327258425 3294440531181552995443819)
                      ·
                        rfl

theorem cell23_6415900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_6415900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415900 prefixEnd_6415900 := by exact prefixLift 6415900
  have htrace : WordTrace (prefixWord ++ tailWord_6415900) baseStart_6415900 baseEnd_6415900 := by
    simpa [prefixWord, tailWord_6415900, baseEnd_6415900] using wordTrace_append hprefix tailTrace_6415900
  have hstable : (prefixWord ++ tailWord_6415900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415900).length < 2 ^ (prefixWord ++ tailWord_6415900).sum := by decide
  have hdescent : baseEnd_6415900 < baseStart_6415900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415903 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_6415903 : Nat := 118140960795 + 6415903 * 2 ^ 59
def prefixEnd_6415903 : Nat := 4983230072969 + 3 ^ 40 * 6415903 * 2
def baseEnd_6415903 : Nat := 3294442071623516483706305

theorem tailTrace_6415903 : CollatzResearch.WordTrace tailWord_6415903 prefixEnd_6415903 3294442071623516483706305 := by
  unfold tailWord_6415903
  simp only [CollatzResearch.WordTrace]
  refine ⟨234007206875286654840476363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156004804583524436560317575 234007206875286654840476363)
  ·
    refine ⟨351010810312929982260714545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234007206875286654840476363 351010810312929982260714545)
    ·
      refine ⟨263258107734697486695535909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351010810312929982260714545 263258107734697486695535909)
      ·
        refine ⟨49360895200255778755412983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263258107734697486695535909 49360895200255778755412983)
        ·
          refine ⟨74041342800383668133119475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49360895200255778755412983 74041342800383668133119475)
          ·
            refine ⟨111062014200575502199679213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74041342800383668133119475 111062014200575502199679213)
            ·
              refine ⟨41648255325215813324879705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111062014200575502199679213 41648255325215813324879705)
              ·
                refine ⟨31236191493911859993659779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41648255325215813324879705 31236191493911859993659779)
                ·
                  refine ⟨46854287240867789990489669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31236191493911859993659779 46854287240867789990489669)
                  ·
                    refine ⟨8785178857662710623216813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46854287240867789990489669 8785178857662710623216813)
                    ·
                      refine ⟨3294442071623516483706305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785178857662710623216813 3294442071623516483706305)
                      ·
                        rfl

theorem cell23_6415903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_6415903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415903 prefixEnd_6415903 := by exact prefixLift 6415903
  have htrace : WordTrace (prefixWord ++ tailWord_6415903) baseStart_6415903 baseEnd_6415903 := by
    simpa [prefixWord, tailWord_6415903, baseEnd_6415903] using wordTrace_append hprefix tailTrace_6415903
  have hstable : (prefixWord ++ tailWord_6415903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415903).length < 2 ^ (prefixWord ++ tailWord_6415903).sum := by decide
  have hdescent : baseEnd_6415903 < baseStart_6415903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415916 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_6415916 : Nat := 118140960795 + 6415916 * 2 ^ 59
def prefixEnd_6415916 : Nat := 4983230072969 + 3 ^ 40 * 6415916 * 2
def baseEnd_6415916 : Nat := 3294448746872024932843745

theorem tailTrace_6415916 : CollatzResearch.WordTrace tailWord_6415916 prefixEnd_6415916 3294448746872024932843745 := by
  unfold tailWord_6415916
  simp only [CollatzResearch.WordTrace]
  refine ⟨117003840512119779030349801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156005120682826372040466401 117003840512119779030349801)
  ·
    refine ⟨87752880384089834272762351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117003840512119779030349801 87752880384089834272762351)
    ·
      refine ⟨131629320576134751409143527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87752880384089834272762351 131629320576134751409143527)
      ·
        refine ⟨197443980864202127113715291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131629320576134751409143527 197443980864202127113715291)
        ·
          refine ⟨296165971296303190670572937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197443980864202127113715291 296165971296303190670572937)
          ·
            refine ⟨222124478472227393002929703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296165971296303190670572937 222124478472227393002929703)
            ·
              refine ⟨333186717708341089504394555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222124478472227393002929703 333186717708341089504394555)
              ·
                refine ⟨499780076562511634256591833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333186717708341089504394555 499780076562511634256591833)
                ·
                  refine ⟨374835057421883725692443875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499780076562511634256591833 374835057421883725692443875)
                  ·
                    refine ⟨562252586132825588538665813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 374835057421883725692443875 562252586132825588538665813)
                    ·
                      refine ⟨3294448746872024932843745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 562252586132825588538665813 3294448746872024932843745)
                      ·
                        rfl

theorem cell23_6415916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_6415916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415916 prefixEnd_6415916 := by exact prefixLift 6415916
  have htrace : WordTrace (prefixWord ++ tailWord_6415916) baseStart_6415916 baseEnd_6415916 := by
    simpa [prefixWord, tailWord_6415916, baseEnd_6415916] using wordTrace_append hprefix tailTrace_6415916
  have hstable : (prefixWord ++ tailWord_6415916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415916).length < 2 ^ (prefixWord ++ tailWord_6415916).sum := by decide
  have hdescent : baseEnd_6415916 < baseStart_6415916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415927 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 1, 4]
def baseStart_6415927 : Nat := 118140960795 + 6415927 * 2 ^ 59
def prefixEnd_6415927 : Nat := 4983230072969 + 3 ^ 40 * 6415927 * 2
def baseEnd_6415927 : Nat := 1098151465053074796602065

theorem tailTrace_6415927 : CollatzResearch.WordTrace tailWord_6415927 prefixEnd_6415927 1098151465053074796602065 := by
  unfold tailWord_6415927
  simp only [CollatzResearch.WordTrace]
  refine ⟨234008082227199706939350035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156005388151466471292900023 234008082227199706939350035)
  ·
    refine ⟨351012123340799560409025053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234008082227199706939350035 351012123340799560409025053)
    ·
      refine ⟨131629546252799835153384395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351012123340799560409025053 131629546252799835153384395)
      ·
        refine ⟨197444319379199752730076593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131629546252799835153384395 197444319379199752730076593)
        ·
          refine ⟨148083239534399814547557445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197444319379199752730076593 148083239534399814547557445)
          ·
            refine ⟨27765607412699965227667021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148083239534399814547557445 27765607412699965227667021)
            ·
              refine ⟨10412102779762486960375133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27765607412699965227667021 10412102779762486960375133)
              ·
                refine ⟨3904538542410932610140675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10412102779762486960375133 3904538542410932610140675)
                ·
                  refine ⟨5856807813616398915211013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904538542410932610140675 5856807813616398915211013)
                  ·
                    refine ⟨1098151465053074796602065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5856807813616398915211013 1098151465053074796602065)
                    ·
                      rfl

theorem cell23_6415927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_6415927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415927 prefixEnd_6415927 := by exact prefixLift 6415927
  have htrace : WordTrace (prefixWord ++ tailWord_6415927) baseStart_6415927 baseEnd_6415927 := by
    simpa [prefixWord, tailWord_6415927, baseEnd_6415927] using wordTrace_append hprefix tailTrace_6415927
  have hstable : (prefixWord ++ tailWord_6415927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415927).length < 2 ^ (prefixWord ++ tailWord_6415927).sum := by decide
  have hdescent : baseEnd_6415927 < baseStart_6415927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415953 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_6415953 : Nat := 118140960795 + 6415953 * 2 ^ 59
def prefixEnd_6415953 : Nat := 4983230072969 + 3 ^ 40 * 6415953 * 2
def baseEnd_6415953 : Nat := 1098155915218747096027025

theorem tailTrace_6415953 : CollatzResearch.WordTrace tailWord_6415953 prefixEnd_6415953 1098155915218747096027025 := by
  unfold tailWord_6415953
  simp only [CollatzResearch.WordTrace]
  refine ⟨234009030525105513379796513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156006020350070342253197675 234009030525105513379796513)
  ·
    refine ⟨175506772893829135034847385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234009030525105513379796513 175506772893829135034847385)
    ·
      refine ⟨131630079670371851276135539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175506772893829135034847385 131630079670371851276135539)
      ·
        refine ⟨197445119505557776914203309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131630079670371851276135539 197445119505557776914203309)
        ·
          refine ⟨74041919814584166342826241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197445119505557776914203309 74041919814584166342826241)
          ·
            refine ⟨55531439860938124757119681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74041919814584166342826241 55531439860938124757119681)
            ·
              refine ⟨41648579895703593567839761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55531439860938124757119681 41648579895703593567839761)
              ·
                refine ⟨31236434921777695175879821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41648579895703593567839761 31236434921777695175879821)
                ·
                  refine ⟨11713663095666635690954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31236434921777695175879821 11713663095666635690954933)
                  ·
                    refine ⟨1098155915218747096027025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11713663095666635690954933 1098155915218747096027025)
                    ·
                      rfl

theorem cell23_6415953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_6415953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415953 prefixEnd_6415953 := by exact prefixLift 6415953
  have htrace : WordTrace (prefixWord ++ tailWord_6415953) baseStart_6415953 baseEnd_6415953 := by
    simpa [prefixWord, tailWord_6415953, baseEnd_6415953] using wordTrace_append hprefix tailTrace_6415953
  have hstable : (prefixWord ++ tailWord_6415953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415953).length < 2 ^ (prefixWord ++ tailWord_6415953).sum := by decide
  have hdescent : baseEnd_6415953 < baseStart_6415953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6415960 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_6415960 : Nat := 118140960795 + 6415960 * 2 ^ 59
def prefixEnd_6415960 : Nat := 4983230072969 + 3 ^ 40 * 6415960 * 2
def baseEnd_6415960 : Nat := 3294471340020822760693543

theorem tailTrace_6415960 : CollatzResearch.WordTrace tailWord_6415960 prefixEnd_6415960 3294471340020822760693543 := by
  unfold tailWord_6415960
  simp only [CollatzResearch.WordTrace]
  refine ⟨117004642918040076787650667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156006190557386769050200889 117004642918040076787650667)
  ·
    refine ⟨175506964377060115181476001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117004642918040076787650667 175506964377060115181476001)
    ·
      refine ⟨131630223282795086386107001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175506964377060115181476001 131630223282795086386107001)
      ·
        refine ⟨98722667462096314789580251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131630223282795086386107001 98722667462096314789580251)
        ·
          refine ⟨148084001193144472184370377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98722667462096314789580251 148084001193144472184370377)
          ·
            refine ⟨111063000894858354138277783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148084001193144472184370377 111063000894858354138277783)
            ·
              refine ⟨166594501342287531207416675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111063000894858354138277783 166594501342287531207416675)
              ·
                refine ⟨249891752013431296811125013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166594501342287531207416675 249891752013431296811125013)
                ·
                  refine ⟨11713675875629592038021485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249891752013431296811125013 11713675875629592038021485)
                  ·
                    refine ⟨4392628453361097014258057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11713675875629592038021485 4392628453361097014258057)
                    ·
                      refine ⟨3294471340020822760693543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392628453361097014258057 3294471340020822760693543)
                      ·
                        rfl

theorem cell23_6415960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_6415960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6415960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6415960 prefixEnd_6415960 := by exact prefixLift 6415960
  have htrace : WordTrace (prefixWord ++ tailWord_6415960) baseStart_6415960 baseEnd_6415960 := by
    simpa [prefixWord, tailWord_6415960, baseEnd_6415960] using wordTrace_append hprefix tailTrace_6415960
  have hstable : (prefixWord ++ tailWord_6415960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6415960).length < 2 ^ (prefixWord ++ tailWord_6415960).sum := by decide
  have hdescent : baseEnd_6415960 < baseStart_6415960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6415960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416001 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_6416001 : Nat := 118140960795 + 6416001 * 2 ^ 59
def prefixEnd_6416001 : Nat := 4983230072969 + 3 ^ 40 * 6416001 * 2
def baseEnd_6416001 : Nat := 3294492392727657100280855

theorem tailTrace_6416001 : CollatzResearch.WordTrace tailWord_6416001 prefixEnd_6416001 3294492392727657100280855 := by
  unfold tailWord_6416001
  simp only [CollatzResearch.WordTrace]
  refine ⟨234010781228931617577543857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156007187485954411718362571 234010781228931617577543857)
  ·
    refine ⟨175508085921698713183157893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234010781228931617577543857 175508085921698713183157893)
    ·
      refine ⟨32907766110318508721842105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175508085921698713183157893 32907766110318508721842105)
      ·
        refine ⟨24680824582738881541381579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32907766110318508721842105 24680824582738881541381579)
        ·
          refine ⟨37021236874108322312072369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680824582738881541381579 37021236874108322312072369)
          ·
            refine ⟨27765927655581241734054277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37021236874108322312072369 27765927655581241734054277)
            ·
              refine ⟨5206111435421482825135177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27765927655581241734054277 5206111435421482825135177)
              ·
                refine ⟨3904583576566112118851383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206111435421482825135177 3904583576566112118851383)
                ·
                  refine ⟨5856875364849168178277075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904583576566112118851383 5856875364849168178277075)
                  ·
                    refine ⟨8785313047273752267415613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856875364849168178277075 8785313047273752267415613)
                    ·
                      refine ⟨3294492392727657100280855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785313047273752267415613 3294492392727657100280855)
                      ·
                        rfl

theorem cell23_6416001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_6416001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416001 prefixEnd_6416001 := by exact prefixLift 6416001
  have htrace : WordTrace (prefixWord ++ tailWord_6416001) baseStart_6416001 baseEnd_6416001 := by
    simpa [prefixWord, tailWord_6416001, baseEnd_6416001] using wordTrace_append hprefix tailTrace_6416001
  have hstable : (prefixWord ++ tailWord_6416001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416001).length < 2 ^ (prefixWord ++ tailWord_6416001).sum := by decide
  have hdescent : baseEnd_6416001 < baseStart_6416001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416003 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_6416003 : Nat := 118140960795 + 6416003 * 2 ^ 59
def prefixEnd_6416003 : Nat := 4983230072969 + 3 ^ 40 * 6416003 * 2
def baseEnd_6416003 : Nat := 3294493419688966092455845

theorem tailTrace_6416003 : CollatzResearch.WordTrace tailWord_6416003 prefixEnd_6416003 3294493419688966092455845 := by
  unfold tailWord_6416003
  simp only [CollatzResearch.WordTrace]
  refine ⟨234010854174924371919116663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156007236116616247946077775 234010854174924371919116663)
  ·
    refine ⟨351016281262386557878674995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234010854174924371919116663 351016281262386557878674995)
    ·
      refine ⟨526524421893579836818012493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351016281262386557878674995 526524421893579836818012493)
      ·
        refine ⟨197446658210092438806754685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526524421893579836818012493 197446658210092438806754685)
        ·
          refine ⟨74042496828784664552533007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197446658210092438806754685 74042496828784664552533007)
          ·
            refine ⟨111063745243176996828799511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74042496828784664552533007 111063745243176996828799511)
            ·
              refine ⟨166595617864765495243199267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111063745243176996828799511 166595617864765495243199267)
              ·
                refine ⟨249893426797148242864798901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166595617864765495243199267 249893426797148242864798901)
                ·
                  refine ⟨23427508762232647768574897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249893426797148242864798901 23427508762232647768574897)
                  ·
                    refine ⟨17570631571674485826431173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23427508762232647768574897 17570631571674485826431173)
                    ·
                      refine ⟨3294493419688966092455845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17570631571674485826431173 3294493419688966092455845)
                      ·
                        rfl

theorem cell23_6416003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_6416003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416003 prefixEnd_6416003 := by exact prefixLift 6416003
  have htrace : WordTrace (prefixWord ++ tailWord_6416003) baseStart_6416003 baseEnd_6416003 := by
    simpa [prefixWord, tailWord_6416003, baseEnd_6416003] using wordTrace_append hprefix tailTrace_6416003
  have hstable : (prefixWord ++ tailWord_6416003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416003).length < 2 ^ (prefixWord ++ tailWord_6416003).sum := by decide
  have hdescent : baseEnd_6416003 < baseStart_6416003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416024 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6416024 : Nat := 118140960795 + 6416024 * 2 ^ 59
def prefixEnd_6416024 : Nat := 4983230072969 + 3 ^ 40 * 6416024 * 2
def baseEnd_6416024 : Nat := 3294504202782710510293249

theorem tailTrace_6416024 : CollatzResearch.WordTrace tailWord_6416024 prefixEnd_6416024 3294504202782710510293249 := by
  unfold tailWord_6416024
  simp only [CollatzResearch.WordTrace]
  refine ⟨117005810053924146252815563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156007746738565528337087417 117005810053924146252815563)
  ·
    refine ⟨175508715080886219379223345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117005810053924146252815563 175508715080886219379223345)
    ·
      refine ⟨131631536310664664534417509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175508715080886219379223345 131631536310664664534417509)
      ·
        refine ⟨24680913058249624600203283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131631536310664664534417509 24680913058249624600203283)
        ·
          refine ⟨37021369587374436900304925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680913058249624600203283 37021369587374436900304925)
          ·
            refine ⟨13883013595265413837614347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37021369587374436900304925 13883013595265413837614347)
            ·
              refine ⟨20824520392898120756421521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13883013595265413837614347 20824520392898120756421521)
              ·
                refine ⟨15618390294673590567316141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20824520392898120756421521 15618390294673590567316141)
                ·
                  refine ⟨5856896360502596462743553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15618390294673590567316141 5856896360502596462743553)
                  ·
                    refine ⟨4392672270376947347057665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5856896360502596462743553 4392672270376947347057665)
                    ·
                      refine ⟨3294504202782710510293249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392672270376947347057665 3294504202782710510293249)
                      ·
                        rfl

theorem cell23_6416024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6416024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416024 prefixEnd_6416024 := by exact prefixLift 6416024
  have htrace : WordTrace (prefixWord ++ tailWord_6416024) baseStart_6416024 baseEnd_6416024 := by
    simpa [prefixWord, tailWord_6416024, baseEnd_6416024] using wordTrace_append hprefix tailTrace_6416024
  have hstable : (prefixWord ++ tailWord_6416024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416024).length < 2 ^ (prefixWord ++ tailWord_6416024).sum := by decide
  have hdescent : baseEnd_6416024 < baseStart_6416024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416074 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_6416074 : Nat := 118140960795 + 6416074 * 2 ^ 59
def prefixEnd_6416074 : Nat := 4983230072969 + 3 ^ 40 * 6416074 * 2
def baseEnd_6416074 : Nat := 3294529876815435314668019

theorem tailTrace_6416074 : CollatzResearch.WordTrace tailWord_6416074 prefixEnd_6416074 3294529876815435314668019 := by
  unfold tailWord_6416074
  simp only [CollatzResearch.WordTrace]
  refine ⟨58503360939416787761237819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156008962505111434029967517 58503360939416787761237819)
  ·
    refine ⟨87755041409125181641856729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58503360939416787761237819 87755041409125181641856729)
    ·
      refine ⟨65816281056843886231392547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87755041409125181641856729 65816281056843886231392547)
      ·
        refine ⟨98724421585265829347088821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65816281056843886231392547 98724421585265829347088821)
        ·
          refine ⟨9255414523618671501289577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98724421585265829347088821 9255414523618671501289577)
          ·
            refine ⟨6941560892714003625967183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9255414523618671501289577 6941560892714003625967183)
            ·
              refine ⟨10412341339071005438950775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941560892714003625967183 10412341339071005438950775)
              ·
                refine ⟨15618512008606508158426163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10412341339071005438950775 15618512008606508158426163)
                ·
                  refine ⟨23427768012909762237639245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15618512008606508158426163 23427768012909762237639245)
                  ·
                    refine ⟨8785413004841160839114717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23427768012909762237639245 8785413004841160839114717)
                    ·
                      refine ⟨3294529876815435314668019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785413004841160839114717 3294529876815435314668019)
                      ·
                        rfl

theorem cell23_6416074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_6416074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416074 prefixEnd_6416074 := by exact prefixLift 6416074
  have htrace : WordTrace (prefixWord ++ tailWord_6416074) baseStart_6416074 baseEnd_6416074 := by
    simpa [prefixWord, tailWord_6416074, baseEnd_6416074] using wordTrace_append hprefix tailTrace_6416074
  have hstable : (prefixWord ++ tailWord_6416074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416074).length < 2 ^ (prefixWord ++ tailWord_6416074).sum := by decide
  have hdescent : baseEnd_6416074 < baseStart_6416074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416092 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6416092 : Nat := 118140960795 + 6416092 * 2 ^ 59
def prefixEnd_6416092 : Nat := 4983230072969 + 3 ^ 40 * 6416092 * 2
def baseEnd_6416092 : Nat := 3294539119467216244242937

theorem tailTrace_6416092 : CollatzResearch.WordTrace tailWord_6416092 prefixEnd_6416092 3294539119467216244242937 := by
  unfold tailWord_6416092
  simp only [CollatzResearch.WordTrace]
  refine ⟨117007050135800970059553265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156009400181067960079404353 117007050135800970059553265)
  ·
    refine ⟨87755287601850727544664949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117007050135800970059553265 87755287601850727544664949)
    ·
      refine ⟨8227058212673505707312339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87755287601850727544664949 8227058212673505707312339)
      ·
        refine ⟨12340587319010258560968509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8227058212673505707312339 12340587319010258560968509)
        ·
          refine ⟨4627720244628846960363191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12340587319010258560968509 4627720244628846960363191)
          ·
            refine ⟨6941580366943270440544787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627720244628846960363191 6941580366943270440544787)
            ·
              refine ⟨10412370550414905660817181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941580366943270440544787 10412370550414905660817181)
              ·
                refine ⟨3904638956405589622806443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10412370550414905660817181 3904638956405589622806443)
                ·
                  refine ⟨5856958434608384434209665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904638956405589622806443 5856958434608384434209665)
                  ·
                    refine ⟨4392718825956288325657249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5856958434608384434209665 4392718825956288325657249)
                    ·
                      refine ⟨3294539119467216244242937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392718825956288325657249 3294539119467216244242937)
                      ·
                        rfl

theorem cell23_6416092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6416092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416092 prefixEnd_6416092 := by exact prefixLift 6416092
  have htrace : WordTrace (prefixWord ++ tailWord_6416092) baseStart_6416092 baseEnd_6416092 := by
    simpa [prefixWord, tailWord_6416092, baseEnd_6416092] using wordTrace_append hprefix tailTrace_6416092
  have hstable : (prefixWord ++ tailWord_6416092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416092).length < 2 ^ (prefixWord ++ tailWord_6416092).sum := by decide
  have hdescent : baseEnd_6416092 < baseStart_6416092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416100 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_6416100 : Nat := 118140960795 + 6416100 * 2 ^ 59
def prefixEnd_6416100 : Nat := 4983230072969 + 3 ^ 40 * 6416100 * 2
def baseEnd_6416100 : Nat := 3294543227312452212942899

theorem tailTrace_6416100 : CollatzResearch.WordTrace tailWord_6416100 prefixEnd_6416100 3294543227312452212942899 := by
  unfold tailWord_6416100
  simp only [CollatzResearch.WordTrace]
  refine ⟨117007196027786478742698877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156009594703715304990265169 117007196027786478742698877)
  ·
    refine ⟨43877698510419929528512079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117007196027786478742698877 43877698510419929528512079)
    ·
      refine ⟨65816547765629894292768119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43877698510419929528512079 65816547765629894292768119)
      ·
        refine ⟨98724821648444841439152179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65816547765629894292768119 98724821648444841439152179)
        ·
          refine ⟨148087232472667262158728269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98724821648444841439152179 148087232472667262158728269)
          ·
            refine ⟨55532712177250223309523101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148087232472667262158728269 55532712177250223309523101)
            ·
              refine ⟨20824767066468833741071163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55532712177250223309523101 20824767066468833741071163)
              ·
                refine ⟨31237150599703250611606745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20824767066468833741071163 31237150599703250611606745)
                ·
                  refine ⟨23427862949777437958705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31237150599703250611606745 23427862949777437958705059)
                  ·
                    refine ⟨35141794424666156938057589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23427862949777437958705059 35141794424666156938057589)
                    ·
                      refine ⟨3294543227312452212942899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35141794424666156938057589 3294543227312452212942899)
                      ·
                        rfl

theorem cell23_6416100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_6416100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416100 prefixEnd_6416100 := by exact prefixLift 6416100
  have htrace : WordTrace (prefixWord ++ tailWord_6416100) baseStart_6416100 baseEnd_6416100 := by
    simpa [prefixWord, tailWord_6416100, baseEnd_6416100] using wordTrace_append hprefix tailTrace_6416100
  have hstable : (prefixWord ++ tailWord_6416100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416100).length < 2 ^ (prefixWord ++ tailWord_6416100).sum := by decide
  have hdescent : baseEnd_6416100 < baseStart_6416100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416114 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6416114 : Nat := 118140960795 + 6416114 * 2 ^ 59
def prefixEnd_6416114 : Nat := 4983230072969 + 3 ^ 40 * 6416114 * 2
def baseEnd_6416114 : Nat := 3294550416041615158167835

theorem tailTrace_6416114 : CollatzResearch.WordTrace tailWord_6416114 prefixEnd_6416114 3294550416041615158167835 := by
  unfold tailWord_6416114
  simp only [CollatzResearch.WordTrace]
  refine ⟨58503725669380559469101849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156009935118348158584271597 58503725669380559469101849)
  ·
    refine ⟨43877794252035419601826387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58503725669380559469101849 43877794252035419601826387)
    ·
      refine ⟨65816691378053129402739581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43877794252035419601826387 65816691378053129402739581)
      ·
        refine ⟨24681259266769923526027343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65816691378053129402739581 24681259266769923526027343)
        ·
          refine ⟨37021888900154885289041015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24681259266769923526027343 37021888900154885289041015)
          ·
            refine ⟨55532833350232327933561523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37021888900154885289041015 55532833350232327933561523)
            ·
              refine ⟨83299250025348491900342285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55532833350232327933561523 83299250025348491900342285)
              ·
                refine ⟨31237218759505684462628357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83299250025348491900342285 31237218759505684462628357)
                ·
                  refine ⟨5856978517407315836742817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31237218759505684462628357 5856978517407315836742817)
                  ·
                    refine ⟨4392733888055486877557113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5856978517407315836742817 4392733888055486877557113)
                    ·
                      refine ⟨3294550416041615158167835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392733888055486877557113 3294550416041615158167835)
                      ·
                        rfl

theorem cell23_6416114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6416114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416114 prefixEnd_6416114 := by exact prefixLift 6416114
  have htrace : WordTrace (prefixWord ++ tailWord_6416114) baseStart_6416114 baseEnd_6416114 := by
    simpa [prefixWord, tailWord_6416114, baseEnd_6416114] using wordTrace_append hprefix tailTrace_6416114
  have hstable : (prefixWord ++ tailWord_6416114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416114).length < 2 ^ (prefixWord ++ tailWord_6416114).sum := by decide
  have hdescent : baseEnd_6416114 < baseStart_6416114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_6416123 : Nat := 118140960795 + 6416123 * 2 ^ 59
def prefixEnd_6416123 : Nat := 4983230072969 + 3 ^ 40 * 6416123 * 2
def baseEnd_6416123 : Nat := 3294555037367505622955293

theorem tailTrace_6416123 : CollatzResearch.WordTrace tailWord_6416123 prefixEnd_6416123 3294555037367505622955293 := by
  unfold tailWord_6416123
  simp only [CollatzResearch.WordTrace]
  refine ⟨234015230934489632413485023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156010153956326421608990015 234015230934489632413485023)
  ·
    refine ⟨351022846401734448620227535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234015230934489632413485023 351022846401734448620227535)
    ·
      refine ⟨526534269602601672930341303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351022846401734448620227535 526534269602601672930341303)
      ·
        refine ⟨789801404403902509395511955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526534269602601672930341303 789801404403902509395511955)
        ·
          refine ⟨1184702106605853764093267933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789801404403902509395511955 1184702106605853764093267933)
          ·
            refine ⟨444263289977195161534975475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184702106605853764093267933 444263289977195161534975475)
            ·
              refine ⟨666394934965792742302463213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444263289977195161534975475 666394934965792742302463213)
              ·
                refine ⟨249898100612172278363423705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666394934965792742302463213 249898100612172278363423705)
                ·
                  refine ⟨187423575459129208772567779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249898100612172278363423705 187423575459129208772567779)
                  ·
                    refine ⟨281135363188693813158851669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187423575459129208772567779 281135363188693813158851669)
                    ·
                      refine ⟨3294555037367505622955293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 281135363188693813158851669 3294555037367505622955293)
                      ·
                        rfl

theorem cell23_6416123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_6416123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416123 prefixEnd_6416123 := by exact prefixLift 6416123
  have htrace : WordTrace (prefixWord ++ tailWord_6416123) baseStart_6416123 baseEnd_6416123 := by
    simpa [prefixWord, tailWord_6416123, baseEnd_6416123] using wordTrace_append hprefix tailTrace_6416123
  have hstable : (prefixWord ++ tailWord_6416123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416123).length < 2 ^ (prefixWord ++ tailWord_6416123).sum := by decide
  have hdescent : baseEnd_6416123 < baseStart_6416123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416131 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 2, 2, 2]
def baseStart_6416131 : Nat := 118140960795 + 6416131 * 2 ^ 59
def prefixEnd_6416131 : Nat := 4983230072969 + 3 ^ 40 * 6416131 * 2
def baseEnd_6416131 : Nat := 3294559145212741591655257

theorem tailTrace_6416131 : CollatzResearch.WordTrace tailWord_6416131 prefixEnd_6416131 3294559145212741591655257 := by
  unfold tailWord_6416131
  simp only [CollatzResearch.WordTrace]
  refine ⟨234015522718460649779776247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156010348478973766519850831 234015522718460649779776247)
  ·
    refine ⟨351023284077690974669664371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234015522718460649779776247 351023284077690974669664371)
    ·
      refine ⟨526534926116536462004496557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351023284077690974669664371 526534926116536462004496557)
      ·
        refine ⟨197450597293701173251686209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526534926116536462004496557 197450597293701173251686209)
        ·
          refine ⟨148087947970275879938764657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197450597293701173251686209 148087947970275879938764657)
          ·
            refine ⟨111065960977706909954073493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148087947970275879938764657 111065960977706909954073493)
            ·
              refine ⟨5206216920830011404097195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111065960977706909954073493 5206216920830011404097195)
              ·
                refine ⟨7809325381245017106145793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206216920830011404097195 7809325381245017106145793)
                ·
                  refine ⟨5856994035933762829609345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7809325381245017106145793 5856994035933762829609345)
                  ·
                    refine ⟨4392745526950322122207009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5856994035933762829609345 4392745526950322122207009)
                    ·
                      refine ⟨3294559145212741591655257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392745526950322122207009 3294559145212741591655257)
                      ·
                        rfl

theorem cell23_6416131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_6416131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416131 prefixEnd_6416131 := by exact prefixLift 6416131
  have htrace : WordTrace (prefixWord ++ tailWord_6416131) baseStart_6416131 baseEnd_6416131 := by
    simpa [prefixWord, tailWord_6416131, baseEnd_6416131] using wordTrace_append hprefix tailTrace_6416131
  have hstable : (prefixWord ++ tailWord_6416131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416131).length < 2 ^ (prefixWord ++ tailWord_6416131).sum := by decide
  have hdescent : baseEnd_6416131 < baseStart_6416131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416160 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6416160 : Nat := 118140960795 + 6416160 * 2 ^ 59
def prefixEnd_6416160 : Nat := 4983230072969 + 3 ^ 40 * 6416160 * 2
def baseEnd_6416160 : Nat := 3294574036151721978192623

theorem tailTrace_6416160 : CollatzResearch.WordTrace tailWord_6416160 prefixEnd_6416160 3294574036151721978192623 := by
  unfold tailWord_6416160
  simp only [CollatzResearch.WordTrace]
  refine ⟨117008290217677793866290967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156011053623570391821721289 117008290217677793866290967)
  ·
    refine ⟨175512435326516690799436451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117008290217677793866290967 175512435326516690799436451)
    ·
      refine ⟨263268652989775036199154677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175512435326516690799436451 263268652989775036199154677)
      ·
        refine ⟨24681436217791409643670751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263268652989775036199154677 24681436217791409643670751)
        ·
          refine ⟨37022154326687114465506127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24681436217791409643670751 37022154326687114465506127)
          ·
            refine ⟨55533231490030671698259191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37022154326687114465506127 55533231490030671698259191)
            ·
              refine ⟨83299847235046007547388787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55533231490030671698259191 83299847235046007547388787)
              ·
                refine ⟨124949770852569011321083181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83299847235046007547388787 124949770852569011321083181)
                ·
                  refine ⟨46856164069713379245406193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124949770852569011321083181 46856164069713379245406193)
                  ·
                    refine ⟨35142123052285034434054645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46856164069713379245406193 35142123052285034434054645)
                    ·
                      refine ⟨3294574036151721978192623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35142123052285034434054645 3294574036151721978192623)
                      ·
                        rfl

theorem cell23_6416160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6416160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416160 prefixEnd_6416160 := by exact prefixLift 6416160
  have htrace : WordTrace (prefixWord ++ tailWord_6416160) baseStart_6416160 baseEnd_6416160 := by
    simpa [prefixWord, tailWord_6416160, baseEnd_6416160] using wordTrace_append hprefix tailTrace_6416160
  have hstable : (prefixWord ++ tailWord_6416160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416160).length < 2 ^ (prefixWord ++ tailWord_6416160).sum := by decide
  have hdescent : baseEnd_6416160 < baseStart_6416160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416197 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_6416197 : Nat := 118140960795 + 6416197 * 2 ^ 59
def prefixEnd_6416197 : Nat := 4983230072969 + 3 ^ 40 * 6416197 * 2
def baseEnd_6416197 : Nat := 1098197678311979444476651

theorem tailTrace_6416197 : CollatzResearch.WordTrace tailWord_6416197 prefixEnd_6416197 1098197678311979444476651 := by
  unfold tailWord_6416197
  simp only [CollatzResearch.WordTrace]
  refine ⟨234017929936221543051678845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156011953290814362034452563 234017929936221543051678845)
  ·
    refine ⟨87756723726083078644379567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234017929936221543051678845 87756723726083078644379567)
    ·
      refine ⟨131635085589124617966569351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87756723726083078644379567 131635085589124617966569351)
      ·
        refine ⟨197452628383686926949854027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131635085589124617966569351 197452628383686926949854027)
        ·
          refine ⟨296178942575530390424781041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197452628383686926949854027 296178942575530390424781041)
          ·
            refine ⟨222134206931647792818585781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296178942575530390424781041 222134206931647792818585781)
            ·
              refine ⟨20825081899841980576742417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222134206931647792818585781 20825081899841980576742417)
              ·
                refine ⟨15618811424881485432556813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20825081899841980576742417 15618811424881485432556813)
                ·
                  refine ⟨5857054284330557037208805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15618811424881485432556813 5857054284330557037208805)
                  ·
                    refine ⟨1098197678311979444476651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5857054284330557037208805 1098197678311979444476651)
                    ·
                      rfl

theorem cell23_6416197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_6416197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416197 prefixEnd_6416197 := by exact prefixLift 6416197
  have htrace : WordTrace (prefixWord ++ tailWord_6416197) baseStart_6416197 baseEnd_6416197 := by
    simpa [prefixWord, tailWord_6416197, baseEnd_6416197] using wordTrace_append hprefix tailTrace_6416197
  have hstable : (prefixWord ++ tailWord_6416197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416197).length < 2 ^ (prefixWord ++ tailWord_6416197).sum := by decide
  have hdescent : baseEnd_6416197 < baseStart_6416197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416227 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 8]
def baseStart_6416227 : Nat := 118140960795 + 6416227 * 2 ^ 59
def prefixEnd_6416227 : Nat := 4983230072969 + 3 ^ 40 * 6416227 * 2
def baseEnd_6416227 : Nat := 366067604372841468450535

theorem tailTrace_6416227 : CollatzResearch.WordTrace tailWord_6416227 prefixEnd_6416227 366067604372841468450535 := by
  unfold tailWord_6416227
  simp only [CollatzResearch.WordTrace]
  refine ⟨234019024126112858175270935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156012682750741905450180623 234019024126112858175270935)
  ·
    refine ⟨351028536189169287262906403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234019024126112858175270935 351028536189169287262906403)
    ·
      refine ⟨526542804283753930894359605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351028536189169287262906403 526542804283753930894359605)
      ·
        refine ⟨49363387901601931021346213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 526542804283753930894359605 49363387901601931021346213)
        ·
          refine ⟨9255635231550362066502415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49363387901601931021346213 9255635231550362066502415)
          ·
            refine ⟨13883452847325543099753623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255635231550362066502415 13883452847325543099753623)
            ·
              refine ⟨20825179270988314649630435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13883452847325543099753623 20825179270988314649630435)
              ·
                refine ⟨31237768906482471974445653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20825179270988314649630435 31237768906482471974445653)
                ·
                  refine ⟨366067604372841468450535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31237768906482471974445653 366067604372841468450535)
                  ·
                    rfl

theorem cell23_6416227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 8].length) (baseStart_6416227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416227 prefixEnd_6416227 := by exact prefixLift 6416227
  have htrace : WordTrace (prefixWord ++ tailWord_6416227) baseStart_6416227 baseEnd_6416227 := by
    simpa [prefixWord, tailWord_6416227, baseEnd_6416227] using wordTrace_append hprefix tailTrace_6416227
  have hstable : (prefixWord ++ tailWord_6416227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416227).length < 2 ^ (prefixWord ++ tailWord_6416227).sum := by decide
  have hdescent : baseEnd_6416227 < baseStart_6416227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416250 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_6416250 : Nat := 118140960795 + 6416250 * 2 ^ 59
def prefixEnd_6416250 : Nat := 4983230072969 + 3 ^ 40 * 6416250 * 2
def baseEnd_6416250 : Nat := 3294620249410626626067209

theorem tailTrace_6416250 : CollatzResearch.WordTrace tailWord_6416250 prefixEnd_6416250 3294620249410626626067209 := by
  unfold tailWord_6416250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58504965751257383275839551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156013242003353022068905469 58504965751257383275839551)
  ·
    refine ⟨87757448626886074913759327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58504965751257383275839551 87757448626886074913759327)
    ·
      refine ⟨131636172940329112370638991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87757448626886074913759327 131636172940329112370638991)
      ·
        refine ⟨197454259410493668555958487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131636172940329112370638991 197454259410493668555958487)
        ·
          refine ⟨296181389115740502833937731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197454259410493668555958487 296181389115740502833937731)
          ·
            refine ⟨444272083673610754250906597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296181389115740502833937731 444272083673610754250906597)
            ·
              refine ⟨83301015688802016422044987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 444272083673610754250906597 83301015688802016422044987)
              ·
                refine ⟨124951523533203024633067481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83301015688802016422044987 124951523533203024633067481)
                ·
                  refine ⟨93713642649902268474800611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124951523533203024633067481 93713642649902268474800611)
                  ·
                    refine ⟨140570463974853402712200917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93713642649902268474800611 140570463974853402712200917)
                    ·
                      refine ⟨3294620249410626626067209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140570463974853402712200917 3294620249410626626067209)
                      ·
                        rfl

theorem cell23_6416250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_6416250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416250 prefixEnd_6416250 := by exact prefixLift 6416250
  have htrace : WordTrace (prefixWord ++ tailWord_6416250) baseStart_6416250 baseEnd_6416250 := by
    simpa [prefixWord, tailWord_6416250, baseEnd_6416250] using wordTrace_append hprefix tailTrace_6416250
  have hstable : (prefixWord ++ tailWord_6416250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416250).length < 2 ^ (prefixWord ++ tailWord_6416250).sum := by decide
  have hdescent : baseEnd_6416250 < baseStart_6416250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416307 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4]
def baseStart_6416307 : Nat := 118140960795 + 6416307 * 2 ^ 59
def prefixEnd_6416307 : Nat := 4983230072969 + 3 ^ 40 * 6416307 * 2
def baseEnd_6416307 : Nat := 3294649517807932903054447

theorem tailTrace_6416307 : CollatzResearch.WordTrace tailWord_6416307 prefixEnd_6416307 3294649517807932903054447 := by
  unfold tailWord_6416307
  simp only [CollatzResearch.WordTrace]
  refine ⟨234021941965823031838183175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156014627977215354558788783 234021941965823031838183175)
  ·
    refine ⟨351032912948734547757274763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234021941965823031838183175 351032912948734547757274763)
    ·
      refine ⟨526549369423101821635912145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351032912948734547757274763 526549369423101821635912145)
      ·
        refine ⟨394912027067326366226934109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526549369423101821635912145 394912027067326366226934109)
        ·
          refine ⟨148092010150247387335100291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394912027067326366226934109 148092010150247387335100291)
          ·
            refine ⟨222138015225371081002650437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148092010150247387335100291 222138015225371081002650437)
            ·
              refine ⟨41650877854757077687996957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222138015225371081002650437 41650877854757077687996957)
              ·
                refine ⟨15619079195533904132998859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41650877854757077687996957 15619079195533904132998859)
                ·
                  refine ⟨23428618793300856199498289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15619079195533904132998859 23428618793300856199498289)
                  ·
                    refine ⟨17571464094975642149623717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23428618793300856199498289 17571464094975642149623717)
                    ·
                      refine ⟨3294649517807932903054447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17571464094975642149623717 3294649517807932903054447)
                      ·
                        rfl

theorem cell23_6416307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_6416307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416307 prefixEnd_6416307 := by exact prefixLift 6416307
  have htrace : WordTrace (prefixWord ++ tailWord_6416307) baseStart_6416307 baseEnd_6416307 := by
    simpa [prefixWord, tailWord_6416307, baseEnd_6416307] using wordTrace_append hprefix tailTrace_6416307
  have hstable : (prefixWord ++ tailWord_6416307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416307).length < 2 ^ (prefixWord ++ tailWord_6416307).sum := by decide
  have hdescent : baseEnd_6416307 < baseStart_6416307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416314 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_6416314 : Nat := 118140960795 + 6416314 * 2 ^ 59
def prefixEnd_6416314 : Nat := 4983230072969 + 3 ^ 40 * 6416314 * 2
def baseEnd_6416314 : Nat := 3294653112172514375666915

theorem tailTrace_6416314 : CollatzResearch.WordTrace tailWord_6416314 prefixEnd_6416314 3294653112172514375666915 := by
  unfold tailWord_6416314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58505549319199418008421999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156014798184531781355791997 58505549319199418008421999)
  ·
    refine ⟨87758323978799127012632999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58505549319199418008421999 87758323978799127012632999)
    ·
      refine ⟨131637485968198690518949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87758323978799127012632999 131637485968198690518949499)
      ·
        refine ⟨197456228952298035778424249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131637485968198690518949499 197456228952298035778424249)
        ·
          refine ⟨148092171714223526833818187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197456228952298035778424249 148092171714223526833818187)
          ·
            refine ⟨222138257571335290250727281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148092171714223526833818187 222138257571335290250727281)
            ·
              refine ⟨166603693178501467688045461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222138257571335290250727281 166603693178501467688045461)
              ·
                refine ⟨7809548117742256297877131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166603693178501467688045461 7809548117742256297877131)
                ·
                  refine ⟨11714322176613384446815697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809548117742256297877131 11714322176613384446815697)
                  ·
                    refine ⟨8785741632460038335111773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11714322176613384446815697 8785741632460038335111773)
                    ·
                      refine ⟨3294653112172514375666915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785741632460038335111773 3294653112172514375666915)
                      ·
                        rfl

theorem cell23_6416314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_6416314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416314 prefixEnd_6416314 := by exact prefixLift 6416314
  have htrace : WordTrace (prefixWord ++ tailWord_6416314) baseStart_6416314 baseEnd_6416314 := by
    simpa [prefixWord, tailWord_6416314, baseEnd_6416314] using wordTrace_append hprefix tailTrace_6416314
  have hstable : (prefixWord ++ tailWord_6416314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416314).length < 2 ^ (prefixWord ++ tailWord_6416314).sum := by decide
  have hdescent : baseEnd_6416314 < baseStart_6416314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416317 : List Nat := [1, 4, 1, 2, 3, 1, 2, 9]
def baseStart_6416317 : Nat := 118140960795 + 6416317 * 2 ^ 59
def prefixEnd_6416317 : Nat := 4983230072969 + 3 ^ 40 * 6416317 * 2
def baseEnd_6416317 : Nat := 122024246393128809775163

theorem tailTrace_6416317 : CollatzResearch.WordTrace tailWord_6416317 prefixEnd_6416317 122024246393128809775163 := by
  unfold tailWord_6416317
  simp only [CollatzResearch.WordTrace]
  refine ⟨234022306695786803546047205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156014871130524535697364803 234022306695786803546047205)
  ·
    refine ⟨43879182505460025664883851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234022306695786803546047205 43879182505460025664883851)
    ·
      refine ⟨65818773758190038497325777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43879182505460025664883851 65818773758190038497325777)
      ·
        refine ⟨49364080318642528872994333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65818773758190038497325777 49364080318642528872994333)
        ·
          refine ⟨18511530119490948327372875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49364080318642528872994333 18511530119490948327372875)
          ·
            refine ⟨27767295179236422491059313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18511530119490948327372875 27767295179236422491059313)
            ·
              refine ⟨20825471384427316868294485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27767295179236422491059313 20825471384427316868294485)
              ·
                refine ⟨122024246393128809775163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20825471384427316868294485 122024246393128809775163)
                ·
                  rfl

theorem cell23_6416317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 9].length) (baseStart_6416317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416317 prefixEnd_6416317 := by exact prefixLift 6416317
  have htrace : WordTrace (prefixWord ++ tailWord_6416317) baseStart_6416317 baseEnd_6416317 := by
    simpa [prefixWord, tailWord_6416317, baseEnd_6416317] using wordTrace_append hprefix tailTrace_6416317
  have hstable : (prefixWord ++ tailWord_6416317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416317).length < 2 ^ (prefixWord ++ tailWord_6416317).sum := by decide
  have hdescent : baseEnd_6416317 < baseStart_6416317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416331 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 1, 2, 3]
def baseStart_6416331 : Nat := 118140960795 + 6416331 * 2 ^ 59
def prefixEnd_6416331 : Nat := 4983230072969 + 3 ^ 40 * 6416331 * 2
def baseEnd_6416331 : Nat := 3294661841343640809154337

theorem tailTrace_6416331 : CollatzResearch.WordTrace tailWord_6416331 prefixEnd_6416331 3294661841343640809154337 := by
  unfold tailWord_6416331
  simp only [CollatzResearch.WordTrace]
  refine ⟨234022817317736083937056847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156015211545157389291371231 234022817317736083937056847)
  ·
    refine ⟨351034225976604125905585271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234022817317736083937056847 351034225976604125905585271)
    ·
      refine ⟨526551338964906188858377907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351034225976604125905585271 526551338964906188858377907)
      ·
        refine ⟨789827008447359283287566861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526551338964906188858377907 789827008447359283287566861)
        ·
          refine ⟨296185128167759731232837573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789827008447359283287566861 296185128167759731232837573)
          ·
            refine ⟨55534711531454949606157045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296185128167759731232837573 55534711531454949606157045)
            ·
              refine ⟨5206379206073901525577223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55534711531454949606157045 5206379206073901525577223)
              ·
                refine ⟨7809568809110852288365835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206379206073901525577223 7809568809110852288365835)
                ·
                  refine ⟨11714353213666278432548753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809568809110852288365835 11714353213666278432548753)
                  ·
                    refine ⟨8785764910249708824411565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11714353213666278432548753 8785764910249708824411565)
                    ·
                      refine ⟨3294661841343640809154337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8785764910249708824411565 3294661841343640809154337)
                      ·
                        rfl

theorem cell23_6416331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 2, 3].length) (baseStart_6416331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416331 prefixEnd_6416331 := by exact prefixLift 6416331
  have htrace : WordTrace (prefixWord ++ tailWord_6416331) baseStart_6416331 baseEnd_6416331 := by
    simpa [prefixWord, tailWord_6416331, baseEnd_6416331] using wordTrace_append hprefix tailTrace_6416331
  have hstable : (prefixWord ++ tailWord_6416331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416331).length < 2 ^ (prefixWord ++ tailWord_6416331).sum := by decide
  have hdescent : baseEnd_6416331 < baseStart_6416331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416338 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_6416338 : Nat := 118140960795 + 6416338 * 2 ^ 59
def prefixEnd_6416338 : Nat := 4983230072969 + 3 ^ 40 * 6416338 * 2
def baseEnd_6416338 : Nat := 1098221811902740760588935

theorem tailTrace_6416338 : CollatzResearch.WordTrace tailWord_6416338 prefixEnd_6416338 1098221811902740760588935 := by
  unfold tailWord_6416338
  simp only [CollatzResearch.WordTrace]
  refine ⟨58505768157177681033140417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156015381752473816088374445 58505768157177681033140417)
  ·
    refine ⟨43879326117883260774855313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58505768157177681033140417 43879326117883260774855313)
    ·
      refine ⟨32909494588412445581141485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43879326117883260774855313 32909494588412445581141485)
      ·
        refine ⟨12341060470654667092928057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32909494588412445581141485 12341060470654667092928057)
        ·
          refine ⟨9255795352991000319696043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12341060470654667092928057 9255795352991000319696043)
          ·
            refine ⟨13883693029486500479544065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255795352991000319696043 13883693029486500479544065)
            ·
              refine ⟨10412769772114875359658049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13883693029486500479544065 10412769772114875359658049)
              ·
                refine ⟨7809577329086156519743537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10412769772114875359658049 7809577329086156519743537)
                ·
                  refine ⟨5857182996814617389807653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7809577329086156519743537 5857182996814617389807653)
                  ·
                    refine ⟨1098221811902740760588935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5857182996814617389807653 1098221811902740760588935)
                    ·
                      rfl

theorem cell23_6416338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_6416338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416338 prefixEnd_6416338 := by exact prefixLift 6416338
  have htrace : WordTrace (prefixWord ++ tailWord_6416338) baseStart_6416338 baseEnd_6416338 := by
    simpa [prefixWord, tailWord_6416338, baseEnd_6416338] using wordTrace_append hprefix tailTrace_6416338
  have hstable : (prefixWord ++ tailWord_6416338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416338).length < 2 ^ (prefixWord ++ tailWord_6416338).sum := by decide
  have hdescent : baseEnd_6416338 < baseStart_6416338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416345 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 1, 2, 2]
def baseStart_6416345 : Nat := 118140960795 + 6416345 * 2 ^ 59
def prefixEnd_6416345 : Nat := 4983230072969 + 3 ^ 40 * 6416345 * 2
def baseEnd_6416345 : Nat := 3294669030072803754379273

theorem tailTrace_6416345 : CollatzResearch.WordTrace tailWord_6416345 prefixEnd_6416345 3294669030072803754379273 := by
  unfold tailWord_6416345
  simp only [CollatzResearch.WordTrace]
  refine ⟨234023327939685364328066489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156015551959790242885377659 234023327939685364328066489)
  ·
    refine ⟨175517495954764023246049867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234023327939685364328066489 175517495954764023246049867)
    ·
      refine ⟨263276243932146034869074801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175517495954764023246049867 263276243932146034869074801)
      ·
        refine ⟨197457182949109526151806101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263276243932146034869074801 197457182949109526151806101)
        ·
          refine ⟨9255805450739509038365911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197457182949109526151806101 9255805450739509038365911)
          ·
            refine ⟨13883708176109263557548867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255805450739509038365911 13883708176109263557548867)
            ·
              refine ⟨20825562264163895336323301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13883708176109263557548867 20825562264163895336323301)
              ·
                refine ⟨3904792924530730375560619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20825562264163895336323301 3904792924530730375560619)
                ·
                  refine ⟨5857189386796095563340929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904792924530730375560619 5857189386796095563340929)
                  ·
                    refine ⟨4392892040097071672505697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5857189386796095563340929 4392892040097071672505697)
                    ·
                      refine ⟨3294669030072803754379273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392892040097071672505697 3294669030072803754379273)
                      ·
                        rfl

theorem cell23_6416345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_6416345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416345 prefixEnd_6416345 := by exact prefixLift 6416345
  have htrace : WordTrace (prefixWord ++ tailWord_6416345) baseStart_6416345 baseEnd_6416345 := by
    simpa [prefixWord, tailWord_6416345, baseEnd_6416345] using wordTrace_append hprefix tailTrace_6416345
  have hstable : (prefixWord ++ tailWord_6416345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416345).length < 2 ^ (prefixWord ++ tailWord_6416345).sum := by decide
  have hdescent : baseEnd_6416345 < baseStart_6416345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416367 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_6416367 : Nat := 118140960795 + 6416367 * 2 ^ 59
def prefixEnd_6416367 : Nat := 4983230072969 + 3 ^ 40 * 6416367 * 2
def baseEnd_6416367 : Nat := 3294680326647202668304171

theorem tailTrace_6416367 : CollatzResearch.WordTrace tailWord_6416367 prefixEnd_6416367 3294680326647202668304171 := by
  unfold tailWord_6416367
  simp only [CollatzResearch.WordTrace]
  refine ⟨234024130345605662085367355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156016086897070441390244903 234024130345605662085367355)
  ·
    refine ⟨351036195518408493128051033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234024130345605662085367355 351036195518408493128051033)
    ·
      refine ⟨263277146638806369846038275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351036195518408493128051033 263277146638806369846038275)
      ·
        refine ⟨394915719958209554769057413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263277146638806369846038275 394915719958209554769057413)
        ·
          refine ⟨74046697492164291519198265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394915719958209554769057413 74046697492164291519198265)
          ·
            refine ⟨55535023119123218639398699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74046697492164291519198265 55535023119123218639398699)
            ·
              refine ⟨83302534678684827959098049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55535023119123218639398699 83302534678684827959098049)
              ·
                refine ⟨62476901009013620969323537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83302534678684827959098049 62476901009013620969323537)
                ·
                  refine ⟨46857675756760215726992653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62476901009013620969323537 46857675756760215726992653)
                  ·
                    refine ⟨17571628408785080897622245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46857675756760215726992653 17571628408785080897622245)
                    ·
                      refine ⟨3294680326647202668304171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17571628408785080897622245 3294680326647202668304171)
                      ·
                        rfl

theorem cell23_6416367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_6416367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416367 prefixEnd_6416367 := by exact prefixLift 6416367
  have htrace : WordTrace (prefixWord ++ tailWord_6416367) baseStart_6416367 baseEnd_6416367 := by
    simpa [prefixWord, tailWord_6416367, baseEnd_6416367] using wordTrace_append hprefix tailTrace_6416367
  have hstable : (prefixWord ++ tailWord_6416367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416367).length < 2 ^ (prefixWord ++ tailWord_6416367).sum := by decide
  have hdescent : baseEnd_6416367 < baseStart_6416367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416384 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2]
def baseStart_6416384 : Nat := 118140960795 + 6416384 * 2 ^ 59
def prefixEnd_6416384 : Nat := 4983230072969 + 3 ^ 40 * 6416384 * 2
def baseEnd_6416384 : Nat := 3294689055818329101791593

theorem tailTrace_6416384 : CollatzResearch.WordTrace tailWord_6416384 prefixEnd_6416384 3294689055818329101791593 := by
  unfold tailWord_6416384
  simp only [CollatzResearch.WordTrace]
  refine ⟨117012375193272036994368103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156016500257696049325824137 117012375193272036994368103)
  ·
    refine ⟨175518562789908055491552155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117012375193272036994368103 175518562789908055491552155)
    ·
      refine ⟨263277844184862083237328233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175518562789908055491552155 263277844184862083237328233)
      ·
        refine ⟨197458383138646562427996175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263277844184862083237328233 197458383138646562427996175)
        ·
          refine ⟨296187574707969843641994263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197458383138646562427996175 296187574707969843641994263)
          ·
            refine ⟨444281362061954765462991395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296187574707969843641994263 444281362061954765462991395)
            ·
              refine ⟨666422043092932148194487093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444281362061954765462991395 666422043092932148194487093)
              ·
                refine ⟨62477066539962388893233165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 666422043092932148194487093 62477066539962388893233165)
                ·
                  refine ⟨23428899952485895834962437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62477066539962388893233165 23428899952485895834962437)
                  ·
                    refine ⟨4392918741091105469055457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23428899952485895834962437 4392918741091105469055457)
                    ·
                      refine ⟨3294689055818329101791593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4392918741091105469055457 3294689055818329101791593)
                      ·
                        rfl

theorem cell23_6416384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_6416384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416384 prefixEnd_6416384 := by exact prefixLift 6416384
  have htrace : WordTrace (prefixWord ++ tailWord_6416384) baseStart_6416384 baseEnd_6416384 := by
    simpa [prefixWord, tailWord_6416384, baseEnd_6416384] using wordTrace_append hprefix tailTrace_6416384
  have hstable : (prefixWord ++ tailWord_6416384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416384).length < 2 ^ (prefixWord ++ tailWord_6416384).sum := by decide
  have hdescent : baseEnd_6416384 < baseStart_6416384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416387 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_6416387 : Nat := 118140960795 + 6416387 * 2 ^ 59
def prefixEnd_6416387 : Nat := 4983230072969 + 3 ^ 40 * 6416387 * 2
def baseEnd_6416387 : Nat := 3294690596260292590054079

theorem tailTrace_6416387 : CollatzResearch.WordTrace tailWord_6416387 prefixEnd_6416387 3294690596260292590054079 := by
  unfold tailWord_6416387
  simp only [CollatzResearch.WordTrace]
  refine ⟨234024859805533205501095415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156016573203688803667396943 234024859805533205501095415)
  ·
    refine ⟨351037289708299808251643123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234024859805533205501095415 351037289708299808251643123)
    ·
      refine ⟨526555934562449712377464685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351037289708299808251643123 526555934562449712377464685)
      ·
        refine ⟨197458475460918642141549257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526555934562449712377464685 197458475460918642141549257)
        ·
          refine ⟨148093856595688981606161943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197458475460918642141549257 148093856595688981606161943)
          ·
            refine ⟨222140784893533472409242915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148093856595688981606161943 222140784893533472409242915)
            ·
              refine ⟨333211177340300208613864373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222140784893533472409242915 333211177340300208613864373)
              ·
                refine ⟨31238547875653144557549785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 333211177340300208613864373 31238547875653144557549785)
                ·
                  refine ⟨23428910906739858418162339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31238547875653144557549785 23428910906739858418162339)
                  ·
                    refine ⟨35143366360109787627243509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23428910906739858418162339 35143366360109787627243509)
                    ·
                      refine ⟨3294690596260292590054079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35143366360109787627243509 3294690596260292590054079)
                      ·
                        rfl

theorem cell23_6416387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_6416387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416387 prefixEnd_6416387 := by exact prefixLift 6416387
  have htrace : WordTrace (prefixWord ++ tailWord_6416387) baseStart_6416387 baseEnd_6416387 := by
    simpa [prefixWord, tailWord_6416387, baseEnd_6416387] using wordTrace_append hprefix tailTrace_6416387
  have hstable : (prefixWord ++ tailWord_6416387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416387).length < 2 ^ (prefixWord ++ tailWord_6416387).sum := by decide
  have hdescent : baseEnd_6416387 < baseStart_6416387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416474 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_6416474 : Nat := 118140960795 + 6416474 * 2 ^ 59
def prefixEnd_6416474 : Nat := 4983230072969 + 3 ^ 40 * 6416474 * 2
def baseEnd_6416474 : Nat := 3294735269077233749666179

theorem tailTrace_6416474 : CollatzResearch.WordTrace tailWord_6416474 prefixEnd_6416474 3294735269077233749666179 := by
  unfold tailWord_6416474
  simp only [CollatzResearch.WordTrace]
  refine ⟨58507008239054504839878119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156018688637478679573008317 58507008239054504839878119)
  ·
    refine ⟨87760512358581757259817179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58507008239054504839878119 87760512358581757259817179)
    ·
      refine ⟨131640768537872635889725769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87760512358581757259817179 131640768537872635889725769)
      ·
        refine ⟨98730576403404476917294327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131640768537872635889725769 98730576403404476917294327)
        ·
          refine ⟨148095864605106715375941491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98730576403404476917294327 148095864605106715375941491)
          ·
            refine ⟨222143796907660073063912237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148095864605106715375941491 222143796907660073063912237)
            ·
              refine ⟨83303923840372527398967089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222143796907660073063912237 83303923840372527398967089)
              ·
                refine ⟨62477942880279395549225317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83303923840372527398967089 62477942880279395549225317)
                ·
                  refine ⟨11714614290052386665479747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62477942880279395549225317 11714614290052386665479747)
                  ·
                    refine ⟨17571921435078579998219621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11714614290052386665479747 17571921435078579998219621)
                    ·
                      refine ⟨3294735269077233749666179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17571921435078579998219621 3294735269077233749666179)
                      ·
                        rfl

theorem cell23_6416474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_6416474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416474 prefixEnd_6416474 := by exact prefixLift 6416474
  have htrace : WordTrace (prefixWord ++ tailWord_6416474) baseStart_6416474 baseEnd_6416474 := by
    simpa [prefixWord, tailWord_6416474, baseEnd_6416474] using wordTrace_append hprefix tailTrace_6416474
  have hstable : (prefixWord ++ tailWord_6416474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416474).length < 2 ^ (prefixWord ++ tailWord_6416474).sum := by decide
  have hdescent : baseEnd_6416474 < baseStart_6416474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416524 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_6416524 : Nat := 118140960795 + 6416524 * 2 ^ 59
def prefixEnd_6416524 : Nat := 4983230072969 + 3 ^ 40 * 6416524 * 2
def baseEnd_6416524 : Nat := 3294760943109958554040949

theorem tailTrace_6416524 : CollatzResearch.WordTrace tailWord_6416524 prefixEnd_6416524 3294760943109958554040949 := by
  unfold tailWord_6416524
  simp only [CollatzResearch.WordTrace]
  refine ⟨117014928303018438949416313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156019904404024585265888417 117014928303018438949416313)
  ·
    refine ⟨87761196227263829212062235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117014928303018438949416313 87761196227263829212062235)
    ·
      refine ⟨131641794340895743818093353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87761196227263829212062235 131641794340895743818093353)
      ·
        refine ⟨98731345755671807863570015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131641794340895743818093353 98731345755671807863570015)
        ·
          refine ⟨148097018633507711795355023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98731345755671807863570015 148097018633507711795355023)
          ·
            refine ⟨222145527950261567693032535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148097018633507711795355023 222145527950261567693032535)
            ·
              refine ⟨333218291925392351539548803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222145527950261567693032535 333218291925392351539548803)
              ·
                refine ⟨499827437888088527309323205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333218291925392351539548803 499827437888088527309323205)
                ·
                  refine ⟨93717644604016598870498101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499827437888088527309323205 93717644604016598870498101)
                  ·
                    refine ⟨8786029181626556144109197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93717644604016598870498101 8786029181626556144109197)
                    ·
                      refine ⟨3294760943109958554040949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786029181626556144109197 3294760943109958554040949)
                      ·
                        rfl

theorem cell23_6416524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_6416524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416524 prefixEnd_6416524 := by exact prefixLift 6416524
  have htrace : WordTrace (prefixWord ++ tailWord_6416524) baseStart_6416524 baseEnd_6416524 := by
    simpa [prefixWord, tailWord_6416524, baseEnd_6416524] using wordTrace_append hprefix tailTrace_6416524
  have hstable : (prefixWord ++ tailWord_6416524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416524).length < 2 ^ (prefixWord ++ tailWord_6416524).sum := by decide
  have hdescent : baseEnd_6416524 < baseStart_6416524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416542 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_6416542 : Nat := 118140960795 + 6416542 * 2 ^ 59
def prefixEnd_6416542 : Nat := 4983230072969 + 3 ^ 40 * 6416542 * 2
def baseEnd_6416542 : Nat := 3294770185761739483615867

theorem tailTrace_6416542 : CollatzResearch.WordTrace tailWord_6416542 prefixEnd_6416542 3294770185761739483615867 := by
  unfold tailWord_6416542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29253814139996458371623485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156020342079981111315325253 29253814139996458371623485)
  ·
    refine ⟨10970180302498671889358807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29253814139996458371623485 10970180302498671889358807)
    ·
      refine ⟨16455270453748007834038211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10970180302498671889358807 16455270453748007834038211)
      ·
        refine ⟨24682905680622011751057317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16455270453748007834038211 24682905680622011751057317)
        ·
          refine ⟨4628044815116627203323247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24682905680622011751057317 4628044815116627203323247)
          ·
            refine ⟨6942067222674940804984871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628044815116627203323247 6942067222674940804984871)
            ·
              refine ⟨10413100834012411207477307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942067222674940804984871 10413100834012411207477307)
              ·
                refine ⟨15619651251018616811215961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10413100834012411207477307 15619651251018616811215961)
                ·
                  refine ⟨11714738438263962608411971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15619651251018616811215961 11714738438263962608411971)
                  ·
                    refine ⟨17572107657395943912617957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11714738438263962608411971 17572107657395943912617957)
                    ·
                      refine ⟨3294770185761739483615867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17572107657395943912617957 3294770185761739483615867)
                      ·
                        rfl

theorem cell23_6416542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_6416542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416542 prefixEnd_6416542 := by exact prefixLift 6416542
  have htrace : WordTrace (prefixWord ++ tailWord_6416542) baseStart_6416542 baseEnd_6416542 := by
    simpa [prefixWord, tailWord_6416542, baseEnd_6416542] using wordTrace_append hprefix tailTrace_6416542
  have hstable : (prefixWord ++ tailWord_6416542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416542).length < 2 ^ (prefixWord ++ tailWord_6416542).sum := by decide
  have hdescent : baseEnd_6416542 < baseStart_6416542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416565 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 6]
def baseStart_6416565 : Nat := 118140960795 + 6416565 * 2 ^ 59
def prefixEnd_6416565 : Nat := 4983230072969 + 3 ^ 40 * 6416565 * 2
def baseEnd_6416565 : Nat := 366086888424088099292029

theorem tailTrace_6416565 : CollatzResearch.WordTrace tailWord_6416565 prefixEnd_6416565 366086888424088099292029 := by
  unfold tailWord_6416565
  simp only [CollatzResearch.WordTrace]
  refine ⟨234031351998888341901075149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156020901332592227934050099 234031351998888341901075149)
  ·
    refine ⟨87761756999583128212903181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234031351998888341901075149 87761756999583128212903181)
    ·
      refine ⟨32910658874843673079838693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87761756999583128212903181 32910658874843673079838693)
      ·
        refine ⟨6170748539033188702469755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32910658874843673079838693 6170748539033188702469755)
        ·
          refine ⟨9256122808549783053704633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170748539033188702469755 9256122808549783053704633)
          ·
            refine ⟨6942092106412337290278475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9256122808549783053704633 6942092106412337290278475)
            ·
              refine ⟨10413138159618505935417713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942092106412337290278475 10413138159618505935417713)
              ·
                refine ⟨7809853619713879451563285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10413138159618505935417713 7809853619713879451563285)
                ·
                  refine ⟨366086888424088099292029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7809853619713879451563285 366086888424088099292029)
                  ·
                    rfl

theorem cell23_6416565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_6416565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416565 prefixEnd_6416565 := by exact prefixLift 6416565
  have htrace : WordTrace (prefixWord ++ tailWord_6416565) baseStart_6416565 baseEnd_6416565 := by
    simpa [prefixWord, tailWord_6416565, baseEnd_6416565] using wordTrace_append hprefix tailTrace_6416565
  have hstable : (prefixWord ++ tailWord_6416565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416565).length < 2 ^ (prefixWord ++ tailWord_6416565).sum := by decide
  have hdescent : baseEnd_6416565 < baseStart_6416565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416601 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_6416601 : Nat := 118140960795 + 6416601 * 2 ^ 59
def prefixEnd_6416601 : Nat := 4983230072969 + 3 ^ 40 * 6416601 * 2
def baseEnd_6416601 : Nat := 3294800481120354752778095

theorem tailTrace_6416601 : CollatzResearch.WordTrace tailWord_6416601 prefixEnd_6416601 3294800481120354752778095 := by
  unfold tailWord_6416601
  simp only [CollatzResearch.WordTrace]
  refine ⟨234032665026757920049385657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156021776684505280032923771 234032665026757920049385657)
  ·
    refine ⟨175524498770068440037039243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234032665026757920049385657 175524498770068440037039243)
    ·
      refine ⟨263286748155102660055558865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175524498770068440037039243 263286748155102660055558865)
      ·
        refine ⟨197465061116326995041669149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263286748155102660055558865 197465061116326995041669149)
        ·
          refine ⟨74049397918622623140625931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197465061116326995041669149 74049397918622623140625931)
          ·
            refine ⟨111074096877933934710938897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74049397918622623140625931 111074096877933934710938897)
            ·
              refine ⟨83305572658450451033204173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111074096877933934710938897 83305572658450451033204173)
              ·
                refine ⟨31239589746918919137451565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83305572658450451033204173 31239589746918919137451565)
                ·
                  refine ⟨11714846155094594676544337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31239589746918919137451565 11714846155094594676544337)
                  ·
                    refine ⟨8786134616320946007408253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11714846155094594676544337 8786134616320946007408253)
                    ·
                      refine ⟨3294800481120354752778095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786134616320946007408253 3294800481120354752778095)
                      ·
                        rfl

theorem cell23_6416601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_6416601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416601 prefixEnd_6416601 := by exact prefixLift 6416601
  have htrace : WordTrace (prefixWord ++ tailWord_6416601) baseStart_6416601 baseEnd_6416601 := by
    simpa [prefixWord, tailWord_6416601, baseEnd_6416601] using wordTrace_append hprefix tailTrace_6416601
  have hstable : (prefixWord ++ tailWord_6416601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416601).length < 2 ^ (prefixWord ++ tailWord_6416601).sum := by decide
  have hdescent : baseEnd_6416601 < baseStart_6416601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416618 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_6416618 : Nat := 118140960795 + 6416618 * 2 ^ 59
def prefixEnd_6416618 : Nat := 4983230072969 + 3 ^ 40 * 6416618 * 2
def baseEnd_6416618 : Nat := 3294809210291481186265517

theorem tailTrace_6416618 : CollatzResearch.WordTrace tailWord_6416618 prefixEnd_6416618 3294809210291481186265517 := by
  unfold tailWord_6416618
  simp only [CollatzResearch.WordTrace]
  refine ⟨58508321266924082988188627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156022190045130887968503005 58508321266924082988188627)
  ·
    refine ⟨87762481900386124482282941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58508321266924082988188627 87762481900386124482282941)
    ·
      refine ⟨32910930712644796680856103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87762481900386124482282941 32910930712644796680856103)
      ·
        refine ⟨49366396068967195021284155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32910930712644796680856103 49366396068967195021284155)
        ·
          refine ⟨74049594103450792531926233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49366396068967195021284155 74049594103450792531926233)
          ·
            refine ⟨55537195577588094398944675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74049594103450792531926233 55537195577588094398944675)
            ·
              refine ⟨83305793366382141598417013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55537195577588094398944675 83305793366382141598417013)
              ·
                refine ⟨7809918128098325774851595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83305793366382141598417013 7809918128098325774851595)
                ·
                  refine ⟨11714877192147488662277393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809918128098325774851595 11714877192147488662277393)
                  ·
                    refine ⟨8786157894110616496708045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11714877192147488662277393 8786157894110616496708045)
                    ·
                      refine ⟨3294809210291481186265517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786157894110616496708045 3294809210291481186265517)
                      ·
                        rfl

theorem cell23_6416618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_6416618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416618 prefixEnd_6416618 := by exact prefixLift 6416618
  have htrace : WordTrace (prefixWord ++ tailWord_6416618) baseStart_6416618 baseEnd_6416618 := by
    simpa [prefixWord, tailWord_6416618, baseEnd_6416618] using wordTrace_append hprefix tailTrace_6416618
  have hstable : (prefixWord ++ tailWord_6416618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416618).length < 2 ^ (prefixWord ++ tailWord_6416618).sum := by decide
  have hdescent : baseEnd_6416618 < baseStart_6416618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416642 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6416642 : Nat := 118140960795 + 6416642 * 2 ^ 59
def prefixEnd_6416642 : Nat := 4983230072969 + 3 ^ 40 * 6416642 * 2
def baseEnd_6416642 : Nat := 1098273844609063030788469

theorem tailTrace_6416642 : CollatzResearch.WordTrace tailWord_6416642 prefixEnd_6416642 1098273844609063030788469 := by
  unfold tailWord_6416642
  simp only [CollatzResearch.WordTrace]
  refine ⟨58508540104902346012907045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156022773613072922701085453 58508540104902346012907045)
  ·
    refine ⟨10970351269669189877420071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58508540104902346012907045 10970351269669189877420071)
    ·
      refine ⟨16455526904503784816130107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10970351269669189877420071 16455526904503784816130107)
      ·
        refine ⟨24683290356755677224195161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16455526904503784816130107 24683290356755677224195161)
        ·
          refine ⟨18512467767566757918146371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24683290356755677224195161 18512467767566757918146371)
          ·
            refine ⟨27768701651350136877219557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18512467767566757918146371 27768701651350136877219557)
            ·
              refine ⟨5206631559628150664478667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27768701651350136877219557 5206631559628150664478667)
              ·
                refine ⟨7809947339442225996718001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206631559628150664478667 7809947339442225996718001)
                ·
                  refine ⟨5857460504581669497538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7809947339442225996718001 5857460504581669497538501)
                  ·
                    refine ⟨1098273844609063030788469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5857460504581669497538501 1098273844609063030788469)
                    ·
                      rfl

theorem cell23_6416642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6416642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416642 prefixEnd_6416642 := by exact prefixLift 6416642
  have htrace : WordTrace (prefixWord ++ tailWord_6416642) baseStart_6416642 baseEnd_6416642 := by
    simpa [prefixWord, tailWord_6416642, baseEnd_6416642] using wordTrace_append hprefix tailTrace_6416642
  have hstable : (prefixWord ++ tailWord_6416642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416642).length < 2 ^ (prefixWord ++ tailWord_6416642).sum := by decide
  have hdescent : baseEnd_6416642 < baseStart_6416642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416691 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3]
def baseStart_6416691 : Nat := 118140960795 + 6416691 * 2 ^ 59
def prefixEnd_6416691 : Nat := 4983230072969 + 3 ^ 40 * 6416691 * 2
def baseEnd_6416691 : Nat := 3294846694379259400652681

theorem tailTrace_6416691 : CollatzResearch.WordTrace tailWord_6416691 prefixEnd_6416691 3294846694379259400652681 := by
  unfold tailWord_6416691
  simp only [CollatzResearch.WordTrace]
  refine ⟨234035947596431865420161927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156023965064287910280107951 234035947596431865420161927)
  ·
    refine ⟨351053921394647798130242891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234035947596431865420161927 351053921394647798130242891)
    ·
      refine ⟨526580882091971697195364337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351053921394647798130242891 526580882091971697195364337)
      ·
        refine ⟨394935661568978772896523253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526580882091971697195364337 394935661568978772896523253)
        ·
          refine ⟨37025218272091759959049055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394935661568978772896523253 37025218272091759959049055)
          ·
            refine ⟨55537827408137639938573583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37025218272091759959049055 55537827408137639938573583)
            ·
              refine ⟨83306741112206459907860375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55537827408137639938573583 83306741112206459907860375)
              ·
                refine ⟨124960111668309689861790563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83306741112206459907860375 124960111668309689861790563)
                ·
                  refine ⟨187440167502464534792685845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124960111668309689861790563 187440167502464534792685845)
                  ·
                    refine ⟨8786257851678025068407149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 187440167502464534792685845 8786257851678025068407149)
                    ·
                      refine ⟨3294846694379259400652681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786257851678025068407149 3294846694379259400652681)
                      ·
                        rfl

theorem cell23_6416691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_6416691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416691 prefixEnd_6416691 := by exact prefixLift 6416691
  have htrace : WordTrace (prefixWord ++ tailWord_6416691) baseStart_6416691 baseEnd_6416691 := by
    simpa [prefixWord, tailWord_6416691, baseEnd_6416691] using wordTrace_append hprefix tailTrace_6416691
  have hstable : (prefixWord ++ tailWord_6416691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416691).length < 2 ^ (prefixWord ++ tailWord_6416691).sum := by decide
  have hdescent : baseEnd_6416691 < baseStart_6416691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416711 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 7]
def baseStart_6416711 : Nat := 118140960795 + 6416711 * 2 ^ 59
def prefixEnd_6416711 : Nat := 4983230072969 + 3 ^ 40 * 6416711 * 2
def baseEnd_6416711 : Nat := 366095218221372146933621

theorem tailTrace_6416711 : CollatzResearch.WordTrace tailWord_6416711 prefixEnd_6416711 366095218221372146933621 := by
  unfold tailWord_6416711
  simp only [CollatzResearch.WordTrace]
  refine ⟨234036677056359408835889987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156024451370906272557259991 234036677056359408835889987)
  ·
    refine ⟨351055015584539113253834981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234036677056359408835889987 351055015584539113253834981)
    ·
      refine ⟨65822815422101083735094059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351055015584539113253834981 65822815422101083735094059)
      ·
        refine ⟨98734223133151625602641089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65822815422101083735094059 98734223133151625602641089)
        ·
          refine ⟨74050667349863719201980817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98734223133151625602641089 74050667349863719201980817)
          ·
            refine ⟨55538000512397789401485613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74050667349863719201980817 55538000512397789401485613)
            ·
              refine ⟨20826750192149171025557105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55538000512397789401485613 20826750192149171025557105)
              ·
                refine ⟨15620062644111878269167829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20826750192149171025557105 15620062644111878269167829)
                ·
                  refine ⟨366095218221372146933621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15620062644111878269167829 366095218221372146933621)
                  ·
                    rfl

theorem cell23_6416711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 7].length) (baseStart_6416711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416711 prefixEnd_6416711 := by exact prefixLift 6416711
  have htrace : WordTrace (prefixWord ++ tailWord_6416711) baseStart_6416711 baseEnd_6416711 := by
    simpa [prefixWord, tailWord_6416711, baseEnd_6416711] using wordTrace_append hprefix tailTrace_6416711
  have hstable : (prefixWord ++ tailWord_6416711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416711).length < 2 ^ (prefixWord ++ tailWord_6416711).sum := by decide
  have hdescent : baseEnd_6416711 < baseStart_6416711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416791 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6416791 : Nat := 118140960795 + 6416791 * 2 ^ 59
def prefixEnd_6416791 : Nat := 4983230072969 + 3 ^ 40 * 6416791 * 2
def baseEnd_6416791 : Nat := 3294898042444709009402221

theorem tailTrace_6416791 : CollatzResearch.WordTrace tailWord_6416791 prefixEnd_6416791 3294898042444709009402221 := by
  unfold tailWord_6416791
  simp only [CollatzResearch.WordTrace]
  refine ⟨234039594896069582498802227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156026396597379721665868151 234039594896069582498802227)
  ·
    refine ⟨351059392344104373748203341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234039594896069582498802227 351059392344104373748203341)
    ·
      refine ⟨131647272129039140155576253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351059392344104373748203341 131647272129039140155576253)
      ·
        refine ⟨49367727048389677558341095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131647272129039140155576253 49367727048389677558341095)
        ·
          refine ⟨74051590572584516337511643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49367727048389677558341095 74051590572584516337511643)
          ·
            refine ⟨111077385858876774506267465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74051590572584516337511643 111077385858876774506267465)
            ·
              refine ⟨83308039394157580879700599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111077385858876774506267465 83308039394157580879700599)
              ·
                refine ⟨124962059091236371319550899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83308039394157580879700599 124962059091236371319550899)
                ·
                  refine ⟨187443088636854556979326349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124962059091236371319550899 187443088636854556979326349)
                  ·
                    refine ⟨70291158238820458867247381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187443088636854556979326349 70291158238820458867247381)
                    ·
                      refine ⟨3294898042444709009402221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70291158238820458867247381 3294898042444709009402221)
                      ·
                        rfl

theorem cell23_6416791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6416791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416791 prefixEnd_6416791 := by exact prefixLift 6416791
  have htrace : WordTrace (prefixWord ++ tailWord_6416791) baseStart_6416791 baseEnd_6416791 := by
    simpa [prefixWord, tailWord_6416791, baseEnd_6416791] using wordTrace_append hprefix tailTrace_6416791
  have hstable : (prefixWord ++ tailWord_6416791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416791).length < 2 ^ (prefixWord ++ tailWord_6416791).sum := by decide
  have hdescent : baseEnd_6416791 < baseStart_6416791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416818 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_6416818 : Nat := 118140960795 + 6416818 * 2 ^ 59
def prefixEnd_6416818 : Nat := 4983230072969 + 3 ^ 40 * 6416818 * 2
def baseEnd_6416818 : Nat := 366101322935820044862733

theorem tailTrace_6416818 : CollatzResearch.WordTrace tailWord_6416818 prefixEnd_6416818 366101322935820044862733 := by
  unfold tailWord_6416818
  simp only [CollatzResearch.WordTrace]
  refine ⟨58510144916742941527508777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156027053111314510740023405 58510144916742941527508777)
  ·
    refine ⟨43882608687557206145631583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58510144916742941527508777 43882608687557206145631583)
    ·
      refine ⟨65823913031335809218447375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43882608687557206145631583 65823913031335809218447375)
      ·
        refine ⟨98735869547003713827671063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65823913031335809218447375 98735869547003713827671063)
        ·
          refine ⟨148103804320505570741506595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98735869547003713827671063 148103804320505570741506595)
          ·
            refine ⟨222155706480758356112259893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148103804320505570741506595 222155706480758356112259893)
            ·
              refine ⟨20827097482571095885524365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222155706480758356112259893 20827097482571095885524365)
              ·
                refine ⟨7810161555964160957071637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20827097482571095885524365 7810161555964160957071637)
                ·
                  refine ⟨366101322935820044862733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7810161555964160957071637 366101322935820044862733)
                  ·
                    rfl

theorem cell23_6416818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_6416818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416818 prefixEnd_6416818 := by exact prefixLift 6416818
  have htrace : WordTrace (prefixWord ++ tailWord_6416818) baseStart_6416818 baseEnd_6416818 := by
    simpa [prefixWord, tailWord_6416818, baseEnd_6416818] using wordTrace_append hprefix tailTrace_6416818
  have hstable : (prefixWord ++ tailWord_6416818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416818).length < 2 ^ (prefixWord ++ tailWord_6416818).sum := by decide
  have hdescent : baseEnd_6416818 < baseStart_6416818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416908 : List Nat := [2, 2, 1, 2, 4, 2, 10]
def baseStart_6416908 : Nat := 118140960795 + 6416908 * 2 ^ 59
def prefixEnd_6416908 : Nat := 4983230072969 + 3 ^ 40 * 6416908 * 2
def baseEnd_6416908 : Nat := 40678495304707222859743

theorem tailTrace_6416908 : CollatzResearch.WordTrace tailWord_6416908 prefixEnd_6416908 40678495304707222859743 := by
  unfold tailWord_6416908
  simp only [CollatzResearch.WordTrace]
  refine ⟨117021931118322855740405689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156029241491097140987207585 117021931118322855740405689)
  ·
    refine ⟨87766448338742141805304267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117021931118322855740405689 87766448338742141805304267)
    ·
      refine ⟨131649672508113212707956401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87766448338742141805304267 131649672508113212707956401)
      ·
        refine ⟨98737254381084909530967301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131649672508113212707956401 98737254381084909530967301)
        ·
          refine ⟨18513235196453420537056369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98737254381084909530967301 18513235196453420537056369)
          ·
            refine ⟨13884926397340065402792277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18513235196453420537056369 13884926397340065402792277)
            ·
              refine ⟨40678495304707222859743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13884926397340065402792277 40678495304707222859743)
              ·
                rfl

theorem cell23_6416908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 10].length) (baseStart_6416908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416908 prefixEnd_6416908 := by exact prefixLift 6416908
  have htrace : WordTrace (prefixWord ++ tailWord_6416908) baseStart_6416908 baseEnd_6416908 := by
    simpa [prefixWord, tailWord_6416908, baseEnd_6416908] using wordTrace_append hprefix tailTrace_6416908
  have hstable : (prefixWord ++ tailWord_6416908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416908).length < 2 ^ (prefixWord ++ tailWord_6416908).sum := by decide
  have hdescent : baseEnd_6416908 < baseStart_6416908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416932 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6416932 : Nat := 118140960795 + 6416932 * 2 ^ 59
def prefixEnd_6416932 : Nat := 4983230072969 + 3 ^ 40 * 6416932 * 2
def baseEnd_6416932 : Nat := 3294970443216992957739073

theorem tailTrace_6416932 : CollatzResearch.WordTrace tailWord_6416932 prefixEnd_6416932 3294970443216992957739073 := by
  unfold tailWord_6416932
  simp only [CollatzResearch.WordTrace]
  refine ⟨117022368794279381789842525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156029825059039175719790033 117022368794279381789842525)
  ·
    refine ⟨43883388297854768171190947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117022368794279381789842525 43883388297854768171190947)
    ·
      refine ⟨65825082446782152256786421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43883388297854768171190947 65825082446782152256786421)
      ·
        refine ⟨6171101479385826774073727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65825082446782152256786421 6171101479385826774073727)
        ·
          refine ⟨9256652219078740161110591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171101479385826774073727 9256652219078740161110591)
          ·
            refine ⟨13884978328618110241665887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256652219078740161110591 13884978328618110241665887)
            ·
              refine ⟨20827467492927165362498831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13884978328618110241665887 20827467492927165362498831)
              ·
                refine ⟨31241201239390748043748247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20827467492927165362498831 31241201239390748043748247)
                ·
                  refine ⟨46861801859086122065622371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31241201239390748043748247 46861801859086122065622371)
                  ·
                    refine ⟨70292702788629183098433557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46861801859086122065622371 70292702788629183098433557)
                    ·
                      refine ⟨3294970443216992957739073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70292702788629183098433557 3294970443216992957739073)
                      ·
                        rfl

theorem cell23_6416932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6416932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416932 prefixEnd_6416932 := by exact prefixLift 6416932
  have htrace : WordTrace (prefixWord ++ tailWord_6416932) baseStart_6416932 baseEnd_6416932 := by
    simpa [prefixWord, tailWord_6416932, baseEnd_6416932] using wordTrace_append hprefix tailTrace_6416932
  have hstable : (prefixWord ++ tailWord_6416932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416932).length < 2 ^ (prefixWord ++ tailWord_6416932).sum := by decide
  have hdescent : baseEnd_6416932 < baseStart_6416932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416968 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_6416968 : Nat := 118140960795 + 6416968 * 2 ^ 59
def prefixEnd_6416968 : Nat := 4983230072969 + 3 ^ 40 * 6416968 * 2
def baseEnd_6416968 : Nat := 1098329642840184938962969

theorem tailTrace_6416968 : CollatzResearch.WordTrace tailWord_6416968 prefixEnd_6416968 1098329642840184938962969 := by
  unfold tailWord_6416968
  simp only [CollatzResearch.WordTrace]
  refine ⟨117023025308214170863997779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156030700410952227818663705 117023025308214170863997779)
  ·
    refine ⟨175534537962321256295996669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117023025308214170863997779 175534537962321256295996669)
    ·
      refine ⟨65825451735870471110998751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175534537962321256295996669 65825451735870471110998751)
      ·
        refine ⟨98738177603805706666498127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65825451735870471110998751 98738177603805706666498127)
        ·
          refine ⟨148107266405708559999747191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98738177603805706666498127 148107266405708559999747191)
          ·
            refine ⟨222160899608562839999620787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148107266405708559999747191 222160899608562839999620787)
            ·
              refine ⟨333241349412844259999431181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222160899608562839999620787 333241349412844259999431181)
              ·
                refine ⟨124965506029816597499786693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333241349412844259999431181 124965506029816597499786693)
                ·
                  refine ⟨23431032380590612031210005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124965506029816597499786693 23431032380590612031210005)
                  ·
                    refine ⟨1098329642840184938962969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23431032380590612031210005 1098329642840184938962969)
                    ·
                      rfl

theorem cell23_6416968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_6416968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416968 prefixEnd_6416968 := by exact prefixLift 6416968
  have htrace : WordTrace (prefixWord ++ tailWord_6416968) baseStart_6416968 baseEnd_6416968 := by
    simpa [prefixWord, tailWord_6416968, baseEnd_6416968] using wordTrace_append hprefix tailTrace_6416968
  have hstable : (prefixWord ++ tailWord_6416968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416968).length < 2 ^ (prefixWord ++ tailWord_6416968).sum := by decide
  have hdescent : baseEnd_6416968 < baseStart_6416968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6416990 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6416990 : Nat := 118140960795 + 6416990 * 2 ^ 59
def prefixEnd_6416990 : Nat := 4983230072969 + 3 ^ 40 * 6416990 * 2
def baseEnd_6416990 : Nat := 3295000225094953730813807

theorem tailTrace_6416990 : CollatzResearch.WordTrace tailWord_6416990 prefixEnd_6416990 3295000225094953730813807 := by
  unfold tailWord_6416990
  simp only [CollatzResearch.WordTrace]
  refine ⟨29255856627793579935662053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156031235348232426323530949 29255856627793579935662053)
  ·
    refine ⟨5485473117711296237936635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29255856627793579935662053 5485473117711296237936635)
    ·
      refine ⟨8228209676566944356904953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5485473117711296237936635 8228209676566944356904953)
      ·
        refine ⟨6171157257425208267678715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8228209676566944356904953 6171157257425208267678715)
        ·
          refine ⟨9256735886137812401518073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171157257425208267678715 9256735886137812401518073)
          ·
            refine ⟨6942551914603359301138555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9256735886137812401518073 6942551914603359301138555)
            ·
              refine ⟨10413827871905038951707833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942551914603359301138555 10413827871905038951707833)
              ·
                refine ⟨7810370903928779213780875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10413827871905038951707833 7810370903928779213780875)
                ·
                  refine ⟨11715556355893168820671313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810370903928779213780875 11715556355893168820671313)
                  ·
                    refine ⟨8786667266919876615503485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11715556355893168820671313 8786667266919876615503485)
                    ·
                      refine ⟨3295000225094953730813807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786667266919876615503485 3295000225094953730813807)
                      ·
                        rfl

theorem cell23_6416990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6416990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6416990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6416990 prefixEnd_6416990 := by exact prefixLift 6416990
  have htrace : WordTrace (prefixWord ++ tailWord_6416990) baseStart_6416990 baseEnd_6416990 := by
    simpa [prefixWord, tailWord_6416990, baseEnd_6416990] using wordTrace_append hprefix tailTrace_6416990
  have hstable : (prefixWord ++ tailWord_6416990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6416990).length < 2 ^ (prefixWord ++ tailWord_6416990).sum := by decide
  have hdescent : baseEnd_6416990 < baseStart_6416990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6416990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417013 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_6417013 : Nat := 118140960795 + 6417013 * 2 ^ 59
def prefixEnd_6417013 : Nat := 4983230072969 + 3 ^ 40 * 6417013 * 2
def baseEnd_6417013 : Nat := 3295012035150007140826201

theorem tailTrace_6417013 : CollatzResearch.WordTrace tailWord_6417013 prefixEnd_6417013 3295012035150007140826201 := by
  unfold tailWord_6417013
  simp only [CollatzResearch.WordTrace]
  refine ⟨234047691901265314413383693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156031794600843542942255795 234047691901265314413383693)
  ·
    refine ⟨87767884462974492905018885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234047691901265314413383693 87767884462974492905018885)
    ·
      refine ⟨16456478336807717419691041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87767884462974492905018885 16456478336807717419691041)
      ·
        refine ⟨12342358752605788064768281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16456478336807717419691041 12342358752605788064768281)
        ·
          refine ⟨9256769064454341048576211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12342358752605788064768281 9256769064454341048576211)
          ·
            refine ⟨13885153596681511572864317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256769064454341048576211 13885153596681511572864317)
            ·
              refine ⟨5206932598755566839824119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13885153596681511572864317 5206932598755566839824119)
              ·
                refine ⟨7810398898133350259736179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206932598755566839824119 7810398898133350259736179)
                ·
                  refine ⟨11715598347200025389604269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810398898133350259736179 11715598347200025389604269)
                  ·
                    refine ⟨4393349380200009521101601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11715598347200025389604269 4393349380200009521101601)
                    ·
                      refine ⟨3295012035150007140826201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393349380200009521101601 3295012035150007140826201)
                      ·
                        rfl

theorem cell23_6417013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_6417013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417013 prefixEnd_6417013 := by exact prefixLift 6417013
  have htrace : WordTrace (prefixWord ++ tailWord_6417013) baseStart_6417013 baseEnd_6417013 := by
    simpa [prefixWord, tailWord_6417013, baseEnd_6417013] using wordTrace_append hprefix tailTrace_6417013
  have hstable : (prefixWord ++ tailWord_6417013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417013).length < 2 ^ (prefixWord ++ tailWord_6417013).sum := by decide
  have hdescent : baseEnd_6417013 < baseStart_6417013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417018 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_6417018 : Nat := 118140960795 + 6417018 * 2 ^ 59
def prefixEnd_6417018 : Nat := 4983230072969 + 3 ^ 40 * 6417018 * 2
def baseEnd_6417018 : Nat := 3295014602553279621263677

theorem tailTrace_6417018 : CollatzResearch.WordTrace tailWord_6417018 prefixEnd_6417018 3295014602553279621263677 := by
  unfold tailWord_6417018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58511968566561800066828927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156031916177498133511543805 58511968566561800066828927)
  ·
    refine ⟨87767952849842700100243391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58511968566561800066828927 87767952849842700100243391)
    ·
      refine ⟨131651929274764050150365087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87767952849842700100243391 131651929274764050150365087)
      ·
        refine ⟨197477893912146075225547631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131651929274764050150365087 197477893912146075225547631)
        ·
          refine ⟨296216840868219112838321447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197477893912146075225547631 296216840868219112838321447)
          ·
            refine ⟨444325261302328669257482171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296216840868219112838321447 444325261302328669257482171)
            ·
              refine ⟨666487891953493003886223257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444325261302328669257482171 666487891953493003886223257)
              ·
                refine ⟨499865918965119752914667443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666487891953493003886223257 499865918965119752914667443)
                ·
                  refine ⟨749798878447679629372001165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 499865918965119752914667443 749798878447679629372001165)
                  ·
                    refine ⟨281174579417879861014500437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 749798878447679629372001165 281174579417879861014500437)
                    ·
                      refine ⟨3295014602553279621263677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 281174579417879861014500437 3295014602553279621263677)
                      ·
                        rfl

theorem cell23_6417018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_6417018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417018 prefixEnd_6417018 := by exact prefixLift 6417018
  have htrace : WordTrace (prefixWord ++ tailWord_6417018) baseStart_6417018 baseEnd_6417018 := by
    simpa [prefixWord, tailWord_6417018, baseEnd_6417018] using wordTrace_append hprefix tailTrace_6417018
  have hstable : (prefixWord ++ tailWord_6417018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417018).length < 2 ^ (prefixWord ++ tailWord_6417018).sum := by decide
  have hdescent : baseEnd_6417018 < baseStart_6417018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417042 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_6417042 : Nat := 118140960795 + 6417042 * 2 ^ 59
def prefixEnd_6417042 : Nat := 4983230072969 + 3 ^ 40 * 6417042 * 2
def baseEnd_6417042 : Nat := 3295026926088987527363567

theorem tailTrace_6417042 : CollatzResearch.WordTrace tailWord_6417042 prefixEnd_6417042 3295026926088987527363567 := by
  unfold tailWord_6417042
  simp only [CollatzResearch.WordTrace]
  refine ⟨58512187404540063091547345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156032499745440168244126253 58512187404540063091547345)
  ·
    refine ⟨43884140553405047318660509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58512187404540063091547345 43884140553405047318660509)
    ·
      refine ⟨16456552707526892744497691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43884140553405047318660509 16456552707526892744497691)
      ·
        refine ⟨24684829061290339116746537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16456552707526892744497691 24684829061290339116746537)
        ·
          refine ⟨18513621795967754337559903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24684829061290339116746537 18513621795967754337559903)
          ·
            refine ⟨27770432693951631506339855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18513621795967754337559903 27770432693951631506339855)
            ·
              refine ⟨41655649040927447259509783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27770432693951631506339855 41655649040927447259509783)
              ·
                refine ⟨62483473561391170889264675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41655649040927447259509783 62483473561391170889264675)
                ·
                  refine ⟨93725210342086756333897013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62483473561391170889264675 93725210342086756333897013)
                  ·
                    refine ⟨8786738469570633406302845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93725210342086756333897013 8786738469570633406302845)
                    ·
                      refine ⟨3295026926088987527363567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786738469570633406302845 3295026926088987527363567)
                      ·
                        rfl

theorem cell23_6417042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_6417042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417042 prefixEnd_6417042 := by exact prefixLift 6417042
  have htrace : WordTrace (prefixWord ++ tailWord_6417042) baseStart_6417042 baseEnd_6417042 := by
    simpa [prefixWord, tailWord_6417042, baseEnd_6417042] using wordTrace_append hprefix tailTrace_6417042
  have hstable : (prefixWord ++ tailWord_6417042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417042).length < 2 ^ (prefixWord ++ tailWord_6417042).sum := by decide
  have hdescent : baseEnd_6417042 < baseStart_6417042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417082 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_6417082 : Nat := 118140960795 + 6417082 * 2 ^ 59
def prefixEnd_6417082 : Nat := 4983230072969 + 3 ^ 40 * 6417082 * 2
def baseEnd_6417082 : Nat := 3295047465315167370863383

theorem tailTrace_6417082 : CollatzResearch.WordTrace tailWord_6417082 prefixEnd_6417082 3295047465315167370863383 := by
  unfold tailWord_6417082
  simp only [CollatzResearch.WordTrace]
  refine ⟨58512552134503834799411375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156033472358676892798430333 58512552134503834799411375)
  ·
    refine ⟨87768828201755752199117063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58512552134503834799411375 87768828201755752199117063)
    ·
      refine ⟨131653242302633628298675595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87768828201755752199117063 131653242302633628298675595)
      ·
        refine ⟨197479863453950442448013393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131653242302633628298675595 197479863453950442448013393)
        ·
          refine ⟨148109897590462831836010045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197479863453950442448013393 148109897590462831836010045)
          ·
            refine ⟨55541211596423561938503767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148109897590462831836010045 55541211596423561938503767)
            ·
              refine ⟨83311817394635342907755651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55541211596423561938503767 83311817394635342907755651)
              ·
                refine ⟨124967726091953014361633477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83311817394635342907755651 124967726091953014361633477)
                ·
                  refine ⟨23431448642241190192806277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124967726091953014361633477 23431448642241190192806277)
                  ·
                    refine ⟨4393396620420223161151177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23431448642241190192806277 4393396620420223161151177)
                    ·
                      refine ⟨3295047465315167370863383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393396620420223161151177 3295047465315167370863383)
                      ·
                        rfl

theorem cell23_6417082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_6417082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417082 prefixEnd_6417082 := by exact prefixLift 6417082
  have htrace : WordTrace (prefixWord ++ tailWord_6417082) baseStart_6417082 baseEnd_6417082 := by
    simpa [prefixWord, tailWord_6417082, baseEnd_6417082] using wordTrace_append hprefix tailTrace_6417082
  have hstable : (prefixWord ++ tailWord_6417082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417082).length < 2 ^ (prefixWord ++ tailWord_6417082).sum := by decide
  have hdescent : baseEnd_6417082 < baseStart_6417082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417102 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_6417102 : Nat := 118140960795 + 6417102 * 2 ^ 59
def prefixEnd_6417102 : Nat := 4983230072969 + 3 ^ 40 * 6417102 * 2
def baseEnd_6417102 : Nat := 3295057734928257292613291

theorem tailTrace_6417102 : CollatzResearch.WordTrace tailWord_6417102 prefixEnd_6417102 3295057734928257292613291 := by
  unfold tailWord_6417102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29256367249742860326671695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156033958665295255075582373 29256367249742860326671695)
  ·
    refine ⟨43884550874614290490007543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29256367249742860326671695 43884550874614290490007543)
    ·
      refine ⟨65826826311921435735011315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43884550874614290490007543 65826826311921435735011315)
      ·
        refine ⟨98740239467882153602516973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65826826311921435735011315 98740239467882153602516973)
        ·
          refine ⟨37027589800455807600943865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98740239467882153602516973 37027589800455807600943865)
          ·
            refine ⟨27770692350341855700707899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37027589800455807600943865 27770692350341855700707899)
            ·
              refine ⟨41656038525512783551061849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27770692350341855700707899 41656038525512783551061849)
              ·
                refine ⟨31242028894134587663296387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41656038525512783551061849 31242028894134587663296387)
                ·
                  refine ⟨46863043341201881494944581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31242028894134587663296387 46863043341201881494944581)
                  ·
                    refine ⟨8786820626475352780302109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46863043341201881494944581 8786820626475352780302109)
                    ·
                      refine ⟨3295057734928257292613291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8786820626475352780302109 3295057734928257292613291)
                      ·
                        rfl

theorem cell23_6417102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_6417102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417102 prefixEnd_6417102 := by exact prefixLift 6417102
  have htrace : WordTrace (prefixWord ++ tailWord_6417102) baseStart_6417102 baseEnd_6417102 := by
    simpa [prefixWord, tailWord_6417102, baseEnd_6417102] using wordTrace_append hprefix tailTrace_6417102
  have hstable : (prefixWord ++ tailWord_6417102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417102).length < 2 ^ (prefixWord ++ tailWord_6417102).sum := by decide
  have hdescent : baseEnd_6417102 < baseStart_6417102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417155 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_6417155 : Nat := 118140960795 + 6417155 * 2 ^ 59
def prefixEnd_6417155 : Nat := 4983230072969 + 3 ^ 40 * 6417155 * 2
def baseEnd_6417155 : Nat := 3295084949402945585250547

theorem tailTrace_6417155 : CollatzResearch.WordTrace tailWord_6417155 prefixEnd_6417155 3295084949402945585250547 := by
  unfold tailWord_6417155
  simp only [CollatzResearch.WordTrace]
  refine ⟨234052871066750872665052919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156035247377833915110035279 234052871066750872665052919)
  ·
    refine ⟨351079306600126308997579379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234052871066750872665052919 351079306600126308997579379)
    ·
      refine ⟨526618959900189463496369069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351079306600126308997579379 526618959900189463496369069)
      ·
        refine ⟨197482109962571048811138401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526618959900189463496369069 197482109962571048811138401)
        ·
          refine ⟨148111582471928286608353801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197482109962571048811138401 148111582471928286608353801)
          ·
            refine ⟨111083686853946214956265351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148111582471928286608353801 111083686853946214956265351)
            ·
              refine ⟨166625530280919322434398027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111083686853946214956265351 166625530280919322434398027)
              ·
                refine ⟨249938295421378983651597041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166625530280919322434398027 249938295421378983651597041)
                ·
                  refine ⟨187453721566034237738697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249938295421378983651597041 187453721566034237738697781)
                  ·
                    refine ⟨17573786396815709788002917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187453721566034237738697781 17573786396815709788002917)
                    ·
                      refine ⟨3295084949402945585250547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17573786396815709788002917 3295084949402945585250547)
                      ·
                        rfl

theorem cell23_6417155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_6417155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417155 prefixEnd_6417155 := by exact prefixLift 6417155
  have htrace : WordTrace (prefixWord ++ tailWord_6417155) baseStart_6417155 baseEnd_6417155 := by
    simpa [prefixWord, tailWord_6417155, baseEnd_6417155] using wordTrace_append hprefix tailTrace_6417155
  have hstable : (prefixWord ++ tailWord_6417155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417155).length < 2 ^ (prefixWord ++ tailWord_6417155).sum := by decide
  have hdescent : baseEnd_6417155 < baseStart_6417155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417186 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_6417186 : Nat := 118140960795 + 6417186 * 2 ^ 59
def prefixEnd_6417186 : Nat := 4983230072969 + 3 ^ 40 * 6417186 * 2
def baseEnd_6417186 : Nat := 1098366955767744987987635

theorem tailTrace_6417186 : CollatzResearch.WordTrace tailWord_6417186 prefixEnd_6417186 1098366955767744987987635 := by
  unfold tailWord_6417186
  simp only [CollatzResearch.WordTrace]
  refine ⟨58513500432409641239857853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156036001153092376639620941 58513500432409641239857853)
  ·
    refine ⟨21942562662153615464946695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58513500432409641239857853 21942562662153615464946695)
    ·
      refine ⟨32913843993230423197420043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21942562662153615464946695 32913843993230423197420043)
      ·
        refine ⟨49370765989845634796130065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32913843993230423197420043 49370765989845634796130065)
        ·
          refine ⟨37028074492384226097097549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49370765989845634796130065 37028074492384226097097549)
          ·
            refine ⟨13885527934644084786411581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37028074492384226097097549 13885527934644084786411581)
            ·
              refine ⟨5207072975491531794904343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13885527934644084786411581 5207072975491531794904343)
              ·
                refine ⟨7810609463237297692356515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207072975491531794904343 7810609463237297692356515)
                ·
                  refine ⟨11715914194855946538534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810609463237297692356515 11715914194855946538534773)
                  ·
                    refine ⟨1098366955767744987987635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11715914194855946538534773 1098366955767744987987635)
                    ·
                      rfl

theorem cell23_6417186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_6417186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417186 prefixEnd_6417186 := by exact prefixLift 6417186
  have htrace : WordTrace (prefixWord ++ tailWord_6417186) baseStart_6417186 baseEnd_6417186 := by
    simpa [prefixWord, tailWord_6417186, baseEnd_6417186] using wordTrace_append hprefix tailTrace_6417186
  have hstable : (prefixWord ++ tailWord_6417186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417186).length < 2 ^ (prefixWord ++ tailWord_6417186).sum := by decide
  have hdescent : baseEnd_6417186 < baseStart_6417186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417202 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6417202 : Nat := 118140960795 + 6417202 * 2 ^ 59
def prefixEnd_6417202 : Nat := 4983230072969 + 3 ^ 40 * 6417202 * 2
def baseEnd_6417202 : Nat := 3295109082993706901362831

theorem tailTrace_6417202 : CollatzResearch.WordTrace tailWord_6417202 prefixEnd_6417202 3295109082993706901362831 := by
  unfold tailWord_6417202
  simp only [CollatzResearch.WordTrace]
  refine ⟨58513646324395149923003465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156036390198387066461342573 58513646324395149923003465)
  ·
    refine ⟨43885234743296362442252599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58513646324395149923003465 43885234743296362442252599)
    ·
      refine ⟨65827852114944543663378899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43885234743296362442252599 65827852114944543663378899)
      ·
        refine ⟨98741778172416815495068349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65827852114944543663378899 98741778172416815495068349)
        ·
          refine ⟨37028166814656305810650631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98741778172416815495068349 37028166814656305810650631)
          ·
            refine ⟨55542250221984458715975947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37028166814656305810650631 55542250221984458715975947)
            ·
              refine ⟨83313375332976688073963921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55542250221984458715975947 83313375332976688073963921)
              ·
                refine ⟨62485031499732516055472941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83313375332976688073963921 62485031499732516055472941)
                ·
                  refine ⟨23431886812399693520802353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62485031499732516055472941 23431886812399693520802353)
                  ·
                    refine ⟨17573915109299770140601765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23431886812399693520802353 17573915109299770140601765)
                    ·
                      refine ⟨3295109082993706901362831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17573915109299770140601765 3295109082993706901362831)
                      ·
                        rfl

theorem cell23_6417202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6417202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417202 prefixEnd_6417202 := by exact prefixLift 6417202
  have htrace : WordTrace (prefixWord ++ tailWord_6417202) baseStart_6417202 baseEnd_6417202 := by
    simpa [prefixWord, tailWord_6417202, baseEnd_6417202] using wordTrace_append hprefix tailTrace_6417202
  have hstable : (prefixWord ++ tailWord_6417202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417202).length < 2 ^ (prefixWord ++ tailWord_6417202).sum := by decide
  have hdescent : baseEnd_6417202 < baseStart_6417202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417239 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_6417239 : Nat := 118140960795 + 6417239 * 2 ^ 59
def prefixEnd_6417239 : Nat := 4983230072969 + 3 ^ 40 * 6417239 * 2
def baseEnd_6417239 : Nat := 3295128081777923256600161

theorem tailTrace_6417239 : CollatzResearch.WordTrace tailWord_6417239 prefixEnd_6417239 3295128081777923256600161 := by
  unfold tailWord_6417239
  simp only [CollatzResearch.WordTrace]
  refine ⟨234055934798446555011110771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156037289865631036674073847 234055934798446555011110771)
  ·
    refine ⟨351083902197669832516666157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234055934798446555011110771 351083902197669832516666157)
    ·
      refine ⟨131656463324126187193749809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351083902197669832516666157 131656463324126187193749809)
      ·
        refine ⟨98742347493094640395312357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131656463324126187193749809 98742347493094640395312357)
        ·
          refine ⟨18514190154955245074121067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98742347493094640395312357 18514190154955245074121067)
          ·
            refine ⟨27771285232432867611181601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18514190154955245074121067 27771285232432867611181601)
            ·
              refine ⟨20828463924324650708386201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27771285232432867611181601 20828463924324650708386201)
              ·
                refine ⟨15621347943243488031289651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20828463924324650708386201 15621347943243488031289651)
                ·
                  refine ⟨23432021914865232046934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15621347943243488031289651 23432021914865232046934477)
                  ·
                    refine ⟨8787008218074462017600429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23432021914865232046934477 8787008218074462017600429)
                    ·
                      refine ⟨3295128081777923256600161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787008218074462017600429 3295128081777923256600161)
                      ·
                        rfl

theorem cell23_6417239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_6417239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417239 prefixEnd_6417239 := by exact prefixLift 6417239
  have htrace : WordTrace (prefixWord ++ tailWord_6417239) baseStart_6417239 baseEnd_6417239 := by
    simpa [prefixWord, tailWord_6417239, baseEnd_6417239] using wordTrace_append hprefix tailTrace_6417239
  have hstable : (prefixWord ++ tailWord_6417239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417239).length < 2 ^ (prefixWord ++ tailWord_6417239).sum := by decide
  have hdescent : baseEnd_6417239 < baseStart_6417239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417249 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_6417249 : Nat := 118140960795 + 6417249 * 2 ^ 59
def prefixEnd_6417249 : Nat := 4983230072969 + 3 ^ 40 * 6417249 * 2
def baseEnd_6417249 : Nat := 3295133216584468217475115

theorem tailTrace_6417249 : CollatzResearch.WordTrace tailWord_6417249 prefixEnd_6417249 3295133216584468217475115 := by
  unfold tailWord_6417249
  simp only [CollatzResearch.WordTrace]
  refine ⟨234056299528410326718974801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156037533018940217812649867 234056299528410326718974801)
  ·
    refine ⟨175542224646307745039231101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234056299528410326718974801 175542224646307745039231101)
    ·
      refine ⟨65828334242365404389711663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175542224646307745039231101 65828334242365404389711663)
      ·
        refine ⟨98742501363548106584567495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65828334242365404389711663 98742501363548106584567495)
        ·
          refine ⟨148113752045322159876851243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98742501363548106584567495 148113752045322159876851243)
          ·
            refine ⟨222170628067983239815276865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148113752045322159876851243 222170628067983239815276865)
            ·
              refine ⟨166627971050987429861457649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222170628067983239815276865 166627971050987429861457649)
              ·
                refine ⟨124970978288240572396093237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166627971050987429861457649 124970978288240572396093237)
                ·
                  refine ⟨11716029214522553662133741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124970978288240572396093237 11716029214522553662133741)
                  ·
                    refine ⟨4393510955445957623300153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11716029214522553662133741 4393510955445957623300153)
                    ·
                      refine ⟨3295133216584468217475115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393510955445957623300153 3295133216584468217475115)
                      ·
                        rfl

theorem cell23_6417249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_6417249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417249 prefixEnd_6417249 := by exact prefixLift 6417249
  have htrace : WordTrace (prefixWord ++ tailWord_6417249) baseStart_6417249 baseEnd_6417249 := by
    simpa [prefixWord, tailWord_6417249, baseEnd_6417249] using wordTrace_append hprefix tailTrace_6417249
  have hstable : (prefixWord ++ tailWord_6417249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417249).length < 2 ^ (prefixWord ++ tailWord_6417249).sum := by decide
  have hdescent : baseEnd_6417249 < baseStart_6417249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417250 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6417250 : Nat := 118140960795 + 6417250 * 2 ^ 59
def prefixEnd_6417250 : Nat := 4983230072969 + 3 ^ 40 * 6417250 * 2
def baseEnd_6417250 : Nat := 1098377910021707571187537

theorem tailTrace_6417250 : CollatzResearch.WordTrace tailWord_6417250 prefixEnd_6417250 1098377910021707571187537 := by
  unfold tailWord_6417250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58514084000351675972440301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156037557334271135926507469 58514084000351675972440301)
  ·
    refine ⟨21942781500131878489665113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58514084000351675972440301 21942781500131878489665113)
    ·
      refine ⟨16457086125098908867248835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21942781500131878489665113 16457086125098908867248835)
      ·
        refine ⟨24685629187648363300873253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16457086125098908867248835 24685629187648363300873253)
        ·
          refine ⟨4628555472684068118913735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24685629187648363300873253 4628555472684068118913735)
          ·
            refine ⟨6942833209026102178370603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628555472684068118913735 6942833209026102178370603)
            ·
              refine ⟨10414249813539153267555905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942833209026102178370603 10414249813539153267555905)
              ·
                refine ⟨7810687360154364950666929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10414249813539153267555905 7810687360154364950666929)
                ·
                  refine ⟨5858015520115773713000197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7810687360154364950666929 5858015520115773713000197)
                  ·
                    refine ⟨1098377910021707571187537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858015520115773713000197 1098377910021707571187537)
                    ·
                      rfl

theorem cell23_6417250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6417250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417250 prefixEnd_6417250 := by exact prefixLift 6417250
  have htrace : WordTrace (prefixWord ++ tailWord_6417250) baseStart_6417250 baseEnd_6417250 := by
    simpa [prefixWord, tailWord_6417250, baseEnd_6417250] using wordTrace_append hprefix tailTrace_6417250
  have hstable : (prefixWord ++ tailWord_6417250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417250).length < 2 ^ (prefixWord ++ tailWord_6417250).sum := by decide
  have hdescent : baseEnd_6417250 < baseStart_6417250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417256 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6417256 : Nat := 118140960795 + 6417256 * 2 ^ 59
def prefixEnd_6417256 : Nat := 4983230072969 + 3 ^ 40 * 6417256 * 2
def baseEnd_6417256 : Nat := 3295136810949049690087583

theorem tailTrace_6417256 : CollatzResearch.WordTrace tailWord_6417256 prefixEnd_6417256 3295136810949049690087583 := by
  unfold tailWord_6417256
  simp only [CollatzResearch.WordTrace]
  refine ⟨117028277419692483457239811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156037703226256644609653081 117028277419692483457239811)
  ·
    refine ⟨175542416129538725185859717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117028277419692483457239811 175542416129538725185859717)
    ·
      refine ⟨32914203024288510972348697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175542416129538725185859717 32914203024288510972348697)
      ·
        refine ⟨24685652268216383229261523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32914203024288510972348697 24685652268216383229261523)
        ·
          refine ⟨37028478402324574843892285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24685652268216383229261523 37028478402324574843892285)
          ·
            refine ⟨13885679400871715566459607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37028478402324574843892285 13885679400871715566459607)
            ·
              refine ⟨20828519101307573349689411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13885679400871715566459607 20828519101307573349689411)
              ·
                refine ⟨31242778651961360024534117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20828519101307573349689411 31242778651961360024534117)
                ·
                  refine ⟨5858020997242755004600147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31242778651961360024534117 5858020997242755004600147)
                  ·
                    refine ⟨8787031495864132506900221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858020997242755004600147 8787031495864132506900221)
                    ·
                      refine ⟨3295136810949049690087583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787031495864132506900221 3295136810949049690087583)
                      ·
                        rfl

theorem cell23_6417256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6417256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417256 prefixEnd_6417256 := by exact prefixLift 6417256
  have htrace : WordTrace (prefixWord ++ tailWord_6417256) baseStart_6417256 baseEnd_6417256 := by
    simpa [prefixWord, tailWord_6417256, baseEnd_6417256] using wordTrace_append hprefix tailTrace_6417256
  have hstable : (prefixWord ++ tailWord_6417256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417256).length < 2 ^ (prefixWord ++ tailWord_6417256).sum := by decide
  have hdescent : baseEnd_6417256 < baseStart_6417256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417273 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 2, 1, 3]
def baseStart_6417273 : Nat := 118140960795 + 6417273 * 2 ^ 59
def prefixEnd_6417273 : Nat := 4983230072969 + 3 ^ 40 * 6417273 * 2
def baseEnd_6417273 : Nat := 3295145540120176123575005

theorem tailTrace_6417273 : CollatzResearch.WordTrace tailWord_6417273 prefixEnd_6417273 3295145540120176123575005 := by
  unfold tailWord_6417273
  simp only [CollatzResearch.WordTrace]
  refine ⟨234057174880323378817848473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156038116586882252545232315 234057174880323378817848473)
  ·
    refine ⟨175542881160242534113386355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234057174880323378817848473 175542881160242534113386355)
    ·
      refine ⟨263314321740363801170079533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175542881160242534113386355 263314321740363801170079533)
      ·
        refine ⟨98742870652636425438779825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263314321740363801170079533 98742870652636425438779825)
        ·
          refine ⟨74057152989477319079084869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98742870652636425438779825 74057152989477319079084869)
          ·
            refine ⟨13885716185526997327328413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74057152989477319079084869 13885716185526997327328413)
            ·
              refine ⟨5207143569572623997748155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13885716185526997327328413 5207143569572623997748155)
              ·
                refine ⟨7810715354358935996622233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207143569572623997748155 7810715354358935996622233)
                ·
                  refine ⟨5858036515769201997466675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7810715354358935996622233 5858036515769201997466675)
                  ·
                    refine ⟨8787054773653802996200013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858036515769201997466675 8787054773653802996200013)
                    ·
                      refine ⟨3295145540120176123575005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787054773653802996200013 3295145540120176123575005)
                      ·
                        rfl

theorem cell23_6417273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_6417273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417273 prefixEnd_6417273 := by exact prefixLift 6417273
  have htrace : WordTrace (prefixWord ++ tailWord_6417273) baseStart_6417273 baseEnd_6417273 := by
    simpa [prefixWord, tailWord_6417273, baseEnd_6417273] using wordTrace_append hprefix tailTrace_6417273
  have hstable : (prefixWord ++ tailWord_6417273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417273).length < 2 ^ (prefixWord ++ tailWord_6417273).sum := by decide
  have hdescent : baseEnd_6417273 < baseStart_6417273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417292 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_6417292 : Nat := 118140960795 + 6417292 * 2 ^ 59
def prefixEnd_6417292 : Nat := 4983230072969 + 3 ^ 40 * 6417292 * 2
def baseEnd_6417292 : Nat := 3295155296252611549237417

theorem tailTrace_6417292 : CollatzResearch.WordTrace tailWord_6417292 prefixEnd_6417292 3295155296252611549237417 := by
  unfold tailWord_6417292
  simp only [CollatzResearch.WordTrace]
  refine ⟨117028933933627272531395065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156038578578169696708526753 117028933933627272531395065)
  ·
    refine ⟨87771700450220454398546299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117028933933627272531395065 87771700450220454398546299)
    ·
      refine ⟨131657550675330681597819449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87771700450220454398546299 131657550675330681597819449)
      ·
        refine ⟨98743163006498011198364587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131657550675330681597819449 98743163006498011198364587)
        ·
          refine ⟨148114744509747016797546881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98743163006498011198364587 148114744509747016797546881)
          ·
            refine ⟨111086058382310262598160161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148114744509747016797546881 111086058382310262598160161)
            ·
              refine ⟨83314543786732696948620121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111086058382310262598160161 83314543786732696948620121)
              ·
                refine ⟨62485907840049522711465091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83314543786732696948620121 62485907840049522711465091)
                ·
                  refine ⟨93728861760074284067197637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62485907840049522711465091 93728861760074284067197637)
                  ·
                    refine ⟨17574161580013928262599557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93728861760074284067197637 17574161580013928262599557)
                    ·
                      refine ⟨3295155296252611549237417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17574161580013928262599557 3295155296252611549237417)
                      ·
                        rfl

theorem cell23_6417292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_6417292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417292 prefixEnd_6417292 := by exact prefixLift 6417292
  have htrace : WordTrace (prefixWord ++ tailWord_6417292) baseStart_6417292 baseEnd_6417292 := by
    simpa [prefixWord, tailWord_6417292, baseEnd_6417292] using wordTrace_append hprefix tailTrace_6417292
  have hstable : (prefixWord ++ tailWord_6417292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417292).length < 2 ^ (prefixWord ++ tailWord_6417292).sum := by decide
  have hdescent : baseEnd_6417292 < baseStart_6417292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417313 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6417313 : Nat := 118140960795 + 6417313 * 2 ^ 59
def prefixEnd_6417313 : Nat := 4983230072969 + 3 ^ 40 * 6417313 * 2
def baseEnd_6417313 : Nat := 3295166079346355967074821

theorem tailTrace_6417313 : CollatzResearch.WordTrace tailWord_6417313 prefixEnd_6417313 3295166079346355967074821 := by
  unfold tailWord_6417313
  simp only [CollatzResearch.WordTrace]
  refine ⟨234058633800178465649304593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156039089200118977099536395 234058633800178465649304593)
  ·
    refine ⟨175543975350133849236978445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234058633800178465649304593 175543975350133849236978445)
    ·
      refine ⟨65828990756300193463866917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175543975350133849236978445 65828990756300193463866917)
      ·
        refine ⟨12342935766806286274475047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65828990756300193463866917 12342935766806286274475047)
        ·
          refine ⟨18514403650209429411712571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12342935766806286274475047 18514403650209429411712571)
          ·
            refine ⟨27771605475314144117568857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18514403650209429411712571 27771605475314144117568857)
            ·
              refine ⟨20828704106485608088176643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27771605475314144117568857 20828704106485608088176643)
              ·
                refine ⟨31243056159728412132264965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20828704106485608088176643 31243056159728412132264965)
                ·
                  refine ⟨5858073029949077274799681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31243056159728412132264965 5858073029949077274799681)
                  ·
                    refine ⟨4393554772461807956099761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858073029949077274799681 4393554772461807956099761)
                    ·
                      refine ⟨3295166079346355967074821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393554772461807956099761 3295166079346355967074821)
                      ·
                        rfl

theorem cell23_6417313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6417313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417313 prefixEnd_6417313 := by exact prefixLift 6417313
  have htrace : WordTrace (prefixWord ++ tailWord_6417313) baseStart_6417313 baseEnd_6417313 := by
    simpa [prefixWord, tailWord_6417313, baseEnd_6417313] using wordTrace_append hprefix tailTrace_6417313
  have hstable : (prefixWord ++ tailWord_6417313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417313).length < 2 ^ (prefixWord ++ tailWord_6417313).sum := by decide
  have hdescent : baseEnd_6417313 < baseStart_6417313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417386 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_6417386 : Nat := 118140960795 + 6417386 * 2 ^ 59
def prefixEnd_6417386 : Nat := 4983230072969 + 3 ^ 40 * 6417386 * 2
def baseEnd_6417386 : Nat := 3295203563434134181461985

theorem tailTrace_6417386 : CollatzResearch.WordTrace tailWord_6417386 prefixEnd_6417386 3295203563434134181461985 := by
  unfold tailWord_6417386
  simp only [CollatzResearch.WordTrace]
  refine ⟨58515324082228499779178003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156040864219275999411141341 58515324082228499779178003)
  ·
    refine ⟨87772986123342749668767005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58515324082228499779178003 87772986123342749668767005)
    ·
      refine ⟨32914869796253531125787627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87772986123342749668767005 32914869796253531125787627)
      ·
        refine ⟨49372304694380296688681441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32914869796253531125787627 49372304694380296688681441)
        ·
          refine ⟨37029228520785222516511081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49372304694380296688681441 37029228520785222516511081)
          ·
            refine ⟨27771921390588916887383311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37029228520785222516511081 27771921390588916887383311)
            ·
              refine ⟨41657882085883375331074967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27771921390588916887383311 41657882085883375331074967)
              ·
                refine ⟨62486823128825062996612451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41657882085883375331074967 62486823128825062996612451)
                ·
                  refine ⟨93730234693237594494918677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62486823128825062996612451 93730234693237594494918677)
                  ·
                    refine ⟨4393604751245512241949313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93730234693237594494918677 4393604751245512241949313)
                    ·
                      refine ⟨3295203563434134181461985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393604751245512241949313 3295203563434134181461985)
                      ·
                        rfl

theorem cell23_6417386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_6417386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417386 prefixEnd_6417386 := by exact prefixLift 6417386
  have htrace : WordTrace (prefixWord ++ tailWord_6417386) baseStart_6417386 baseEnd_6417386 := by
    simpa [prefixWord, tailWord_6417386, baseEnd_6417386] using wordTrace_append hprefix tailTrace_6417386
  have hstable : (prefixWord ++ tailWord_6417386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417386).length < 2 ^ (prefixWord ++ tailWord_6417386).sum := by decide
  have hdescent : baseEnd_6417386 < baseStart_6417386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417392 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 10]
def baseStart_6417392 : Nat := 118140960795 + 6417392 * 2 ^ 59
def prefixEnd_6417392 : Nat := 4983230072969 + 3 ^ 40 * 6417392 * 2
def baseEnd_6417392 : Nat := 366134071590895684220773

theorem tailTrace_6417392 : CollatzResearch.WordTrace tailWord_6417392 prefixEnd_6417392 366134071590895684220773 := by
  unfold tailWord_6417392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117030757583446131070715215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156041010111261508094286953 117030757583446131070715215)
  ·
    refine ⟨175546136375169196606072823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117030757583446131070715215 175546136375169196606072823)
    ·
      refine ⟨263319204562753794909109235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175546136375169196606072823 263319204562753794909109235)
      ·
        refine ⟨394978806844130692363663853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263319204562753794909109235 394978806844130692363663853)
        ·
          refine ⟨148117052566549009636373945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394978806844130692363663853 148117052566549009636373945)
          ·
            refine ⟨111087789424911757227280459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148117052566549009636373945 111087789424911757227280459)
            ·
              refine ⟨166631684137367635840920689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111087789424911757227280459 166631684137367635840920689)
              ·
                refine ⟨124973763103025726880690517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166631684137367635840920689 124973763103025726880690517)
                ·
                  refine ⟨366134071590895684220773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124973763103025726880690517 366134071590895684220773)
                  ·
                    rfl

theorem cell23_6417392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_6417392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417392 prefixEnd_6417392 := by exact prefixLift 6417392
  have htrace : WordTrace (prefixWord ++ tailWord_6417392) baseStart_6417392 baseEnd_6417392 := by
    simpa [prefixWord, tailWord_6417392, baseEnd_6417392] using wordTrace_append hprefix tailTrace_6417392
  have hstable : (prefixWord ++ tailWord_6417392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417392).length < 2 ^ (prefixWord ++ tailWord_6417392).sum := by decide
  have hdescent : baseEnd_6417392 < baseStart_6417392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417413 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_6417413 : Nat := 118140960795 + 6417413 * 2 ^ 59
def prefixEnd_6417413 : Nat := 4983230072969 + 3 ^ 40 * 6417413 * 2
def baseEnd_6417413 : Nat := 1098405809137268525274787

theorem tailTrace_6417413 : CollatzResearch.WordTrace tailWord_6417413 prefixEnd_6417413 1098405809137268525274787 := by
  unfold tailWord_6417413
  simp only [CollatzResearch.WordTrace]
  refine ⟨234062281099816182727944893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156041520733210788485296595 234062281099816182727944893)
  ·
    refine ⟨87773355412431068522979335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234062281099816182727944893 87773355412431068522979335)
    ·
      refine ⟨131660033118646602784469003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87773355412431068522979335 131660033118646602784469003)
      ·
        refine ⟨197490049677969904176703505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131660033118646602784469003 197490049677969904176703505)
        ·
          refine ⟨148117537258477428132527629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197490049677969904176703505 148117537258477428132527629)
          ·
            refine ⟨55544076471929035549697861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148117537258477428132527629 55544076471929035549697861)
            ·
              refine ⟨10414514338486694165568349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55544076471929035549697861 10414514338486694165568349)
              ·
                refine ⟨3905442876932510312088131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10414514338486694165568349 3905442876932510312088131)
                ·
                  refine ⟨5858164315398765468132197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905442876932510312088131 5858164315398765468132197)
                  ·
                    refine ⟨1098405809137268525274787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858164315398765468132197 1098405809137268525274787)
                    ·
                      rfl

theorem cell23_6417413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_6417413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417413 prefixEnd_6417413 := by exact prefixLift 6417413
  have htrace : WordTrace (prefixWord ++ tailWord_6417413) baseStart_6417413 baseEnd_6417413 := by
    simpa [prefixWord, tailWord_6417413, baseEnd_6417413] using wordTrace_append hprefix tailTrace_6417413
  have hstable : (prefixWord ++ tailWord_6417413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417413).length < 2 ^ (prefixWord ++ tailWord_6417413).sum := by decide
  have hdescent : baseEnd_6417413 < baseStart_6417413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417429 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_6417429 : Nat := 118140960795 + 6417429 * 2 ^ 59
def prefixEnd_6417429 : Nat := 4983230072969 + 3 ^ 40 * 6417429 * 2
def baseEnd_6417429 : Nat := 3295225643102277513224287

theorem tailTrace_6417429 : CollatzResearch.WordTrace tailWord_6417429 prefixEnd_6417429 3295225643102277513224287 := by
  unfold tailWord_6417429
  simp only [CollatzResearch.WordTrace]
  refine ⟨234062864667758217460527341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156041909778505478307018227 234062864667758217460527341)
  ·
    refine ⟨87773574250409331547697753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234062864667758217460527341 87773574250409331547697753)
    ·
      refine ⟨65830180687806998660773315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87773574250409331547697753 65830180687806998660773315)
      ·
        refine ⟨98745271031710497991159973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65830180687806998660773315 98745271031710497991159973)
        ·
          refine ⟨18514738318445718373342495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98745271031710497991159973 18514738318445718373342495)
          ·
            refine ⟨27772107477668577560013743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18514738318445718373342495 27772107477668577560013743)
            ·
              refine ⟨41658161216502866340020615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27772107477668577560013743 41658161216502866340020615)
              ·
                refine ⟨62487241824754299510030923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41658161216502866340020615 62487241824754299510030923)
                ·
                  refine ⟨93730862737131449265046385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62487241824754299510030923 93730862737131449265046385)
                  ·
                    refine ⟨70298147052848586948784789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93730862737131449265046385 70298147052848586948784789)
                    ·
                      refine ⟨3295225643102277513224287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70298147052848586948784789 3295225643102277513224287)
                      ·
                        rfl

theorem cell23_6417429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_6417429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417429 prefixEnd_6417429 := by exact prefixLift 6417429
  have htrace : WordTrace (prefixWord ++ tailWord_6417429) baseStart_6417429 baseEnd_6417429 := by
    simpa [prefixWord, tailWord_6417429, baseEnd_6417429] using wordTrace_append hprefix tailTrace_6417429
  have hstable : (prefixWord ++ tailWord_6417429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417429).length < 2 ^ (prefixWord ++ tailWord_6417429).sum := by decide
  have hdescent : baseEnd_6417429 < baseStart_6417429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417456 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_6417456 : Nat := 118140960795 + 6417456 * 2 ^ 59
def prefixEnd_6417456 : Nat := 4983230072969 + 3 ^ 40 * 6417456 * 2
def baseEnd_6417456 : Nat := 1098413169026649635862221

theorem tailTrace_6417456 : CollatzResearch.WordTrace tailWord_6417456 prefixEnd_6417456 1098413169026649635862221 := by
  unfold tailWord_6417456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117031924719330200535880111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156042566292440267381173481 117031924719330200535880111)
  ·
    refine ⟨175547887078995300803820167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117031924719330200535880111 175547887078995300803820167)
    ·
      refine ⟨263321830618492951205730251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175547887078995300803820167 263321830618492951205730251)
      ·
        refine ⟨394982745927739426808595377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263321830618492951205730251 394982745927739426808595377)
        ·
          refine ⟨296237059445804570106446533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394982745927739426808595377 296237059445804570106446533)
          ·
            refine ⟨55544448646088356894958725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296237059445804570106446533 55544448646088356894958725)
            ·
              refine ⟨10414584121141566917804761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55544448646088356894958725 10414584121141566917804761)
              ·
                refine ⟨7810938090856175188353571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10414584121141566917804761 7810938090856175188353571)
                ·
                  refine ⟨11716407136284262782530357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810938090856175188353571 11716407136284262782530357)
                  ·
                    refine ⟨1098413169026649635862221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11716407136284262782530357 1098413169026649635862221)
                    ·
                      rfl

theorem cell23_6417456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_6417456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417456 prefixEnd_6417456 := by exact prefixLift 6417456
  have htrace : WordTrace (prefixWord ++ tailWord_6417456) baseStart_6417456 baseEnd_6417456 := by
    simpa [prefixWord, tailWord_6417456, baseEnd_6417456] using wordTrace_append hprefix tailTrace_6417456
  have hstable : (prefixWord ++ tailWord_6417456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417456).length < 2 ^ (prefixWord ++ tailWord_6417456).sum := by decide
  have hdescent : baseEnd_6417456 < baseStart_6417456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417486 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_6417486 : Nat := 118140960795 + 6417486 * 2 ^ 59
def prefixEnd_6417486 : Nat := 4983230072969 + 3 ^ 40 * 6417486 * 2
def baseEnd_6417486 : Nat := 1098418303833194596737175

theorem tailTrace_6417486 : CollatzResearch.WordTrace tailWord_6417486 prefixEnd_6417486 1098418303833194596737175 := by
  unfold tailWord_6417486
  simp only [CollatzResearch.WordTrace]
  refine ⟨29258117953568964524419039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156043295752367810796901541 29258117953568964524419039)
  ·
    refine ⟨43887176930353446786628559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29258117953568964524419039 43887176930353446786628559)
    ·
      refine ⟨65830765395530170179942839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43887176930353446786628559 65830765395530170179942839)
      ·
        refine ⟨98746148093295255269914259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65830765395530170179942839 98746148093295255269914259)
        ·
          refine ⟨148119222139942882904871389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98746148093295255269914259 148119222139942882904871389)
          ·
            refine ⟨55544708302478581089326771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148119222139942882904871389 55544708302478581089326771)
            ·
              refine ⟨83317062453717871633990157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55544708302478581089326771 83317062453717871633990157)
              ·
                refine ⟨31243898420144201862746309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83317062453717871633990157 31243898420144201862746309)
                ·
                  refine ⟨5858230953777037849264933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31243898420144201862746309 5858230953777037849264933)
                  ·
                    refine ⟨1098418303833194596737175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858230953777037849264933 1098418303833194596737175)
                    ·
                      rfl

theorem cell23_6417486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_6417486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417486 prefixEnd_6417486 := by exact prefixLift 6417486
  have htrace : WordTrace (prefixWord ++ tailWord_6417486) baseStart_6417486 baseEnd_6417486 := by
    simpa [prefixWord, tailWord_6417486, baseEnd_6417486] using wordTrace_append hprefix tailTrace_6417486
  have hstable : (prefixWord ++ tailWord_6417486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417486).length < 2 ^ (prefixWord ++ tailWord_6417486).sum := by decide
  have hdescent : baseEnd_6417486 < baseStart_6417486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417489 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_6417489 : Nat := 118140960795 + 6417489 * 2 ^ 59
def prefixEnd_6417489 : Nat := 4983230072969 + 3 ^ 40 * 6417489 * 2
def baseEnd_6417489 : Nat := 3295256451941547278474011

theorem tailTrace_6417489 : CollatzResearch.WordTrace tailWord_6417489 prefixEnd_6417489 3295256451941547278474011 := by
  unfold tailWord_6417489
  simp only [CollatzResearch.WordTrace]
  refine ⟨234065053047540847707711521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156043368698360565138474347 234065053047540847707711521)
  ·
    refine ⟨175548789785655635780783641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234065053047540847707711521 175548789785655635780783641)
    ·
      refine ⟨131661592339241726835587731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175548789785655635780783641 131661592339241726835587731)
      ·
        refine ⟨197492388508862590253381597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131661592339241726835587731 197492388508862590253381597)
        ·
          refine ⟨74059645690823471345018099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197492388508862590253381597 74059645690823471345018099)
          ·
            refine ⟨111089468536235207017527149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74059645690823471345018099 111089468536235207017527149)
            ·
              refine ⟨41658550701088202631572681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111089468536235207017527149 41658550701088202631572681)
              ·
                refine ⟨31243913025816151973679511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41658550701088202631572681 31243913025816151973679511)
                ·
                  refine ⟨46865869538724227960519267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31243913025816151973679511 46865869538724227960519267)
                  ·
                    refine ⟨70298804308086341940778901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46865869538724227960519267 70298804308086341940778901)
                    ·
                      refine ⟨3295256451941547278474011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70298804308086341940778901 3295256451941547278474011)
                      ·
                        rfl

theorem cell23_6417489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_6417489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417489 prefixEnd_6417489 := by exact prefixLift 6417489
  have htrace : WordTrace (prefixWord ++ tailWord_6417489) baseStart_6417489 baseEnd_6417489 := by
    simpa [prefixWord, tailWord_6417489, baseEnd_6417489] using wordTrace_append hprefix tailTrace_6417489
  have hstable : (prefixWord ++ tailWord_6417489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417489).length < 2 ^ (prefixWord ++ tailWord_6417489).sum := by decide
  have hdescent : baseEnd_6417489 < baseStart_6417489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417494 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_6417494 : Nat := 118140960795 + 6417494 * 2 ^ 59
def prefixEnd_6417494 : Nat := 4983230072969 + 3 ^ 40 * 6417494 * 2
def baseEnd_6417494 : Nat := 366139891038313306545721

theorem tailTrace_6417494 : CollatzResearch.WordTrace tailWord_6417494 prefixEnd_6417494 366139891038313306545721 := by
  unfold tailWord_6417494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14629077213282670847602721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156043490275015155707762357 14629077213282670847602721)
  ·
    refine ⟨10971807909962003135702041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14629077213282670847602721 10971807909962003135702041)
    ·
      refine ⟨8228855932471502351776531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10971807909962003135702041 8228855932471502351776531)
      ·
        refine ⟨12343283898707253527664797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8228855932471502351776531 12343283898707253527664797)
        ·
          refine ⟨4628731462015220072874299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12343283898707253527664797 4628731462015220072874299)
          ·
            refine ⟨6943097193022830109311449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628731462015220072874299 6943097193022830109311449)
            ·
              refine ⟨5207322894767122581983587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6943097193022830109311449 5207322894767122581983587)
              ·
                refine ⟨7810984342150683872975381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207322894767122581983587 7810984342150683872975381)
                ·
                  refine ⟨366139891038313306545721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7810984342150683872975381 366139891038313306545721)
                  ·
                    rfl

theorem cell23_6417494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_6417494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417494 prefixEnd_6417494 := by exact prefixLift 6417494
  have htrace : WordTrace (prefixWord ++ tailWord_6417494) baseStart_6417494 baseEnd_6417494 := by
    simpa [prefixWord, tailWord_6417494, baseEnd_6417494] using wordTrace_append hprefix tailTrace_6417494
  have hstable : (prefixWord ++ tailWord_6417494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417494).length < 2 ^ (prefixWord ++ tailWord_6417494).sum := by decide
  have hdescent : baseEnd_6417494 < baseStart_6417494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417496 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_6417496 : Nat := 118140960795 + 6417496 * 2 ^ 59
def prefixEnd_6417496 : Nat := 4983230072969 + 3 ^ 40 * 6417496 * 2
def baseEnd_6417496 : Nat := 3295260046306128751086479

theorem tailTrace_6417496 : CollatzResearch.WordTrace tailWord_6417496 prefixEnd_6417496 3295260046306128751086479 := by
  unfold tailWord_6417496
  simp only [CollatzResearch.WordTrace]
  refine ⟨117032654179257743951608171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156043538905676991935477561 117032654179257743951608171)
  ·
    refine ⟨175548981268886615927412257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117032654179257743951608171 175548981268886615927412257)
    ·
      refine ⟨131661735951664961945559193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175548981268886615927412257 131661735951664961945559193)
      ·
        refine ⟨98746301963748721459169395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131661735951664961945559193 98746301963748721459169395)
        ·
          refine ⟨148119452945623082188754093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98746301963748721459169395 148119452945623082188754093)
          ·
            refine ⟨55544794854608655820782785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148119452945623082188754093 55544794854608655820782785)
            ·
              refine ⟨41658596140956491865587089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55544794854608655820782785 41658596140956491865587089)
              ·
                refine ⟨31243947105717368899190317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41658596140956491865587089 31243947105717368899190317)
                ·
                  refine ⟨11716480164644013337196369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31243947105717368899190317 11716480164644013337196369)
                  ·
                    refine ⟨8787360123483010002897277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11716480164644013337196369 8787360123483010002897277)
                    ·
                      refine ⟨3295260046306128751086479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787360123483010002897277 3295260046306128751086479)
                      ·
                        rfl

theorem cell23_6417496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_6417496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417496 prefixEnd_6417496 := by exact prefixLift 6417496
  have htrace : WordTrace (prefixWord ++ tailWord_6417496) baseStart_6417496 baseEnd_6417496 := by
    simpa [prefixWord, tailWord_6417496, baseEnd_6417496] using wordTrace_append hprefix tailTrace_6417496
  have hstable : (prefixWord ++ tailWord_6417496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417496).length < 2 ^ (prefixWord ++ tailWord_6417496).sum := by decide
  have hdescent : baseEnd_6417496 < baseStart_6417496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417513 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_6417513 : Nat := 118140960795 + 6417513 * 2 ^ 59
def prefixEnd_6417513 : Nat := 4983230072969 + 3 ^ 40 * 6417513 * 2
def baseEnd_6417513 : Nat := 3295268775477255184573901

theorem tailTrace_6417513 : CollatzResearch.WordTrace tailWord_6417513 prefixEnd_6417513 3295268775477255184573901 := by
  unfold tailWord_6417513
  simp only [CollatzResearch.WordTrace]
  refine ⟨234065928399453899806585193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156043952266302599871056795 234065928399453899806585193)
  ·
    refine ⟨175549446299590424854938895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234065928399453899806585193 175549446299590424854938895)
    ·
      refine ⟨263324169449385637282408343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175549446299590424854938895 263324169449385637282408343)
      ·
        refine ⟨394986254174078455923612515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263324169449385637282408343 394986254174078455923612515)
        ·
          refine ⟨592479381261117683885418773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394986254174078455923612515 592479381261117683885418773)
          ·
            refine ⟨27772470996614891432129005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 592479381261117683885418773 27772470996614891432129005)
            ·
              refine ⟨10414676623730584287048377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27772470996614891432129005 10414676623730584287048377)
              ·
                refine ⟨7811007467797938215286283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10414676623730584287048377 7811007467797938215286283)
                ·
                  refine ⟨11716511201696907322929425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811007467797938215286283 11716511201696907322929425)
                  ·
                    refine ⟨8787383401272680492197069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11716511201696907322929425 8787383401272680492197069)
                    ·
                      refine ⟨3295268775477255184573901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787383401272680492197069 3295268775477255184573901)
                      ·
                        rfl

theorem cell23_6417513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_6417513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417513 prefixEnd_6417513 := by exact prefixLift 6417513
  have htrace : WordTrace (prefixWord ++ tailWord_6417513) baseStart_6417513 baseEnd_6417513 := by
    simpa [prefixWord, tailWord_6417513, baseEnd_6417513] using wordTrace_append hprefix tailTrace_6417513
  have hstable : (prefixWord ++ tailWord_6417513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417513).length < 2 ^ (prefixWord ++ tailWord_6417513).sum := by decide
  have hdescent : baseEnd_6417513 < baseStart_6417513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417544 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6417544 : Nat := 118140960795 + 6417544 * 2 ^ 59
def prefixEnd_6417544 : Nat := 4983230072969 + 3 ^ 40 * 6417544 * 2
def baseEnd_6417544 : Nat := 3295284693377544563286259

theorem tailTrace_6417544 : CollatzResearch.WordTrace tailWord_6417544 prefixEnd_6417544 3295284693377544563286259 := by
  unfold tailWord_6417544
  simp only [CollatzResearch.WordTrace]
  refine ⟨117033529531170796050481843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156044706041561061400642457 117033529531170796050481843)
  ·
    refine ⟨175550294296756194075722765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117033529531170796050481843 175550294296756194075722765)
    ·
      refine ⟨65831360361283572778396037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175550294296756194075722765 65831360361283572778396037)
      ·
        refine ⟨12343380067740669895949257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65831360361283572778396037 12343380067740669895949257)
        ·
          refine ⟨9257535050805502421961943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12343380067740669895949257 9257535050805502421961943)
          ·
            refine ⟨13886302576208253632942915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9257535050805502421961943 13886302576208253632942915)
            ·
              refine ⟨20829453864312380449414373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886302576208253632942915 20829453864312380449414373)
              ·
                refine ⟨3905522599558571334265195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20829453864312380449414373 3905522599558571334265195)
                ·
                  refine ⟨5858283899337857001397793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905522599558571334265195 5858283899337857001397793)
                  ·
                    refine ⟨4393712924503392751048345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858283899337857001397793 4393712924503392751048345)
                    ·
                      refine ⟨3295284693377544563286259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393712924503392751048345 3295284693377544563286259)
                      ·
                        rfl

theorem cell23_6417544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6417544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417544 prefixEnd_6417544 := by exact prefixLift 6417544
  have htrace : WordTrace (prefixWord ++ tailWord_6417544) baseStart_6417544 baseEnd_6417544 := by
    simpa [prefixWord, tailWord_6417544, baseEnd_6417544] using wordTrace_append hprefix tailTrace_6417544
  have hstable : (prefixWord ++ tailWord_6417544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417544).length < 2 ^ (prefixWord ++ tailWord_6417544).sum := by decide
  have hdescent : baseEnd_6417544 < baseStart_6417544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417560 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6417560 : Nat := 118140960795 + 6417560 * 2 ^ 59
def prefixEnd_6417560 : Nat := 4983230072969 + 3 ^ 40 * 6417560 * 2
def baseEnd_6417560 : Nat := 3295292909068016500686185

theorem tailTrace_6417560 : CollatzResearch.WordTrace tailWord_6417560 prefixEnd_6417560 3295292909068016500686185 := by
  unfold tailWord_6417560
  simp only [CollatzResearch.WordTrace]
  refine ⟨117033821315141813416773067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156045095086855751222364089 117033821315141813416773067)
  ·
    refine ⟨175550731972712720125159601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117033821315141813416773067 175550731972712720125159601)
    ·
      refine ⟨131663048979534540093869701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175550731972712720125159601 131663048979534540093869701)
      ·
        refine ⟨24686821683662726267600569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131663048979534540093869701 24686821683662726267600569)
        ·
          refine ⟨18515116262747044700700427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24686821683662726267600569 18515116262747044700700427)
          ·
            refine ⟨27772674394120567051050641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18515116262747044700700427 27772674394120567051050641)
            ·
              refine ⟨20829505795590425288287981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27772674394120567051050641 20829505795590425288287981)
              ·
                refine ⟨7811064673346409483107993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20829505795590425288287981 7811064673346409483107993)
                ·
                  refine ⟨5858298505009807112330995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7811064673346409483107993 5858298505009807112330995)
                  ·
                    refine ⟨8787447757514710668496493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858298505009807112330995 8787447757514710668496493)
                    ·
                      refine ⟨3295292909068016500686185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787447757514710668496493 3295292909068016500686185)
                      ·
                        rfl

theorem cell23_6417560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6417560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417560 prefixEnd_6417560 := by exact prefixLift 6417560
  have htrace : WordTrace (prefixWord ++ tailWord_6417560) baseStart_6417560 baseEnd_6417560 := by
    simpa [prefixWord, tailWord_6417560, baseEnd_6417560] using wordTrace_append hprefix tailTrace_6417560
  have hstable : (prefixWord ++ tailWord_6417560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417560).length < 2 ^ (prefixWord ++ tailWord_6417560).sum := by decide
  have hdescent : baseEnd_6417560 < baseStart_6417560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417583 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 1, 4, 2]
def baseStart_6417583 : Nat := 118140960795 + 6417583 * 2 ^ 59
def prefixEnd_6417583 : Nat := 4983230072969 + 3 ^ 40 * 6417583 * 2
def baseEnd_6417583 : Nat := 3295304719123069910698579

theorem tailTrace_6417583 : CollatzResearch.WordTrace tailWord_6417583 prefixEnd_6417583 3295304719123069910698579 := by
  unfold tailWord_6417583
  simp only [CollatzResearch.WordTrace]
  refine ⟨234068481509200301761633403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156045654339466867841088935 234068481509200301761633403)
  ·
    refine ⟨351102722263800452642450105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234068481509200301761633403 351102722263800452642450105)
    ·
      refine ⟨263327041697850339481837579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351102722263800452642450105 263327041697850339481837579)
      ·
        refine ⟨394990562546775509222756369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263327041697850339481837579 394990562546775509222756369)
        ·
          refine ⟨296242921910081631917067277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394990562546775509222756369 296242921910081631917067277)
          ·
            refine ⟨111091095716280611968900229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296242921910081631917067277 111091095716280611968900229)
            ·
              refine ⟨20829580446802614744168793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111091095716280611968900229 20829580446802614744168793)
              ·
                refine ⟨15622185335101961058126595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20829580446802614744168793 15622185335101961058126595)
                ·
                  refine ⟨23433278002652941587189893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15622185335101961058126595 23433278002652941587189893)
                  ·
                    refine ⟨4393739625497426547598105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23433278002652941587189893 4393739625497426547598105)
                    ·
                      refine ⟨3295304719123069910698579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393739625497426547598105 3295304719123069910698579)
                      ·
                        rfl

theorem cell23_6417583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4, 2].length) (baseStart_6417583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417583 prefixEnd_6417583 := by exact prefixLift 6417583
  have htrace : WordTrace (prefixWord ++ tailWord_6417583) baseStart_6417583 baseEnd_6417583 := by
    simpa [prefixWord, tailWord_6417583, baseEnd_6417583] using wordTrace_append hprefix tailTrace_6417583
  have hstable : (prefixWord ++ tailWord_6417583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417583).length < 2 ^ (prefixWord ++ tailWord_6417583).sum := by decide
  have hdescent : baseEnd_6417583 < baseStart_6417583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417636 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_6417636 : Nat := 118140960795 + 6417636 * 2 ^ 59
def prefixEnd_6417636 : Nat := 4983230072969 + 3 ^ 40 * 6417636 * 2
def baseEnd_6417636 : Nat := 1098443977865919401111945

theorem tailTrace_6417636 : CollatzResearch.WordTrace tailWord_6417636 prefixEnd_6417636 1098443977865919401111945 := by
  unfold tailWord_6417636
  simp only [CollatzResearch.WordTrace]
  refine ⟨117035207289004145906656381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156046943052005527875541841 117035207289004145906656381)
  ·
    refine ⟨43888202733376554714996143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117035207289004145906656381 43888202733376554714996143)
    ·
      refine ⟨65832304100064832072494215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43888202733376554714996143 65832304100064832072494215)
      ·
        refine ⟨98748456150097248108741323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65832304100064832072494215 98748456150097248108741323)
        ·
          refine ⟨148122684225145872163111985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98748456150097248108741323 148122684225145872163111985)
          ·
            refine ⟨111092013168859404122333989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148122684225145872163111985 111092013168859404122333989)
            ·
              refine ⟨20829752469161138272937623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111092013168859404122333989 20829752469161138272937623)
              ·
                refine ⟨31244628703741707409406435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20829752469161138272937623 31244628703741707409406435)
                ·
                  refine ⟨46866943055612561114109653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31244628703741707409406435 46866943055612561114109653)
                  ·
                    refine ⟨1098443977865919401111945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46866943055612561114109653 1098443977865919401111945)
                    ·
                      rfl

theorem cell23_6417636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_6417636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417636 prefixEnd_6417636 := by exact prefixLift 6417636
  have htrace : WordTrace (prefixWord ++ tailWord_6417636) baseStart_6417636 baseEnd_6417636 := by
    simpa [prefixWord, tailWord_6417636, baseEnd_6417636] using wordTrace_append hprefix tailTrace_6417636
  have hstable : (prefixWord ++ tailWord_6417636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417636).length < 2 ^ (prefixWord ++ tailWord_6417636).sum := by decide
  have hdescent : baseEnd_6417636 < baseStart_6417636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417673 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 6, 2]
def baseStart_6417673 : Nat := 118140960795 + 6417673 * 2 ^ 59
def prefixEnd_6417673 : Nat := 4983230072969 + 3 ^ 40 * 6417673 * 2
def baseEnd_6417673 : Nat := 3295350932381974558573165

theorem tailTrace_6417673 : CollatzResearch.WordTrace tailWord_6417673 prefixEnd_6417673 3295350932381974558573165 := by
  unfold tailWord_6417673
  simp only [CollatzResearch.WordTrace]
  refine ⟨234071764078874247132409673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156047842719249498088273115 234071764078874247132409673)
  ·
    refine ⟨175553823059155685349307255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234071764078874247132409673 175553823059155685349307255)
    ·
      refine ⟨263330734588733528023960883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175553823059155685349307255 263330734588733528023960883)
      ·
        refine ⟨394996101883100292035941325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263330734588733528023960883 394996101883100292035941325)
        ·
          refine ⟨148123538206162609513477997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394996101883100292035941325 148123538206162609513477997)
          ·
            refine ⟨55546326827310978567554249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148123538206162609513477997 55546326827310978567554249)
            ·
              refine ⟨41659745120483233925665687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55546326827310978567554249 41659745120483233925665687)
              ·
                refine ⟨62489617680724850888498531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41659745120483233925665687 62489617680724850888498531)
                ·
                  refine ⟨93734426521087276332747797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62489617680724850888498531 93734426521087276332747797)
                  ·
                    refine ⟨4393801243175966078097553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93734426521087276332747797 4393801243175966078097553)
                    ·
                      refine ⟨3295350932381974558573165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393801243175966078097553 3295350932381974558573165)
                      ·
                        rfl

theorem cell23_6417673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 6, 2].length) (baseStart_6417673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417673 prefixEnd_6417673 := by exact prefixLift 6417673
  have htrace : WordTrace (prefixWord ++ tailWord_6417673) baseStart_6417673 baseEnd_6417673 := by
    simpa [prefixWord, tailWord_6417673, baseEnd_6417673] using wordTrace_append hprefix tailTrace_6417673
  have hstable : (prefixWord ++ tailWord_6417673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417673).length < 2 ^ (prefixWord ++ tailWord_6417673).sum := by decide
  have hdescent : baseEnd_6417673 < baseStart_6417673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417690 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_6417690 : Nat := 118140960795 + 6417690 * 2 ^ 59
def prefixEnd_6417690 : Nat := 4983230072969 + 3 ^ 40 * 6417690 * 2
def baseEnd_6417690 : Nat := 3295359661553100992060587

theorem tailTrace_6417690 : CollatzResearch.WordTrace tailWord_6417690 prefixEnd_6417690 3295359661553100992060587 := by
  unfold tailWord_6417690
  simp only [CollatzResearch.WordTrace]
  refine ⟨58518096029953164758944631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156048256079875106023852349 58518096029953164758944631)
  ·
    refine ⟨87777144044929747138416947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58518096029953164758944631 87777144044929747138416947)
    ·
      refine ⟨131665716067394620707625421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87777144044929747138416947 131665716067394620707625421)
      ·
        refine ⟨49374643525272982765359533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131665716067394620707625421 49374643525272982765359533)
        ·
          refine ⟨18515491321977368537009825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49374643525272982765359533 18515491321977368537009825)
          ·
            refine ⟨13886618491483026402757369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18515491321977368537009825 13886618491483026402757369)
            ·
              refine ⟨10414963868612269802068027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13886618491483026402757369 10414963868612269802068027)
              ·
                refine ⟨15622445802918404703102041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10414963868612269802068027 15622445802918404703102041)
                ·
                  refine ⟨11716834352188803527326531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15622445802918404703102041 11716834352188803527326531)
                  ·
                    refine ⟨17575251528283205290989797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11716834352188803527326531 17575251528283205290989797)
                    ·
                      refine ⟨3295359661553100992060587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17575251528283205290989797 3295359661553100992060587)
                      ·
                        rfl

theorem cell23_6417690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_6417690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417690 prefixEnd_6417690 := by exact prefixLift 6417690
  have htrace : WordTrace (prefixWord ++ tailWord_6417690) baseStart_6417690 baseEnd_6417690 := by
    simpa [prefixWord, tailWord_6417690, baseEnd_6417690] using wordTrace_append hprefix tailTrace_6417690
  have hstable : (prefixWord ++ tailWord_6417690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417690).length < 2 ^ (prefixWord ++ tailWord_6417690).sum := by decide
  have hdescent : baseEnd_6417690 < baseStart_6417690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417713 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 6]
def baseStart_6417713 : Nat := 118140960795 + 6417713 * 2 ^ 59
def prefixEnd_6417713 : Nat := 4983230072969 + 3 ^ 40 * 6417713 * 2
def baseEnd_6417713 : Nat := 366152385734239378008109

theorem tailTrace_6417713 : CollatzResearch.WordTrace tailWord_6417713 prefixEnd_6417713 366152385734239378008109 := by
  unfold tailWord_6417713
  simp only [CollatzResearch.WordTrace]
  refine ⟨234073222998729333963865793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156048815332486222642577195 234073222998729333963865793)
  ·
    refine ⟨175554917249047000472899345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234073222998729333963865793 175554917249047000472899345)
    ·
      refine ⟨131666187936785250354674509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175554917249047000472899345 131666187936785250354674509)
      ·
        refine ⟨49374820476294468883002941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131666187936785250354674509 49374820476294468883002941)
        ·
          refine ⟨18515557678610425831126103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49374820476294468883002941 18515557678610425831126103)
          ·
            refine ⟨27773336517915638746689155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18515557678610425831126103 27773336517915638746689155)
            ·
              refine ⟨41660004776873458120033733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27773336517915638746689155 41660004776873458120033733)
              ·
                refine ⟨7811250895663773397506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41660004776873458120033733 7811250895663773397506325)
                ·
                  refine ⟨366152385734239378008109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7811250895663773397506325 366152385734239378008109)
                  ·
                    rfl

theorem cell23_6417713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_6417713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417713 prefixEnd_6417713 := by exact prefixLift 6417713
  have htrace : WordTrace (prefixWord ++ tailWord_6417713) baseStart_6417713 baseEnd_6417713 := by
    simpa [prefixWord, tailWord_6417713, baseEnd_6417713] using wordTrace_append hprefix tailTrace_6417713
  have hstable : (prefixWord ++ tailWord_6417713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417713).length < 2 ^ (prefixWord ++ tailWord_6417713).sum := by decide
  have hdescent : baseEnd_6417713 < baseStart_6417713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417717 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_6417717 : Nat := 118140960795 + 6417717 * 2 ^ 59
def prefixEnd_6417717 : Nat := 4983230072969 + 3 ^ 40 * 6417717 * 2
def baseEnd_6417717 : Nat := 1098457841843590795474321

theorem tailTrace_6417717 : CollatzResearch.WordTrace tailWord_6417717 prefixEnd_6417717 1098457841843590795474321 := by
  unfold tailWord_6417717
  simp only [CollatzResearch.WordTrace]
  refine ⟨234073368890714842647011405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156048912593809895098007603 234073368890714842647011405)
  ·
    refine ⟨87777513334018065992629277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234073368890714842647011405 87777513334018065992629277)
    ·
      refine ⟨32916567500256774747235979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87777513334018065992629277 32916567500256774747235979)
      ·
        refine ⟨49374851250385162120853969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32916567500256774747235979 49374851250385162120853969)
        ·
          refine ⟨37031138437788871590640477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49374851250385162120853969 37031138437788871590640477)
          ·
            refine ⟨13886676914170826846490179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37031138437788871590640477 13886676914170826846490179)
            ·
              refine ⟨20830015371256240269735269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886676914170826846490179 20830015371256240269735269)
              ·
                refine ⟨3905627882110545050575363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20830015371256240269735269 3905627882110545050575363)
                ·
                  refine ⟨5858441823165817575863045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905627882110545050575363 5858441823165817575863045)
                  ·
                    refine ⟨1098457841843590795474321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858441823165817575863045 1098457841843590795474321)
                    ·
                      rfl

theorem cell23_6417717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_6417717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417717 prefixEnd_6417717 := by exact prefixLift 6417717
  have htrace : WordTrace (prefixWord ++ tailWord_6417717) baseStart_6417717 baseEnd_6417717 := by
    simpa [prefixWord, tailWord_6417717, baseEnd_6417717] using wordTrace_append hprefix tailTrace_6417717
  have hstable : (prefixWord ++ tailWord_6417717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417717).length < 2 ^ (prefixWord ++ tailWord_6417717).sum := by decide
  have hdescent : baseEnd_6417717 < baseStart_6417717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417736 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_6417736 : Nat := 118140960795 + 6417736 * 2 ^ 59
def prefixEnd_6417736 : Nat := 4983230072969 + 3 ^ 40 * 6417736 * 2
def baseEnd_6417736 : Nat := 3295383281663207812085375

theorem tailTrace_6417736 : CollatzResearch.WordTrace tailWord_6417736 prefixEnd_6417736 3295383281663207812085375 := by
  unfold tailWord_6417736
  simp only [CollatzResearch.WordTrace]
  refine ⟨117037030938823004445976531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156049374585097339261302041 117037030938823004445976531)
  ·
    refine ⟨175555546408234506668964797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117037030938823004445976531 175555546408234506668964797)
    ·
      refine ⟨65833329903087940000861799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175555546408234506668964797 65833329903087940000861799)
      ·
        refine ⟨98749994854631910001292699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65833329903087940000861799 98749994854631910001292699)
        ·
          refine ⟨148124992281947865001939049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98749994854631910001292699 148124992281947865001939049)
          ·
            refine ⟨111093744211460898751454287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148124992281947865001939049 111093744211460898751454287)
            ·
              refine ⟨166640616317191348127181431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111093744211460898751454287 166640616317191348127181431)
              ·
                refine ⟨249960924475787022190772147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166640616317191348127181431 249960924475787022190772147)
                ·
                  refine ⟨374941386713680533286158221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249960924475787022190772147 374941386713680533286158221)
                  ·
                    refine ⟨140603020017630199982309333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 374941386713680533286158221 140603020017630199982309333)
                    ·
                      refine ⟨3295383281663207812085375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140603020017630199982309333 3295383281663207812085375)
                      ·
                        rfl

theorem cell23_6417736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_6417736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417736 prefixEnd_6417736 := by exact prefixLift 6417736
  have htrace : WordTrace (prefixWord ++ tailWord_6417736) baseStart_6417736 baseEnd_6417736 := by
    simpa [prefixWord, tailWord_6417736, baseEnd_6417736] using wordTrace_append hprefix tailTrace_6417736
  have hstable : (prefixWord ++ tailWord_6417736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417736).length < 2 ^ (prefixWord ++ tailWord_6417736).sum := by decide
  have hdescent : baseEnd_6417736 < baseStart_6417736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417740 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6417740 : Nat := 118140960795 + 6417740 * 2 ^ 59
def prefixEnd_6417740 : Nat := 4983230072969 + 3 ^ 40 * 6417740 * 2
def baseEnd_6417740 : Nat := 3295385335585825796435357

theorem tailTrace_6417740 : CollatzResearch.WordTrace tailWord_6417740 prefixEnd_6417740 3295385335585825796435357 := by
  unfold tailWord_6417740
  simp only [CollatzResearch.WordTrace]
  refine ⟨117037103884815758787549337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156049471846421011716732449 117037103884815758787549337)
  ·
    refine ⟨87777827913611819090662003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117037103884815758787549337 87777827913611819090662003)
    ·
      refine ⟨131666741870417728635993005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87777827913611819090662003 131666741870417728635993005)
      ·
        refine ⟨49375028201406648238497377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131666741870417728635993005 49375028201406648238497377)
        ·
          refine ⟨37031271151054986178873033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49375028201406648238497377 37031271151054986178873033)
          ·
            refine ⟨27773453363291239634154775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37031271151054986178873033 27773453363291239634154775)
            ·
              refine ⟨41660180044936859451232163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27773453363291239634154775 41660180044936859451232163)
              ·
                refine ⟨62490270067405289176848245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41660180044936859451232163 62490270067405289176848245)
                ·
                  refine ⟨5858462818819245860329523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62490270067405289176848245 5858462818819245860329523)
                  ·
                    refine ⟨8787694228228868790494285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858462818819245860329523 8787694228228868790494285)
                    ·
                      refine ⟨3295385335585825796435357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787694228228868790494285 3295385335585825796435357)
                      ·
                        rfl

theorem cell23_6417740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6417740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417740 prefixEnd_6417740 := by exact prefixLift 6417740
  have htrace : WordTrace (prefixWord ++ tailWord_6417740) baseStart_6417740 baseEnd_6417740 := by
    simpa [prefixWord, tailWord_6417740, baseEnd_6417740] using wordTrace_append hprefix tailTrace_6417740
  have hstable : (prefixWord ++ tailWord_6417740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417740).length < 2 ^ (prefixWord ++ tailWord_6417740).sum := by decide
  have hdescent : baseEnd_6417740 < baseStart_6417740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417741 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6417741 : Nat := 118140960795 + 6417741 * 2 ^ 59
def prefixEnd_6417741 : Nat := 4983230072969 + 3 ^ 40 * 6417741 * 2
def baseEnd_6417741 : Nat := 3295385849066480292522853

theorem tailTrace_6417741 : CollatzResearch.WordTrace tailWord_6417741 prefixEnd_6417741 3295385849066480292522853 := by
  unfold tailWord_6417741
  simp only [CollatzResearch.WordTrace]
  refine ⟨234074244242627894745885077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156049496161751929830590051 234074244242627894745885077)
  ·
    refine ⟨10972230198873182566213363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234074244242627894745885077 10972230198873182566213363)
    ·
      refine ⟨16458345298309773849320045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10972230198873182566213363 16458345298309773849320045)
      ·
        refine ⟨6171879486866165193495017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16458345298309773849320045 6171879486866165193495017)
        ·
          refine ⟨4628909615149623895121263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6171879486866165193495017 4628909615149623895121263)
          ·
            refine ⟨6943364422724435842681895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628909615149623895121263 6943364422724435842681895)
            ·
              refine ⟨10415046634086653764022843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943364422724435842681895 10415046634086653764022843)
              ·
                refine ⟨15622569951129980646034265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10415046634086653764022843 15622569951129980646034265)
                ·
                  refine ⟨11716927463347485484525699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15622569951129980646034265 11716927463347485484525699)
                  ·
                    refine ⟨17575391195021228226788549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11716927463347485484525699 17575391195021228226788549)
                    ·
                      refine ⟨3295385849066480292522853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17575391195021228226788549 3295385849066480292522853)
                      ·
                        rfl

theorem cell23_6417741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6417741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417741 prefixEnd_6417741 := by exact prefixLift 6417741
  have htrace : WordTrace (prefixWord ++ tailWord_6417741) baseStart_6417741 baseEnd_6417741 := by
    simpa [prefixWord, tailWord_6417741, baseEnd_6417741] using wordTrace_append hprefix tailTrace_6417741
  have hstable : (prefixWord ++ tailWord_6417741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417741).length < 2 ^ (prefixWord ++ tailWord_6417741).sum := by decide
  have hdescent : baseEnd_6417741 < baseStart_6417741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417760 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_6417760 : Nat := 118140960795 + 6417760 * 2 ^ 59
def prefixEnd_6417760 : Nat := 4983230072969 + 3 ^ 40 * 6417760 * 2
def baseEnd_6417760 : Nat := 1098465201732971906061755

theorem tailTrace_6417760 : CollatzResearch.WordTrace tailWord_6417760 prefixEnd_6417760 1098465201732971906061755 := by
  unfold tailWord_6417760
  simp only [CollatzResearch.WordTrace]
  refine ⟨117037468614779530495413367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156049958153039373993884489 117037468614779530495413367)
  ·
    refine ⟨175556202922169295743120051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117037468614779530495413367 175556202922169295743120051)
    ·
      refine ⟨263334304383253943614680077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175556202922169295743120051 263334304383253943614680077)
      ·
        refine ⟨98750364143720228855505029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263334304383253943614680077 98750364143720228855505029)
        ·
          refine ⟨18515693276947542910407193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98750364143720228855505029 18515693276947542910407193)
          ·
            refine ⟨13886769957710657182805395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18515693276947542910407193 13886769957710657182805395)
            ·
              refine ⟨20830154936565985774208093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886769957710657182805395 20830154936565985774208093)
              ·
                refine ⟨7811308101212244665328035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20830154936565985774208093 7811308101212244665328035)
                ·
                  refine ⟨11716962151818366997992053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811308101212244665328035 11716962151818366997992053)
                  ·
                    refine ⟨1098465201732971906061755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11716962151818366997992053 1098465201732971906061755)
                    ·
                      rfl

theorem cell23_6417760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_6417760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417760 prefixEnd_6417760 := by exact prefixLift 6417760
  have htrace : WordTrace (prefixWord ++ tailWord_6417760) baseStart_6417760 baseEnd_6417760 := by
    simpa [prefixWord, tailWord_6417760, baseEnd_6417760] using wordTrace_append hprefix tailTrace_6417760
  have hstable : (prefixWord ++ tailWord_6417760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417760).length < 2 ^ (prefixWord ++ tailWord_6417760).sum := by decide
  have hdescent : baseEnd_6417760 < baseStart_6417760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417783 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_6417783 : Nat := 118140960795 + 6417783 * 2 ^ 59
def prefixEnd_6417783 : Nat := 4983230072969 + 3 ^ 40 * 6417783 * 2
def baseEnd_6417783 : Nat := 3295407415253969128197659

theorem tailTrace_6417783 : CollatzResearch.WordTrace tailWord_6417783 prefixEnd_6417783 3295407415253969128197659 := by
  unfold tailWord_6417783
  simp only [CollatzResearch.WordTrace]
  refine ⟨234075776108475735918914003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156050517405650490612609335 234075776108475735918914003)
  ·
    refine ⟨351113664162713603878371005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234075776108475735918914003 351113664162713603878371005)
    ·
      refine ⟨131667624061017601454389127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351113664162713603878371005 131667624061017601454389127)
      ·
        refine ⟨197501436091526402181583691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131667624061017601454389127 197501436091526402181583691)
        ·
          refine ⟨296252154137289603272375537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197501436091526402181583691 296252154137289603272375537)
          ·
            refine ⟨222189115602967202454281653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296252154137289603272375537 222189115602967202454281653)
            ·
              refine ⟨20830229587778175230088905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222189115602967202454281653 20830229587778175230088905)
              ·
                refine ⟨15622672190833631422566679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20830229587778175230088905 15622672190833631422566679)
                ·
                  refine ⟨23434008286250447133850019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15622672190833631422566679 23434008286250447133850019)
                  ·
                    refine ⟨35151012429375670700775029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23434008286250447133850019 35151012429375670700775029)
                    ·
                      refine ⟨3295407415253969128197659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35151012429375670700775029 3295407415253969128197659)
                      ·
                        rfl

theorem cell23_6417783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_6417783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417783 prefixEnd_6417783 := by exact prefixLift 6417783
  have htrace : WordTrace (prefixWord ++ tailWord_6417783) baseStart_6417783 baseEnd_6417783 := by
    simpa [prefixWord, tailWord_6417783, baseEnd_6417783] using wordTrace_append hprefix tailTrace_6417783
  have hstable : (prefixWord ++ tailWord_6417783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417783).length < 2 ^ (prefixWord ++ tailWord_6417783).sum := by decide
  have hdescent : baseEnd_6417783 < baseStart_6417783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417794 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6417794 : Nat := 118140960795 + 6417794 * 2 ^ 59
def prefixEnd_6417794 : Nat := 4983230072969 + 3 ^ 40 * 6417794 * 2
def baseEnd_6417794 : Nat := 1098471021180389528386703

theorem tailTrace_6417794 : CollatzResearch.WordTrace tailWord_6417794 prefixEnd_6417794 1098471021180389528386703 := by
  unfold tailWord_6417794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58519044327858971199391109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156050784874290589865042957 58519044327858971199391109)
  ·
    refine ⟨10972320811473557099885833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58519044327858971199391109 10972320811473557099885833)
    ·
      refine ⟨8229240608605167824914375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10972320811473557099885833 8229240608605167824914375)
      ·
        refine ⟨12343860912907751737371563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8229240608605167824914375 12343860912907751737371563)
        ·
          refine ⟨18515791369361627606057345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12343860912907751737371563 18515791369361627606057345)
          ·
            refine ⟨13886843527021220704543009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18515791369361627606057345 13886843527021220704543009)
            ·
              refine ⟨10415132645265915528407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13886843527021220704543009 10415132645265915528407257)
              ·
                refine ⟨7811349483949436646305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10415132645265915528407257 7811349483949436646305443)
                ·
                  refine ⟨11717024225924154969458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811349483949436646305443 11717024225924154969458165)
                  ·
                    refine ⟨1098471021180389528386703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11717024225924154969458165 1098471021180389528386703)
                    ·
                      rfl

theorem cell23_6417794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6417794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417794 prefixEnd_6417794 := by exact prefixLift 6417794
  have htrace : WordTrace (prefixWord ++ tailWord_6417794) baseStart_6417794 baseEnd_6417794 := by
    simpa [prefixWord, tailWord_6417794, baseEnd_6417794] using wordTrace_append hprefix tailTrace_6417794
  have hstable : (prefixWord ++ tailWord_6417794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417794).length < 2 ^ (prefixWord ++ tailWord_6417794).sum := by decide
  have hdescent : baseEnd_6417794 < baseStart_6417794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417797 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_6417797 : Nat := 118140960795 + 6417797 * 2 ^ 59
def prefixEnd_6417797 : Nat := 4983230072969 + 3 ^ 40 * 6417797 * 2
def baseEnd_6417797 : Nat := 3295414603983132073422595

theorem tailTrace_6417797 : CollatzResearch.WordTrace tailWord_6417797 prefixEnd_6417797 3295414603983132073422595 := by
  unfold tailWord_6417797
  simp only [CollatzResearch.WordTrace]
  refine ⟨234076286730425016309923645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156050857820283344206615763 234076286730425016309923645)
  ·
    refine ⟨87778607523909381116221367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234076286730425016309923645 87778607523909381116221367)
    ·
      refine ⟨131667911285864071674332051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87778607523909381116221367 131667911285864071674332051)
      ·
        refine ⟨197501866928796107511498077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131667911285864071674332051 197501866928796107511498077)
        ·
          refine ⟨74063200098298540316811779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197501866928796107511498077 74063200098298540316811779)
          ·
            refine ⟨111094800147447810475217669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74063200098298540316811779 111094800147447810475217669)
            ·
              refine ⟨20830275027646464464103313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111094800147447810475217669 20830275027646464464103313)
              ·
                refine ⟨15622706270734848348077485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20830275027646464464103313 15622706270734848348077485)
                ·
                  refine ⟨5858514851525568130529057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15622706270734848348077485 5858514851525568130529057)
                  ·
                    refine ⟨4393886138644176097896793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858514851525568130529057 4393886138644176097896793)
                    ·
                      refine ⟨3295414603983132073422595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393886138644176097896793 3295414603983132073422595)
                      ·
                        rfl

theorem cell23_6417797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_6417797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417797 prefixEnd_6417797 := by exact prefixLift 6417797
  have htrace : WordTrace (prefixWord ++ tailWord_6417797) baseStart_6417797 baseEnd_6417797 := by
    simpa [prefixWord, tailWord_6417797, baseEnd_6417797] using wordTrace_append hprefix tailTrace_6417797
  have hstable : (prefixWord ++ tailWord_6417797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417797).length < 2 ^ (prefixWord ++ tailWord_6417797).sum := by decide
  have hdescent : baseEnd_6417797 < baseStart_6417797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417847 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_6417847 : Nat := 118140960795 + 6417847 * 2 ^ 59
def prefixEnd_6417847 : Nat := 4983230072969 + 3 ^ 40 * 6417847 * 2
def baseEnd_6417847 : Nat := 3295440278015856877797365

theorem tailTrace_6417847 : CollatzResearch.WordTrace tailWord_6417847 prefixEnd_6417847 3295440278015856877797365 := by
  unfold tailWord_6417847
  simp only [CollatzResearch.WordTrace]
  refine ⟨234078110380243874849243795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156052073586829249899495863 234078110380243874849243795)
  ·
    refine ⟨351117165570365812273865693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234078110380243874849243795 351117165570365812273865693)
    ·
      refine ⟨131668937088887179602699635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351117165570365812273865693 131668937088887179602699635)
      ·
        refine ⟨197503405633330769404049453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131668937088887179602699635 197503405633330769404049453)
        ·
          refine ⟨74063777112499038526518545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197503405633330769404049453 74063777112499038526518545)
          ·
            refine ⟨55547832834374278894888909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74063777112499038526518545 55547832834374278894888909)
            ·
              refine ⟨20830437312890354585583341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55547832834374278894888909 20830437312890354585583341)
              ·
                refine ⟨7811413992333882969593753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20830437312890354585583341 7811413992333882969593753)
                ·
                  refine ⟨5858560494250412227195315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7811413992333882969593753 5858560494250412227195315)
                  ·
                    refine ⟨8787840741375618340792973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858560494250412227195315 8787840741375618340792973)
                    ·
                      refine ⟨3295440278015856877797365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8787840741375618340792973 3295440278015856877797365)
                      ·
                        rfl

theorem cell23_6417847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_6417847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417847 prefixEnd_6417847 := by exact prefixLift 6417847
  have htrace : WordTrace (prefixWord ++ tailWord_6417847) baseStart_6417847 baseEnd_6417847 := by
    simpa [prefixWord, tailWord_6417847, baseEnd_6417847] using wordTrace_append hprefix tailTrace_6417847
  have hstable : (prefixWord ++ tailWord_6417847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417847).length < 2 ^ (prefixWord ++ tailWord_6417847).sum := by decide
  have hdescent : baseEnd_6417847 < baseStart_6417847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417883 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_6417883 : Nat := 118140960795 + 6417883 * 2 ^ 59
def prefixEnd_6417883 : Nat := 4983230072969 + 3 ^ 40 * 6417883 * 2
def baseEnd_6417883 : Nat := 3295458763319418736947199

theorem tailTrace_6417883 : CollatzResearch.WordTrace tailWord_6417883 prefixEnd_6417883 3295458763319418736947199 := by
  unfold tailWord_6417883
  simp only [CollatzResearch.WordTrace]
  refine ⟨234079423408113452997554303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156052948938742301998369535 234079423408113452997554303)
  ·
    refine ⟨351119135112170179496331455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234079423408113452997554303 351119135112170179496331455)
    ·
      refine ⟨526678702668255269244497183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351119135112170179496331455 526678702668255269244497183)
      ·
        refine ⟨790018054002382903866745775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526678702668255269244497183 790018054002382903866745775)
        ·
          refine ⟨1185027081003574355800118663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790018054002382903866745775 1185027081003574355800118663)
          ·
            refine ⟨1777540621505361533700177995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185027081003574355800118663 1777540621505361533700177995)
            ·
              refine ⟨2666310932258042300550266993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777540621505361533700177995 2666310932258042300550266993)
              ·
                refine ⟨1999733199193531725412700245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666310932258042300550266993 1999733199193531725412700245)
                ·
                  refine ⟨23434373428049199907180081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1999733199193531725412700245 23434373428049199907180081)
                  ·
                    refine ⟨17575780071036899930385061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23434373428049199907180081 17575780071036899930385061)
                    ·
                      refine ⟨3295458763319418736947199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17575780071036899930385061 3295458763319418736947199)
                      ·
                        rfl

theorem cell23_6417883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_6417883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417883 prefixEnd_6417883 := by exact prefixLift 6417883
  have htrace : WordTrace (prefixWord ++ tailWord_6417883) baseStart_6417883 baseEnd_6417883 := by
    simpa [prefixWord, tailWord_6417883, baseEnd_6417883] using wordTrace_append hprefix tailTrace_6417883
  have hstable : (prefixWord ++ tailWord_6417883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417883).length < 2 ^ (prefixWord ++ tailWord_6417883).sum := by decide
  have hdescent : baseEnd_6417883 < baseStart_6417883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417904 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2]
def baseStart_6417904 : Nat := 118140960795 + 6417904 * 2 ^ 59
def prefixEnd_6417904 : Nat := 4983230072969 + 3 ^ 40 * 6417904 * 2
def baseEnd_6417904 : Nat := 3295469546413163154784603

theorem tailTrace_6417904 : CollatzResearch.WordTrace tailWord_6417904 prefixEnd_6417904 3295469546413163154784603 := by
  unfold tailWord_6417904
  simp only [CollatzResearch.WordTrace]
  refine ⟨117040094670518686792034383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156053459560691582389379177 117040094670518686792034383)
  ·
    refine ⟨175560142005778030188051575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117040094670518686792034383 175560142005778030188051575)
    ·
      refine ⟨263340213008667045282077363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175560142005778030188051575 263340213008667045282077363)
      ·
        refine ⟨395010319513000567923116045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263340213008667045282077363 395010319513000567923116045)
        ·
          refine ⟨148128869817375212971168517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395010319513000567923116045 148128869817375212971168517)
          ·
            refine ⟨27774163090757852432094097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148128869817375212971168517 27774163090757852432094097)
            ·
              refine ⟨20830622318068389324070573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27774163090757852432094097 20830622318068389324070573)
              ·
                refine ⟨7811483369275645996526465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20830622318068389324070573 7811483369275645996526465)
                ·
                  refine ⟨5858612526956734497394849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7811483369275645996526465 5858612526956734497394849)
                  ·
                    refine ⟨4393959395217550873046137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858612526956734497394849 4393959395217550873046137)
                    ·
                      refine ⟨3295469546413163154784603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4393959395217550873046137 3295469546413163154784603)
                      ·
                        rfl

theorem cell23_6417904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2].length) (baseStart_6417904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417904 prefixEnd_6417904 := by exact prefixLift 6417904
  have htrace : WordTrace (prefixWord ++ tailWord_6417904) baseStart_6417904 baseEnd_6417904 := by
    simpa [prefixWord, tailWord_6417904, baseEnd_6417904] using wordTrace_append hprefix tailTrace_6417904
  have hstable : (prefixWord ++ tailWord_6417904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417904).length < 2 ^ (prefixWord ++ tailWord_6417904).sum := by decide
  have hdescent : baseEnd_6417904 < baseStart_6417904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417910 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6417910 : Nat := 118140960795 + 6417910 * 2 ^ 59
def prefixEnd_6417910 : Nat := 4983230072969 + 3 ^ 40 * 6417910 * 2
def baseEnd_6417910 : Nat := 366163625255232236812175

theorem tailTrace_6417910 : CollatzResearch.WordTrace tailWord_6417910 prefixEnd_6417910 366163625255232236812175 := by
  unfold tailWord_6417910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630025511188477288049199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156053605452677091072524789 14630025511188477288049199)
  ·
    refine ⟨21945038266782715932073799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14630025511188477288049199 21945038266782715932073799)
    ·
      refine ⟨32917557400174073898110699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21945038266782715932073799 32917557400174073898110699)
      ·
        refine ⟨49376336100261110847166049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32917557400174073898110699 49376336100261110847166049)
        ·
          refine ⟨37032252075195833135374537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49376336100261110847166049 37032252075195833135374537)
          ·
            refine ⟨27774189056396874851530903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37032252075195833135374537 27774189056396874851530903)
            ·
              refine ⟨41661283584595312277296355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27774189056396874851530903 41661283584595312277296355)
              ·
                refine ⟨62491925376892968415944533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41661283584595312277296355 62491925376892968415944533)
                ·
                  refine ⟨366163625255232236812175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62491925376892968415944533 366163625255232236812175)
                  ·
                    rfl

theorem cell23_6417910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6417910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417910 prefixEnd_6417910 := by exact prefixLift 6417910
  have htrace : WordTrace (prefixWord ++ tailWord_6417910) baseStart_6417910 baseEnd_6417910 := by
    simpa [prefixWord, tailWord_6417910, baseEnd_6417910] using wordTrace_append hprefix tailTrace_6417910
  have hstable : (prefixWord ++ tailWord_6417910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417910).length < 2 ^ (prefixWord ++ tailWord_6417910).sum := by decide
  have hdescent : baseEnd_6417910 < baseStart_6417910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6417927 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 5]
def baseStart_6417927 : Nat := 118140960795 + 6417927 * 2 ^ 59
def prefixEnd_6417927 : Nat := 4983230072969 + 3 ^ 40 * 6417927 * 2
def baseEnd_6417927 : Nat := 366164595163135173866333

theorem tailTrace_6417927 : CollatzResearch.WordTrace tailWord_6417927 prefixEnd_6417927 366164595163135173866333 := by
  unfold tailWord_6417927
  simp only [CollatzResearch.WordTrace]
  refine ⟨234081028219954048512156035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156054018813302699008104023 234081028219954048512156035)
  ·
    refine ⟨351121542329931072768234053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234081028219954048512156035 351121542329931072768234053)
    ·
      refine ⟨65835289186862076144043885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351121542329931072768234053 65835289186862076144043885)
      ·
        refine ⟨24688233445073278554016457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65835289186862076144043885 24688233445073278554016457)
        ·
          refine ⟨18516175083804958915512343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24688233445073278554016457 18516175083804958915512343)
          ·
            refine ⟨27774262625707438373268515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18516175083804958915512343 27774262625707438373268515)
            ·
              refine ⟨41661393938561157559902773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27774262625707438373268515 41661393938561157559902773)
              ·
                refine ⟨3905755681740108521240885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41661393938561157559902773 3905755681740108521240885)
                ·
                  refine ⟨366164595163135173866333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3905755681740108521240885 366164595163135173866333)
                  ·
                    rfl

theorem cell23_6417927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 5].length) (baseStart_6417927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6417927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6417927 prefixEnd_6417927 := by exact prefixLift 6417927
  have htrace : WordTrace (prefixWord ++ tailWord_6417927) baseStart_6417927 baseEnd_6417927 := by
    simpa [prefixWord, tailWord_6417927, baseEnd_6417927] using wordTrace_append hprefix tailTrace_6417927
  have hstable : (prefixWord ++ tailWord_6417927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6417927).length < 2 ^ (prefixWord ++ tailWord_6417927).sum := by decide
  have hdescent : baseEnd_6417927 < baseStart_6417927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6417927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418000 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 6]
def baseStart_6418000 : Nat := 118140960795 + 6418000 * 2 ^ 59
def prefixEnd_6418000 : Nat := 4983230072969 + 3 ^ 40 * 6418000 * 2
def baseEnd_6418000 : Nat := 366168760061777197687129

theorem tailTrace_6418000 : CollatzResearch.WordTrace tailWord_6418000 prefixEnd_6418000 366168760061777197687129 := by
  unfold tailWord_6418000
  simp only [CollatzResearch.WordTrace]
  refine ⟨117041845374344790989781727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156055793832459721319708969 117041845374344790989781727)
  ·
    refine ⟨175562768061517186484672591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117041845374344790989781727 175562768061517186484672591)
    ·
      refine ⟨263344152092275779727008887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175562768061517186484672591 263344152092275779727008887)
      ·
        refine ⟨395016228138413669590513331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263344152092275779727008887 395016228138413669590513331)
        ·
          refine ⟨592524342207620504385769997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395016228138413669590513331 592524342207620504385769997)
          ·
            refine ⟨222196628327857689144663749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592524342207620504385769997 222196628327857689144663749)
            ·
              refine ⟨41661867811473316714624453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222196628327857689144663749 41661867811473316714624453)
              ·
                refine ⟨7811600214651246883992085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41661867811473316714624453 7811600214651246883992085)
                ·
                  refine ⟨366168760061777197687129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7811600214651246883992085 366168760061777197687129)
                  ·
                    rfl

theorem cell23_6418000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_6418000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418000 prefixEnd_6418000 := by exact prefixLift 6418000
  have htrace : WordTrace (prefixWord ++ tailWord_6418000) baseStart_6418000 baseEnd_6418000 := by
    simpa [prefixWord, tailWord_6418000, baseEnd_6418000] using wordTrace_append hprefix tailTrace_6418000
  have hstable : (prefixWord ++ tailWord_6418000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418000).length < 2 ^ (prefixWord ++ tailWord_6418000).sum := by decide
  have hdescent : baseEnd_6418000 < baseStart_6418000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418060 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_6418060 : Nat := 118140960795 + 6418060 * 2 ^ 59
def prefixEnd_6418060 : Nat := 4983230072969 + 3 ^ 40 * 6418060 * 2
def baseEnd_6418060 : Nat := 1098516549798421514811295

theorem tailTrace_6418060 : CollatzResearch.WordTrace tailWord_6418060 prefixEnd_6418060 1098516549798421514811295 := by
  unfold tailWord_6418060
  simp only [CollatzResearch.WordTrace]
  refine ⟨117042939564236106113373817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156057252752314808151165089 117042939564236106113373817)
  ·
    refine ⟨87782204673177079585030363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117042939564236106113373817 87782204673177079585030363)
    ·
      refine ⟨131673307009765619377545545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87782204673177079585030363 131673307009765619377545545)
      ·
        refine ⟨98754980257324214533159159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131673307009765619377545545 98754980257324214533159159)
        ·
          refine ⟨148132470385986321799738739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98754980257324214533159159 148132470385986321799738739)
          ·
            refine ⟨222198705578979482699608109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148132470385986321799738739 222198705578979482699608109)
            ·
              refine ⟨83324514592117306012353041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222198705578979482699608109 83324514592117306012353041)
              ·
                refine ⟨62493385944087979509264781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83324514592117306012353041 62493385944087979509264781)
                ·
                  refine ⟨23435019729032992315974293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62493385944087979509264781 23435019729032992315974293)
                  ·
                    refine ⟨1098516549798421514811295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23435019729032992315974293 1098516549798421514811295)
                    ·
                      rfl

theorem cell23_6418060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_6418060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418060 prefixEnd_6418060 := by exact prefixLift 6418060
  have htrace : WordTrace (prefixWord ++ tailWord_6418060) baseStart_6418060 baseEnd_6418060 := by
    simpa [prefixWord, tailWord_6418060, baseEnd_6418060] using wordTrace_append hprefix tailTrace_6418060
  have hstable : (prefixWord ++ tailWord_6418060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418060).length < 2 ^ (prefixWord ++ tailWord_6418060).sum := by decide
  have hdescent : baseEnd_6418060 < baseStart_6418060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418077 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6418077 : Nat := 118140960795 + 6418077 * 2 ^ 59
def prefixEnd_6418077 : Nat := 4983230072969 + 3 ^ 40 * 6418077 * 2
def baseEnd_6418077 : Nat := 1098519459522130325973769

theorem tailTrace_6418077 : CollatzResearch.WordTrace tailWord_6418077 prefixEnd_6418077 1098519459522130325973769 := by
  unfold tailWord_6418077
  simp only [CollatzResearch.WordTrace]
  refine ⟨234086499169410624130116485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156057666112940416086744323 234086499169410624130116485)
  ·
    refine ⟨43891218594264492024396841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234086499169410624130116485 43891218594264492024396841)
    ·
      refine ⟨32918413945698369018297631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43891218594264492024396841 32918413945698369018297631)
      ·
        refine ⟨49377620918547553527446447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32918413945698369018297631 49377620918547553527446447)
        ·
          refine ⟨74066431377821330291169671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49377620918547553527446447 74066431377821330291169671)
          ·
            refine ⟨111099647066731995436754507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74066431377821330291169671 111099647066731995436754507)
            ·
              refine ⟨166649470600097993155131761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111099647066731995436754507 166649470600097993155131761)
              ·
                refine ⟨124987102950073494866348821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166649470600097993155131761 124987102950073494866348821)
                ·
                  refine ⟨5858770450784695071860101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124987102950073494866348821 5858770450784695071860101)
                  ·
                    refine ⟨1098519459522130325973769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858770450784695071860101 1098519459522130325973769)
                    ·
                      rfl

theorem cell23_6418077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6418077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418077 prefixEnd_6418077 := by exact prefixLift 6418077
  have htrace : WordTrace (prefixWord ++ tailWord_6418077) baseStart_6418077 baseEnd_6418077 := by
    simpa [prefixWord, tailWord_6418077, baseEnd_6418077] using wordTrace_append hprefix tailTrace_6418077
  have hstable : (prefixWord ++ tailWord_6418077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418077).length < 2 ^ (prefixWord ++ tailWord_6418077).sum := by decide
  have hdescent : baseEnd_6418077 < baseStart_6418077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
