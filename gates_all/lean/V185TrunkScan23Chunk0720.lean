import V185TrunkScan23Chunk0719

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4257462 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4257462 : Nat := 118140960795 + 4257462 * 2 ^ 59
def prefixEnd_4257462 : Nat := 4983230072969 + 3 ^ 40 * 4257462 * 2
def baseEnd_4257462 : Nat := 2186124374252326894045295

theorem tailTrace_4257462 : CollatzResearch.WordTrace tailWord_4257462 prefixEnd_4257462 2186124374252326894045295 := by
  unfold tailWord_4257462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9705149756371860341624915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103521597401299843643999093 9705149756371860341624915)
  ·
    refine ⟨14557724634557790512437373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9705149756371860341624915 14557724634557790512437373)
    ·
      refine ⟨5459146737959171442164015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14557724634557790512437373 5459146737959171442164015)
      ·
        refine ⟨8188720106938757163246023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459146737959171442164015 8188720106938757163246023)
        ·
          refine ⟨12283080160408135744869035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188720106938757163246023 12283080160408135744869035)
          ·
            refine ⟨18424620240612203617303553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12283080160408135744869035 18424620240612203617303553)
            ·
              refine ⟨13818465180459152712977665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18424620240612203617303553 13818465180459152712977665)
              ·
                refine ⟨10363848885344364534733249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13818465180459152712977665 10363848885344364534733249)
                ·
                  refine ⟨7772886664008273401049937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10363848885344364534733249 7772886664008273401049937)
                  ·
                    refine ⟨5829664998006205050787453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7772886664008273401049937 5829664998006205050787453)
                    ·
                      refine ⟨2186124374252326894045295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5829664998006205050787453 2186124374252326894045295)
                      ·
                        rfl

theorem cell23_4257462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4257462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257462 prefixEnd_4257462 := by exact prefixLift 4257462
  have htrace : WordTrace (prefixWord ++ tailWord_4257462) baseStart_4257462 baseEnd_4257462 := by
    simpa [prefixWord, tailWord_4257462, baseEnd_4257462] using wordTrace_append hprefix tailTrace_4257462
  have hstable : (prefixWord ++ tailWord_4257462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257462).length < 2 ^ (prefixWord ++ tailWord_4257462).sum := by decide
  have hdescent : baseEnd_4257462 < baseStart_4257462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257492 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4257492 : Nat := 118140960795 + 4257492 * 2 ^ 59
def prefixEnd_4257492 : Nat := 4983230072969 + 3 ^ 40 * 4257492 * 2
def baseEnd_4257492 : Nat := 2186139778671961776670157

theorem tailTrace_4257492 : CollatzResearch.WordTrace tailWord_4257492 prefixEnd_4257492 2186139778671961776670157 := by
  unfold tailWord_4257492
  simp only [CollatzResearch.WordTrace]
  refine ⟨77641745145920540294795365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103522326861227387059727153 77641745145920540294795365)
  ·
    refine ⟨14557827214860101305274131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77641745145920540294795365 14557827214860101305274131)
    ·
      refine ⟨21836740822290151957911197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14557827214860101305274131 21836740822290151957911197)
      ·
        refine ⟨8188777808358806984216699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21836740822290151957911197 8188777808358806984216699)
        ·
          refine ⟨12283166712538210476325049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188777808358806984216699 12283166712538210476325049)
          ·
            refine ⟨9212375034403657857243787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12283166712538210476325049 9212375034403657857243787)
            ·
              refine ⟨13818562551605486785865681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9212375034403657857243787 13818562551605486785865681)
              ·
                refine ⟨10363921913704115089399261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13818562551605486785865681 10363921913704115089399261)
                ·
                  refine ⟨3886470717639043158524723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10363921913704115089399261 3886470717639043158524723)
                  ·
                    refine ⟨5829706076458564737787085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3886470717639043158524723 5829706076458564737787085)
                    ·
                      refine ⟨2186139778671961776670157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5829706076458564737787085 2186139778671961776670157)
                      ·
                        rfl

theorem cell23_4257492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4257492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257492 prefixEnd_4257492 := by exact prefixLift 4257492
  have htrace : WordTrace (prefixWord ++ tailWord_4257492) baseStart_4257492 baseEnd_4257492 := by
    simpa [prefixWord, tailWord_4257492, baseEnd_4257492] using wordTrace_append hprefix tailTrace_4257492
  have hstable : (prefixWord ++ tailWord_4257492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257492).length < 2 ^ (prefixWord ++ tailWord_4257492).sum := by decide
  have hdescent : baseEnd_4257492 < baseStart_4257492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257498 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_4257498 : Nat := 118140960795 + 4257498 * 2 ^ 59
def prefixEnd_4257498 : Nat := 4983230072969 + 3 ^ 40 * 4257498 * 2
def baseEnd_4257498 : Nat := 2186142859555888753195129

theorem tailTrace_4257498 : CollatzResearch.WordTrace tailWord_4257498 prefixEnd_4257498 2186142859555888753195129 := by
  unfold tailWord_4257498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38820927282454835903577287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103522472753212895742872765 38820927282454835903577287)
  ·
    refine ⟨58231390923682253855365931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38820927282454835903577287 58231390923682253855365931)
    ·
      refine ⟨87347086385523380783048897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58231390923682253855365931 87347086385523380783048897)
      ·
        refine ⟨65510314789142535587286673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87347086385523380783048897 65510314789142535587286673)
        ·
          refine ⟨49132736091856901690465005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65510314789142535587286673 49132736091856901690465005)
          ·
            refine ⟨18424776034446338133924377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49132736091856901690465005 18424776034446338133924377)
            ·
              refine ⟨13818582025834753600443283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18424776034446338133924377 13818582025834753600443283)
              ·
                refine ⟨20727873038752130400664925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13818582025834753600443283 20727873038752130400664925)
                ·
                  refine ⟨7772952389532048900249347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20727873038752130400664925 7772952389532048900249347)
                  ·
                    refine ⟨11659428584298073350374021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7772952389532048900249347 11659428584298073350374021)
                    ·
                      refine ⟨2186142859555888753195129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11659428584298073350374021 2186142859555888753195129)
                      ·
                        rfl

theorem cell23_4257498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_4257498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257498 prefixEnd_4257498 := by exact prefixLift 4257498
  have htrace : WordTrace (prefixWord ++ tailWord_4257498) baseStart_4257498 baseEnd_4257498 := by
    simpa [prefixWord, tailWord_4257498, baseEnd_4257498] using wordTrace_append hprefix tailTrace_4257498
  have hstable : (prefixWord ++ tailWord_4257498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257498).length < 2 ^ (prefixWord ++ tailWord_4257498).sum := by decide
  have hdescent : baseEnd_4257498 < baseStart_4257498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257508 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_4257508 : Nat := 118140960795 + 4257508 * 2 ^ 59
def prefixEnd_4257508 : Nat := 4983230072969 + 3 ^ 40 * 4257508 * 2
def baseEnd_4257508 : Nat := 728715998120811238023361

theorem tailTrace_4257508 : CollatzResearch.WordTrace tailWord_4257508 prefixEnd_4257508 728715998120811238023361 := by
  unfold tailWord_4257508
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642036929891557661086589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103522715906522076881448785 77642036929891557661086589)
  ·
    refine ⟨29115763848709334122907471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77642036929891557661086589 29115763848709334122907471)
    ·
      refine ⟨43673645773064001184361207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29115763848709334122907471 43673645773064001184361207)
      ·
        refine ⟨65510468659596001776541811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43673645773064001184361207 65510468659596001776541811)
        ·
          refine ⟨98265702989394002664812717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65510468659596001776541811 98265702989394002664812717)
          ·
            refine ⟨36849638621022750999304769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98265702989394002664812717 36849638621022750999304769)
            ·
              refine ⟨27637228965767063249478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36849638621022750999304769 27637228965767063249478577)
              ·
                refine ⟨20727921724325297437108933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27637228965767063249478577 20727921724325297437108933)
                ·
                  refine ⟨3886485323310993269457925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20727921724325297437108933 3886485323310993269457925)
                  ·
                    refine ⟨728715998120811238023361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3886485323310993269457925 728715998120811238023361)
                    ·
                      rfl

theorem cell23_4257508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_4257508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257508 prefixEnd_4257508 := by exact prefixLift 4257508
  have htrace : WordTrace (prefixWord ++ tailWord_4257508) baseStart_4257508 baseEnd_4257508 := by
    simpa [prefixWord, tailWord_4257508, baseEnd_4257508] using wordTrace_append hprefix tailTrace_4257508
  have hstable : (prefixWord ++ tailWord_4257508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257508).length < 2 ^ (prefixWord ++ tailWord_4257508).sum := by decide
  have hdescent : baseEnd_4257508 < baseStart_4257508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257512 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 1, 5]
def baseStart_4257512 : Nat := 118140960795 + 4257512 * 2 ^ 59
def prefixEnd_4257512 : Nat := 4983230072969 + 3 ^ 40 * 4257512 * 2
def baseEnd_4257512 : Nat := 728716682761683899473355

theorem tailTrace_4257512 : CollatzResearch.WordTrace tailWord_4257512 prefixEnd_4257512 728716682761683899473355 := by
  unfold tailWord_4257512
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642109875884312002659395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103522813167845749336879193 77642109875884312002659395)
  ·
    refine ⟨116463164813826468003989093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77642109875884312002659395 116463164813826468003989093)
    ·
      refine ⟨21836843402592462750747955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116463164813826468003989093 21836843402592462750747955)
      ·
        refine ⟨32755265103888694126121933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21836843402592462750747955 32755265103888694126121933)
        ·
          refine ⟨12283224413958260297295725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32755265103888694126121933 12283224413958260297295725)
          ·
            refine ⟨4606209155234347611485897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12283224413958260297295725 4606209155234347611485897)
            ·
              refine ⟨3454656866425760708614423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606209155234347611485897 3454656866425760708614423)
              ·
                refine ⟨5181985299638641062921635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454656866425760708614423 5181985299638641062921635)
                ·
                  refine ⟨7772977949457961594382453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181985299638641062921635 7772977949457961594382453)
                  ·
                    refine ⟨728716682761683899473355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7772977949457961594382453 728716682761683899473355)
                    ·
                      rfl

theorem cell23_4257512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_4257512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257512 prefixEnd_4257512 := by exact prefixLift 4257512
  have htrace : WordTrace (prefixWord ++ tailWord_4257512) baseStart_4257512 baseEnd_4257512 := by
    simpa [prefixWord, tailWord_4257512, baseEnd_4257512] using wordTrace_append hprefix tailTrace_4257512
  have hstable : (prefixWord ++ tailWord_4257512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257512).length < 2 ^ (prefixWord ++ tailWord_4257512).sum := by decide
  have hdescent : baseEnd_4257512 < baseStart_4257512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257515 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 1, 1, 4]
def baseStart_4257515 : Nat := 118140960795 + 4257515 * 2 ^ 59
def prefixEnd_4257515 : Nat := 4983230072969 + 3 ^ 40 * 4257515 * 2
def baseEnd_4257515 : Nat := 2186151588727015186682551

theorem tailTrace_4257515 : CollatzResearch.WordTrace tailWord_4257515 prefixEnd_4257515 2186151588727015186682551 := by
  unfold tailWord_4257515
  simp only [CollatzResearch.WordTrace]
  refine ⟨155284329170757755517677999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103522886113838503678451999 155284329170757755517677999)
  ·
    refine ⟨232926493756136633276516999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155284329170757755517677999 232926493756136633276516999)
    ·
      refine ⟨349389740634204949914775499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232926493756136633276516999 349389740634204949914775499)
      ·
        refine ⟨524084610951307424872163249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349389740634204949914775499 524084610951307424872163249)
        ·
          refine ⟨393063458213480568654122437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524084610951307424872163249 393063458213480568654122437)
          ·
            refine ⟨73699398415027606622647957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393063458213480568654122437 73699398415027606622647957)
            ·
              refine ⟨3454659300704419060436623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73699398415027606622647957 3454659300704419060436623)
              ·
                refine ⟨5181988951056628590654935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454659300704419060436623 5181988951056628590654935)
                ·
                  refine ⟨7772983426584942885982403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181988951056628590654935 7772983426584942885982403)
                  ·
                    refine ⟨11659475139877414328973605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7772983426584942885982403 11659475139877414328973605)
                    ·
                      refine ⟨2186151588727015186682551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11659475139877414328973605 2186151588727015186682551)
                      ·
                        rfl

theorem cell23_4257515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 1, 1, 4].length) (baseStart_4257515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257515 prefixEnd_4257515 := by exact prefixLift 4257515
  have htrace : WordTrace (prefixWord ++ tailWord_4257515) baseStart_4257515 baseEnd_4257515 := by
    simpa [prefixWord, tailWord_4257515, baseEnd_4257515] using wordTrace_append hprefix tailTrace_4257515
  have hstable : (prefixWord ++ tailWord_4257515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257515).length < 2 ^ (prefixWord ++ tailWord_4257515).sum := by decide
  have hdescent : baseEnd_4257515 < baseStart_4257515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257518 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4257518 : Nat := 118140960795 + 4257518 * 2 ^ 59
def prefixEnd_4257518 : Nat := 4983230072969 + 3 ^ 40 * 4257518 * 2
def baseEnd_4257518 : Nat := 2186153129168978674945037

theorem tailTrace_4257518 : CollatzResearch.WordTrace tailWord_4257518 prefixEnd_4257518 2186153129168978674945037 := by
  unfold tailWord_4257518
  simp only [CollatzResearch.WordTrace]
  refine ⟨19410554823718360878754651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103522959059831258020024805 19410554823718360878754651)
  ·
    refine ⟨29115832235577541318131977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19410554823718360878754651 29115832235577541318131977)
    ·
      refine ⟨21836874176683155988598983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29115832235577541318131977 21836874176683155988598983)
      ·
        refine ⟨32755311265024733982898475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21836874176683155988598983 32755311265024733982898475)
        ·
          refine ⟨49132966897537100974347713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32755311265024733982898475 49132966897537100974347713)
          ·
            refine ⟨36849725173152825730760785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49132966897537100974347713 36849725173152825730760785)
            ·
              refine ⟨27637293879864619298070589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36849725173152825730760785 27637293879864619298070589)
              ·
                refine ⟨10363985204949232236776471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27637293879864619298070589 10363985204949232236776471)
                ·
                  refine ⟨15545977807423848355164707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10363985204949232236776471 15545977807423848355164707)
                  ·
                    refine ⟨23318966711135772532747061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15545977807423848355164707 23318966711135772532747061)
                    ·
                      refine ⟨2186153129168978674945037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23318966711135772532747061 2186153129168978674945037)
                      ·
                        rfl

theorem cell23_4257518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4257518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257518 prefixEnd_4257518 := by exact prefixLift 4257518
  have htrace : WordTrace (prefixWord ++ tailWord_4257518) baseStart_4257518 baseEnd_4257518 := by
    simpa [prefixWord, tailWord_4257518, baseEnd_4257518] using wordTrace_append hprefix tailTrace_4257518
  have hstable : (prefixWord ++ tailWord_4257518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257518).length < 2 ^ (prefixWord ++ tailWord_4257518).sum := by decide
  have hdescent : baseEnd_4257518 < baseStart_4257518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257521 : List Nat := [1, 2, 2, 2, 2, 4, 10]
def baseStart_4257521 : Nat := 118140960795 + 4257521 * 2 ^ 59
def prefixEnd_4257521 : Nat := 4983230072969 + 3 ^ 40 * 4257521 * 2
def baseEnd_4257521 : Nat := 26989563822357310656883

theorem tailTrace_4257521 : CollatzResearch.WordTrace tailWord_4257521 prefixEnd_4257521 26989563822357310656883 := by
  unfold tailWord_4257521
  simp only [CollatzResearch.WordTrace]
  refine ⟨155284548008736018542396417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103523032005824012361597611 155284548008736018542396417)
  ·
    refine ⟨116463411006552013906797313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155284548008736018542396417 116463411006552013906797313)
    ·
      refine ⟨87347558254914010430097985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116463411006552013906797313 87347558254914010430097985)
      ·
        refine ⟨65510668691185507822573489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87347558254914010430097985 65510668691185507822573489)
        ·
          refine ⟨49133001518389130866930117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65510668691185507822573489 49133001518389130866930117)
          ·
            refine ⟨9212437784697962037549397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49133001518389130866930117 9212437784697962037549397)
            ·
              refine ⟨26989563822357310656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9212437784697962037549397 26989563822357310656883)
              ·
                rfl

theorem cell23_4257521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 10].length) (baseStart_4257521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257521 prefixEnd_4257521 := by exact prefixLift 4257521
  have htrace : WordTrace (prefixWord ++ tailWord_4257521) baseStart_4257521 baseEnd_4257521 := by
    simpa [prefixWord, tailWord_4257521, baseEnd_4257521] using wordTrace_append hprefix tailTrace_4257521
  have hstable : (prefixWord ++ tailWord_4257521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257521).length < 2 ^ (prefixWord ++ tailWord_4257521).sum := by decide
  have hdescent : baseEnd_4257521 < baseStart_4257521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257532 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_4257532 : Nat := 118140960795 + 4257532 * 2 ^ 59
def prefixEnd_4257532 : Nat := 4983230072969 + 3 ^ 40 * 4257532 * 2
def baseEnd_4257532 : Nat := 2186160317898141620169973

theorem tailTrace_4257532 : CollatzResearch.WordTrace tailWord_4257532 prefixEnd_4257532 2186160317898141620169973 := by
  unfold tailWord_4257532
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642474605848083710523425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103523299474464111614031233 77642474605848083710523425)
  ·
    refine ⟨58231855954386062782892569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77642474605848083710523425 58231855954386062782892569)
    ·
      refine ⟨43673891965789547087169427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58231855954386062782892569 43673891965789547087169427)
      ·
        refine ⟨65510837948684320630754141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43673891965789547087169427 65510837948684320630754141)
        ·
          refine ⟨24566564230756620236532803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65510837948684320630754141 24566564230756620236532803)
          ·
            refine ⟨36849846346134930354799205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24566564230756620236532803 36849846346134930354799205)
            ·
              refine ⟨6909346189900299441524851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36849846346134930354799205 6909346189900299441524851)
              ·
                refine ⟨10364019284850449162287277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6909346189900299441524851 10364019284850449162287277)
                ·
                  refine ⟨3886507231818918435857729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10364019284850449162287277 3886507231818918435857729)
                  ·
                    refine ⟨2914880423864188826893297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3886507231818918435857729 2914880423864188826893297)
                    ·
                      refine ⟨2186160317898141620169973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2914880423864188826893297 2186160317898141620169973)
                      ·
                        rfl

theorem cell23_4257532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_4257532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257532 prefixEnd_4257532 := by exact prefixLift 4257532
  have htrace : WordTrace (prefixWord ++ tailWord_4257532) baseStart_4257532 baseEnd_4257532 := by
    simpa [prefixWord, tailWord_4257532, baseEnd_4257532] using wordTrace_append hprefix tailTrace_4257532
  have hstable : (prefixWord ++ tailWord_4257532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257532).length < 2 ^ (prefixWord ++ tailWord_4257532).sum := by decide
  have hdescent : baseEnd_4257532 < baseStart_4257532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257538 : List Nat := [3, 4, 1, 1, 1, 1, 2, 10]
def baseStart_4257538 : Nat := 118140960795 + 4257538 * 2 ^ 59
def prefixEnd_4257538 : Nat := 4983230072969 + 3 ^ 40 * 4257538 * 2
def baseEnd_4257538 : Nat := 80969014769706244322035

theorem tailTrace_4257538 : CollatzResearch.WordTrace tailWord_4257538 prefixEnd_4257538 80969014769706244322035 := by
  unfold tailWord_4257538
  simp only [CollatzResearch.WordTrace]
  refine ⟨38821292012418607611441317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103523445366449620297176845 38821292012418607611441317)
  ·
    refine ⟨7278992252328488927145247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38821292012418607611441317 7278992252328488927145247)
    ·
      refine ⟨10918488378492733390717871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7278992252328488927145247 10918488378492733390717871)
      ·
        refine ⟨16377732567739100086076807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10918488378492733390717871 16377732567739100086076807)
        ·
          refine ⟨24566598851608650129115211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16377732567739100086076807 24566598851608650129115211)
          ·
            refine ⟨36849898277412975193672817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24566598851608650129115211 36849898277412975193672817)
            ·
              refine ⟨27637423708059731395254613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36849898277412975193672817 27637423708059731395254613)
              ·
                refine ⟨80969014769706244322035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27637423708059731395254613 80969014769706244322035)
                ·
                  rfl

theorem cell23_4257538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_4257538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257538 prefixEnd_4257538 := by exact prefixLift 4257538
  have htrace : WordTrace (prefixWord ++ tailWord_4257538) baseStart_4257538 baseEnd_4257538 := by
    simpa [prefixWord, tailWord_4257538, baseEnd_4257538] using wordTrace_append hprefix tailTrace_4257538
  have hstable : (prefixWord ++ tailWord_4257538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257538).length < 2 ^ (prefixWord ++ tailWord_4257538).sum := by decide
  have hdescent : baseEnd_4257538 < baseStart_4257538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257605 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_4257605 : Nat := 118140960795 + 4257605 * 2 ^ 59
def prefixEnd_4257605 : Nat := 4983230072969 + 3 ^ 40 * 4257605 * 2
def baseEnd_4257605 : Nat := 2186197801985919834557137

theorem tailTrace_4257605 : CollatzResearch.WordTrace tailWord_4257605 prefixEnd_4257605 2186197801985919834557137 := by
  unfold tailWord_4257605
  simp only [CollatzResearch.WordTrace]
  refine ⟨155287611740431700888454269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103525074493621133925636179 155287611740431700888454269)
  ·
    refine ⟨58232854402661887833170351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155287611740431700888454269 58232854402661887833170351)
    ·
      refine ⟨87349281603992831749755527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58232854402661887833170351 87349281603992831749755527)
      ·
        refine ⟨131023922405989247624633291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87349281603992831749755527 131023922405989247624633291)
        ·
          refine ⟨196535883608983871436949937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131023922405989247624633291 196535883608983871436949937)
          ·
            refine ⟨147401912706737903577712453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196535883608983871436949937 147401912706737903577712453)
            ·
              refine ⟨27637858632513356920821085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147401912706737903577712453 27637858632513356920821085)
              ·
                refine ⟨10364196987192508845307907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27637858632513356920821085 10364196987192508845307907)
                ·
                  refine ⟨15546295480788763267961861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10364196987192508845307907 15546295480788763267961861)
                  ·
                    refine ⟨2914930402647893112742849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15546295480788763267961861 2914930402647893112742849)
                    ·
                      refine ⟨2186197801985919834557137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2914930402647893112742849 2186197801985919834557137)
                      ·
                        rfl

theorem cell23_4257605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_4257605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257605 prefixEnd_4257605 := by exact prefixLift 4257605
  have htrace : WordTrace (prefixWord ++ tailWord_4257605) baseStart_4257605 baseEnd_4257605 := by
    simpa [prefixWord, tailWord_4257605, baseEnd_4257605] using wordTrace_append hprefix tailTrace_4257605
  have hstable : (prefixWord ++ tailWord_4257605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257605).length < 2 ^ (prefixWord ++ tailWord_4257605).sum := by decide
  have hdescent : baseEnd_4257605 < baseStart_4257605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257608 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_4257608 : Nat := 118140960795 + 4257608 * 2 ^ 59
def prefixEnd_4257608 : Nat := 4983230072969 + 3 ^ 40 * 4257608 * 2
def baseEnd_4257608 : Nat := 2186199342427883322819623

theorem tailTrace_4257608 : CollatzResearch.WordTrace tailWord_4257608 prefixEnd_4257608 2186199342427883322819623 := by
  unfold tailWord_4257608
  simp only [CollatzResearch.WordTrace]
  refine ⟨77643860579710416200406739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103525147439613888267208985 77643860579710416200406739)
  ·
    refine ⟨116465790869565624300610109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77643860579710416200406739 116465790869565624300610109)
    ·
      refine ⟨43674671576087109112728791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116465790869565624300610109 43674671576087109112728791)
      ·
        refine ⟨65512007364130663669093187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43674671576087109112728791 65512007364130663669093187)
        ·
          refine ⟨98268011046195995503639781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65512007364130663669093187 98268011046195995503639781)
          ·
            refine ⟨18425252071161749156932459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98268011046195995503639781 18425252071161749156932459)
            ·
              refine ⟨27637878106742623735398689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18425252071161749156932459 27637878106742623735398689)
              ·
                refine ⟨20728408580056967801549017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27637878106742623735398689 20728408580056967801549017)
                ·
                  refine ⟨15546306435042725851161763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20728408580056967801549017 15546306435042725851161763)
                  ·
                    refine ⟨23319459652564088776742645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15546306435042725851161763 23319459652564088776742645)
                    ·
                      refine ⟨2186199342427883322819623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23319459652564088776742645 2186199342427883322819623)
                      ·
                        rfl

theorem cell23_4257608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_4257608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257608 prefixEnd_4257608 := by exact prefixLift 4257608
  have htrace : WordTrace (prefixWord ++ tailWord_4257608) baseStart_4257608 baseEnd_4257608 := by
    simpa [prefixWord, tailWord_4257608, baseEnd_4257608] using wordTrace_append hprefix tailTrace_4257608
  have hstable : (prefixWord ++ tailWord_4257608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257608).length < 2 ^ (prefixWord ++ tailWord_4257608).sum := by decide
  have hdescent : baseEnd_4257608 < baseStart_4257608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257639 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_4257639 : Nat := 118140960795 + 4257639 * 2 ^ 59
def prefixEnd_4257639 : Nat := 4983230072969 + 3 ^ 40 * 4257639 * 2
def baseEnd_4257639 : Nat := 2186215260328172701531981

theorem tailTrace_4257639 : CollatzResearch.WordTrace tailWord_4257639 prefixEnd_4257639 2186215260328172701531981 := by
  unfold tailWord_4257639
  simp only [CollatzResearch.WordTrace]
  refine ⟨155288851822308524695191971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103525901214872349796794647 155288851822308524695191971)
  ·
    refine ⟨232933277733462787042787957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155288851822308524695191971 232933277733462787042787957)
    ·
      refine ⟨21837494787512136285261371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232933277733462787042787957 21837494787512136285261371)
      ·
        refine ⟨32756242181268204427892057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21837494787512136285261371 32756242181268204427892057)
        ·
          refine ⟨24567181635951153320919043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32756242181268204427892057 24567181635951153320919043)
          ·
            refine ⟨36850772453926729981378565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24567181635951153320919043 36850772453926729981378565)
            ·
              refine ⟨6909519835111261871508481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36850772453926729981378565 6909519835111261871508481)
              ·
                refine ⟨5182139876333446403631361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6909519835111261871508481 5182139876333446403631361)
                ·
                  refine ⟨3886604907250084802723521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182139876333446403631361 3886604907250084802723521)
                  ·
                    refine ⟨2914953680437563602042641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3886604907250084802723521 2914953680437563602042641)
                    ·
                      refine ⟨2186215260328172701531981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2914953680437563602042641 2186215260328172701531981)
                      ·
                        rfl

theorem cell23_4257639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_4257639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257639 prefixEnd_4257639 := by exact prefixLift 4257639
  have htrace : WordTrace (prefixWord ++ tailWord_4257639) baseStart_4257639 baseEnd_4257639 := by
    simpa [prefixWord, tailWord_4257639, baseEnd_4257639] using wordTrace_append hprefix tailTrace_4257639
  have hstable : (prefixWord ++ tailWord_4257639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257639).length < 2 ^ (prefixWord ++ tailWord_4257639).sum := by decide
  have hdescent : baseEnd_4257639 < baseStart_4257639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257658 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_4257658 : Nat := 118140960795 + 4257658 * 2 ^ 59
def prefixEnd_4257658 : Nat := 4983230072969 + 3 ^ 40 * 4257658 * 2
def baseEnd_4257658 : Nat := 728741672153536042398131

theorem tailTrace_4257658 : CollatzResearch.WordTrace tailWord_4257658 prefixEnd_4257658 728741672153536042398131 := by
  unfold tailWord_4257658
  simp only [CollatzResearch.WordTrace]
  refine ⟨38822386202309922735033407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103526363206159793960089085 38822386202309922735033407)
  ·
    refine ⟨58233579303464884102550111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38822386202309922735033407 58233579303464884102550111)
    ·
      refine ⟨87350368955197326153825167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58233579303464884102550111 87350368955197326153825167)
      ·
        refine ⟨131025553432795989230737751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87350368955197326153825167 131025553432795989230737751)
        ·
          refine ⟨196538330149193983846106627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131025553432795989230737751 196538330149193983846106627)
          ·
            refine ⟨294807495223790975769159941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196538330149193983846106627 294807495223790975769159941)
            ·
              refine ⟨55276405354460807956717489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294807495223790975769159941 55276405354460807956717489)
              ·
                refine ⟨41457304015845605967538117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55276405354460807956717489 41457304015845605967538117)
                ·
                  refine ⟨7773244502971051118913397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41457304015845605967538117 7773244502971051118913397)
                  ·
                    refine ⟨728741672153536042398131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7773244502971051118913397 728741672153536042398131)
                    ·
                      rfl

theorem cell23_4257658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_4257658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257658 prefixEnd_4257658 := by exact prefixLift 4257658
  have htrace : WordTrace (prefixWord ++ tailWord_4257658) baseStart_4257658 baseEnd_4257658 := by
    simpa [prefixWord, tailWord_4257658, baseEnd_4257658] using wordTrace_append hprefix tailTrace_4257658
  have hstable : (prefixWord ++ tailWord_4257658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257658).length < 2 ^ (prefixWord ++ tailWord_4257658).sum := by decide
  have hdescent : baseEnd_4257658 < baseStart_4257658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257662 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_4257662 : Nat := 118140960795 + 4257662 * 2 ^ 59
def prefixEnd_4257662 : Nat := 4983230072969 + 3 ^ 40 * 4257662 * 2
def baseEnd_4257662 : Nat := 242914118931469567949375

theorem tailTrace_4257662 : CollatzResearch.WordTrace tailWord_4257662 prefixEnd_4257662 242914118931469567949375 := by
  unfold tailWord_4257662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411211337653149952909905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103526460467483466415519493 19411211337653149952909905)
  ·
    refine ⟨14558408503239862464682429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19411211337653149952909905 14558408503239862464682429)
    ·
      refine ⟨5459403188714948424255911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14558408503239862464682429 5459403188714948424255911)
      ·
        refine ⟨8189104783072422636383867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459403188714948424255911 8189104783072422636383867)
        ·
          refine ⟨12283657174608633954575801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189104783072422636383867 12283657174608633954575801)
          ·
            refine ⟨9212742880956475465931851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12283657174608633954575801 9212742880956475465931851)
            ·
              refine ⟨13819114321434713198897777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9212742880956475465931851 13819114321434713198897777)
              ·
                refine ⟨10364335741076034899173333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13819114321434713198897777 10364335741076034899173333)
                ·
                  refine ⟨242914118931469567949375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10364335741076034899173333 242914118931469567949375)
                  ·
                    rfl

theorem cell23_4257662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_4257662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257662 prefixEnd_4257662 := by exact prefixLift 4257662
  have htrace : WordTrace (prefixWord ++ tailWord_4257662) baseStart_4257662 baseEnd_4257662 := by
    simpa [prefixWord, tailWord_4257662, baseEnd_4257662] using wordTrace_append hprefix tailTrace_4257662
  have hstable : (prefixWord ++ tailWord_4257662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257662).length < 2 ^ (prefixWord ++ tailWord_4257662).sum := by decide
  have hdescent : baseEnd_4257662 < baseStart_4257662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257668 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4257668 : Nat := 118140960795 + 4257668 * 2 ^ 59
def prefixEnd_4257668 : Nat := 4983230072969 + 3 ^ 40 * 4257668 * 2
def baseEnd_4257668 : Nat := 2186230151267153088069347

theorem tailTrace_4257668 : CollatzResearch.WordTrace tailWord_4257668 prefixEnd_4257668 2186230151267153088069347 := by
  unfold tailWord_4257668
  simp only [CollatzResearch.WordTrace]
  refine ⟨77644954769601731323998829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103526606359468975098665105 77644954769601731323998829)
  ·
    refine ⟨29116858038600649246499561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77644954769601731323998829 29116858038600649246499561)
    ·
      refine ⟨21837643528950486934874671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29116858038600649246499561 21837643528950486934874671)
      ·
        refine ⟨32756465293425730402312007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21837643528950486934874671 32756465293425730402312007)
        ·
          refine ⟨49134697940138595603468011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32756465293425730402312007 49134697940138595603468011)
          ·
            refine ⟨73702046910207893405202017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49134697940138595603468011 73702046910207893405202017)
            ·
              refine ⟨55276535182655920053901513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73702046910207893405202017 55276535182655920053901513)
              ·
                refine ⟨41457401386991940040426135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55276535182655920053901513 41457401386991940040426135)
                ·
                  refine ⟨62186102080487910060639203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41457401386991940040426135 62186102080487910060639203)
                  ·
                    refine ⟨93279153120731865090958805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62186102080487910060639203 93279153120731865090958805)
                    ·
                      refine ⟨2186230151267153088069347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93279153120731865090958805 2186230151267153088069347)
                      ·
                        rfl

theorem cell23_4257668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4257668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257668 prefixEnd_4257668 := by exact prefixLift 4257668
  have htrace : WordTrace (prefixWord ++ tailWord_4257668) baseStart_4257668 baseEnd_4257668 := by
    simpa [prefixWord, tailWord_4257668, baseEnd_4257668] using wordTrace_append hprefix tailTrace_4257668
  have hstable : (prefixWord ++ tailWord_4257668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257668).length < 2 ^ (prefixWord ++ tailWord_4257668).sum := by decide
  have hdescent : baseEnd_4257668 < baseStart_4257668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257708 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_4257708 : Nat := 118140960795 + 4257708 * 2 ^ 59
def prefixEnd_4257708 : Nat := 4983230072969 + 3 ^ 40 * 4257708 * 2
def baseEnd_4257708 : Nat := 2186250690493332931569163

theorem tailTrace_4257708 : CollatzResearch.WordTrace tailWord_4257708 prefixEnd_4257708 2186250690493332931569163 := by
  unfold tailWord_4257708
  simp only [CollatzResearch.WordTrace]
  refine ⟨77645684229529274739726889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103527578972705699652969185 77645684229529274739726889)
  ·
    refine ⟨58234263172146956054795167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77645684229529274739726889 58234263172146956054795167)
    ·
      refine ⟨87351394758220434082192751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58234263172146956054795167 87351394758220434082192751)
      ·
        refine ⟨131027092137330651123289127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87351394758220434082192751 131027092137330651123289127)
        ·
          refine ⟨196540638205995976684933691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131027092137330651123289127 196540638205995976684933691)
          ·
            refine ⟨294810957308993965027400537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196540638205995976684933691 294810957308993965027400537)
            ·
              refine ⟨221108217981745473770550403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294810957308993965027400537 221108217981745473770550403)
              ·
                refine ⟨331662326972618210655825605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221108217981745473770550403 331662326972618210655825605)
                ·
                  refine ⟨62186686307365914497967301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331662326972618210655825605 62186686307365914497967301)
                  ·
                    refine ⟨11660003682631108968368869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62186686307365914497967301 11660003682631108968368869)
                    ·
                      refine ⟨2186250690493332931569163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11660003682631108968368869 2186250690493332931569163)
                      ·
                        rfl

theorem cell23_4257708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_4257708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257708 prefixEnd_4257708 := by exact prefixLift 4257708
  have htrace : WordTrace (prefixWord ++ tailWord_4257708) baseStart_4257708 baseEnd_4257708 := by
    simpa [prefixWord, tailWord_4257708, baseEnd_4257708] using wordTrace_append hprefix tailTrace_4257708
  have hstable : (prefixWord ++ tailWord_4257708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257708).length < 2 ^ (prefixWord ++ tailWord_4257708).sum := by decide
  have hdescent : baseEnd_4257708 < baseStart_4257708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257795 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 6, 4]
def baseStart_4257795 : Nat := 118140960795 + 4257795 * 2 ^ 59
def prefixEnd_4257795 : Nat := 4983230072969 + 3 ^ 40 * 4257795 * 2
def baseEnd_4257795 : Nat := 728765121103424697060421

theorem tailTrace_4257795 : CollatzResearch.WordTrace tailWord_4257795 prefixEnd_4257795 728765121103424697060421 := by
  unfold tailWord_4257795
  simp only [CollatzResearch.WordTrace]
  refine ⟨155294541609743363337870839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103529694406495575558580559 155294541609743363337870839)
  ·
    refine ⟨232941812414615045006806259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155294541609743363337870839 232941812414615045006806259)
    ·
      refine ⟨349412718621922567510209389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232941812414615045006806259 349412718621922567510209389)
      ·
        refine ⟨131029769483220962816328521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349412718621922567510209389 131029769483220962816328521)
        ·
          refine ⟨98272327112415722112246391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131029769483220962816328521 98272327112415722112246391)
          ·
            refine ⟨147408490668623583168369587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98272327112415722112246391 147408490668623583168369587)
            ·
              refine ⟨221112736002935374752554381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147408490668623583168369587 221112736002935374752554381)
              ·
                refine ⟨82917276001100765532207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221112736002935374752554381 82917276001100765532207893)
                ·
                  refine ⟨3886747312551598384322245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82917276001100765532207893 3886747312551598384322245)
                  ·
                    refine ⟨728765121103424697060421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3886747312551598384322245 728765121103424697060421)
                    ·
                      rfl

theorem cell23_4257795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 4].length) (baseStart_4257795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257795 prefixEnd_4257795 := by exact prefixLift 4257795
  have htrace : WordTrace (prefixWord ++ tailWord_4257795) baseStart_4257795 baseEnd_4257795 := by
    simpa [prefixWord, tailWord_4257795, baseEnd_4257795] using wordTrace_append hprefix tailTrace_4257795
  have hstable : (prefixWord ++ tailWord_4257795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257795).length < 2 ^ (prefixWord ++ tailWord_4257795).sum := by decide
  have hdescent : baseEnd_4257795 < baseStart_4257795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257799 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 1, 5]
def baseStart_4257799 : Nat := 118140960795 + 4257799 * 2 ^ 59
def prefixEnd_4257799 : Nat := 4983230072969 + 3 ^ 40 * 4257799 * 2
def baseEnd_4257799 : Nat := 728765805744297358510415

theorem tailTrace_4257799 : CollatzResearch.WordTrace tailWord_4257799 prefixEnd_4257799 728765805744297358510415 := by
  unfold tailWord_4257799
  simp only [CollatzResearch.WordTrace]
  refine ⟨155294687501728872021016451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103529791667819248014010967 155294687501728872021016451)
  ·
    refine ⟨232942031252593308031524677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155294687501728872021016451 232942031252593308031524677)
    ·
      refine ⟨43676630859861245255910877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232942031252593308031524677 43676630859861245255910877)
      ·
        refine ⟨16378736572447966970966579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43676630859861245255910877 16378736572447966970966579)
        ·
          refine ⟨24568104858671950456449869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16378736572447966970966579 24568104858671950456449869)
          ·
            refine ⟨9213039322001981421168701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24568104858671950456449869 9213039322001981421168701)
            ·
              refine ⟨3454889745750743032938263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9213039322001981421168701 3454889745750743032938263)
              ·
                refine ⟨5182334618626114549407395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454889745750743032938263 5182334618626114549407395)
                ·
                  refine ⟨7773501927939171824111093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182334618626114549407395 7773501927939171824111093)
                  ·
                    refine ⟨728765805744297358510415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7773501927939171824111093 728765805744297358510415)
                    ·
                      rfl

theorem cell23_4257799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_4257799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257799 prefixEnd_4257799 := by exact prefixLift 4257799
  have htrace : WordTrace (prefixWord ++ tailWord_4257799) baseStart_4257799 baseEnd_4257799 := by
    simpa [prefixWord, tailWord_4257799, baseEnd_4257799] using wordTrace_append hprefix tailTrace_4257799
  have hstable : (prefixWord ++ tailWord_4257799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257799).length < 2 ^ (prefixWord ++ tailWord_4257799).sum := by decide
  have hdescent : baseEnd_4257799 < baseStart_4257799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257842 : List Nat := [3, 2, 1, 1, 2, 4, 3, 7]
def baseStart_4257842 : Nat := 118140960795 + 4257842 * 2 ^ 59
def prefixEnd_4257842 : Nat := 4983230072969 + 3 ^ 40 * 4257842 * 2
def baseEnd_4257842 : Nat := 80974796181519829899761

theorem tailTrace_4257842 : CollatzResearch.WordTrace tailWord_4257842 prefixEnd_4257842 80974796181519829899761 := by
  unfold tailWord_4257842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38824063960143272591207945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103530837227048726909887853 38824063960143272591207945)
  ·
    refine ⟨29118047970107454443405959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38824063960143272591207945 29118047970107454443405959)
    ·
      refine ⟨43677071955161181665108939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29118047970107454443405959 43677071955161181665108939)
      ·
        refine ⟨65515607932741772497663409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43677071955161181665108939 65515607932741772497663409)
        ·
          refine ⟨49136705949556329373247557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65515607932741772497663409 49136705949556329373247557)
          ·
            refine ⟨9213132365541811757483917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49136705949556329373247557 9213132365541811757483917)
            ·
              refine ⟨3454924637078179409056469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9213132365541811757483917 3454924637078179409056469)
              ·
                refine ⟨80974796181519829899761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3454924637078179409056469 80974796181519829899761)
                ·
                  rfl

theorem cell23_4257842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_4257842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257842 prefixEnd_4257842 := by exact prefixLift 4257842
  have htrace : WordTrace (prefixWord ++ tailWord_4257842) baseStart_4257842 baseEnd_4257842 := by
    simpa [prefixWord, tailWord_4257842, baseEnd_4257842] using wordTrace_append hprefix tailTrace_4257842
  have hstable : (prefixWord ++ tailWord_4257842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257842).length < 2 ^ (prefixWord ++ tailWord_4257842).sum := by decide
  have hdescent : baseEnd_4257842 < baseStart_4257842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257852 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_4257852 : Nat := 118140960795 + 4257852 * 2 ^ 59
def prefixEnd_4257852 : Nat := 4983230072969 + 3 ^ 40 * 4257852 * 2
def baseEnd_4257852 : Nat := 2186324631707580368168501

theorem tailTrace_4257852 : CollatzResearch.WordTrace tailWord_4257852 prefixEnd_4257852 2186324631707580368168501 := by
  unfold tailWord_4257852
  simp only [CollatzResearch.WordTrace]
  refine ⟨77648310285268431036347905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103531080380357908048463873 77648310285268431036347905)
  ·
    refine ⟨58236232713951323277260929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77648310285268431036347905 58236232713951323277260929)
    ·
      refine ⟨43677174535463492457945697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58236232713951323277260929 43677174535463492457945697)
      ·
        refine ⟨32757880901597619343459273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43677174535463492457945697 32757880901597619343459273)
        ·
          refine ⟨24568410676198214507594455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32757880901597619343459273 24568410676198214507594455)
          ·
            refine ⟨36852616014297321761391683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24568410676198214507594455 36852616014297321761391683)
            ·
              refine ⟨55278924021445982642087525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36852616014297321761391683 55278924021445982642087525)
              ·
                refine ⟨10364798254021121745391411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55278924021445982642087525 10364798254021121745391411)
                ·
                  refine ⟨15547197381031682618087117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10364798254021121745391411 15547197381031682618087117)
                  ·
                    refine ⟨5830199017886880981782669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15547197381031682618087117 5830199017886880981782669)
                    ·
                      refine ⟨2186324631707580368168501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830199017886880981782669 2186324631707580368168501)
                      ·
                        rfl

theorem cell23_4257852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_4257852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257852 prefixEnd_4257852 := by exact prefixLift 4257852
  have htrace : WordTrace (prefixWord ++ tailWord_4257852) baseStart_4257852 baseEnd_4257852 := by
    simpa [prefixWord, tailWord_4257852, baseEnd_4257852] using wordTrace_append hprefix tailTrace_4257852
  have hstable : (prefixWord ++ tailWord_4257852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257852).length < 2 ^ (prefixWord ++ tailWord_4257852).sum := by decide
  have hdescent : baseEnd_4257852 < baseStart_4257852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257853 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_4257853 : Nat := 118140960795 + 4257853 * 2 ^ 59
def prefixEnd_4257853 : Nat := 4983230072969 + 3 ^ 40 * 4257853 * 2
def baseEnd_4257853 : Nat := 2186325145188234864255997

theorem tailTrace_4257853 : CollatzResearch.WordTrace tailWord_4257853 prefixEnd_4257853 2186325145188234864255997 := by
  unfold tailWord_4257853
  simp only [CollatzResearch.WordTrace]
  refine ⟨155296657043533239243482213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103531104695688826162321475 155296657043533239243482213)
  ·
    refine ⟨29118123195662482358152915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155296657043533239243482213 29118123195662482358152915)
    ·
      refine ⟨43677184793493723537229373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29118123195662482358152915 43677184793493723537229373)
      ·
        refine ⟨16378944297560146326461015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43677184793493723537229373 16378944297560146326461015)
        ·
          refine ⟨24568416446340219489691523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16378944297560146326461015 24568416446340219489691523)
          ·
            refine ⟨36852624669510329234537285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24568416446340219489691523 36852624669510329234537285)
            ·
              refine ⟨6909867125533186731475741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36852624669510329234537285 6909867125533186731475741)
              ·
                refine ⟨2591200172074945024303403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6909867125533186731475741 2591200172074945024303403)
                ·
                  refine ⟨3886800258112417536455105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591200172074945024303403 3886800258112417536455105)
                  ·
                    refine ⟨2915100193584313152341329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3886800258112417536455105 2915100193584313152341329)
                    ·
                      refine ⟨2186325145188234864255997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915100193584313152341329 2186325145188234864255997)
                      ·
                        rfl

theorem cell23_4257853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_4257853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257853 prefixEnd_4257853 := by exact prefixLift 4257853
  have htrace : WordTrace (prefixWord ++ tailWord_4257853) baseStart_4257853 baseEnd_4257853 := by
    simpa [prefixWord, tailWord_4257853, baseEnd_4257853] using wordTrace_append hprefix tailTrace_4257853
  have hstable : (prefixWord ++ tailWord_4257853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257853).length < 2 ^ (prefixWord ++ tailWord_4257853).sum := by decide
  have hdescent : baseEnd_4257853 < baseStart_4257853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257856 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3]
def baseStart_4257856 : Nat := 118140960795 + 4257856 * 2 ^ 59
def prefixEnd_4257856 : Nat := 4983230072969 + 3 ^ 40 * 4257856 * 2
def baseEnd_4257856 : Nat := 2186326685630198352518483

theorem tailTrace_4257856 : CollatzResearch.WordTrace tailWord_4257856 prefixEnd_4257856 2186326685630198352518483 := by
  unfold tailWord_4257856
  simp only [CollatzResearch.WordTrace]
  refine ⟨77648383231261185377920711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103531177641681580503894281 77648383231261185377920711)
  ·
    refine ⟨116472574846891778066881067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77648383231261185377920711 116472574846891778066881067)
    ·
      refine ⟨174708862270337667100321601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116472574846891778066881067 174708862270337667100321601)
      ·
        refine ⟨131031646702753250325241201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174708862270337667100321601 131031646702753250325241201)
        ·
          refine ⟨98273735027064937743930901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131031646702753250325241201 98273735027064937743930901)
          ·
            refine ⟨4606581329393668956746761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98273735027064937743930901 4606581329393668956746761)
            ·
              refine ⟨3454935997045251717560071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606581329393668956746761 3454935997045251717560071)
              ·
                refine ⟨5182403995567877576340107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454935997045251717560071 5182403995567877576340107)
                ·
                  refine ⟨7773605993351816364510161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182403995567877576340107 7773605993351816364510161)
                  ·
                    refine ⟨5830204495013862273382621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7773605993351816364510161 5830204495013862273382621)
                    ·
                      refine ⟨2186326685630198352518483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830204495013862273382621 2186326685630198352518483)
                      ·
                        rfl

theorem cell23_4257856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_4257856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257856 prefixEnd_4257856 := by exact prefixLift 4257856
  have htrace : WordTrace (prefixWord ++ tailWord_4257856) baseStart_4257856 baseEnd_4257856 := by
    simpa [prefixWord, tailWord_4257856, baseEnd_4257856] using wordTrace_append hprefix tailTrace_4257856
  have hstable : (prefixWord ++ tailWord_4257856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257856).length < 2 ^ (prefixWord ++ tailWord_4257856).sum := by decide
  have hdescent : baseEnd_4257856 < baseStart_4257856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257943 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_4257943 : Nat := 118140960795 + 4257943 * 2 ^ 59
def prefixEnd_4257943 : Nat := 4983230072969 + 3 ^ 40 * 4257943 * 2
def baseEnd_4257943 : Nat := 2186371358447139512130583

theorem tailTrace_4257943 : CollatzResearch.WordTrace tailWord_4257943 prefixEnd_4257943 2186371358447139512130583 := by
  unfold tailWord_4257943
  simp only [CollatzResearch.WordTrace]
  refine ⟨155299939613207184614258483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103533293075471456409505655 155299939613207184614258483)
  ·
    refine ⟨232949909419810776921387725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155299939613207184614258483 232949909419810776921387725)
    ·
      refine ⟨87356216032429041345520397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232949909419810776921387725 87356216032429041345520397)
      ·
        refine ⟨32758581012160890504570149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87356216032429041345520397 32758581012160890504570149)
        ·
          refine ⟨6142233939780166969606903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32758581012160890504570149 6142233939780166969606903)
          ·
            refine ⟨9213350909670250454410355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6142233939780166969606903 9213350909670250454410355)
            ·
              refine ⟨13820026364505375681615533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9213350909670250454410355 13820026364505375681615533)
              ·
                refine ⟨5182509886689515880605825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13820026364505375681615533 5182509886689515880605825)
                ·
                  refine ⟨3886882415017136910454369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182509886689515880605825 3886882415017136910454369)
                  ·
                    refine ⟨2915161811262852682840777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3886882415017136910454369 2915161811262852682840777)
                    ·
                      refine ⟨2186371358447139512130583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915161811262852682840777 2186371358447139512130583)
                      ·
                        rfl

theorem cell23_4257943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_4257943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257943 prefixEnd_4257943 := by exact prefixLift 4257943
  have htrace : WordTrace (prefixWord ++ tailWord_4257943) baseStart_4257943 baseEnd_4257943 := by
    simpa [prefixWord, tailWord_4257943, baseEnd_4257943] using wordTrace_append hprefix tailTrace_4257943
  have hstable : (prefixWord ++ tailWord_4257943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257943).length < 2 ^ (prefixWord ++ tailWord_4257943).sum := by decide
  have hdescent : baseEnd_4257943 < baseStart_4257943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257945 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_4257945 : Nat := 118140960795 + 4257945 * 2 ^ 59
def prefixEnd_4257945 : Nat := 4983230072969 + 3 ^ 40 * 4257945 * 2
def baseEnd_4257945 : Nat := 728790795136149501435191

theorem tailTrace_4257945 : CollatzResearch.WordTrace tailWord_4257945 prefixEnd_4257945 728790795136149501435191 := by
  unfold tailWord_4257945
  simp only [CollatzResearch.WordTrace]
  refine ⟨155300012559199938955831289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103533341706133292637220859 155300012559199938955831289)
  ·
    refine ⟨116475009419399954216873467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155300012559199938955831289 116475009419399954216873467)
    ·
      refine ⟨174712514129099931325310201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116475009419399954216873467 174712514129099931325310201)
      ·
        refine ⟨131034385596824948493982651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174712514129099931325310201 131034385596824948493982651)
        ·
          refine ⟨196551578395237422740973977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131034385596824948493982651 196551578395237422740973977)
          ·
            refine ⟨147413683796428067055730483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196551578395237422740973977 147413683796428067055730483)
            ·
              refine ⟨221120525694642100583595725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147413683796428067055730483 221120525694642100583595725)
              ·
                refine ⟨82920197135490787718848397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221120525694642100583595725 82920197135490787718848397)
                ·
                  refine ⟨31095073925809045394568149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82920197135490787718848397 31095073925809045394568149)
                  ·
                    refine ⟨728790795136149501435191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31095073925809045394568149 728790795136149501435191)
                    ·
                      rfl

theorem cell23_4257945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_4257945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257945 prefixEnd_4257945 := by exact prefixLift 4257945
  have htrace : WordTrace (prefixWord ++ tailWord_4257945) baseStart_4257945 baseEnd_4257945 := by
    simpa [prefixWord, tailWord_4257945, baseEnd_4257945] using wordTrace_append hprefix tailTrace_4257945
  have hstable : (prefixWord ++ tailWord_4257945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257945).length < 2 ^ (prefixWord ++ tailWord_4257945).sum := by decide
  have hdescent : baseEnd_4257945 < baseStart_4257945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4257999 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 2, 4, 2]
def baseStart_4257999 : Nat := 118140960795 + 4257999 * 2 ^ 59
def prefixEnd_4257999 : Nat := 4983230072969 + 3 ^ 40 * 4257999 * 2
def baseEnd_4257999 : Nat := 2186400113363791293030325

theorem tailTrace_4257999 : CollatzResearch.WordTrace tailWord_4257999 prefixEnd_4257999 2186400113363791293030325 := by
  unfold tailWord_4257999
  simp only [CollatzResearch.WordTrace]
  refine ⟨155301982101004306178297051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103534654734002870785531367 155301982101004306178297051)
  ·
    refine ⟨232952973151506459267445577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155301982101004306178297051 232952973151506459267445577)
    ·
      refine ⟨174714729863629844450584183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232952973151506459267445577 174714729863629844450584183)
      ·
        refine ⟨262072094795444766675876275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174714729863629844450584183 262072094795444766675876275)
        ·
          refine ⟨393108142193167150013814413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262072094795444766675876275 393108142193167150013814413)
          ·
            refine ⟨147415553322437681255180405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393108142193167150013814413 147415553322437681255180405)
            ·
              refine ⟨13820208123978532617673163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147415553322437681255180405 13820208123978532617673163)
              ·
                refine ⟨20730312185967798926509745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13820208123978532617673163 20730312185967798926509745)
                ·
                  refine ⟨15547734139475849194882309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20730312185967798926509745 15547734139475849194882309)
                  ·
                    refine ⟨2915200151151721724040433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15547734139475849194882309 2915200151151721724040433)
                    ·
                      refine ⟨2186400113363791293030325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915200151151721724040433 2186400113363791293030325)
                      ·
                        rfl

theorem cell23_4257999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4, 2].length) (baseStart_4257999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4257999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4257999 prefixEnd_4257999 := by exact prefixLift 4257999
  have htrace : WordTrace (prefixWord ++ tailWord_4257999) baseStart_4257999 baseEnd_4257999 := by
    simpa [prefixWord, tailWord_4257999, baseEnd_4257999] using wordTrace_append hprefix tailTrace_4257999
  have hstable : (prefixWord ++ tailWord_4257999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4257999).length < 2 ^ (prefixWord ++ tailWord_4257999).sum := by decide
  have hdescent : baseEnd_4257999 < baseStart_4257999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4257999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258032 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_4258032 : Nat := 118140960795 + 4258032 * 2 ^ 59
def prefixEnd_4258032 : Nat := 4983230072969 + 3 ^ 40 * 4258032 * 2
def baseEnd_4258032 : Nat := 2186417058225389663917673

theorem tailTrace_4258032 : CollatzResearch.WordTrace tailWord_4258032 prefixEnd_4258032 2186417058225389663917673 := by
  unfold tailWord_4258032
  simp only [CollatzResearch.WordTrace]
  refine ⟨77651592854942376407124175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103535457139923168542832233 77651592854942376407124175)
  ·
    refine ⟨116477389282413564610686263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77651592854942376407124175 116477389282413564610686263)
    ·
      refine ⟨174716083923620346916029395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116477389282413564610686263 174716083923620346916029395)
      ·
        refine ⟨262074125885430520374044093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174716083923620346916029395 262074125885430520374044093)
        ·
          refine ⟨98277797207036445140266535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262074125885430520374044093 98277797207036445140266535)
          ·
            refine ⟨147416695810554667710399803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98277797207036445140266535 147416695810554667710399803)
            ·
              refine ⟨221125043715832001565599705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147416695810554667710399803 221125043715832001565599705)
              ·
                refine ⟨165843782786874001174199779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221125043715832001565599705 165843782786874001174199779)
                ·
                  refine ⟨248765674180311001761299669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165843782786874001174199779 248765674180311001761299669)
                  ·
                    refine ⟨5830445488601039103780461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 248765674180311001761299669 5830445488601039103780461)
                    ·
                      refine ⟨2186417058225389663917673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830445488601039103780461 2186417058225389663917673)
                      ·
                        rfl

theorem cell23_4258032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_4258032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258032 prefixEnd_4258032 := by exact prefixLift 4258032
  have htrace : WordTrace (prefixWord ++ tailWord_4258032) baseStart_4258032 baseEnd_4258032 := by
    simpa [prefixWord, tailWord_4258032, baseEnd_4258032] using wordTrace_append hprefix tailTrace_4258032
  have hstable : (prefixWord ++ tailWord_4258032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258032).length < 2 ^ (prefixWord ++ tailWord_4258032).sum := by decide
  have hdescent : baseEnd_4258032 < baseStart_4258032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258042 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_4258042 : Nat := 118140960795 + 4258042 * 2 ^ 59
def prefixEnd_4258042 : Nat := 4983230072969 + 3 ^ 40 * 4258042 * 2
def baseEnd_4258042 : Nat := 2186422193031934624792627

theorem tailTrace_4258042 : CollatzResearch.WordTrace tailWord_4258042 prefixEnd_4258042 2186422193031934624792627 := by
  unfold tailWord_4258042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38825887609962131130528095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103535700293232349681408253 38825887609962131130528095)
  ·
    refine ⟨58238831414943196695792143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38825887609962131130528095 58238831414943196695792143)
    ·
      refine ⟨87358247122414795043688215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58238831414943196695792143 87358247122414795043688215)
      ·
        refine ⟨131037370683622192565532323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87358247122414795043688215 131037370683622192565532323)
        ·
          refine ⟨196556056025433288848298485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131037370683622192565532323 196556056025433288848298485)
          ·
            refine ⟨18427130252384370829527983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196556056025433288848298485 18427130252384370829527983)
            ·
              refine ⟨27640695378576556244291975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18427130252384370829527983 27640695378576556244291975)
              ·
                refine ⟨41461043067864834366437963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27640695378576556244291975 41461043067864834366437963)
                ·
                  refine ⟨62191564601797251549656945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41461043067864834366437963 62191564601797251549656945)
                  ·
                    refine ⟨46643673451347938662242709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62191564601797251549656945 46643673451347938662242709)
                    ·
                      refine ⟨2186422193031934624792627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46643673451347938662242709 2186422193031934624792627)
                      ·
                        rfl

theorem cell23_4258042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_4258042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258042 prefixEnd_4258042 := by exact prefixLift 4258042
  have htrace : WordTrace (prefixWord ++ tailWord_4258042) baseStart_4258042 baseEnd_4258042 := by
    simpa [prefixWord, tailWord_4258042, baseEnd_4258042] using wordTrace_append hprefix tailTrace_4258042
  have hstable : (prefixWord ++ tailWord_4258042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258042).length < 2 ^ (prefixWord ++ tailWord_4258042).sum := by decide
  have hdescent : baseEnd_4258042 < baseStart_4258042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258056 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 6]
def baseStart_4258056 : Nat := 118140960795 + 4258056 * 2 ^ 59
def prefixEnd_4258056 : Nat := 4983230072969 + 3 ^ 40 * 4258056 * 2
def baseEnd_4258056 : Nat := 242936597973455285557507

theorem tailTrace_4258056 : CollatzResearch.WordTrace tailWord_4258056 prefixEnd_4258056 242936597973455285557507 := by
  unfold tailWord_4258056
  simp only [CollatzResearch.WordTrace]
  refine ⟨77652030530898902456561011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103536040707865203275414681 77652030530898902456561011)
  ·
    refine ⟨116478045796348353684841517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77652030530898902456561011 116478045796348353684841517)
    ·
      refine ⟨43679267173630632631815569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116478045796348353684841517 43679267173630632631815569)
      ·
        refine ⟨32759450380222974473861677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43679267173630632631815569 32759450380222974473861677)
        ·
          refine ⟨12284793892583615427698129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32759450380222974473861677 12284793892583615427698129)
          ·
            refine ⟨9213595419437711570773597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12284793892583615427698129 9213595419437711570773597)
            ·
              refine ⟨3455098282289141839040099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9213595419437711570773597 3455098282289141839040099)
              ·
                refine ⟨5182647423433712758560149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455098282289141839040099 5182647423433712758560149)
                ·
                  refine ⟨242936597973455285557507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5182647423433712758560149 242936597973455285557507)
                  ·
                    rfl

theorem cell23_4258056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 6].length) (baseStart_4258056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258056 prefixEnd_4258056 := by exact prefixLift 4258056
  have htrace : WordTrace (prefixWord ++ tailWord_4258056) baseStart_4258056 baseEnd_4258056 := by
    simpa [prefixWord, tailWord_4258056, baseEnd_4258056] using wordTrace_append hprefix tailTrace_4258056
  have hstable : (prefixWord ++ tailWord_4258056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258056).length < 2 ^ (prefixWord ++ tailWord_4258056).sum := by decide
  have hdescent : baseEnd_4258056 < baseStart_4258056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258059 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 5, 2]
def baseStart_4258059 : Nat := 118140960795 + 4258059 * 2 ^ 59
def prefixEnd_4258059 : Nat := 4983230072969 + 3 ^ 40 * 4258059 * 2
def baseEnd_4258059 : Nat := 2186430922203061058280049

theorem tailTrace_4258059 : CollatzResearch.WordTrace tailWord_4258059 prefixEnd_4258059 2186430922203061058280049 := by
  unfold tailWord_4258059
  simp only [CollatzResearch.WordTrace]
  refine ⟨155304170480786936425481231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103536113653857957616987487 155304170480786936425481231)
  ·
    refine ⟨232956255721180404638221847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155304170480786936425481231 232956255721180404638221847)
    ·
      refine ⟨349434383581770606957332771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232956255721180404638221847 349434383581770606957332771)
      ·
        refine ⟨524151575372655910435999157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349434383581770606957332771 524151575372655910435999157)
        ·
          refine ⟨49139210191186491603374921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 524151575372655910435999157 49139210191186491603374921)
          ·
            refine ⟨36854407643389868702531191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49139210191186491603374921 36854407643389868702531191)
            ·
              refine ⟨55281611465084803053796787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36854407643389868702531191 55281611465084803053796787)
              ·
                refine ⟨82922417197627204580695181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55281611465084803053796787 82922417197627204580695181)
                ·
                  refine ⟨31095906449110201717760693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82922417197627204580695181 31095906449110201717760693)
                  ·
                    refine ⟨2915241229604081411040065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31095906449110201717760693 2915241229604081411040065)
                    ·
                      refine ⟨2186430922203061058280049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915241229604081411040065 2186430922203061058280049)
                      ·
                        rfl

theorem cell23_4258059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5, 2].length) (baseStart_4258059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258059 prefixEnd_4258059 := by exact prefixLift 4258059
  have htrace : WordTrace (prefixWord ++ tailWord_4258059) baseStart_4258059 baseEnd_4258059 := by
    simpa [prefixWord, tailWord_4258059, baseEnd_4258059] using wordTrace_append hprefix tailTrace_4258059
  have hstable : (prefixWord ++ tailWord_4258059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258059).length < 2 ^ (prefixWord ++ tailWord_4258059).sum := by decide
  have hdescent : baseEnd_4258059 < baseStart_4258059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258069 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_4258069 : Nat := 118140960795 + 4258069 * 2 ^ 59
def prefixEnd_4258069 : Nat := 4983230072969 + 3 ^ 40 * 4258069 * 2
def baseEnd_4258069 : Nat := 728812019003202006385001

theorem tailTrace_4258069 : CollatzResearch.WordTrace tailWord_4258069 prefixEnd_4258069 728812019003202006385001 := by
  unfold tailWord_4258069
  simp only [CollatzResearch.WordTrace]
  refine ⟨155304535210750708133345261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103536356807167138755563507 155304535210750708133345261)
  ·
    refine ⟨58239200704031515550004473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155304535210750708133345261 58239200704031515550004473)
    ·
      refine ⟨43679400528023636662503355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58239200704031515550004473 43679400528023636662503355)
      ·
        refine ⟨65519100792035454993755033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43679400528023636662503355 65519100792035454993755033)
        ·
          refine ⟨49139325594026591245316275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65519100792035454993755033 49139325594026591245316275)
          ·
            refine ⟨73708988391039886867974413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49139325594026591245316275 73708988391039886867974413)
            ·
              refine ⟨27640870646639957575490405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73708988391039886867974413 27640870646639957575490405)
              ·
                refine ⟨5182663246244992045404451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27640870646639957575490405 5182663246244992045404451)
                ·
                  refine ⟨7773994869367488068106677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182663246244992045404451 7773994869367488068106677)
                  ·
                    refine ⟨728812019003202006385001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7773994869367488068106677 728812019003202006385001)
                    ·
                      rfl

theorem cell23_4258069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_4258069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258069 prefixEnd_4258069 := by exact prefixLift 4258069
  have htrace : WordTrace (prefixWord ++ tailWord_4258069) baseStart_4258069 baseEnd_4258069 := by
    simpa [prefixWord, tailWord_4258069, baseEnd_4258069] using wordTrace_append hprefix tailTrace_4258069
  have hstable : (prefixWord ++ tailWord_4258069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258069).length < 2 ^ (prefixWord ++ tailWord_4258069).sum := by decide
  have hdescent : baseEnd_4258069 < baseStart_4258069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258076 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4258076 : Nat := 118140960795 + 4258076 * 2 ^ 59
def prefixEnd_4258076 : Nat := 4983230072969 + 3 ^ 40 * 4258076 * 2
def baseEnd_4258076 : Nat := 2186439651374187491767471

theorem tailTrace_4258076 : CollatzResearch.WordTrace tailWord_4258076 prefixEnd_4258076 2186439651374187491767471 := by
  unfold tailWord_4258076
  simp only [CollatzResearch.WordTrace]
  refine ⟨77652395260862674164425041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103536527014483565552566721 77652395260862674164425041)
  ·
    refine ⟨58239296445647005623318781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77652395260862674164425041 58239296445647005623318781)
    ·
      refine ⟨21839736167117627108744543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58239296445647005623318781 21839736167117627108744543)
      ·
        refine ⟨32759604250676440663116815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21839736167117627108744543 32759604250676440663116815)
        ·
          refine ⟨49139406376014660994675223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32759604250676440663116815 49139406376014660994675223)
          ·
            refine ⟨73709109564021991492012835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49139406376014660994675223 73709109564021991492012835)
            ·
              refine ⟨110563664346032987238019253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73709109564021991492012835 110563664346032987238019253)
              ·
                refine ⟨10365343532440592553564305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110563664346032987238019253 10365343532440592553564305)
                ·
                  refine ⟨7774007649330444415173229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10365343532440592553564305 7774007649330444415173229)
                  ·
                    refine ⟨2915252868498916655689961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7774007649330444415173229 2915252868498916655689961)
                    ·
                      refine ⟨2186439651374187491767471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915252868498916655689961 2186439651374187491767471)
                      ·
                        rfl

theorem cell23_4258076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4258076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258076 prefixEnd_4258076 := by exact prefixLift 4258076
  have htrace : WordTrace (prefixWord ++ tailWord_4258076) baseStart_4258076 baseEnd_4258076 := by
    simpa [prefixWord, tailWord_4258076, baseEnd_4258076] using wordTrace_append hprefix tailTrace_4258076
  have hstable : (prefixWord ++ tailWord_4258076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258076).length < 2 ^ (prefixWord ++ tailWord_4258076).sum := by decide
  have hdescent : baseEnd_4258076 < baseStart_4258076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258077 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_4258077 : Nat := 118140960795 + 4258077 * 2 ^ 59
def prefixEnd_4258077 : Nat := 4983230072969 + 3 ^ 40 * 4258077 * 2
def baseEnd_4258077 : Nat := 728813388284947329284989

theorem tailTrace_4258077 : CollatzResearch.WordTrace tailWord_4258077 prefixEnd_4258077 728813388284947329284989 := by
  unfold tailWord_4258077
  simp only [CollatzResearch.WordTrace]
  refine ⟨155304826994721725499636485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103536551329814483666424323 155304826994721725499636485)
  ·
    refine ⟨29119655061510323531181841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155304826994721725499636485 29119655061510323531181841)
    ·
      refine ⟨21839741296132742648386381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29119655061510323531181841 21839741296132742648386381)
      ·
        refine ⟨8189902986049778493144893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21839741296132742648386381 8189902986049778493144893)
        ·
          refine ⟨3071213619768666934929335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8189902986049778493144893 3071213619768666934929335)
          ·
            refine ⟨4606820429653000402394003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071213619768666934929335 4606820429653000402394003)
            ·
              refine ⟨6910230644479500603591005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606820429653000402394003 6910230644479500603591005)
              ·
                refine ⟨2591336491679812726346627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6910230644479500603591005 2591336491679812726346627)
                ·
                  refine ⟨3887004737519719089519941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591336491679812726346627 3887004737519719089519941)
                  ·
                    refine ⟨728813388284947329284989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887004737519719089519941 728813388284947329284989)
                    ·
                      rfl

theorem cell23_4258077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_4258077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258077 prefixEnd_4258077 := by exact prefixLift 4258077
  have htrace : WordTrace (prefixWord ++ tailWord_4258077) baseStart_4258077 baseEnd_4258077 := by
    simpa [prefixWord, tailWord_4258077, baseEnd_4258077] using wordTrace_append hprefix tailTrace_4258077
  have hstable : (prefixWord ++ tailWord_4258077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258077).length < 2 ^ (prefixWord ++ tailWord_4258077).sum := by decide
  have hdescent : baseEnd_4258077 < baseStart_4258077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258099 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 4, 4]
def baseStart_4258099 : Nat := 118140960795 + 4258099 * 2 ^ 59
def prefixEnd_4258099 : Nat := 4983230072969 + 3 ^ 40 * 4258099 * 2
def baseEnd_4258099 : Nat := 728817153809746967259955

theorem tailTrace_4258099 : CollatzResearch.WordTrace tailWord_4258099 prefixEnd_4258099 728817153809746967259955 := by
  unfold tailWord_4258099
  simp only [CollatzResearch.WordTrace]
  refine ⟨155305629400642023256937351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103537086267094682171291567 155305629400642023256937351)
  ·
    refine ⟨232958444100963034885406027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155305629400642023256937351 232958444100963034885406027)
    ·
      refine ⟨349437666151444552328109041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232958444100963034885406027 349437666151444552328109041)
      ·
        refine ⟨262078249613583414246081781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349437666151444552328109041 262078249613583414246081781)
        ·
          refine ⟨24569835901273445085570167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 262078249613583414246081781 24569835901273445085570167)
          ·
            refine ⟨36854753851910167628355251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24569835901273445085570167 36854753851910167628355251)
            ·
              refine ⟨55282130777865251442532877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36854753851910167628355251 55282130777865251442532877)
              ·
                refine ⟨20730799041699469290949829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55282130777865251442532877 20730799041699469290949829)
                ·
                  refine ⟨3887024820318650492053093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20730799041699469290949829 3887024820318650492053093)
                  ·
                    refine ⟨728817153809746967259955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887024820318650492053093 728817153809746967259955)
                    ·
                      rfl

theorem cell23_4258099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 4].length) (baseStart_4258099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258099 prefixEnd_4258099 := by exact prefixLift 4258099
  have htrace : WordTrace (prefixWord ++ tailWord_4258099) baseStart_4258099 baseEnd_4258099 := by
    simpa [prefixWord, tailWord_4258099, baseEnd_4258099] using wordTrace_append hprefix tailTrace_4258099
  have hstable : (prefixWord ++ tailWord_4258099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258099).length < 2 ^ (prefixWord ++ tailWord_4258099).sum := by decide
  have hdescent : baseEnd_4258099 < baseStart_4258099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258100 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4258100 : Nat := 118140960795 + 4258100 * 2 ^ 59
def prefixEnd_4258100 : Nat := 4983230072969 + 3 ^ 40 * 4258100 * 2
def baseEnd_4258100 : Nat := 2186451974909895397867361

theorem tailTrace_4258100 : CollatzResearch.WordTrace tailWord_4258100 prefixEnd_4258100 2186451974909895397867361 := by
  unfold tailWord_4258100
  simp only [CollatzResearch.WordTrace]
  refine ⟨77652832936819200213861877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103537110582425600285149169 77652832936819200213861877)
  ·
    refine ⟨7279953087826800020049551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77652832936819200213861877 7279953087826800020049551)
    ·
      refine ⟨10919929631740200030074327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279953087826800020049551 10919929631740200030074327)
      ·
        refine ⟨16379894447610300045111491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10919929631740200030074327 16379894447610300045111491)
        ·
          refine ⟨24569841671415450067667237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16379894447610300045111491 24569841671415450067667237)
          ·
            refine ⟨4606845313390396887687607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24569841671415450067667237 4606845313390396887687607)
            ·
              refine ⟨6910267970085595331531411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606845313390396887687607 6910267970085595331531411)
              ·
                refine ⟨10365401955128392997297117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6910267970085595331531411 10365401955128392997297117)
                ·
                  refine ⟨3887025733173147373986419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10365401955128392997297117 3887025733173147373986419)
                  ·
                    refine ⟨5830538599759721060979629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887025733173147373986419 5830538599759721060979629)
                    ·
                      refine ⟨2186451974909895397867361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830538599759721060979629 2186451974909895397867361)
                      ·
                        rfl

theorem cell23_4258100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4258100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258100 prefixEnd_4258100 := by exact prefixLift 4258100
  have htrace : WordTrace (prefixWord ++ tailWord_4258100) baseStart_4258100 baseEnd_4258100 := by
    simpa [prefixWord, tailWord_4258100, baseEnd_4258100] using wordTrace_append hprefix tailTrace_4258100
  have hstable : (prefixWord ++ tailWord_4258100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258100).length < 2 ^ (prefixWord ++ tailWord_4258100).sum := by decide
  have hdescent : baseEnd_4258100 < baseStart_4258100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258119 : List Nat := [1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_4258119 : Nat := 118140960795 + 4258119 * 2 ^ 59
def prefixEnd_4258119 : Nat := 4983230072969 + 3 ^ 40 * 4258119 * 2
def baseEnd_4258119 : Nat := 2186461731042330823529773

theorem tailTrace_4258119 : CollatzResearch.WordTrace tailWord_4258119 prefixEnd_4258119 2186461731042330823529773 := by
  unfold tailWord_4258119
  simp only [CollatzResearch.WordTrace]
  refine ⟨155306358860569566672665411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103537572573713044448443607 155306358860569566672665411)
  ·
    refine ⟨232959538290854350008998117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155306358860569566672665411 232959538290854350008998117)
    ·
      refine ⟨43679913429535190626687147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232959538290854350008998117 43679913429535190626687147)
      ·
        refine ⟨65519870144302785940030721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43679913429535190626687147 65519870144302785940030721)
        ·
          refine ⟨49139902608227089455023041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65519870144302785940030721 49139902608227089455023041)
          ·
            refine ⟨36854926956170317091267281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49139902608227089455023041 36854926956170317091267281)
            ·
              refine ⟨27641195217127737818450461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36854926956170317091267281 27641195217127737818450461)
              ·
                refine ⟨10365448206422901681918923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27641195217127737818450461 10365448206422901681918923)
                ·
                  refine ⟨15548172309634352522878385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10365448206422901681918923 15548172309634352522878385)
                  ·
                    refine ⟨11661129232225764392158789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15548172309634352522878385 11661129232225764392158789)
                    ·
                      refine ⟨2186461731042330823529773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11661129232225764392158789 2186461731042330823529773)
                      ·
                        rfl

theorem cell23_4258119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_4258119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258119 prefixEnd_4258119 := by exact prefixLift 4258119
  have htrace : WordTrace (prefixWord ++ tailWord_4258119) baseStart_4258119 baseEnd_4258119 := by
    simpa [prefixWord, tailWord_4258119, baseEnd_4258119] using wordTrace_append hprefix tailTrace_4258119
  have hstable : (prefixWord ++ tailWord_4258119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258119).length < 2 ^ (prefixWord ++ tailWord_4258119).sum := by decide
  have hdescent : baseEnd_4258119 < baseStart_4258119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258126 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_4258126 : Nat := 118140960795 + 4258126 * 2 ^ 59
def prefixEnd_4258126 : Nat := 4983230072969 + 3 ^ 40 * 4258126 * 2
def baseEnd_4258126 : Nat := 2186465325406912296142241

theorem tailTrace_4258126 : CollatzResearch.WordTrace tailWord_4258126 prefixEnd_4258126 2186465325406912296142241 := by
  unfold tailWord_4258126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413326771443025858521279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103537742781029471245446821 19413326771443025858521279)
  ·
    refine ⟨29119990157164538787781919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19413326771443025858521279 29119990157164538787781919)
    ·
      refine ⟨43679985235746808181672879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29119990157164538787781919 43679985235746808181672879)
      ·
        refine ⟨65519977853620212272509319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43679985235746808181672879 65519977853620212272509319)
        ·
          refine ⟨98279966780430318408763979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65519977853620212272509319 98279966780430318408763979)
          ·
            refine ⟨147419950170645477613145969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98279966780430318408763979 147419950170645477613145969)
            ·
              refine ⟨110564962627984108209859477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147419950170645477613145969 110564962627984108209859477)
              ·
                refine ⟨5182732623186755072337163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110564962627984108209859477 5182732623186755072337163)
                ·
                  refine ⟨7774098934780132608505745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182732623186755072337163 7774098934780132608505745)
                  ·
                    refine ⟨5830574201085099456379309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7774098934780132608505745 5830574201085099456379309)
                    ·
                      refine ⟨2186465325406912296142241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830574201085099456379309 2186465325406912296142241)
                      ·
                        rfl

theorem cell23_4258126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_4258126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258126 prefixEnd_4258126 := by exact prefixLift 4258126
  have htrace : WordTrace (prefixWord ++ tailWord_4258126) baseStart_4258126 baseEnd_4258126 := by
    simpa [prefixWord, tailWord_4258126, baseEnd_4258126] using wordTrace_append hprefix tailTrace_4258126
  have hstable : (prefixWord ++ tailWord_4258126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258126).length < 2 ^ (prefixWord ++ tailWord_4258126).sum := by decide
  have hdescent : baseEnd_4258126 < baseStart_4258126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258173 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_4258173 : Nat := 118140960795 + 4258173 * 2 ^ 59
def prefixEnd_4258173 : Nat := 4983230072969 + 3 ^ 40 * 4258173 * 2
def baseEnd_4258173 : Nat := 2186489458997673612254525

theorem tailTrace_4258173 : CollatzResearch.WordTrace tailWord_4258173 prefixEnd_4258173 2186489458997673612254525 := by
  unfold tailWord_4258173
  simp only [CollatzResearch.WordTrace]
  refine ⟨155308328402373933895131173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103538885601582622596754115 155308328402373933895131173)
  ·
    refine ⟨29120311575445112605337095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155308328402373933895131173 29120311575445112605337095)
    ·
      refine ⟨43680467363167668908005643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29120311575445112605337095 43680467363167668908005643)
      ·
        refine ⟨65520701044751503362008465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43680467363167668908005643 65520701044751503362008465)
        ·
          refine ⟨49140525783563627521506349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65520701044751503362008465 49140525783563627521506349)
          ·
            refine ⟨18427697168836360320564881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49140525783563627521506349 18427697168836360320564881)
            ·
              refine ⟨13820772876627270240423661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18427697168836360320564881 13820772876627270240423661)
              ·
                refine ⟨5182789828735226340158873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13820772876627270240423661 5182789828735226340158873)
                ·
                  refine ⟨3887092371551419755119155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182789828735226340158873 3887092371551419755119155)
                  ·
                    refine ⟨5830638557327129632678733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887092371551419755119155 5830638557327129632678733)
                    ·
                      refine ⟨2186489458997673612254525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830638557327129632678733 2186489458997673612254525)
                      ·
                        rfl

theorem cell23_4258173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_4258173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258173 prefixEnd_4258173 := by exact prefixLift 4258173
  have htrace : WordTrace (prefixWord ++ tailWord_4258173) baseStart_4258173 baseEnd_4258173 := by
    simpa [prefixWord, tailWord_4258173, baseEnd_4258173] using wordTrace_append hprefix tailTrace_4258173
  have hstable : (prefixWord ++ tailWord_4258173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258173).length < 2 ^ (prefixWord ++ tailWord_4258173).sum := by decide
  have hdescent : baseEnd_4258173 < baseStart_4258173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258183 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_4258183 : Nat := 118140960795 + 4258183 * 2 ^ 59
def prefixEnd_4258183 : Nat := 4983230072969 + 3 ^ 40 * 4258183 * 2
def baseEnd_4258183 : Nat := 2186494593804218573129479

theorem tailTrace_4258183 : CollatzResearch.WordTrace tailWord_4258183 prefixEnd_4258183 2186494593804218573129479 := by
  unfold tailWord_4258183
  simp only [CollatzResearch.WordTrace]
  refine ⟨155308693132337705602995203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103539128754891803735330135 155308693132337705602995203)
  ·
    refine ⟨232963039698506558404492805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155308693132337705602995203 232963039698506558404492805)
    ·
      refine ⟨43680569943469979700842401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232963039698506558404492805 43680569943469979700842401)
      ·
        refine ⟨32760427457602484775631801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43680569943469979700842401 32760427457602484775631801)
        ·
          refine ⟨24570320593201863581723851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32760427457602484775631801 24570320593201863581723851)
          ·
            refine ⟨36855480889802795372585777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24570320593201863581723851 36855480889802795372585777)
            ·
              refine ⟨27641610667352096529439333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36855480889802795372585777 27641610667352096529439333)
              ·
                refine ⟨5182802000128518099269875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27641610667352096529439333 5182802000128518099269875)
                ·
                  refine ⟨7774203000192777148904813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182802000128518099269875 7774203000192777148904813)
                  ·
                    refine ⟨2915326125072291430839305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7774203000192777148904813 2915326125072291430839305)
                    ·
                      refine ⟨2186494593804218573129479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915326125072291430839305 2186494593804218573129479)
                      ·
                        rfl

theorem cell23_4258183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_4258183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258183 prefixEnd_4258183 := by exact prefixLift 4258183
  have htrace : WordTrace (prefixWord ++ tailWord_4258183) baseStart_4258183 baseEnd_4258183 := by
    simpa [prefixWord, tailWord_4258183, baseEnd_4258183] using wordTrace_append hprefix tailTrace_4258183
  have hstable : (prefixWord ++ tailWord_4258183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258183).length < 2 ^ (prefixWord ++ tailWord_4258183).sum := by decide
  have hdescent : baseEnd_4258183 < baseStart_4258183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258199 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4258199 : Nat := 118140960795 + 4258199 * 2 ^ 59
def prefixEnd_4258199 : Nat := 4983230072969 + 3 ^ 40 * 4258199 * 2
def baseEnd_4258199 : Nat := 2186502809494690510529405

theorem tailTrace_4258199 : CollatzResearch.WordTrace tailWord_4258199 prefixEnd_4258199 2186502809494690510529405 := by
  unfold tailWord_4258199
  simp only [CollatzResearch.WordTrace]
  refine ⟨155309276700279740335577651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103539517800186493557051767 155309276700279740335577651)
  ·
    refine ⟨232963915050419610503366477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155309276700279740335577651 232963915050419610503366477)
    ·
      refine ⟨87361468143907353938762429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232963915050419610503366477 87361468143907353938762429)
      ·
        refine ⟨32760550553965257727035911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87361468143907353938762429 32760550553965257727035911)
        ·
          refine ⟨49140825830947886590553867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32760550553965257727035911 49140825830947886590553867)
          ·
            refine ⟨73711238746421829885830801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49140825830947886590553867 73711238746421829885830801)
            ·
              refine ⟨55283429059816372414373101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73711238746421829885830801 55283429059816372414373101)
              ·
                refine ⟨20731285897431139655389913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55283429059816372414373101 20731285897431139655389913)
                ·
                  refine ⟨15548464423073354741542435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20731285897431139655389913 15548464423073354741542435)
                  ·
                    refine ⟨23322696634610032112313653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15548464423073354741542435 23322696634610032112313653)
                    ·
                      refine ⟨2186502809494690510529405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23322696634610032112313653 2186502809494690510529405)
                      ·
                        rfl

theorem cell23_4258199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4258199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258199 prefixEnd_4258199 := by exact prefixLift 4258199
  have htrace : WordTrace (prefixWord ++ tailWord_4258199) baseStart_4258199 baseEnd_4258199 := by
    simpa [prefixWord, tailWord_4258199, baseEnd_4258199] using wordTrace_append hprefix tailTrace_4258199
  have hstable : (prefixWord ++ tailWord_4258199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258199).length < 2 ^ (prefixWord ++ tailWord_4258199).sum := by decide
  have hdescent : baseEnd_4258199 < baseStart_4258199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258200 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4258200 : Nat := 118140960795 + 4258200 * 2 ^ 59
def prefixEnd_4258200 : Nat := 4983230072969 + 3 ^ 40 * 4258200 * 2
def baseEnd_4258200 : Nat := 2186503322975345006616901

theorem tailTrace_4258200 : CollatzResearch.WordTrace tailWord_4258200 prefixEnd_4258200 2186503322975345006616901 := by
  unfold tailWord_4258200
  simp only [CollatzResearch.WordTrace]
  refine ⟨77654656586638058753182027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103539542115517411670909369 77654656586638058753182027)
  ·
    refine ⟨116481984879957088129773041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77654656586638058753182027 116481984879957088129773041)
    ·
      refine ⟨87361488659967816097329781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116481984879957088129773041 87361488659967816097329781)
      ·
        refine ⟨8190139561871982759124667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87361488659967816097329781 8190139561871982759124667)
        ·
          refine ⟨12285209342807974138687001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8190139561871982759124667 12285209342807974138687001)
          ·
            refine ⟨9213907007105980604015251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12285209342807974138687001 9213907007105980604015251)
            ·
              refine ⟨13820860510658970906022877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9213907007105980604015251 13820860510658970906022877)
              ·
                refine ⟨5182822691497114089758579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13820860510658970906022877 5182822691497114089758579)
                ·
                  refine ⟨7774234037245671134637869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182822691497114089758579 7774234037245671134637869)
                  ·
                    refine ⟨2915337763967126675489201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7774234037245671134637869 2915337763967126675489201)
                    ·
                      refine ⟨2186503322975345006616901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915337763967126675489201 2186503322975345006616901)
                      ·
                        rfl

theorem cell23_4258200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4258200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258200 prefixEnd_4258200 := by exact prefixLift 4258200
  have htrace : WordTrace (prefixWord ++ tailWord_4258200) baseStart_4258200 baseEnd_4258200 := by
    simpa [prefixWord, tailWord_4258200, baseEnd_4258200] using wordTrace_append hprefix tailTrace_4258200
  have hstable : (prefixWord ++ tailWord_4258200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258200).length < 2 ^ (prefixWord ++ tailWord_4258200).sum := by decide
  have hdescent : baseEnd_4258200 < baseStart_4258200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258213 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_4258213 : Nat := 118140960795 + 4258213 * 2 ^ 59
def prefixEnd_4258213 : Nat := 4983230072969 + 3 ^ 40 * 4258213 * 2
def baseEnd_4258213 : Nat := 2186509998223853455754341

theorem tailTrace_4258213 : CollatzResearch.WordTrace tailWord_4258213 prefixEnd_4258213 2186509998223853455754341 := by
  unfold tailWord_4258213
  simp only [CollatzResearch.WordTrace]
  refine ⟨155309787322229020726587293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103539858214819347151058195 155309787322229020726587293)
  ·
    refine ⟨58241170245835882772470235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155309787322229020726587293 58241170245835882772470235)
    ·
      refine ⟨87361755368753824158705353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58241170245835882772470235 87361755368753824158705353)
      ·
        refine ⟨65521316526565368119029015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87361755368753824158705353 65521316526565368119029015)
        ·
          refine ⟨98281974789848052178543523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65521316526565368119029015 98281974789848052178543523)
          ·
            refine ⟨147422962184772078267815285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98281974789848052178543523 147422962184772078267815285)
            ·
              refine ⟨13820902704822382337607683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147422962184772078267815285 13820902704822382337607683)
              ·
                refine ⟨20731354057233573506411525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13820902704822382337607683 20731354057233573506411525)
                ·
                  refine ⟨3887128885731295032452161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20731354057233573506411525 3887128885731295032452161)
                  ·
                    refine ⟨2915346664298471274339121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887128885731295032452161 2915346664298471274339121)
                    ·
                      refine ⟨2186509998223853455754341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915346664298471274339121 2186509998223853455754341)
                      ·
                        rfl

theorem cell23_4258213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_4258213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258213 prefixEnd_4258213 := by exact prefixLift 4258213
  have htrace : WordTrace (prefixWord ++ tailWord_4258213) baseStart_4258213 baseEnd_4258213 := by
    simpa [prefixWord, tailWord_4258213, baseEnd_4258213] using wordTrace_append hprefix tailTrace_4258213
  have hstable : (prefixWord ++ tailWord_4258213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258213).length < 2 ^ (prefixWord ++ tailWord_4258213).sum := by decide
  have hdescent : baseEnd_4258213 < baseStart_4258213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258236 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 7]
def baseStart_4258236 : Nat := 118140960795 + 4258236 * 2 ^ 59
def prefixEnd_4258236 : Nat := 4983230072969 + 3 ^ 40 * 4258236 * 2
def baseEnd_4258236 : Nat := 242946867586545207307415

theorem tailTrace_4258236 : CollatzResearch.WordTrace tailWord_4258236 prefixEnd_4258236 242946867586545207307415 := by
  unfold tailWord_4258236
  simp only [CollatzResearch.WordTrace]
  refine ⟨77655313100572847827337281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103540417467430463769783041 77655313100572847827337281)
  ·
    refine ⟨58241484825429635870502961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77655313100572847827337281 58241484825429635870502961)
    ·
      refine ⟨43681113619072226902877221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58241484825429635870502961 43681113619072226902877221)
      ·
        refine ⟨8190208803576042544289479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43681113619072226902877221 8190208803576042544289479)
        ·
          refine ⟨12285313205364063816434219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8190208803576042544289479 12285313205364063816434219)
          ·
            refine ⟨18427969808046095724651329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12285313205364063816434219 18427969808046095724651329)
            ·
              refine ⟨13820977356034571793488497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18427969808046095724651329 13820977356034571793488497)
              ·
                refine ⟨10365733017025928845116373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13820977356034571793488497 10365733017025928845116373)
                ·
                  refine ⟨242946867586545207307415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10365733017025928845116373 242946867586545207307415)
                  ·
                    rfl

theorem cell23_4258236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_4258236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258236 prefixEnd_4258236 := by exact prefixLift 4258236
  have htrace : WordTrace (prefixWord ++ tailWord_4258236) baseStart_4258236 baseEnd_4258236 := by
    simpa [prefixWord, tailWord_4258236, baseEnd_4258236] using wordTrace_append hprefix tailTrace_4258236
  have hstable : (prefixWord ++ tailWord_4258236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258236).length < 2 ^ (prefixWord ++ tailWord_4258236).sum := by decide
  have hdescent : baseEnd_4258236 < baseStart_4258236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258249 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_4258249 : Nat := 118140960795 + 4258249 * 2 ^ 59
def prefixEnd_4258249 : Nat := 4983230072969 + 3 ^ 40 * 4258249 * 2
def baseEnd_4258249 : Nat := 728842827842471771634725

theorem tailTrace_4258249 : CollatzResearch.WordTrace tailWord_4258249 prefixEnd_4258249 728842827842471771634725 := by
  unfold tailWord_4258249
  simp only [CollatzResearch.WordTrace]
  refine ⟨155311100350098598874897801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103540733566732399249931867 155311100350098598874897801)
  ·
    refine ⟨116483325262573949156173351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155311100350098598874897801 116483325262573949156173351)
    ·
      refine ⟨174724987893860923734260027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116483325262573949156173351 174724987893860923734260027)
      ·
        refine ⟨262087481840791385601390041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174724987893860923734260027 262087481840791385601390041)
        ·
          refine ⟨196565611380593539201042531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262087481840791385601390041 196565611380593539201042531)
          ·
            refine ⟨294848417070890308801563797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196565611380593539201042531 294848417070890308801563797)
            ·
              refine ⟨13821019550197983225073303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 294848417070890308801563797 13821019550197983225073303)
              ·
                refine ⟨20731529325296974837609955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13821019550197983225073303 20731529325296974837609955)
                ·
                  refine ⟨31097293987945462256414933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20731529325296974837609955 31097293987945462256414933)
                  ·
                    refine ⟨728842827842471771634725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31097293987945462256414933 728842827842471771634725)
                    ·
                      rfl

theorem cell23_4258249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_4258249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258249 prefixEnd_4258249 := by exact prefixLift 4258249
  have htrace : WordTrace (prefixWord ++ tailWord_4258249) baseStart_4258249 baseEnd_4258249 := by
    simpa [prefixWord, tailWord_4258249, baseEnd_4258249] using wordTrace_append hprefix tailTrace_4258249
  have hstable : (prefixWord ++ tailWord_4258249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258249).length < 2 ^ (prefixWord ++ tailWord_4258249).sum := by decide
  have hdescent : baseEnd_4258249 < baseStart_4258249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258266 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_4258266 : Nat := 118140960795 + 4258266 * 2 ^ 59
def prefixEnd_4258266 : Nat := 4983230072969 + 3 ^ 40 * 4258266 * 2
def baseEnd_4258266 : Nat := 728845737566180582797199

theorem tailTrace_4258266 : CollatzResearch.WordTrace tailWord_4258266 prefixEnd_4258266 728845737566180582797199 := by
  unfold tailWord_4258266
  simp only [CollatzResearch.WordTrace]
  refine ⟨38827930097759252694566663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103541146927358007185511101 38827930097759252694566663)
  ·
    refine ⟨58241895146638879041849995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38827930097759252694566663 58241895146638879041849995)
    ·
      refine ⟨87362842719958318562774993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58241895146638879041849995 87362842719958318562774993)
      ·
        refine ⟨65522132039968738922081245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87362842719958318562774993 65522132039968738922081245)
        ·
          refine ⟨24570799514988277095780467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65522132039968738922081245 24570799514988277095780467)
          ·
            refine ⟨36856199272482415643670701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24570799514988277095780467 36856199272482415643670701)
            ·
              refine ⟨13821074727180905866376513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36856199272482415643670701 13821074727180905866376513)
              ·
                refine ⟨10365806045385679399782385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13821074727180905866376513 10365806045385679399782385)
                ·
                  refine ⟨7774354534039259549836789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10365806045385679399782385 7774354534039259549836789)
                  ·
                    refine ⟨728845737566180582797199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7774354534039259549836789 728845737566180582797199)
                    ·
                      rfl

theorem cell23_4258266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_4258266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258266 prefixEnd_4258266 := by exact prefixLift 4258266
  have htrace : WordTrace (prefixWord ++ tailWord_4258266) baseStart_4258266 baseEnd_4258266 := by
    simpa [prefixWord, tailWord_4258266, baseEnd_4258266] using wordTrace_append hprefix tailTrace_4258266
  have hstable : (prefixWord ++ tailWord_4258266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258266).length < 2 ^ (prefixWord ++ tailWord_4258266).sum := by decide
  have hdescent : baseEnd_4258266 < baseStart_4258266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258296 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_4258296 : Nat := 118140960795 + 4258296 * 2 ^ 59
def prefixEnd_4258296 : Nat := 4983230072969 + 3 ^ 40 * 4258296 * 2
def baseEnd_4258296 : Nat := 728850872372725543672153

theorem tailTrace_4258296 : CollatzResearch.WordTrace tailWord_4258296 prefixEnd_4258296 728850872372725543672153 := by
  unfold tailWord_4258296
  simp only [CollatzResearch.WordTrace]
  refine ⟨77656407290464162950929371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103541876387285550601239161 77656407290464162950929371)
  ·
    refine ⟨116484610935696244426394057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77656407290464162950929371 116484610935696244426394057)
    ·
      refine ⟨87363458201772183319795543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116484610935696244426394057 87363458201772183319795543)
      ·
        refine ⟨131045187302658274979693315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87363458201772183319795543 131045187302658274979693315)
        ·
          refine ⟨196567780953987412469539973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131045187302658274979693315 196567780953987412469539973)
          ·
            refine ⟨36856458928872639838038745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196567780953987412469539973 36856458928872639838038745)
            ·
              refine ⟨27642344196654479878529059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36856458928872639838038745 27642344196654479878529059)
              ·
                refine ⟨41463516294981719817793589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27642344196654479878529059 41463516294981719817793589)
                ·
                  refine ⟨3887204652654536232918149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41463516294981719817793589 3887204652654536232918149)
                  ·
                    refine ⟨728850872372725543672153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887204652654536232918149 728850872372725543672153)
                    ·
                      rfl

theorem cell23_4258296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_4258296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258296 prefixEnd_4258296 := by exact prefixLift 4258296
  have htrace : WordTrace (prefixWord ++ tailWord_4258296) baseStart_4258296 baseEnd_4258296 := by
    simpa [prefixWord, tailWord_4258296, baseEnd_4258296] using wordTrace_append hprefix tailTrace_4258296
  have hstable : (prefixWord ++ tailWord_4258296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258296).length < 2 ^ (prefixWord ++ tailWord_4258296).sum := by decide
  have hdescent : baseEnd_4258296 < baseStart_4258296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258309 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 10]
def baseStart_4258309 : Nat := 118140960795 + 4258309 * 2 ^ 59
def prefixEnd_4258309 : Nat := 4983230072969 + 3 ^ 40 * 4258309 * 2
def baseEnd_4258309 : Nat := 242951032485187231128211

theorem tailTrace_4258309 : CollatzResearch.WordTrace tailWord_4258309 prefixEnd_4258309 242951032485187231128211 := by
  unfold tailWord_4258309
  simp only [CollatzResearch.WordTrace]
  refine ⟨155313288729881229122081981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103542192486587486081387987 155313288729881229122081981)
  ·
    refine ⟨58242483273705460920780743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155313288729881229122081981 58242483273705460920780743)
    ·
      refine ⟨87363724910558191381171115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58242483273705460920780743 87363724910558191381171115)
      ·
        refine ⟨131045587365837287071756673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87363724910558191381171115 131045587365837287071756673)
        ·
          refine ⟨98284190524377965303817505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131045587365837287071756673 98284190524377965303817505)
          ·
            refine ⟨73713142893283473977863129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98284190524377965303817505 73713142893283473977863129)
            ·
              refine ⟨55284857169962605483397347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73713142893283473977863129 55284857169962605483397347)
              ·
                refine ⟨82927285754943908225096021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55284857169962605483397347 82927285754943908225096021)
                ·
                  refine ⟨242951032485187231128211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82927285754943908225096021 242951032485187231128211)
                  ·
                    rfl

theorem cell23_4258309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_4258309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258309 prefixEnd_4258309 := by exact prefixLift 4258309
  have htrace : WordTrace (prefixWord ++ tailWord_4258309) baseStart_4258309 baseEnd_4258309 := by
    simpa [prefixWord, tailWord_4258309, baseEnd_4258309] using wordTrace_append hprefix tailTrace_4258309
  have hstable : (prefixWord ++ tailWord_4258309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258309).length < 2 ^ (prefixWord ++ tailWord_4258309).sum := by decide
  have hdescent : baseEnd_4258309 < baseStart_4258309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258329 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_4258329 : Nat := 118140960795 + 4258329 * 2 ^ 59
def prefixEnd_4258329 : Nat := 4983230072969 + 3 ^ 40 * 4258329 * 2
def baseEnd_4258329 : Nat := 2186569561979775001903807

theorem tailTrace_4258329 : CollatzResearch.WordTrace tailWord_4258329 prefixEnd_4258329 2186569561979775001903807 := by
  unfold tailWord_4258329
  simp only [CollatzResearch.WordTrace]
  refine ⟨155314018189808772537810041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103542678793205848358540027 155314018189808772537810041)
  ·
    refine ⟨116485513642356579403357531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155314018189808772537810041 116485513642356579403357531)
    ·
      refine ⟨174728270463534869105036297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116485513642356579403357531 174728270463534869105036297)
      ·
        refine ⟨131046202847651151828777223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174728270463534869105036297 131046202847651151828777223)
        ·
          refine ⟨196569304271476727743165835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131046202847651151828777223 196569304271476727743165835)
          ·
            refine ⟨294853956407215091614748753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196569304271476727743165835 294853956407215091614748753)
            ·
              refine ⟨221140467305411318711061565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294853956407215091614748753 221140467305411318711061565)
              ·
                refine ⟨82927675239529244516648087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221140467305411318711061565 82927675239529244516648087)
                ·
                  refine ⟨124391512859293866774972131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82927675239529244516648087 124391512859293866774972131)
                  ·
                    refine ⟨186587269288940800162458197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124391512859293866774972131 186587269288940800162458197)
                    ·
                      refine ⟨2186569561979775001903807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 186587269288940800162458197 2186569561979775001903807)
                      ·
                        rfl

theorem cell23_4258329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_4258329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258329 prefixEnd_4258329 := by exact prefixLift 4258329
  have htrace : WordTrace (prefixWord ++ tailWord_4258329) baseStart_4258329 baseEnd_4258329 := by
    simpa [prefixWord, tailWord_4258329, baseEnd_4258329] using wordTrace_append hprefix tailTrace_4258329
  have hstable : (prefixWord ++ tailWord_4258329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258329).length < 2 ^ (prefixWord ++ tailWord_4258329).sum := by decide
  have hdescent : baseEnd_4258329 < baseStart_4258329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258353 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_4258353 : Nat := 118140960795 + 4258353 * 2 ^ 59
def prefixEnd_4258353 : Nat := 4983230072969 + 3 ^ 40 * 4258353 * 2
def baseEnd_4258353 : Nat := 2186581885515482908003697

theorem tailTrace_4258353 : CollatzResearch.WordTrace tailWord_4258353 prefixEnd_4258353 2186581885515482908003697 := by
  unfold tailWord_4258353
  simp only [CollatzResearch.WordTrace]
  refine ⟨155314893541721824636683713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103543262361147883091122475 155314893541721824636683713)
  ·
    refine ⟨116486170156291368477512785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155314893541721824636683713 116486170156291368477512785)
    ·
      refine ⟨87364627617218526358134589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116486170156291368477512785 87364627617218526358134589)
      ·
        refine ⟨32761735356456947384300471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87364627617218526358134589 32761735356456947384300471)
        ·
          refine ⟨49142603034685421076450707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32761735356456947384300471 49142603034685421076450707)
          ·
            refine ⟨73713904552028131614676061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49142603034685421076450707 73713904552028131614676061)
            ·
              refine ⟨27642714207010549355503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73713904552028131614676061 27642714207010549355503523)
              ·
                refine ⟨41464071310515824033255285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27642714207010549355503523 41464071310515824033255285)
                ·
                  refine ⟨3887256685360858503117683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41464071310515824033255285 3887256685360858503117683)
                  ·
                    refine ⟨5830885028041287754676525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887256685360858503117683 5830885028041287754676525)
                    ·
                      refine ⟨2186581885515482908003697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830885028041287754676525 2186581885515482908003697)
                      ·
                        rfl

theorem cell23_4258353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_4258353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258353 prefixEnd_4258353 := by exact prefixLift 4258353
  have htrace : WordTrace (prefixWord ++ tailWord_4258353) baseStart_4258353 baseEnd_4258353 := by
    simpa [prefixWord, tailWord_4258353, baseEnd_4258353] using wordTrace_append hprefix tailTrace_4258353
  have hstable : (prefixWord ++ tailWord_4258353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258353).length < 2 ^ (prefixWord ++ tailWord_4258353).sum := by decide
  have hdescent : baseEnd_4258353 < baseStart_4258353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258373 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_4258373 : Nat := 118140960795 + 4258373 * 2 ^ 59
def prefixEnd_4258373 : Nat := 4983230072969 + 3 ^ 40 * 4258373 * 2
def baseEnd_4258373 : Nat := 728864051709524276584535

theorem tailTrace_4258373 : CollatzResearch.WordTrace tailWord_4258373 prefixEnd_4258373 728864051709524276584535 := by
  unfold tailWord_4258373
  simp only [CollatzResearch.WordTrace]
  refine ⟨155315623001649368052411773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103543748667766245368274515 155315623001649368052411773)
  ·
    refine ⟨58243358625618513019654415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155315623001649368052411773 58243358625618513019654415)
    ·
      refine ⟨87365037938427769529481623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58243358625618513019654415 87365037938427769529481623)
      ·
        refine ⟨131047556907641654294222435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87365037938427769529481623 131047556907641654294222435)
        ·
          refine ⟨196571335361462481441333653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131047556907641654294222435 196571335361462481441333653)
          ·
            refine ⟨9214281345068553817562515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196571335361462481441333653 9214281345068553817562515)
            ·
              refine ⟨13821422017602830726343773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9214281345068553817562515 13821422017602830726343773)
              ·
                refine ⟨5183033256601061522378915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13821422017602830726343773 5183033256601061522378915)
                ·
                  refine ⟨7774549884901592283568373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5183033256601061522378915 7774549884901592283568373)
                  ·
                    refine ⟨728864051709524276584535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7774549884901592283568373 728864051709524276584535)
                    ·
                      rfl

theorem cell23_4258373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_4258373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258373 prefixEnd_4258373 := by exact prefixLift 4258373
  have htrace : WordTrace (prefixWord ++ tailWord_4258373) baseStart_4258373 baseEnd_4258373 := by
    simpa [prefixWord, tailWord_4258373, baseEnd_4258373] using wordTrace_append hprefix tailTrace_4258373
  have hstable : (prefixWord ++ tailWord_4258373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258373).length < 2 ^ (prefixWord ++ tailWord_4258373).sum := by decide
  have hdescent : baseEnd_4258373 < baseStart_4258373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258410 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4258410 : Nat := 118140960795 + 4258410 * 2 ^ 59
def prefixEnd_4258410 : Nat := 4983230072969 + 3 ^ 40 * 4258410 * 2
def baseEnd_4258410 : Nat := 2186611153912789184990935

theorem tailTrace_4258410 : CollatzResearch.WordTrace tailWord_4258410 prefixEnd_4258410 2186611153912789184990935 := by
  unfold tailWord_4258410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38829243125628830842877171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103544648335010215581005789 38829243125628830842877171)
  ·
    refine ⟨58243864688443246264315757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38829243125628830842877171 58243864688443246264315757)
    ·
      refine ⟨21841449258166217349118409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58243864688443246264315757 21841449258166217349118409)
      ·
        refine ⟨16381086943624663011838807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21841449258166217349118409 16381086943624663011838807)
        ·
          refine ⟨24571630415436994517758211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16381086943624663011838807 24571630415436994517758211)
          ·
            refine ⟨36857445623155491776637317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24571630415436994517758211 36857445623155491776637317)
            ·
              refine ⟨6910771054341654708119497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36857445623155491776637317 6910771054341654708119497)
              ·
                refine ⟨5183078290756241031089623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6910771054341654708119497 5183078290756241031089623)
                ·
                  refine ⟨7774617436134361546634435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5183078290756241031089623 7774617436134361546634435)
                  ·
                    refine ⟨11661926154201542319951653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7774617436134361546634435 11661926154201542319951653)
                    ·
                      refine ⟨2186611153912789184990935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11661926154201542319951653 2186611153912789184990935)
                      ·
                        rfl

theorem cell23_4258410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4258410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258410 prefixEnd_4258410 := by exact prefixLift 4258410
  have htrace : WordTrace (prefixWord ++ tailWord_4258410) baseStart_4258410 baseEnd_4258410 := by
    simpa [prefixWord, tailWord_4258410, baseEnd_4258410] using wordTrace_append hprefix tailTrace_4258410
  have hstable : (prefixWord ++ tailWord_4258410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258410).length < 2 ^ (prefixWord ++ tailWord_4258410).sum := by decide
  have hdescent : baseEnd_4258410 < baseStart_4258410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258421 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4258421 : Nat := 118140960795 + 4258421 * 2 ^ 59
def prefixEnd_4258421 : Nat := 4983230072969 + 3 ^ 40 * 4258421 * 2
def baseEnd_4258421 : Nat := 2186616802199988641953385

theorem tailTrace_4258421 : CollatzResearch.WordTrace tailWord_4258421 prefixEnd_4258421 2186616802199988641953385 := by
  unfold tailWord_4258421
  simp only [CollatzResearch.WordTrace]
  refine ⟨155317373705475472250159117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103544915803650314833439411 155317373705475472250159117)
  ·
    refine ⟨58244015139553302093809669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155317373705475472250159117 58244015139553302093809669)
    ·
      refine ⟨10920752838666244142589313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58244015139553302093809669 10920752838666244142589313)
      ·
        refine ⟨8190564628999683106941985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10920752838666244142589313 8190564628999683106941985)
        ·
          refine ⟨6142923471749762330206489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8190564628999683106941985 6142923471749762330206489)
          ·
            refine ⟨4607192603812321747654867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6142923471749762330206489 4607192603812321747654867)
            ·
              refine ⟨6910788905718482621482301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607192603812321747654867 6910788905718482621482301)
              ·
                refine ⟨2591545839644430983055863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6910788905718482621482301 2591545839644430983055863)
                ·
                  refine ⟨3887318759466646474583795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591545839644430983055863 3887318759466646474583795)
                  ·
                    refine ⟨5830978139199969711875693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887318759466646474583795 5830978139199969711875693)
                    ·
                      refine ⟨2186616802199988641953385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5830978139199969711875693 2186616802199988641953385)
                      ·
                        rfl

theorem cell23_4258421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4258421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258421 prefixEnd_4258421 := by exact prefixLift 4258421
  have htrace : WordTrace (prefixWord ++ tailWord_4258421) baseStart_4258421 baseEnd_4258421 := by
    simpa [prefixWord, tailWord_4258421, baseEnd_4258421] using wordTrace_append hprefix tailTrace_4258421
  have hstable : (prefixWord ++ tailWord_4258421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258421).length < 2 ^ (prefixWord ++ tailWord_4258421).sum := by decide
  have hdescent : baseEnd_4258421 < baseStart_4258421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258427 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 1, 2, 2]
def baseStart_4258427 : Nat := 118140960795 + 4258427 * 2 ^ 59
def prefixEnd_4258427 : Nat := 4983230072969 + 3 ^ 40 * 4258427 * 2
def baseEnd_4258427 : Nat := 2186619883083915618478357

theorem tailTrace_4258427 : CollatzResearch.WordTrace tailWord_4258427 prefixEnd_4258427 2186619883083915618478357 := by
  unfold tailWord_4258427
  simp only [CollatzResearch.WordTrace]
  refine ⟨155317592543453735274877535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103545061695635823516585023 155317592543453735274877535)
  ·
    refine ⟨232976388815180602912316303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155317592543453735274877535 232976388815180602912316303)
    ·
      refine ⟨349464583222770904368474455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232976388815180602912316303 349464583222770904368474455)
      ·
        refine ⟨524196874834156356552711683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349464583222770904368474455 524196874834156356552711683)
        ·
          refine ⟨786295312251234534829067525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524196874834156356552711683 786295312251234534829067525)
          ·
            refine ⟨147430371047106475280450161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 786295312251234534829067525 147430371047106475280450161)
            ·
              refine ⟨110572778285329856460337621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147430371047106475280450161 110572778285329856460337621)
              ·
                refine ⟨2591549491062418510789163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110572778285329856460337621 2591549491062418510789163)
                ·
                  refine ⟨3887324236593627766183745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591549491062418510789163 3887324236593627766183745)
                  ·
                    refine ⟨2915493177445220824637809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887324236593627766183745 2915493177445220824637809)
                    ·
                      refine ⟨2186619883083915618478357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915493177445220824637809 2186619883083915618478357)
                      ·
                        rfl

theorem cell23_4258427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 2, 2].length) (baseStart_4258427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258427 prefixEnd_4258427 := by exact prefixLift 4258427
  have htrace : WordTrace (prefixWord ++ tailWord_4258427) baseStart_4258427 baseEnd_4258427 := by
    simpa [prefixWord, tailWord_4258427, baseEnd_4258427] using wordTrace_append hprefix tailTrace_4258427
  have hstable : (prefixWord ++ tailWord_4258427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258427).length < 2 ^ (prefixWord ++ tailWord_4258427).sum := by decide
  have hdescent : baseEnd_4258427 < baseStart_4258427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258453 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_4258453 : Nat := 118140960795 + 4258453 * 2 ^ 59
def prefixEnd_4258453 : Nat := 4983230072969 + 3 ^ 40 * 4258453 * 2
def baseEnd_4258453 : Nat := 2186633233580932516753237

theorem tailTrace_4258453 : CollatzResearch.WordTrace tailWord_4258453 prefixEnd_4258453 2186633233580932516753237 := by
  unfold tailWord_4258453
  simp only [CollatzResearch.WordTrace]
  refine ⟨155318540841359541715324013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103545693894239694476882675 155318540841359541715324013)
  ·
    refine ⟨58244452815509828143246505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155318540841359541715324013 58244452815509828143246505)
    ·
      refine ⟨43683339611632371107434879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58244452815509828143246505 43683339611632371107434879)
      ·
        refine ⟨65525009417448556661152319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43683339611632371107434879 65525009417448556661152319)
        ·
          refine ⟨98287514126172834991728479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65525009417448556661152319 98287514126172834991728479)
          ·
            refine ⟨147431271189259252487592719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98287514126172834991728479 147431271189259252487592719)
            ·
              refine ⟨221146906783888878731389079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147431271189259252487592719 221146906783888878731389079)
              ·
                refine ⟨331720360175833318097083619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221146906783888878731389079 331720360175833318097083619)
                ·
                  refine ⟨497580540263749977145625429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331720360175833318097083619 497580540263749977145625429)
                  ·
                    refine ⟨2915510978107910022337649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 497580540263749977145625429 2915510978107910022337649)
                    ·
                      refine ⟨2186633233580932516753237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915510978107910022337649 2186633233580932516753237)
                      ·
                        rfl

theorem cell23_4258453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_4258453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258453 prefixEnd_4258453 := by exact prefixLift 4258453
  have htrace : WordTrace (prefixWord ++ tailWord_4258453) baseStart_4258453 baseEnd_4258453 := by
    simpa [prefixWord, tailWord_4258453, baseEnd_4258453] using wordTrace_append hprefix tailTrace_4258453
  have hstable : (prefixWord ++ tailWord_4258453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258453).length < 2 ^ (prefixWord ++ tailWord_4258453).sum := by decide
  have hdescent : baseEnd_4258453 < baseStart_4258453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258464 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3]
def baseStart_4258464 : Nat := 118140960795 + 4258464 * 2 ^ 59
def prefixEnd_4258464 : Nat := 4983230072969 + 3 ^ 40 * 4258464 * 2
def baseEnd_4258464 : Nat := 2186638881868131973715687

theorem tailTrace_4258464 : CollatzResearch.WordTrace tailWord_4258464 prefixEnd_4258464 2186638881868131973715687 := by
  unfold tailWord_4258464
  simp only [CollatzResearch.WordTrace]
  refine ⟨77659471022159845296987223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103545961362879793729316297 77659471022159845296987223)
  ·
    refine ⟨116489206533239767945480835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77659471022159845296987223 116489206533239767945480835)
    ·
      refine ⟨174733809799859651918221253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116489206533239767945480835 174733809799859651918221253)
      ·
        refine ⟨32762589337473684734666485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174733809799859651918221253 32762589337473684734666485)
        ·
          refine ⟨3071492750388157943874983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32762589337473684734666485 3071492750388157943874983)
          ·
            refine ⟨4607239125582236915812475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071492750388157943874983 4607239125582236915812475)
            ·
              refine ⟨6910858688373355373718713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607239125582236915812475 6910858688373355373718713)
              ·
                refine ⟨5183144016280016530289035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6910858688373355373718713 5183144016280016530289035)
                ·
                  refine ⟨7774716024420024795433553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5183144016280016530289035 7774716024420024795433553)
                  ·
                    refine ⟨5831037018315018596575165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7774716024420024795433553 5831037018315018596575165)
                    ·
                      refine ⟨2186638881868131973715687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831037018315018596575165 2186638881868131973715687)
                      ·
                        rfl

theorem cell23_4258464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_4258464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258464 prefixEnd_4258464 := by exact prefixLift 4258464
  have htrace : WordTrace (prefixWord ++ tailWord_4258464) baseStart_4258464 baseEnd_4258464 := by
    simpa [prefixWord, tailWord_4258464, baseEnd_4258464] using wordTrace_append hprefix tailTrace_4258464
  have hstable : (prefixWord ++ tailWord_4258464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258464).length < 2 ^ (prefixWord ++ tailWord_4258464).sum := by decide
  have hdescent : baseEnd_4258464 < baseStart_4258464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258513 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_4258513 : Nat := 118140960795 + 4258513 * 2 ^ 59
def prefixEnd_4258513 : Nat := 4983230072969 + 3 ^ 40 * 4258513 * 2
def baseEnd_4258513 : Nat := 2186664042420202282002961

theorem tailTrace_4258513 : CollatzResearch.WordTrace tailWord_4258513 prefixEnd_4258513 2186664042420202282002961 := by
  unfold tailWord_4258513
  simp only [CollatzResearch.WordTrace]
  refine ⟨155320729221142171962508193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103547152814094781308338795 155320729221142171962508193)
  ·
    refine ⟨116490546915856628971881145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155320729221142171962508193 116490546915856628971881145)
    ·
      refine ⟨87367910186892471728910859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116490546915856628971881145 87367910186892471728910859)
      ·
        refine ⟨131051865280338707593366289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87367910186892471728910859 131051865280338707593366289)
        ·
          refine ⟨98288898960254030695024717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131051865280338707593366289 98288898960254030695024717)
          ·
            refine ⟨36858337110095261510634269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98288898960254030695024717 36858337110095261510634269)
            ·
              refine ⟨13821876416285723066487851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36858337110095261510634269 13821876416285723066487851)
              ·
                refine ⟨20732814624428584599731777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13821876416285723066487851 20732814624428584599731777)
                ·
                  refine ⟨15549610968321438449798833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20732814624428584599731777 15549610968321438449798833)
                  ·
                    refine ⟨11662208226241078837349125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15549610968321438449798833 11662208226241078837349125)
                    ·
                      refine ⟨2186664042420202282002961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11662208226241078837349125 2186664042420202282002961)
                      ·
                        rfl

theorem cell23_4258513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_4258513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258513 prefixEnd_4258513 := by exact prefixLift 4258513
  have htrace : WordTrace (prefixWord ++ tailWord_4258513) baseStart_4258513 baseEnd_4258513 := by
    simpa [prefixWord, tailWord_4258513, baseEnd_4258513] using wordTrace_append hprefix tailTrace_4258513
  have hstable : (prefixWord ++ tailWord_4258513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258513).length < 2 ^ (prefixWord ++ tailWord_4258513).sum := by decide
  have hdescent : baseEnd_4258513 < baseStart_4258513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258550 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4258550 : Nat := 118140960795 + 4258550 * 2 ^ 59
def prefixEnd_4258550 : Nat := 4983230072969 + 3 ^ 40 * 4258550 * 2
def baseEnd_4258550 : Nat := 2186683041204418637240291

theorem tailTrace_4258550 : CollatzResearch.WordTrace tailWord_4258550 prefixEnd_4258550 2186683041204418637240291 := by
  unfold tailWord_4258550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9707629920125507955100319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103548052481338751521070069 9707629920125507955100319)
  ·
    refine ⟨14561444880188261932650479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9707629920125507955100319 14561444880188261932650479)
    ·
      refine ⟨21842167320282392898975719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14561444880188261932650479 21842167320282392898975719)
      ·
        refine ⟨32763250980423589348463579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21842167320282392898975719 32763250980423589348463579)
        ·
          refine ⟨49144876470635384022695369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32763250980423589348463579 49144876470635384022695369)
          ·
            refine ⟨36858657352976538017021527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49144876470635384022695369 36858657352976538017021527)
            ·
              refine ⟨55287986029464807025532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36858657352976538017021527 55287986029464807025532291)
              ·
                refine ⟨82931979044197210538298437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55287986029464807025532291 82931979044197210538298437)
                ·
                  refine ⟨15549746070786976975930957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82931979044197210538298437 15549746070786976975930957)
                  ·
                    refine ⟨5831154776545116365974109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15549746070786976975930957 5831154776545116365974109)
                    ·
                      refine ⟨2186683041204418637240291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831154776545116365974109 2186683041204418637240291)
                      ·
                        rfl

theorem cell23_4258550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4258550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258550 prefixEnd_4258550 := by exact prefixLift 4258550
  have htrace : WordTrace (prefixWord ++ tailWord_4258550) baseStart_4258550 baseEnd_4258550 := by
    simpa [prefixWord, tailWord_4258550, baseEnd_4258550] using wordTrace_append hprefix tailTrace_4258550
  have hstable : (prefixWord ++ tailWord_4258550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258550).length < 2 ^ (prefixWord ++ tailWord_4258550).sum := by decide
  have hdescent : baseEnd_4258550 < baseStart_4258550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258553 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_4258553 : Nat := 118140960795 + 4258553 * 2 ^ 59
def prefixEnd_4258553 : Nat := 4983230072969 + 3 ^ 40 * 4258553 * 2
def baseEnd_4258553 : Nat := 728894860548794041834259

theorem tailTrace_4258553 : CollatzResearch.WordTrace tailWord_4258553 prefixEnd_4258553 728894860548794041834259 := by
  unfold tailWord_4258553
  simp only [CollatzResearch.WordTrace]
  refine ⟨155322188140997258793964313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103548125427331505862642875 155322188140997258793964313)
  ·
    refine ⟨116491641105747944095473235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155322188140997258793964313 116491641105747944095473235)
    ·
      refine ⟨174737461658621916143209853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116491641105747944095473235 174737461658621916143209853)
      ·
        refine ⟨65526548121983218553703695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174737461658621916143209853 65526548121983218553703695)
        ·
          refine ⟨98289822182974827830555543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65526548121983218553703695 98289822182974827830555543)
          ·
            refine ⟨147434733274462241745833315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98289822182974827830555543 147434733274462241745833315)
            ·
              refine ⟨221152099911693362618749973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147434733274462241745833315 221152099911693362618749973)
              ·
                refine ⟨10366504683360626372753905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221152099911693362618749973 10366504683360626372753905)
                ·
                  refine ⟨7774878512520469779565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10366504683360626372753905 7774878512520469779565429)
                  ·
                    refine ⟨728894860548794041834259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7774878512520469779565429 728894860548794041834259)
                    ·
                      rfl

theorem cell23_4258553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_4258553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258553 prefixEnd_4258553 := by exact prefixLift 4258553
  have htrace : WordTrace (prefixWord ++ tailWord_4258553) baseStart_4258553 baseEnd_4258553 := by
    simpa [prefixWord, tailWord_4258553, baseEnd_4258553] using wordTrace_append hprefix tailTrace_4258553
  have hstable : (prefixWord ++ tailWord_4258553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258553).length < 2 ^ (prefixWord ++ tailWord_4258553).sum := by decide
  have hdescent : baseEnd_4258553 < baseStart_4258553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258644 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_4258644 : Nat := 118140960795 + 4258644 * 2 ^ 59
def prefixEnd_4258644 : Nat := 4983230072969 + 3 ^ 40 * 4258644 * 2
def baseEnd_4258644 : Nat := 2186731308385941269464859

theorem tailTrace_4258644 : CollatzResearch.WordTrace tailWord_4258644 prefixEnd_4258644 2186731308385941269464859 := by
  unfold tailWord_4258644
  simp only [CollatzResearch.WordTrace]
  refine ⟨77662753591833790667763493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103550338122445054223684657 77662753591833790667763493)
  ·
    refine ⟨14561766298468835750205655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77662753591833790667763493 14561766298468835750205655)
    ·
      refine ⟨21842649447703253625308483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14561766298468835750205655 21842649447703253625308483)
      ·
        refine ⟨32763974171554880437962725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21842649447703253625308483 32763974171554880437962725)
        ·
          refine ⟨6143245157166540082118011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32763974171554880437962725 6143245157166540082118011)
          ·
            refine ⟨9214867735749810123177017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143245157166540082118011 9214867735749810123177017)
            ·
              refine ⟨6911150801812357592382763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9214867735749810123177017 6911150801812357592382763)
              ·
                refine ⟨10366726202718536388574145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6911150801812357592382763 10366726202718536388574145)
                ·
                  refine ⟨7775044652038902291430609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10366726202718536388574145 7775044652038902291430609)
                  ·
                    refine ⟨5831283489029176718572957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7775044652038902291430609 5831283489029176718572957)
                    ·
                      refine ⟨2186731308385941269464859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831283489029176718572957 2186731308385941269464859)
                      ·
                        rfl

theorem cell23_4258644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_4258644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258644 prefixEnd_4258644 := by exact prefixLift 4258644
  have htrace : WordTrace (prefixWord ++ tailWord_4258644) baseStart_4258644 baseEnd_4258644 := by
    simpa [prefixWord, tailWord_4258644, baseEnd_4258644] using wordTrace_append hprefix tailTrace_4258644
  have hstable : (prefixWord ++ tailWord_4258644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258644).length < 2 ^ (prefixWord ++ tailWord_4258644).sum := by decide
  have hdescent : baseEnd_4258644 < baseStart_4258644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258667 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 2, 3, 2]
def baseStart_4258667 : Nat := 118140960795 + 4258667 * 2 ^ 59
def prefixEnd_4258667 : Nat := 4983230072969 + 3 ^ 40 * 4258667 * 2
def baseEnd_4258667 : Nat := 2186743118440994679477253

theorem tailTrace_4258667 : CollatzResearch.WordTrace tailWord_4258667 prefixEnd_4258667 2186743118440994679477253 := by
  unfold tailWord_4258667
  simp only [CollatzResearch.WordTrace]
  refine ⟨155326346062584256263614255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103550897375056170842409503 155326346062584256263614255)
  ·
    refine ⟨232989519093876384395421383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155326346062584256263614255 232989519093876384395421383)
    ·
      refine ⟨349484278640814576593132075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232989519093876384395421383 349484278640814576593132075)
      ·
        refine ⟨524226417961221864889698113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349484278640814576593132075 524226417961221864889698113)
        ·
          refine ⟨393169813470916398667273585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524226417961221864889698113 393169813470916398667273585)
          ·
            refine ⟨294877360103187299000455189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393169813470916398667273585 294877360103187299000455189)
            ·
              refine ⟨13822376254836904640646337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 294877360103187299000455189 13822376254836904640646337)
              ·
                refine ⟨10366782191127678480484753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13822376254836904640646337 10366782191127678480484753)
                ·
                  refine ⟨7775086643345758860363565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10366782191127678480484753 7775086643345758860363565)
                  ·
                    refine ⟨2915657491254659572636337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7775086643345758860363565 2915657491254659572636337)
                    ·
                      refine ⟨2186743118440994679477253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915657491254659572636337 2186743118440994679477253)
                      ·
                        rfl

theorem cell23_4258667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 3, 2].length) (baseStart_4258667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258667 prefixEnd_4258667 := by exact prefixLift 4258667
  have htrace : WordTrace (prefixWord ++ tailWord_4258667) baseStart_4258667 baseEnd_4258667 := by
    simpa [prefixWord, tailWord_4258667, baseEnd_4258667] using wordTrace_append hprefix tailTrace_4258667
  have hstable : (prefixWord ++ tailWord_4258667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258667).length < 2 ^ (prefixWord ++ tailWord_4258667).sum := by decide
  have hdescent : baseEnd_4258667 < baseStart_4258667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258714 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4258714 : Nat := 118140960795 + 4258714 * 2 ^ 59
def prefixEnd_4258714 : Nat := 4983230072969 + 3 ^ 40 * 4258714 * 2
def baseEnd_4258714 : Nat := 2186767252031755995589537

theorem tailTrace_4258714 : CollatzResearch.WordTrace tailWord_4258714 prefixEnd_4258714 2186767252031755995589537 := by
  unfold tailWord_4258714
  simp only [CollatzResearch.WordTrace]
  refine ⟨38832015073353495822643799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103552040195609322193716797 38832015073353495822643799)
  ·
    refine ⟨58248022610030243733965699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38832015073353495822643799 58248022610030243733965699)
    ·
      refine ⟨87372033915045365600948549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58248022610030243733965699 87372033915045365600948549)
      ·
        refine ⟨16382256359071006050177853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87372033915045365600948549 16382256359071006050177853)
        ·
          refine ⟨6143346134651627268816695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16382256359071006050177853 6143346134651627268816695)
          ·
            refine ⟨9215019201977440903225043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143346134651627268816695 9215019201977440903225043)
            ·
              refine ⟨13822528802966161354837565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215019201977440903225043 13822528802966161354837565)
              ·
                refine ⟨5183448301112310508064087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13822528802966161354837565 5183448301112310508064087)
                ·
                  refine ⟨7775172451668465762096131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5183448301112310508064087 7775172451668465762096131)
                  ·
                    refine ⟨11662758677502698643144197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7775172451668465762096131 11662758677502698643144197)
                    ·
                      refine ⟨2186767252031755995589537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11662758677502698643144197 2186767252031755995589537)
                      ·
                        rfl

theorem cell23_4258714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4258714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258714 prefixEnd_4258714 := by exact prefixLift 4258714
  have htrace : WordTrace (prefixWord ++ tailWord_4258714) baseStart_4258714 baseEnd_4258714 := by
    simpa [prefixWord, tailWord_4258714, baseEnd_4258714] using wordTrace_append hprefix tailTrace_4258714
  have hstable : (prefixWord ++ tailWord_4258714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258714).length < 2 ^ (prefixWord ++ tailWord_4258714).sum := by decide
  have hdescent : baseEnd_4258714 < baseStart_4258714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258757 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_4258757 : Nat := 118140960795 + 4258757 * 2 ^ 59
def prefixEnd_4258757 : Nat := 4983230072969 + 3 ^ 40 * 4258757 * 2
def baseEnd_4258757 : Nat := 2186789331699899327351839

theorem tailTrace_4258757 : CollatzResearch.WordTrace tailWord_4258757 prefixEnd_4258757 2186789331699899327351839 := by
  unfold tailWord_4258757
  simp only [CollatzResearch.WordTrace]
  refine ⟨155329628632258201634390525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103553085754838801089593683 155329628632258201634390525)
  ·
    refine ⟨58248610737096825612896447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155329628632258201634390525 58248610737096825612896447)
    ·
      refine ⟨87372916105645238419344671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58248610737096825612896447 87372916105645238419344671)
      ·
        refine ⟨131059374158467857629017007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87372916105645238419344671 131059374158467857629017007)
        ·
          refine ⟨196589061237701786443525511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131059374158467857629017007 196589061237701786443525511)
          ·
            refine ⟨294883591856552679665288267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196589061237701786443525511 294883591856552679665288267)
            ·
              refine ⟨442325387784829019497932401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294883591856552679665288267 442325387784829019497932401)
              ·
                refine ⟨331744040838621764623449301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442325387784829019497932401 331744040838621764623449301)
                ·
                  refine ⟨7775250957155197608362093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 331744040838621764623449301 7775250957155197608362093)
                  ·
                    refine ⟨2915719108933199103135785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7775250957155197608362093 2915719108933199103135785)
                    ·
                      refine ⟨2186789331699899327351839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915719108933199103135785 2186789331699899327351839)
                      ·
                        rfl

theorem cell23_4258757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_4258757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258757 prefixEnd_4258757 := by exact prefixLift 4258757
  have htrace : WordTrace (prefixWord ++ tailWord_4258757) baseStart_4258757 baseEnd_4258757 := by
    simpa [prefixWord, tailWord_4258757, baseEnd_4258757] using wordTrace_append hprefix tailTrace_4258757
  have hstable : (prefixWord ++ tailWord_4258757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258757).length < 2 ^ (prefixWord ++ tailWord_4258757).sum := by decide
  have hdescent : baseEnd_4258757 < baseStart_4258757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258800 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_4258800 : Nat := 118140960795 + 4258800 * 2 ^ 59
def prefixEnd_4258800 : Nat := 4983230072969 + 3 ^ 40 * 4258800 * 2
def baseEnd_4258800 : Nat := 2186811411368042659114141

theorem tailTrace_4258800 : CollatzResearch.WordTrace tailWord_4258800 prefixEnd_4258800 2186811411368042659114141 := by
  unfold tailWord_4258800
  simp only [CollatzResearch.WordTrace]
  refine ⟨77665598485551209989102927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103554131314068279985470569 77665598485551209989102927)
  ·
    refine ⟨116498397728326814983654391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77665598485551209989102927 116498397728326814983654391)
    ·
      refine ⟨174747596592490222475481587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116498397728326814983654391 174747596592490222475481587)
      ·
        refine ⟨262121394888735333713222381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174747596592490222475481587 262121394888735333713222381)
        ·
          refine ⟨98295523083275750142458393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262121394888735333713222381 98295523083275750142458393)
          ·
            refine ⟨73721642312456812606843795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98295523083275750142458393 73721642312456812606843795)
            ·
              refine ⟨110582463468685218910265693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73721642312456812606843795 110582463468685218910265693)
              ·
                refine ⟨41468423800756957091349635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110582463468685218910265693 41468423800756957091349635)
                ·
                  refine ⟨62202635701135435637024453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41468423800756957091349635 62202635701135435637024453)
                  ·
                    refine ⟨11662994193962894181942085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62202635701135435637024453 11662994193962894181942085)
                    ·
                      refine ⟨2186811411368042659114141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11662994193962894181942085 2186811411368042659114141)
                      ·
                        rfl

theorem cell23_4258800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_4258800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258800 prefixEnd_4258800 := by exact prefixLift 4258800
  have htrace : WordTrace (prefixWord ++ tailWord_4258800) baseStart_4258800 baseEnd_4258800 := by
    simpa [prefixWord, tailWord_4258800, baseEnd_4258800] using wordTrace_append hprefix tailTrace_4258800
  have hstable : (prefixWord ++ tailWord_4258800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258800).length < 2 ^ (prefixWord ++ tailWord_4258800).sum := by decide
  have hdescent : baseEnd_4258800 < baseStart_4258800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258810 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_4258810 : Nat := 118140960795 + 4258810 * 2 ^ 59
def prefixEnd_4258810 : Nat := 4983230072969 + 3 ^ 40 * 4258810 * 2
def baseEnd_4258810 : Nat := 242979616241620846665455

theorem tailTrace_4258810 : CollatzResearch.WordTrace tailWord_4258810 prefixEnd_4258810 242979616241620846665455 := by
  unfold tailWord_4258810
  simp only [CollatzResearch.WordTrace]
  refine ⟨38832890425266547921517471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103554374467377461124046589 38832890425266547921517471)
  ·
    refine ⟨58249335637899821882276207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38832890425266547921517471 58249335637899821882276207)
    ·
      refine ⟨87374003456849732823414311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58249335637899821882276207 87374003456849732823414311)
      ·
        refine ⟨131061005185274599235121467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87374003456849732823414311 131061005185274599235121467)
        ·
          refine ⟨196591507777911898852682201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131061005185274599235121467 196591507777911898852682201)
          ·
            refine ⟨147443630833433924139511651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196591507777911898852682201 147443630833433924139511651)
            ·
              refine ⟨221165446250150886209267477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147443630833433924139511651 221165446250150886209267477)
              ·
                refine ⟨10367130292975822791059413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221165446250150886209267477 10367130292975822791059413)
                ·
                  refine ⟨242979616241620846665455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10367130292975822791059413 242979616241620846665455)
                  ·
                    rfl

theorem cell23_4258810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_4258810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258810 prefixEnd_4258810 := by exact prefixLift 4258810
  have htrace : WordTrace (prefixWord ++ tailWord_4258810) baseStart_4258810 baseEnd_4258810 := by
    simpa [prefixWord, tailWord_4258810, baseEnd_4258810] using wordTrace_append hprefix tailTrace_4258810
  have hstable : (prefixWord ++ tailWord_4258810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258810).length < 2 ^ (prefixWord ++ tailWord_4258810).sum := by decide
  have hdescent : baseEnd_4258810 < baseStart_4258810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258894 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_4258894 : Nat := 118140960795 + 4258894 * 2 ^ 59
def prefixEnd_4258894 : Nat := 4983230072969 + 3 ^ 40 * 4258894 * 2
def baseEnd_4258894 : Nat := 2186859678549565291338709

theorem tailTrace_4258894 : CollatzResearch.WordTrace tailWord_4258894 prefixEnd_4258894 2186859678549565291338709 := by
  unfold tailWord_4258894
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416828179095234254015967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103556416955174582688085157 19416828179095234254015967)
  ·
    refine ⟨29125242268642851381023951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19416828179095234254015967 29125242268642851381023951)
    ·
      refine ⟨43687863402964277071535927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29125242268642851381023951 43687863402964277071535927)
      ·
        refine ⟨65531795104446415607303891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43687863402964277071535927 65531795104446415607303891)
        ·
          refine ⟨98297692656669623410955837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65531795104446415607303891 98297692656669623410955837)
          ·
            refine ⟨36861634746251108779108439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98297692656669623410955837 36861634746251108779108439)
            ·
              refine ⟨55292452119376663168662659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36861634746251108779108439 55292452119376663168662659)
              ·
                refine ⟨82938678179064994752993989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55292452119376663168662659 82938678179064994752993989)
                ·
                  refine ⟨15551002158574686516186373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82938678179064994752993989 15551002158574686516186373)
                  ·
                    refine ⟨2915812904732753721784945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15551002158574686516186373 2915812904732753721784945)
                    ·
                      refine ⟨2186859678549565291338709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915812904732753721784945 2186859678549565291338709)
                      ·
                        rfl

theorem cell23_4258894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_4258894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258894 prefixEnd_4258894 := by exact prefixLift 4258894
  have htrace : WordTrace (prefixWord ++ tailWord_4258894) baseStart_4258894 baseEnd_4258894 := by
    simpa [prefixWord, tailWord_4258894, baseEnd_4258894] using wordTrace_append hprefix tailTrace_4258894
  have hstable : (prefixWord ++ tailWord_4258894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258894).length < 2 ^ (prefixWord ++ tailWord_4258894).sum := by decide
  have hdescent : baseEnd_4258894 < baseStart_4258894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258904 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_4258904 : Nat := 118140960795 + 4258904 * 2 ^ 59
def prefixEnd_4258904 : Nat := 4983230072969 + 3 ^ 40 * 4258904 * 2
def baseEnd_4258904 : Nat := 728954937785370084071221

theorem tailTrace_4258904 : CollatzResearch.WordTrace tailWord_4258904 prefixEnd_4258904 728954937785370084071221 := by
  unfold tailWord_4258904
  simp only [CollatzResearch.WordTrace]
  refine ⟨77667495081362822869995883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103556660108483763826661177 77667495081362822869995883)
  ·
    refine ⟨116501242622044234304993825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77667495081362822869995883 116501242622044234304993825)
    ·
      refine ⟨87375931966533175728745369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116501242622044234304993825 87375931966533175728745369)
      ·
        refine ⟨65531948974899881796559027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87375931966533175728745369 65531948974899881796559027)
        ·
          refine ⟨98297923462349822694838541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65531948974899881796559027 98297923462349822694838541)
          ·
            refine ⟨36861721298381183510564453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98297923462349822694838541 36861721298381183510564453)
            ·
              refine ⟨6911572743446471908230835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36861721298381183510564453 6911572743446471908230835)
              ·
                refine ⟨10367359115169707862346253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6911572743446471908230835 10367359115169707862346253)
                ·
                  refine ⟨3887759668188640448379845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10367359115169707862346253 3887759668188640448379845)
                  ·
                    refine ⟨728954937785370084071221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887759668188640448379845 728954937785370084071221)
                    ·
                      rfl

theorem cell23_4258904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_4258904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258904 prefixEnd_4258904 := by exact prefixLift 4258904
  have htrace : WordTrace (prefixWord ++ tailWord_4258904) baseStart_4258904 baseEnd_4258904 := by
    simpa [prefixWord, tailWord_4258904, baseEnd_4258904] using wordTrace_append hprefix tailTrace_4258904
  have hstable : (prefixWord ++ tailWord_4258904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258904).length < 2 ^ (prefixWord ++ tailWord_4258904).sum := by decide
  have hdescent : baseEnd_4258904 < baseStart_4258904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258927 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_4258927 : Nat := 118140960795 + 4258927 * 2 ^ 59
def prefixEnd_4258927 : Nat := 4983230072969 + 3 ^ 40 * 4258927 * 2
def baseEnd_4258927 : Nat := 2186876623411163662226057

theorem tailTrace_4258927 : CollatzResearch.WordTrace tailWord_4258927 prefixEnd_4258927 2186876623411163662226057 := by
  unfold tailWord_4258927
  simp only [CollatzResearch.WordTrace]
  refine ⟨155335829041642320668079035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103557219361094880445386023 155335829041642320668079035)
  ·
    refine ⟨233003743562463481002118553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155335829041642320668079035 233003743562463481002118553)
    ·
      refine ⟨174752807671847610751588915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233003743562463481002118553 174752807671847610751588915)
      ·
        refine ⟨262129211507771416127383373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174752807671847610751588915 262129211507771416127383373)
        ·
          refine ⟨98298454315414281047768765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262129211507771416127383373 98298454315414281047768765)
          ·
            refine ⟨36861920368280355392913287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98298454315414281047768765 36861920368280355392913287)
            ·
              refine ⟨55292880552420533089369931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36861920368280355392913287 55292880552420533089369931)
              ·
                refine ⟨82939320828630799634054897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55292880552420533089369931 82939320828630799634054897)
                ·
                  refine ⟨62204490621473099725541173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82939320828630799634054897 62204490621473099725541173)
                  ·
                    refine ⟨5831670995763103099269485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62204490621473099725541173 5831670995763103099269485)
                    ·
                      refine ⟨2186876623411163662226057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831670995763103099269485 2186876623411163662226057)
                      ·
                        rfl

theorem cell23_4258927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_4258927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258927 prefixEnd_4258927 := by exact prefixLift 4258927
  have htrace : WordTrace (prefixWord ++ tailWord_4258927) baseStart_4258927 baseEnd_4258927 := by
    simpa [prefixWord, tailWord_4258927, baseEnd_4258927] using wordTrace_append hprefix tailTrace_4258927
  have hstable : (prefixWord ++ tailWord_4258927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258927).length < 2 ^ (prefixWord ++ tailWord_4258927).sum := by decide
  have hdescent : baseEnd_4258927 < baseStart_4258927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258944 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3]
def baseStart_4258944 : Nat := 118140960795 + 4258944 * 2 ^ 59
def prefixEnd_4258944 : Nat := 4983230072969 + 3 ^ 40 * 4258944 * 2
def baseEnd_4258944 : Nat := 2186885352582290095713479

theorem tailTrace_4258944 : CollatzResearch.WordTrace tailWord_4258944 prefixEnd_4258944 2186885352582290095713479 := by
  unfold tailWord_4258944
  simp only [CollatzResearch.WordTrace]
  refine ⟨77668224541290366285723943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103557632721720488380965257 77668224541290366285723943)
  ·
    refine ⟨116502336811935549428585915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77668224541290366285723943 116502336811935549428585915)
    ·
      refine ⟨174753505217903324142878873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116502336811935549428585915 174753505217903324142878873)
      ·
        refine ⟨131065128913427493107159155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174753505217903324142878873 131065128913427493107159155)
        ·
          refine ⟨196597693370141239660738733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131065128913427493107159155 196597693370141239660738733)
          ·
            refine ⟨73724135013802964872777025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196597693370141239660738733 73724135013802964872777025)
            ·
              refine ⟨55293101260352223654582769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73724135013802964872777025 55293101260352223654582769)
              ·
                refine ⟨41469825945264167740937077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55293101260352223654582769 41469825945264167740937077)
                ·
                  refine ⟨3887796182368515725712851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41469825945264167740937077 3887796182368515725712851)
                  ·
                    refine ⟨5831694273552773588569277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887796182368515725712851 5831694273552773588569277)
                    ·
                      refine ⟨2186885352582290095713479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831694273552773588569277 2186885352582290095713479)
                      ·
                        rfl

theorem cell23_4258944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_4258944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258944 prefixEnd_4258944 := by exact prefixLift 4258944
  have htrace : WordTrace (prefixWord ++ tailWord_4258944) baseStart_4258944 baseEnd_4258944 := by
    simpa [prefixWord, tailWord_4258944, baseEnd_4258944] using wordTrace_append hprefix tailTrace_4258944
  have hstable : (prefixWord ++ tailWord_4258944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258944).length < 2 ^ (prefixWord ++ tailWord_4258944).sum := by decide
  have hdescent : baseEnd_4258944 < baseStart_4258944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258981 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_4258981 : Nat := 118140960795 + 4258981 * 2 ^ 59
def prefixEnd_4258981 : Nat := 4983230072969 + 3 ^ 40 * 4258981 * 2
def baseEnd_4258981 : Nat := 728968117122168816983603

theorem tailTrace_4258981 : CollatzResearch.WordTrace tailWord_4258981 prefixEnd_4258981 728968117122168816983603 := by
  unfold tailWord_4258981
  simp only [CollatzResearch.WordTrace]
  refine ⟨155337798583446687890544797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103558532388964458593696531 155337798583446687890544797)
  ·
    refine ⟨58251674468792507958954299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155337798583446687890544797 58251674468792507958954299)
    ·
      refine ⟨87377511703188761938431449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58251674468792507958954299 87377511703188761938431449)
      ·
        refine ⟨65533133777391571453823587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87377511703188761938431449 65533133777391571453823587)
        ·
          refine ⟨98299700666087357180735381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65533133777391571453823587 98299700666087357180735381)
          ·
            refine ⟨4607798468722844867846971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98299700666087357180735381 4607798468722844867846971)
            ·
              refine ⟨6911697703084267301770457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607798468722844867846971 6911697703084267301770457)
              ·
                refine ⟨5183773277313200476327843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6911697703084267301770457 5183773277313200476327843)
                ·
                  refine ⟨7775659915969800714491765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5183773277313200476327843 7775659915969800714491765)
                  ·
                    refine ⟨728968117122168816983603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7775659915969800714491765 728968117122168816983603)
                    ·
                      rfl

theorem cell23_4258981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_4258981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258981 prefixEnd_4258981 := by exact prefixLift 4258981
  have htrace : WordTrace (prefixWord ++ tailWord_4258981) baseStart_4258981 baseEnd_4258981 := by
    simpa [prefixWord, tailWord_4258981, baseEnd_4258981] using wordTrace_append hprefix tailTrace_4258981
  have hstable : (prefixWord ++ tailWord_4258981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258981).length < 2 ^ (prefixWord ++ tailWord_4258981).sum := by decide
  have hdescent : baseEnd_4258981 < baseStart_4258981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4258994 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_4258994 : Nat := 118140960795 + 4258994 * 2 ^ 59
def prefixEnd_4258994 : Nat := 4983230072969 + 3 ^ 40 * 4258994 * 2
def baseEnd_4258994 : Nat := 728970342205004966696083

theorem tailTrace_4258994 : CollatzResearch.WordTrace tailWord_4258994 prefixEnd_4258994 728970342205004966696083 := by
  unfold tailWord_4258994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38834568183099897777692009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103558848488266394073845357 38834568183099897777692009)
  ·
    refine ⟨29125926137324923333269007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38834568183099897777692009 29125926137324923333269007)
    ·
      refine ⟨43688889205987384999903511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29125926137324923333269007 43688889205987384999903511)
      ·
        refine ⟨65533333808981077499855267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43688889205987384999903511 65533333808981077499855267)
        ·
          refine ⟨98300000713471616249782901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65533333808981077499855267 98300000713471616249782901)
          ·
            refine ⟨9215625066887964023417147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98300000713471616249782901 9215625066887964023417147)
            ·
              refine ⟨13823437600331946035125721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215625066887964023417147 13823437600331946035125721)
              ·
                refine ⟨10367578200248959526344291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13823437600331946035125721 10367578200248959526344291)
                ·
                  refine ⟨15551367300373439289516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10367578200248959526344291 15551367300373439289516437)
                  ·
                    refine ⟨728970342205004966696083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15551367300373439289516437 728970342205004966696083)
                    ·
                      rfl

theorem cell23_4258994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_4258994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4258994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4258994 prefixEnd_4258994 := by exact prefixLift 4258994
  have htrace : WordTrace (prefixWord ++ tailWord_4258994) baseStart_4258994 baseEnd_4258994 := by
    simpa [prefixWord, tailWord_4258994, baseEnd_4258994] using wordTrace_append hprefix tailTrace_4258994
  have hstable : (prefixWord ++ tailWord_4258994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4258994).length < 2 ^ (prefixWord ++ tailWord_4258994).sum := by decide
  have hdescent : baseEnd_4258994 < baseStart_4258994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4258994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259028 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4259028 : Nat := 118140960795 + 4259028 * 2 ^ 59
def prefixEnd_4259028 : Nat := 4983230072969 + 3 ^ 40 * 4259028 * 2
def baseEnd_4259028 : Nat := 728976161652422589021031

theorem tailTrace_4259028 : CollatzResearch.WordTrace tailWord_4259028 prefixEnd_4259028 728976161652422589021031 := by
  unfold tailWord_4259028
  simp only [CollatzResearch.WordTrace]
  refine ⟨77669756407138207458752869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103559675209517609945003825 77669756407138207458752869)
  ·
    refine ⟨14563079326338413898516163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77669756407138207458752869 14563079326338413898516163)
    ·
      refine ⟨21844618989507620847774245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14563079326338413898516163 21844618989507620847774245)
      ·
        refine ⟨4095866060532678908957671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21844618989507620847774245 4095866060532678908957671)
        ·
          refine ⟨6143799090799018363436507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095866060532678908957671 6143799090799018363436507)
          ·
            refine ⟨9215698636198527545154761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143799090799018363436507 9215698636198527545154761)
            ·
              refine ⟨6911773977148895658866071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9215698636198527545154761 6911773977148895658866071)
              ·
                refine ⟨10367660965723343488299107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6911773977148895658866071 10367660965723343488299107)
                ·
                  refine ⟨15551491448585015232448661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10367660965723343488299107 15551491448585015232448661)
                  ·
                    refine ⟨728976161652422589021031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15551491448585015232448661 728976161652422589021031)
                    ·
                      rfl

theorem cell23_4259028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4259028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259028 prefixEnd_4259028 := by exact prefixLift 4259028
  have htrace : WordTrace (prefixWord ++ tailWord_4259028) baseStart_4259028 baseEnd_4259028 := by
    simpa [prefixWord, tailWord_4259028, baseEnd_4259028] using wordTrace_append hprefix tailTrace_4259028
  have hstable : (prefixWord ++ tailWord_4259028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259028).length < 2 ^ (prefixWord ++ tailWord_4259028).sum := by decide
  have hdescent : baseEnd_4259028 < baseStart_4259028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259055 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 1, 2, 3]
def baseStart_4259055 : Nat := 118140960795 + 4259055 * 2 ^ 59
def prefixEnd_4259055 : Nat := 4983230072969 + 3 ^ 40 * 4259055 * 2
def baseEnd_4259055 : Nat := 2186942348934939161425469

theorem tailTrace_4259055 : CollatzResearch.WordTrace tailWord_4259055 prefixEnd_4259055 2186942348934939161425469 := by
  unfold tailWord_4259055
  simp only [CollatzResearch.WordTrace]
  refine ⟨155340497585178598528738619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103560331723452399019159079 155340497585178598528738619)
  ·
    refine ⟨233010746377767897793107929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155340497585178598528738619 233010746377767897793107929)
    ·
      refine ⟨174758059783325923344830947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233010746377767897793107929 174758059783325923344830947)
      ·
        refine ⟨262137089674988885017246421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174758059783325923344830947 262137089674988885017246421)
        ·
          refine ⟨6143838039257551992591713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 262137089674988885017246421 6143838039257551992591713)
          ·
            refine ⟨4607878529443163994443785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6143838039257551992591713 4607878529443163994443785)
            ·
              refine ⟨3455908897082372995832839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4607878529443163994443785 3455908897082372995832839)
              ·
                refine ⟨5183863345623559493749259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455908897082372995832839 5183863345623559493749259)
                ·
                  refine ⟨7775795018435339240623889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5183863345623559493749259 7775795018435339240623889)
                  ·
                    refine ⟨5831846263826504430467917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7775795018435339240623889 5831846263826504430467917)
                    ·
                      refine ⟨2186942348934939161425469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831846263826504430467917 2186942348934939161425469)
                      ·
                        rfl

theorem cell23_4259055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 2, 3].length) (baseStart_4259055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259055 prefixEnd_4259055 := by exact prefixLift 4259055
  have htrace : WordTrace (prefixWord ++ tailWord_4259055) baseStart_4259055 baseEnd_4259055 := by
    simpa [prefixWord, tailWord_4259055, baseEnd_4259055] using wordTrace_append hprefix tailTrace_4259055
  have hstable : (prefixWord ++ tailWord_4259055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259055).length < 2 ^ (prefixWord ++ tailWord_4259055).sum := by decide
  have hdescent : baseEnd_4259055 < baseStart_4259055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259068 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_4259068 : Nat := 118140960795 + 4259068 * 2 ^ 59
def prefixEnd_4259068 : Nat := 4983230072969 + 3 ^ 40 * 4259068 * 2
def baseEnd_4259068 : Nat := 2186949024183447610562909

theorem tailTrace_4259068 : CollatzResearch.WordTrace tailWord_4259068 prefixEnd_4259068 2186949024183447610562909 := by
  unfold tailWord_4259068
  simp only [CollatzResearch.WordTrace]
  refine ⟨77670485867065750874480929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103560647822754334499307905 77670485867065750874480929)
  ·
    refine ⟨58252864400299313155860697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77670485867065750874480929 58252864400299313155860697)
    ·
      refine ⟨43689648300224484866895523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58252864400299313155860697 43689648300224484866895523)
      ·
        refine ⟨65534472450336727300343285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43689648300224484866895523 65534472450336727300343285)
        ·
          refine ⟨6143856792219068184407183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65534472450336727300343285 6143856792219068184407183)
          ·
            refine ⟨9215785188328602276610775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143856792219068184407183 9215785188328602276610775)
            ·
              refine ⟨13823677782492903414916163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215785188328602276610775 13823677782492903414916163)
              ·
                refine ⟨20735516673739355122374245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13823677782492903414916163 20735516673739355122374245)
                ·
                  refine ⟨3887909376326129085445171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20735516673739355122374245 3887909376326129085445171)
                  ·
                    refine ⟨5831864064489193628167757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887909376326129085445171 5831864064489193628167757)
                    ·
                      refine ⟨2186949024183447610562909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5831864064489193628167757 2186949024183447610562909)
                      ·
                        rfl

theorem cell23_4259068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_4259068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259068 prefixEnd_4259068 := by exact prefixLift 4259068
  have htrace : WordTrace (prefixWord ++ tailWord_4259068) baseStart_4259068 baseEnd_4259068 := by
    simpa [prefixWord, tailWord_4259068, baseEnd_4259068] using wordTrace_append hprefix tailTrace_4259068
  have hstable : (prefixWord ++ tailWord_4259068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259068).length < 2 ^ (prefixWord ++ tailWord_4259068).sum := by decide
  have hdescent : baseEnd_4259068 < baseStart_4259068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259084 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_4259084 : Nat := 118140960795 + 4259084 * 2 ^ 59
def prefixEnd_4259084 : Nat := 4983230072969 + 3 ^ 40 * 4259084 * 2
def baseEnd_4259084 : Nat := 728985746624639849320945

theorem tailTrace_4259084 : CollatzResearch.WordTrace tailWord_4259084 prefixEnd_4259084 728985746624639849320945 := by
  unfold tailWord_4259084
  simp only [CollatzResearch.WordTrace]
  refine ⟨77670777651036768240772153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103561036868049024321029537 77670777651036768240772153)
  ·
    refine ⟨58253083238277576180579115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77670777651036768240772153 58253083238277576180579115)
    ·
      refine ⟨87379624857416364270868673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58253083238277576180579115 87379624857416364270868673)
      ·
        refine ⟨65534718643062273203151505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87379624857416364270868673 65534718643062273203151505)
        ·
          refine ⟨49151038982296704902363629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65534718643062273203151505 49151038982296704902363629)
          ·
            refine ⟨18431639618361264338386361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49151038982296704902363629 18431639618361264338386361)
            ·
              refine ⟨13823729713770948253789771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18431639618361264338386361 13823729713770948253789771)
              ·
                refine ⟨20735594570656422380684657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13823729713770948253789771 20735594570656422380684657)
                ·
                  refine ⟨15551695927992316785513493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20735594570656422380684657 15551695927992316785513493)
                  ·
                    refine ⟨728985746624639849320945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15551695927992316785513493 728985746624639849320945)
                    ·
                      rfl

theorem cell23_4259084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_4259084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259084 prefixEnd_4259084 := by exact prefixLift 4259084
  have htrace : WordTrace (prefixWord ++ tailWord_4259084) baseStart_4259084 baseEnd_4259084 := by
    simpa [prefixWord, tailWord_4259084, baseEnd_4259084] using wordTrace_append hprefix tailTrace_4259084
  have hstable : (prefixWord ++ tailWord_4259084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259084).length < 2 ^ (prefixWord ++ tailWord_4259084).sum := by decide
  have hdescent : baseEnd_4259084 < baseStart_4259084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259108 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_4259108 : Nat := 118140960795 + 4259108 * 2 ^ 59
def prefixEnd_4259108 : Nat := 4983230072969 + 3 ^ 40 * 4259108 * 2
def baseEnd_4259108 : Nat := 2186969563409627454062725

theorem tailTrace_4259108 : CollatzResearch.WordTrace tailWord_4259108 prefixEnd_4259108 2186969563409627454062725 := by
  unfold tailWord_4259108
  simp only [CollatzResearch.WordTrace]
  refine ⟨77671215326993294290208989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103561620435991059053611985 77671215326993294290208989)
  ·
    refine ⟨29126705747622485358828371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77671215326993294290208989 29126705747622485358828371)
    ·
      refine ⟨43690058621433728038242557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29126705747622485358828371 43690058621433728038242557)
      ·
        refine ⟨16383771983037648014340959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43690058621433728038242557 16383771983037648014340959)
        ·
          refine ⟨24575657974556472021511439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16383771983037648014340959 24575657974556472021511439)
          ·
            refine ⟨36863486961834708032267159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24575657974556472021511439 36863486961834708032267159)
            ·
              refine ⟨55295230442752062048400739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36863486961834708032267159 55295230442752062048400739)
              ·
                refine ⟨82942845664128093072601109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55295230442752062048400739 82942845664128093072601109)
                ·
                  refine ⟨3887945890506004362778177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82942845664128093072601109 3887945890506004362778177)
                  ·
                    refine ⟨2915959417879503272083633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887945890506004362778177 2915959417879503272083633)
                    ·
                      refine ⟨2186969563409627454062725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2915959417879503272083633 2186969563409627454062725)
                      ·
                        rfl

theorem cell23_4259108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_4259108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259108 prefixEnd_4259108 := by exact prefixLift 4259108
  have htrace : WordTrace (prefixWord ++ tailWord_4259108) baseStart_4259108 baseEnd_4259108 := by
    simpa [prefixWord, tailWord_4259108, baseEnd_4259108] using wordTrace_append hprefix tailTrace_4259108
  have hstable : (prefixWord ++ tailWord_4259108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259108).length < 2 ^ (prefixWord ++ tailWord_4259108).sum := by decide
  have hdescent : baseEnd_4259108 < baseStart_4259108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259144 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_4259144 : Nat := 118140960795 + 4259144 * 2 ^ 59
def prefixEnd_4259144 : Nat := 4983230072969 + 3 ^ 40 * 4259144 * 2
def baseEnd_4259144 : Nat := 728996016237729771070853

theorem tailTrace_4259144 : CollatzResearch.WordTrace tailWord_4259144 prefixEnd_4259144 728996016237729771070853 := by
  unfold tailWord_4259144
  simp only [CollatzResearch.WordTrace]
  refine ⟨77671871840928083364364243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103562495787904111152485657 77671871840928083364364243)
  ·
    refine ⟨116507807761392125046546365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77671871840928083364364243 116507807761392125046546365)
    ·
      refine ⟨43690427910522046892454887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116507807761392125046546365 43690427910522046892454887)
      ·
        refine ⟨65535641865783070338682331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43690427910522046892454887 65535641865783070338682331)
        ·
          refine ⟨98303462798674605508023497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65535641865783070338682331 98303462798674605508023497)
          ·
            refine ⟨73727597099005954131017623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98303462798674605508023497 73727597099005954131017623)
            ·
              refine ⟨110591395648508931196526435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73727597099005954131017623 110591395648508931196526435)
              ·
                refine ⟨165887093472763396794789653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110591395648508931196526435 165887093472763396794789653)
                ·
                  refine ⟨7775957506535784224755765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165887093472763396794789653 7775957506535784224755765)
                  ·
                    refine ⟨728996016237729771070853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7775957506535784224755765 728996016237729771070853)
                    ·
                      rfl

theorem cell23_4259144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_4259144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259144 prefixEnd_4259144 := by exact prefixLift 4259144
  have htrace : WordTrace (prefixWord ++ tailWord_4259144) baseStart_4259144 baseEnd_4259144 := by
    simpa [prefixWord, tailWord_4259144, baseEnd_4259144] using wordTrace_append hprefix tailTrace_4259144
  have hstable : (prefixWord ++ tailWord_4259144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259144).length < 2 ^ (prefixWord ++ tailWord_4259144).sum := by decide
  have hdescent : baseEnd_4259144 < baseStart_4259144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259154 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_4259154 : Nat := 118140960795 + 4259154 * 2 ^ 59
def prefixEnd_4259154 : Nat := 4983230072969 + 3 ^ 40 * 4259154 * 2
def baseEnd_4259154 : Nat := 2186993183519734274087513

theorem tailTrace_4259154 : CollatzResearch.WordTrace tailWord_4259154 prefixEnd_4259154 2186993183519734274087513 := by
  unfold tailWord_4259154
  simp only [CollatzResearch.WordTrace]
  refine ⟨38836027102954984609148129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103562738941213292291061677 38836027102954984609148129)
  ·
    refine ⟨29127020327216238456861097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38836027102954984609148129 29127020327216238456861097)
    ·
      refine ⟨21845265245412178842645823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29127020327216238456861097 21845265245412178842645823)
      ·
        refine ⟨32767897868118268263968735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21845265245412178842645823 32767897868118268263968735)
        ·
          refine ⟨49151846802177402395953103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32767897868118268263968735 49151846802177402395953103)
          ·
            refine ⟨73727770203266103593929655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49151846802177402395953103 73727770203266103593929655)
            ·
              refine ⟨110591655304899155390894483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73727770203266103593929655 110591655304899155390894483)
              ·
                refine ⟨165887482957348733086341725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110591655304899155390894483 165887482957348733086341725)
                ·
                  refine ⟨62207806109005774907378147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165887482957348733086341725 62207806109005774907378147)
                  ·
                    refine ⟨93311709163508662361067221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62207806109005774907378147 93311709163508662361067221)
                    ·
                      refine ⟨2186993183519734274087513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93311709163508662361067221 2186993183519734274087513)
                      ·
                        rfl

theorem cell23_4259154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_4259154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259154 prefixEnd_4259154 := by exact prefixLift 4259154
  have htrace : WordTrace (prefixWord ++ tailWord_4259154) baseStart_4259154 baseEnd_4259154 := by
    simpa [prefixWord, tailWord_4259154, baseEnd_4259154] using wordTrace_append hprefix tailTrace_4259154
  have hstable : (prefixWord ++ tailWord_4259154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259154).length < 2 ^ (prefixWord ++ tailWord_4259154).sum := by decide
  have hdescent : baseEnd_4259154 < baseStart_4259154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259184 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_4259184 : Nat := 118140960795 + 4259184 * 2 ^ 59
def prefixEnd_4259184 : Nat := 4983230072969 + 3 ^ 40 * 4259184 * 2
def baseEnd_4259184 : Nat := 2187008587939369156712375

theorem tailTrace_4259184 : CollatzResearch.WordTrace tailWord_4259184 prefixEnd_4259184 2187008587939369156712375 := by
  unfold tailWord_4259184
  simp only [CollatzResearch.WordTrace]
  refine ⟨77672601300855626780092303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103563468401140835706789737 77672601300855626780092303)
  ·
    refine ⟨116508901951283440170138455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77672601300855626780092303 116508901951283440170138455)
    ·
      refine ⟨174763352926925160255207683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116508901951283440170138455 174763352926925160255207683)
      ·
        refine ⟨262145029390387740382811525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174763352926925160255207683 262145029390387740382811525)
        ·
          refine ⟨49152193010697701321777161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262145029390387740382811525 49152193010697701321777161)
          ·
            refine ⟨36864144758023275991332871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49152193010697701321777161 36864144758023275991332871)
            ·
              refine ⟨55296217137034913986999307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36864144758023275991332871 55296217137034913986999307)
              ·
                refine ⟨82944325705552370980498961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55296217137034913986999307 82944325705552370980498961)
                ·
                  refine ⟨62208244279164278235374221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82944325705552370980498961 62208244279164278235374221)
                  ·
                    refine ⟨23328091604686604338265333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62208244279164278235374221 23328091604686604338265333)
                    ·
                      refine ⟨2187008587939369156712375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23328091604686604338265333 2187008587939369156712375)
                      ·
                        rfl

theorem cell23_4259184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_4259184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259184 prefixEnd_4259184 := by exact prefixLift 4259184
  have htrace : WordTrace (prefixWord ++ tailWord_4259184) baseStart_4259184 baseEnd_4259184 := by
    simpa [prefixWord, tailWord_4259184, baseEnd_4259184] using wordTrace_append hprefix tailTrace_4259184
  have hstable : (prefixWord ++ tailWord_4259184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259184).length < 2 ^ (prefixWord ++ tailWord_4259184).sum := by decide
  have hdescent : baseEnd_4259184 < baseStart_4259184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259191 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 3, 4]
def baseStart_4259191 : Nat := 118140960795 + 4259191 * 2 ^ 59
def prefixEnd_4259191 : Nat := 4983230072969 + 3 ^ 40 * 4259191 * 2
def baseEnd_4259191 : Nat := 729004060767983543108281

theorem tailTrace_4259191 : CollatzResearch.WordTrace tailWord_4259191 prefixEnd_4259191 729004060767983543108281 := by
  unfold tailWord_4259191
  simp only [CollatzResearch.WordTrace]
  refine ⟨155345457912685893755689427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103563638608457262503792951 155345457912685893755689427)
  ·
    refine ⟨233018186869028840633534141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155345457912685893755689427 233018186869028840633534141)
    ·
      refine ⟨87381820075885815237575303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233018186869028840633534141 87381820075885815237575303)
      ·
        refine ⟨131072730113828722856362955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87381820075885815237575303 131072730113828722856362955)
        ·
          refine ⟨196609095170743084284544433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131072730113828722856362955 196609095170743084284544433)
          ·
            refine ⟨147456821378057313213408325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196609095170743084284544433 147456821378057313213408325)
            ·
              refine ⟨27648154008385746227514061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147456821378057313213408325 27648154008385746227514061)
              ·
                refine ⟨10368057753144654835317773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27648154008385746227514061 10368057753144654835317773)
                ·
                  refine ⟨3888021657429245563244165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10368057753144654835317773 3888021657429245563244165)
                  ·
                    refine ⟨729004060767983543108281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888021657429245563244165 729004060767983543108281)
                    ·
                      rfl

theorem cell23_4259191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_4259191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259191 prefixEnd_4259191 := by exact prefixLift 4259191
  have htrace : WordTrace (prefixWord ++ tailWord_4259191) baseStart_4259191 baseEnd_4259191 := by
    simpa [prefixWord, tailWord_4259191, baseEnd_4259191] using wordTrace_append hprefix tailTrace_4259191
  have hstable : (prefixWord ++ tailWord_4259191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259191).length < 2 ^ (prefixWord ++ tailWord_4259191).sum := by decide
  have hdescent : baseEnd_4259191 < baseStart_4259191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259194 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_4259194 : Nat := 118140960795 + 4259194 * 2 ^ 59
def prefixEnd_4259194 : Nat := 4983230072969 + 3 ^ 40 * 4259194 * 2
def baseEnd_4259194 : Nat := 2187013722745914117587329

theorem tailTrace_4259194 : CollatzResearch.WordTrace tailWord_4259194 prefixEnd_4259194 2187013722745914117587329 := by
  unfold tailWord_4259194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38836391832918756317012159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103563711554450016845365757 38836391832918756317012159)
  ·
    refine ⟨58254587749378134475518239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38836391832918756317012159 58254587749378134475518239)
    ·
      refine ⟨87381881624067201713277359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58254587749378134475518239 87381881624067201713277359)
      ·
        refine ⟨131072822436100802569916039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87381881624067201713277359 131072822436100802569916039)
        ·
          refine ⟨196609233654151203854874059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131072822436100802569916039 196609233654151203854874059)
          ·
            refine ⟨294913850481226805782311089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196609233654151203854874059 294913850481226805782311089)
            ·
              refine ⟨221185387860920104336733317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294913850481226805782311089 221185387860920104336733317)
              ·
                refine ⟨41472260223922519563137497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221185387860920104336733317 41472260223922519563137497)
                ·
                  refine ⟨31104195167941889672353123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41472260223922519563137497 31104195167941889672353123)
                  ·
                    refine ⟨46656292751912834508529685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31104195167941889672353123 46656292751912834508529685)
                    ·
                      refine ⟨2187013722745914117587329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46656292751912834508529685 2187013722745914117587329)
                      ·
                        rfl

theorem cell23_4259194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_4259194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259194 prefixEnd_4259194 := by exact prefixLift 4259194
  have htrace : WordTrace (prefixWord ++ tailWord_4259194) baseStart_4259194 baseEnd_4259194 := by
    simpa [prefixWord, tailWord_4259194, baseEnd_4259194] using wordTrace_append hprefix tailTrace_4259194
  have hstable : (prefixWord ++ tailWord_4259194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259194).length < 2 ^ (prefixWord ++ tailWord_4259194).sum := by decide
  have hdescent : baseEnd_4259194 < baseStart_4259194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259208 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_4259208 : Nat := 118140960795 + 4259208 * 2 ^ 59
def prefixEnd_4259208 : Nat := 4983230072969 + 3 ^ 40 * 4259208 * 2
def baseEnd_4259208 : Nat := 729006970491692354270755

theorem tailTrace_4259208 : CollatzResearch.WordTrace tailWord_4259208 prefixEnd_4259208 729006970491692354270755 := by
  unfold tailWord_4259208
  simp only [CollatzResearch.WordTrace]
  refine ⟨77673038976812152829529139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103564051969082870439372185 77673038976812152829529139)
  ·
    refine ⟨116509558465218229244293709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77673038976812152829529139 116509558465218229244293709)
    ·
      refine ⟨43691084424456835966610141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116509558465218229244293709 43691084424456835966610141)
      ·
        refine ⟨16384156659171313487478803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43691084424456835966610141 16384156659171313487478803)
        ·
          refine ⟨24576234988756970231218205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16384156659171313487478803 24576234988756970231218205)
          ·
            refine ⟨9216088120783863836706827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24576234988756970231218205 9216088120783863836706827)
            ·
              refine ⟨13824132181175795755060241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9216088120783863836706827 13824132181175795755060241)
              ·
                refine ⟨10368099135881846816295181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13824132181175795755060241 10368099135881846816295181)
                ·
                  refine ⟨3888037175955692556110693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10368099135881846816295181 3888037175955692556110693)
                  ·
                    refine ⟨729006970491692354270755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888037175955692556110693 729006970491692354270755)
                    ·
                      rfl

theorem cell23_4259208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_4259208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259208 prefixEnd_4259208 := by exact prefixLift 4259208
  have htrace : WordTrace (prefixWord ++ tailWord_4259208) baseStart_4259208 baseEnd_4259208 := by
    simpa [prefixWord, tailWord_4259208, baseEnd_4259208] using wordTrace_append hprefix tailTrace_4259208
  have hstable : (prefixWord ++ tailWord_4259208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259208).length < 2 ^ (prefixWord ++ tailWord_4259208).sum := by decide
  have hdescent : baseEnd_4259208 < baseStart_4259208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259225 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 1, 4]
def baseStart_4259225 : Nat := 118140960795 + 4259225 * 2 ^ 59
def prefixEnd_4259225 : Nat := 4983230072969 + 3 ^ 40 * 4259225 * 2
def baseEnd_4259225 : Nat := 729009880215401165433229

theorem tailTrace_4259225 : CollatzResearch.WordTrace tailWord_4259225 prefixEnd_4259225 729009880215401165433229 := by
  unfold tailWord_4259225
  simp only [CollatzResearch.WordTrace]
  refine ⟨155346697994562717562427129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103564465329708478374951419 155346697994562717562427129)
  ·
    refine ⟨116510023495922038171820347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155346697994562717562427129 116510023495922038171820347)
    ·
      refine ⟨174765035243883057257730521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116510023495922038171820347 174765035243883057257730521)
      ·
        refine ⟨131073776432912292943297891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174765035243883057257730521 131073776432912292943297891)
        ·
          refine ⟨196610664649368439414946837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131073776432912292943297891 196610664649368439414946837)
          ·
            refine ⟨9216124905439145597575633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196610664649368439414946837 9216124905439145597575633)
            ·
              refine ⟨6912093679079359198181725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9216124905439145597575633 6912093679079359198181725)
              ·
                refine ⟨2592035129654759699318147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6912093679079359198181725 2592035129654759699318147)
                ·
                  refine ⟨3888052694482139548977221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592035129654759699318147 3888052694482139548977221)
                  ·
                    refine ⟨729009880215401165433229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888052694482139548977221 729009880215401165433229)
                    ·
                      rfl

theorem cell23_4259225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 1, 4].length) (baseStart_4259225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259225 prefixEnd_4259225 := by exact prefixLift 4259225
  have htrace : WordTrace (prefixWord ++ tailWord_4259225) baseStart_4259225 baseEnd_4259225 := by
    simpa [prefixWord, tailWord_4259225, baseEnd_4259225] using wordTrace_append hprefix tailTrace_4259225
  have hstable : (prefixWord ++ tailWord_4259225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259225).length < 2 ^ (prefixWord ++ tailWord_4259225).sum := by decide
  have hdescent : baseEnd_4259225 < baseStart_4259225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259288 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_4259288 : Nat := 118140960795 + 4259288 * 2 ^ 59
def prefixEnd_4259288 : Nat := 4983230072969 + 3 ^ 40 * 4259288 * 2
def baseEnd_4259288 : Nat := 2187061989927436749811897

theorem tailTrace_4259288 : CollatzResearch.WordTrace tailWord_4259288 prefixEnd_4259288 2187061989927436749811897 := by
  unfold tailWord_4259288
  simp only [CollatzResearch.WordTrace]
  refine ⟨77674497896667239660985259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103565997195556319547980345 77674497896667239660985259)
  ·
    refine ⟨116511746845000859491477889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77674497896667239660985259 116511746845000859491477889)
    ·
      refine ⟨87383810133750644618608417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116511746845000859491477889 87383810133750644618608417)
      ·
        refine ⟨65537857600312983463956313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87383810133750644618608417 65537857600312983463956313)
        ·
          refine ⟨49153393200234737597967235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65537857600312983463956313 49153393200234737597967235)
          ·
            refine ⟨73730089800352106396950853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49153393200234737597967235 73730089800352106396950853)
            ·
              refine ⟨13824391837566019949428285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73730089800352106396950853 13824391837566019949428285)
              ·
                refine ⟨5184146939087257481035607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13824391837566019949428285 5184146939087257481035607)
                ·
                  refine ⟨7776220408630886221553411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5184146939087257481035607 7776220408630886221553411)
                  ·
                    refine ⟨11664330612946329332330117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7776220408630886221553411 11664330612946329332330117)
                    ·
                      refine ⟨2187061989927436749811897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11664330612946329332330117 2187061989927436749811897)
                      ·
                        rfl

theorem cell23_4259288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_4259288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259288 prefixEnd_4259288 := by exact prefixLift 4259288
  have htrace : WordTrace (prefixWord ++ tailWord_4259288) baseStart_4259288 baseEnd_4259288 := by
    simpa [prefixWord, tailWord_4259288, baseEnd_4259288] using wordTrace_append hprefix tailTrace_4259288
  have hstable : (prefixWord ++ tailWord_4259288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259288).length < 2 ^ (prefixWord ++ tailWord_4259288).sum := by decide
  have hdescent : baseEnd_4259288 < baseStart_4259288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259299 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 1, 1, 3]
def baseStart_4259299 : Nat := 118140960795 + 4259299 * 2 ^ 59
def prefixEnd_4259299 : Nat := 4983230072969 + 3 ^ 40 * 4259299 * 2
def baseEnd_4259299 : Nat := 2187067638214636206774347

theorem tailTrace_4259299 : CollatzResearch.WordTrace tailWord_4259299 prefixEnd_4259299 2187067638214636206774347 := by
  unfold tailWord_4259299
  simp only [CollatzResearch.WordTrace]
  refine ⟨155349396996294628200620951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103566264664196418800413967 155349396996294628200620951)
  ·
    refine ⟨233024095494441942300931427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155349396996294628200620951 233024095494441942300931427)
    ·
      refine ⟨349536143241662913451397141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233024095494441942300931427 349536143241662913451397141)
      ·
        refine ⟨16384506714452949068034241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 349536143241662913451397141 16384506714452949068034241)
        ·
          refine ⟨12288380035839711801025681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16384506714452949068034241 12288380035839711801025681)
          ·
            refine ⟨9216285026879783850769261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12288380035839711801025681 9216285026879783850769261)
            ·
              refine ⟨3456106885079918944038473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9216285026879783850769261 3456106885079918944038473)
              ·
                refine ⟨2592080163809939208028855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3456106885079918944038473 2592080163809939208028855)
                ·
                  refine ⟨3888120245714908812043283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592080163809939208028855 3888120245714908812043283)
                  ·
                    refine ⟨5832180368572363218064925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3888120245714908812043283 5832180368572363218064925)
                    ·
                      refine ⟨2187067638214636206774347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832180368572363218064925 2187067638214636206774347)
                      ·
                        rfl

theorem cell23_4259299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_4259299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259299 prefixEnd_4259299 := by exact prefixLift 4259299
  have htrace : WordTrace (prefixWord ++ tailWord_4259299) baseStart_4259299 baseEnd_4259299 := by
    simpa [prefixWord, tailWord_4259299, baseEnd_4259299] using wordTrace_append hprefix tailTrace_4259299
  have hstable : (prefixWord ++ tailWord_4259299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259299).length < 2 ^ (prefixWord ++ tailWord_4259299).sum := by decide
  have hdescent : baseEnd_4259299 < baseStart_4259299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259318 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4259318 : Nat := 118140960795 + 4259318 * 2 ^ 59
def prefixEnd_4259318 : Nat := 4983230072969 + 3 ^ 40 * 4259318 * 2
def baseEnd_4259318 : Nat := 2187077394347071632436759

theorem tailTrace_4259318 : CollatzResearch.WordTrace tailWord_4259318 prefixEnd_4259318 2187077394347071632436759 := by
  unfold tailWord_4259318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709380623951612152847663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103566726655483862963708405 9709380623951612152847663)
  ·
    refine ⟨14564070935927418229271495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9709380623951612152847663 14564070935927418229271495)
    ·
      refine ⟨21846106403891127343907243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14564070935927418229271495 21846106403891127343907243)
      ·
        refine ⟨32769159605836691015860865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21846106403891127343907243 32769159605836691015860865)
        ·
          refine ⟨24576869704377518261895649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32769159605836691015860865 24576869704377518261895649)
          ·
            refine ⟨18432652278283138696421737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24576869704377518261895649 18432652278283138696421737)
            ·
              refine ⟨13824489208712354022316303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18432652278283138696421737 13824489208712354022316303)
              ·
                refine ⟨20736733813068531033474455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13824489208712354022316303 20736733813068531033474455)
                ·
                  refine ⟨31105100719602796550211683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20736733813068531033474455 31105100719602796550211683)
                  ·
                    refine ⟨46657651079404194825317525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31105100719602796550211683 46657651079404194825317525)
                    ·
                      refine ⟨2187077394347071632436759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46657651079404194825317525 2187077394347071632436759)
                      ·
                        rfl

theorem cell23_4259318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4259318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259318 prefixEnd_4259318 := by exact prefixLift 4259318
  have htrace : WordTrace (prefixWord ++ tailWord_4259318) baseStart_4259318 baseEnd_4259318 := by
    simpa [prefixWord, tailWord_4259318, baseEnd_4259318] using wordTrace_append hprefix tailTrace_4259318
  have hstable : (prefixWord ++ tailWord_4259318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259318).length < 2 ^ (prefixWord ++ tailWord_4259318).sum := by decide
  have hdescent : baseEnd_4259318 < baseStart_4259318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259325 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_4259325 : Nat := 118140960795 + 4259325 * 2 ^ 59
def prefixEnd_4259325 : Nat := 4983230072969 + 3 ^ 40 * 4259325 * 2
def baseEnd_4259325 : Nat := 2187080988711653105049227

theorem tailTrace_4259325 : CollatzResearch.WordTrace tailWord_4259325 prefixEnd_4259325 2187080988711653105049227 := by
  unfold tailWord_4259325
  simp only [CollatzResearch.WordTrace]
  refine ⟨155350345294200434641067429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103566896862800289760711619 155350345294200434641067429)
  ·
    refine ⟨29128189742662581495200143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155350345294200434641067429 29128189742662581495200143)
    ·
      refine ⟨43692284613993872242800215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29128189742662581495200143 43692284613993872242800215)
      ·
        refine ⟨65538426920990808364200323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43692284613993872242800215 65538426920990808364200323)
        ·
          refine ⟨98307640381486212546300485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65538426920990808364200323 98307640381486212546300485)
          ·
            refine ⟨18432682571528664852431341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98307640381486212546300485 18432682571528664852431341)
            ·
              refine ⟨6912255964323249319661753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18432682571528664852431341 6912255964323249319661753)
              ·
                refine ⟨5184191973242436989746315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6912255964323249319661753 5184191973242436989746315)
                ·
                  refine ⟨7776287959863655484619473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5184191973242436989746315 7776287959863655484619473)
                  ·
                    refine ⟨5832215969897741613464605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7776287959863655484619473 5832215969897741613464605)
                    ·
                      refine ⟨2187080988711653105049227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832215969897741613464605 2187080988711653105049227)
                      ·
                        rfl

theorem cell23_4259325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_4259325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259325 prefixEnd_4259325 := by exact prefixLift 4259325
  have htrace : WordTrace (prefixWord ++ tailWord_4259325) baseStart_4259325 baseEnd_4259325 := by
    simpa [prefixWord, tailWord_4259325, baseEnd_4259325] using wordTrace_append hprefix tailTrace_4259325
  have hstable : (prefixWord ++ tailWord_4259325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259325).length < 2 ^ (prefixWord ++ tailWord_4259325).sum := by decide
  have hdescent : baseEnd_4259325 < baseStart_4259325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259338 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_4259338 : Nat := 118140960795 + 4259338 * 2 ^ 59
def prefixEnd_4259338 : Nat := 4983230072969 + 3 ^ 40 * 4259338 * 2
def baseEnd_4259338 : Nat := 2187087663960161554186667

theorem tailTrace_4259338 : CollatzResearch.WordTrace tailWord_4259338 prefixEnd_4259338 2187087663960161554186667 := by
  unfold tailWord_4259338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38837704860788334465322667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103567212962102225240860445 38837704860788334465322667)
  ·
    refine ⟨58256557291182501697984001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38837704860788334465322667 58256557291182501697984001)
    ·
      refine ⟨43692417968386876273488001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58256557291182501697984001 43692417968386876273488001)
      ·
        refine ⟨32769313476290157205116001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43692417968386876273488001 32769313476290157205116001)
        ·
          refine ⟨24576985107217617903837001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32769313476290157205116001 24576985107217617903837001)
          ·
            refine ⟨18432738830413213427877751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24576985107217617903837001 18432738830413213427877751)
            ·
              refine ⟨27649108245619820141816627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18432738830413213427877751 27649108245619820141816627)
              ·
                refine ⟨41473662368429730212724941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27649108245619820141816627 41473662368429730212724941)
                ·
                  refine ⟨15552623388161148829771853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41473662368429730212724941 15552623388161148829771853)
                  ·
                    refine ⟨5832233770560430811164445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15552623388161148829771853 5832233770560430811164445)
                    ·
                      refine ⟨2187087663960161554186667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832233770560430811164445 2187087663960161554186667)
                      ·
                        rfl

theorem cell23_4259338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_4259338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259338 prefixEnd_4259338 := by exact prefixLift 4259338
  have htrace : WordTrace (prefixWord ++ tailWord_4259338) baseStart_4259338 baseEnd_4259338 := by
    simpa [prefixWord, tailWord_4259338, baseEnd_4259338] using wordTrace_append hprefix tailTrace_4259338
  have hstable : (prefixWord ++ tailWord_4259338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259338).length < 2 ^ (prefixWord ++ tailWord_4259338).sum := by decide
  have hdescent : baseEnd_4259338 < baseStart_4259338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259342 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4259342 : Nat := 118140960795 + 4259342 * 2 ^ 59
def prefixEnd_4259342 : Nat := 4983230072969 + 3 ^ 40 * 4259342 * 2
def baseEnd_4259342 : Nat := 2187089717882779538536649

theorem tailTrace_4259342 : CollatzResearch.WordTrace tailWord_4259342 prefixEnd_4259342 2187089717882779538536649 := by
  unfold tailWord_4259342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19418870666892355818054535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103567310223425897696290853 19418870666892355818054535)
  ·
    refine ⟨29128306000338533727081803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19418870666892355818054535 29128306000338533727081803)
    ·
      refine ⟨43692459000507800590622705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29128306000338533727081803 43692459000507800590622705)
      ·
        refine ⟨32769344250380850442967029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43692459000507800590622705 32769344250380850442967029)
        ·
          refine ⟨3072126023473204729028159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32769344250380850442967029 3072126023473204729028159)
          ·
            refine ⟨4608189035209807093542239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072126023473204729028159 4608189035209807093542239)
            ·
              refine ⟨6912283552814710640313359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608189035209807093542239 6912283552814710640313359)
              ·
                refine ⟨10368425329222065960470039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6912283552814710640313359 10368425329222065960470039)
                ·
                  refine ⟨15552637993833098940705059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10368425329222065960470039 15552637993833098940705059)
                  ·
                    refine ⟨23328956990749648411057589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15552637993833098940705059 23328956990749648411057589)
                    ·
                      refine ⟨2187089717882779538536649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23328956990749648411057589 2187089717882779538536649)
                      ·
                        rfl

theorem cell23_4259342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4259342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259342 prefixEnd_4259342 := by exact prefixLift 4259342
  have htrace : WordTrace (prefixWord ++ tailWord_4259342) baseStart_4259342 baseEnd_4259342 := by
    simpa [prefixWord, tailWord_4259342, baseEnd_4259342] using wordTrace_append hprefix tailTrace_4259342
  have hstable : (prefixWord ++ tailWord_4259342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259342).length < 2 ^ (prefixWord ++ tailWord_4259342).sum := by decide
  have hdescent : baseEnd_4259342 < baseStart_4259342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259412 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_4259412 : Nat := 118140960795 + 4259412 * 2 ^ 59
def prefixEnd_4259412 : Nat := 4983230072969 + 3 ^ 40 * 4259412 * 2
def baseEnd_4259412 : Nat := 2187125661528594264661327

theorem tailTrace_4259412 : CollatzResearch.WordTrace tailWord_4259412 prefixEnd_4259412 2187125661528594264661327 := by
  unfold tailWord_4259412
  simp only [CollatzResearch.WordTrace]
  refine ⟨77676759222442624249742245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103569012296590165666322993 77676759222442624249742245)
  ·
    refine ⟨14564392354207992046826671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77676759222442624249742245 14564392354207992046826671)
    ·
      refine ⟨21846588531311988070240007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14564392354207992046826671 21846588531311988070240007)
      ·
        refine ⟨32769882796967982105360011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21846588531311988070240007 32769882796967982105360011)
        ·
          refine ⟨49154824195451973158040017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32769882796967982105360011 49154824195451973158040017)
          ·
            refine ⟨36866118146588979868530013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49154824195451973158040017 36866118146588979868530013)
            ·
              refine ⟨13824794304970867450698755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36866118146588979868530013 13824794304970867450698755)
              ·
                refine ⟨20737191457456301176048133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13824794304970867450698755 20737191457456301176048133)
                ·
                  refine ⟨3888223398273056470509025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20737191457456301176048133 3888223398273056470509025)
                  ·
                    refine ⟨2916167548704792352881769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3888223398273056470509025 2916167548704792352881769)
                    ·
                      refine ⟨2187125661528594264661327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916167548704792352881769 2187125661528594264661327)
                      ·
                        rfl

theorem cell23_4259412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_4259412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259412 prefixEnd_4259412 := by exact prefixLift 4259412
  have htrace : WordTrace (prefixWord ++ tailWord_4259412) baseStart_4259412 baseEnd_4259412 := by
    simpa [prefixWord, tailWord_4259412, baseEnd_4259412] using wordTrace_append hprefix tailTrace_4259412
  have hstable : (prefixWord ++ tailWord_4259412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259412).length < 2 ^ (prefixWord ++ tailWord_4259412).sum := by decide
  have hdescent : baseEnd_4259412 < baseStart_4259412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259485 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_4259485 : Nat := 118140960795 + 4259485 * 2 ^ 59
def prefixEnd_4259485 : Nat := 4983230072969 + 3 ^ 40 * 4259485 * 2
def baseEnd_4259485 : Nat := 2187163145616372479048491

theorem tailTrace_4259485 : CollatzResearch.WordTrace tailWord_4259485 prefixEnd_4259485 2187163145616372479048491 := by
  unfold tailWord_4259485
  simp only [CollatzResearch.WordTrace]
  refine ⟨155356180973620781966891909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103570787315747187977927939 155356180973620781966891909)
  ·
    refine ⟨29129283932553896618792233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155356180973620781966891909 29129283932553896618792233)
    ·
      refine ⟨21846962949415422464094175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29129283932553896618792233 21846962949415422464094175)
      ·
        refine ⟨32770444424123133696141263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21846962949415422464094175 32770444424123133696141263)
        ·
          refine ⟨49155666636184700544211895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32770444424123133696141263 49155666636184700544211895)
          ·
            refine ⟨73733499954277050816317843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49155666636184700544211895 73733499954277050816317843)
            ·
              refine ⟨110600249931415576224476765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73733499954277050816317843 110600249931415576224476765)
              ·
                refine ⟨41475093724280841084178787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110600249931415576224476765 41475093724280841084178787)
                ·
                  refine ⟨62212640586421261626268181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41475093724280841084178787 62212640586421261626268181)
                  ·
                    refine ⟨2916217527488496638731321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62212640586421261626268181 2916217527488496638731321)
                    ·
                      refine ⟨2187163145616372479048491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916217527488496638731321 2187163145616372479048491)
                      ·
                        rfl

theorem cell23_4259485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_4259485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259485 prefixEnd_4259485 := by exact prefixLift 4259485
  have htrace : WordTrace (prefixWord ++ tailWord_4259485) baseStart_4259485 baseEnd_4259485 := by
    simpa [prefixWord, tailWord_4259485, baseEnd_4259485] using wordTrace_append hprefix tailTrace_4259485
  have hstable : (prefixWord ++ tailWord_4259485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259485).length < 2 ^ (prefixWord ++ tailWord_4259485).sum := by decide
  have hdescent : baseEnd_4259485 < baseStart_4259485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259528 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_4259528 : Nat := 118140960795 + 4259528 * 2 ^ 59
def prefixEnd_4259528 : Nat := 4983230072969 + 3 ^ 40 * 4259528 * 2
def baseEnd_4259528 : Nat := 2187185225284515810810793

theorem tailTrace_4259528 : CollatzResearch.WordTrace tailWord_4259528 prefixEnd_4259528 2187185225284515810810793 := by
  unfold tailWord_4259528
  simp only [CollatzResearch.WordTrace]
  refine ⟨77678874656232500155353619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103571832874976666873804825 77678874656232500155353619)
  ·
    refine ⟨116518311984348750233030429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77678874656232500155353619 116518311984348750233030429)
    ·
      refine ⟨43694366994130781337386411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116518311984348750233030429 43694366994130781337386411)
      ·
        refine ⟨65541550491196172006079617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43694366994130781337386411 65541550491196172006079617)
        ·
          refine ⟨49156162868397129004559713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65541550491196172006079617 49156162868397129004559713)
          ·
            refine ⟨36867122151297846753419785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49156162868397129004559713 36867122151297846753419785)
            ·
              refine ⟨27650341613473385065064839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36867122151297846753419785 27650341613473385065064839)
              ·
                refine ⟨41475512420210077597597259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27650341613473385065064839 41475512420210077597597259)
                ·
                  refine ⟨62213268630315116396395889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41475512420210077597597259 62213268630315116396395889)
                  ·
                    refine ⟨46659951472736337297296917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62213268630315116396395889 46659951472736337297296917)
                    ·
                      refine ⟨2187185225284515810810793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46659951472736337297296917 2187185225284515810810793)
                      ·
                        rfl

theorem cell23_4259528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_4259528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259528 prefixEnd_4259528 := by exact prefixLift 4259528
  have htrace : WordTrace (prefixWord ++ tailWord_4259528) baseStart_4259528 baseEnd_4259528 := by
    simpa [prefixWord, tailWord_4259528, baseEnd_4259528] using wordTrace_append hprefix tailTrace_4259528
  have hstable : (prefixWord ++ tailWord_4259528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259528).length < 2 ^ (prefixWord ++ tailWord_4259528).sum := by decide
  have hdescent : baseEnd_4259528 < baseStart_4259528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259535 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 3]
def baseStart_4259535 : Nat := 118140960795 + 4259535 * 2 ^ 59
def prefixEnd_4259535 : Nat := 4983230072969 + 3 ^ 40 * 4259535 * 2
def baseEnd_4259535 : Nat := 2187188819649097283423261

theorem tailTrace_4259535 : CollatzResearch.WordTrace tailWord_4259535 prefixEnd_4259535 2187188819649097283423261 := by
  unfold tailWord_4259535
  simp only [CollatzResearch.WordTrace]
  refine ⟨155358004623439640506212059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103572003082293093670808039 155358004623439640506212059)
  ·
    refine ⟨233037006935159460759318089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155358004623439640506212059 233037006935159460759318089)
    ·
      refine ⟨174777755201369595569488567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233037006935159460759318089 174777755201369595569488567)
      ·
        refine ⟨262166632802054393354232851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174777755201369595569488567 262166632802054393354232851)
        ·
          refine ⟨393249949203081590031349277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262166632802054393354232851 393249949203081590031349277)
          ·
            refine ⟨147468730951155596261755979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393249949203081590031349277 147468730951155596261755979)
            ·
              refine ⟨221203096426733394392633969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147468730951155596261755979 221203096426733394392633969)
              ·
                refine ⟨165902322320050045794475477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221203096426733394392633969 165902322320050045794475477)
                ·
                  refine ⟨3888335679376172948308019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 165902322320050045794475477 3888335679376172948308019)
                  ·
                    refine ⟨5832503519064259422462029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3888335679376172948308019 5832503519064259422462029)
                    ·
                      refine ⟨2187188819649097283423261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832503519064259422462029 2187188819649097283423261)
                      ·
                        rfl

theorem cell23_4259535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_4259535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259535 prefixEnd_4259535 := by exact prefixLift 4259535
  have htrace : WordTrace (prefixWord ++ tailWord_4259535) baseStart_4259535 baseEnd_4259535 := by
    simpa [prefixWord, tailWord_4259535, baseEnd_4259535] using wordTrace_append hprefix tailTrace_4259535
  have hstable : (prefixWord ++ tailWord_4259535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259535).length < 2 ^ (prefixWord ++ tailWord_4259535).sum := by decide
  have hdescent : baseEnd_4259535 < baseStart_4259535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259568 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_4259568 : Nat := 118140960795 + 4259568 * 2 ^ 59
def prefixEnd_4259568 : Nat := 4983230072969 + 3 ^ 40 * 4259568 * 2
def baseEnd_4259568 : Nat := 729068588170231884770203

theorem tailTrace_4259568 : CollatzResearch.WordTrace tailWord_4259568 prefixEnd_4259568 729068588170231884770203 := by
  unfold tailWord_4259568
  simp only [CollatzResearch.WordTrace]
  refine ⟨77679604116160043571081679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103572805488213391428108905 77679604116160043571081679)
  ·
    refine ⟨116519406174240065356622519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77679604116160043571081679 116519406174240065356622519)
    ·
      refine ⟨174779109261360098034933779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116519406174240065356622519 174779109261360098034933779)
      ·
        refine ⟨262168663892040147052400669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174779109261360098034933779 262168663892040147052400669)
        ·
          refine ⟨98313248959515055144650251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262168663892040147052400669 98313248959515055144650251)
          ·
            refine ⟨147469873439272582716975377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98313248959515055144650251 147469873439272582716975377)
            ·
              refine ⟨110602405079454437037731533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147469873439272582716975377 110602405079454437037731533)
              ·
                refine ⟨41475901904795413889149325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110602405079454437037731533 41475901904795413889149325)
                ·
                  refine ⟨15553463214298280208430997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41475901904795413889149325 15553463214298280208430997)
                  ·
                    refine ⟨729068588170231884770203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15553463214298280208430997 729068588170231884770203)
                    ·
                      rfl

theorem cell23_4259568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_4259568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259568 prefixEnd_4259568 := by exact prefixLift 4259568
  have htrace : WordTrace (prefixWord ++ tailWord_4259568) baseStart_4259568 baseEnd_4259568 := by
    simpa [prefixWord, tailWord_4259568, baseEnd_4259568] using wordTrace_append hprefix tailTrace_4259568
  have hstable : (prefixWord ++ tailWord_4259568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259568).length < 2 ^ (prefixWord ++ tailWord_4259568).sum := by decide
  have hdescent : baseEnd_4259568 < baseStart_4259568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259569 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 1, 1, 3]
def baseStart_4259569 : Nat := 118140960795 + 4259569 * 2 ^ 59
def prefixEnd_4259569 : Nat := 4983230072969 + 3 ^ 40 * 4259569 * 2
def baseEnd_4259569 : Nat := 2187206277991350150398105

theorem tailTrace_4259569 : CollatzResearch.WordTrace tailWord_4259569 prefixEnd_4259569 2187206277991350150398105 := by
  unfold tailWord_4259569
  simp only [CollatzResearch.WordTrace]
  refine ⟨155359244705316464312949761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103572829803544309541966507 155359244705316464312949761)
  ·
    refine ⟨116519433528987348234712321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155359244705316464312949761 116519433528987348234712321)
    ·
      refine ⟨87389575146740511176034241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116519433528987348234712321 87389575146740511176034241)
      ·
        refine ⟨65542181360055383382025681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87389575146740511176034241 65542181360055383382025681)
        ·
          refine ⟨49156636020041537536519261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65542181360055383382025681 49156636020041537536519261)
          ·
            refine ⟨18433738507515576576194723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49156636020041537536519261 18433738507515576576194723)
            ·
              refine ⟨27650607761273364864292085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18433738507515576576194723 27650607761273364864292085)
              ·
                refine ⟨2592244477619377956027383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27650607761273364864292085 2592244477619377956027383)
                ·
                  refine ⟨3888366716429066934041075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592244477619377956027383 3888366716429066934041075)
                  ·
                    refine ⟨5832550074643600401061613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3888366716429066934041075 5832550074643600401061613)
                    ·
                      refine ⟨2187206277991350150398105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832550074643600401061613 2187206277991350150398105)
                      ·
                        rfl

theorem cell23_4259569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_4259569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259569 prefixEnd_4259569 := by exact prefixLift 4259569
  have htrace : WordTrace (prefixWord ++ tailWord_4259569) baseStart_4259569 baseEnd_4259569 := by
    simpa [prefixWord, tailWord_4259569, baseEnd_4259569] using wordTrace_append hprefix tailTrace_4259569
  have hstable : (prefixWord ++ tailWord_4259569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259569).length < 2 ^ (prefixWord ++ tailWord_4259569).sum := by decide
  have hdescent : baseEnd_4259569 < baseStart_4259569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259586 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4259586 : Nat := 118140960795 + 4259586 * 2 ^ 59
def prefixEnd_4259586 : Nat := 4983230072969 + 3 ^ 40 * 4259586 * 2
def baseEnd_4259586 : Nat := 2187215007162476583885527

theorem tailTrace_4259586 : CollatzResearch.WordTrace tailWord_4259586 prefixEnd_4259586 2187215007162476583885527 := by
  unfold tailWord_4259586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38839966186563719054079653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103573243164169917477545741 38839966186563719054079653)
  ·
    refine ⟨7282493659980697322639935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38839966186563719054079653 7282493659980697322639935)
    ·
      refine ⟨10923740489971045983959903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7282493659980697322639935 10923740489971045983959903)
      ·
        refine ⟨16385610734956568975939855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10923740489971045983959903 16385610734956568975939855)
        ·
          refine ⟨24578416102434853463909783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16385610734956568975939855 24578416102434853463909783)
          ·
            refine ⟨36867624153652280195864675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24578416102434853463909783 36867624153652280195864675)
            ·
              refine ⟨55301436230478420293797013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36867624153652280195864675 55301436230478420293797013)
              ·
                refine ⟨2592254823303675951271735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55301436230478420293797013 2592254823303675951271735)
                ·
                  refine ⟨3888382234955513926907603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592254823303675951271735 3888382234955513926907603)
                  ·
                    refine ⟨5832573352433270890361405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3888382234955513926907603 5832573352433270890361405)
                    ·
                      refine ⟨2187215007162476583885527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832573352433270890361405 2187215007162476583885527)
                      ·
                        rfl

theorem cell23_4259586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4259586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259586 prefixEnd_4259586 := by exact prefixLift 4259586
  have htrace : WordTrace (prefixWord ++ tailWord_4259586) baseStart_4259586 baseEnd_4259586 := by
    simpa [prefixWord, tailWord_4259586, baseEnd_4259586] using wordTrace_append hprefix tailTrace_4259586
  have hstable : (prefixWord ++ tailWord_4259586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259586).length < 2 ^ (prefixWord ++ tailWord_4259586).sum := by decide
  have hdescent : baseEnd_4259586 < baseStart_4259586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259595 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3]
def baseStart_4259595 : Nat := 118140960795 + 4259595 * 2 ^ 59
def prefixEnd_4259595 : Nat := 4983230072969 + 3 ^ 40 * 4259595 * 2
def baseEnd_4259595 : Nat := 2187219628488367048672985

theorem tailTrace_4259595 : CollatzResearch.WordTrace tailWord_4259595 prefixEnd_4259595 2187219628488367048672985 := by
  unfold tailWord_4259595
  simp only [CollatzResearch.WordTrace]
  refine ⟨155360193003222270753396239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103573462002148180502264159 155360193003222270753396239)
  ·
    refine ⟨233040289504833406130094359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155360193003222270753396239 233040289504833406130094359)
    ·
      refine ⟨349560434257250109195141539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233040289504833406130094359 349560434257250109195141539)
      ·
        refine ⟨524340651385875163792712309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349560434257250109195141539 524340651385875163792712309)
        ·
          refine ⟨49156936067425796605566779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 524340651385875163792712309 49156936067425796605566779)
          ·
            refine ⟨73735404101138694908350169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49156936067425796605566779 73735404101138694908350169)
            ·
              refine ⟨55301553075854021181262627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73735404101138694908350169 55301553075854021181262627)
              ·
                refine ⟨82952329613781031771893941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55301553075854021181262627 82952329613781031771893941)
                ·
                  refine ⟨7776780901291971728615057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82952329613781031771893941 7776780901291971728615057)
                  ·
                    refine ⟨5832585675968978796461293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7776780901291971728615057 5832585675968978796461293)
                    ·
                      refine ⟨2187219628488367048672985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832585675968978796461293 2187219628488367048672985)
                      ·
                        rfl

theorem cell23_4259595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3].length) (baseStart_4259595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259595 prefixEnd_4259595 := by exact prefixLift 4259595
  have htrace : WordTrace (prefixWord ++ tailWord_4259595) baseStart_4259595 baseEnd_4259595 := by
    simpa [prefixWord, tailWord_4259595, baseEnd_4259595] using wordTrace_append hprefix tailTrace_4259595
  have hstable : (prefixWord ++ tailWord_4259595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259595).length < 2 ^ (prefixWord ++ tailWord_4259595).sum := by decide
  have hdescent : baseEnd_4259595 < baseStart_4259595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259605 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4259605 : Nat := 118140960795 + 4259605 * 2 ^ 59
def prefixEnd_4259605 : Nat := 4983230072969 + 3 ^ 40 * 4259605 * 2
def baseEnd_4259605 : Nat := 2187224763294912009547939

theorem tailTrace_4259605 : CollatzResearch.WordTrace tailWord_4259605 prefixEnd_4259605 2187224763294912009547939 := by
  unfold tailWord_4259605
  simp only [CollatzResearch.WordTrace]
  refine ⟨155360557733186042461260269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103573705155457361640840179 155360557733186042461260269)
  ·
    refine ⟨58260209149944765922972601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155360557733186042461260269 58260209149944765922972601)
    ·
      refine ⟨43695156862458574442229451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58260209149944765922972601 43695156862458574442229451)
      ·
        refine ⟨65542735293687861663344177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43695156862458574442229451 65542735293687861663344177)
        ·
          refine ⟨49157051470265896247508133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65542735293687861663344177 49157051470265896247508133)
          ·
            refine ⟨9216947150674855546407775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49157051470265896247508133 9216947150674855546407775)
            ·
              refine ⟨13825420726012283319611663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9216947150674855546407775 13825420726012283319611663)
              ·
                refine ⟨20738131089018424979417495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13825420726012283319611663 20738131089018424979417495)
                ·
                  refine ⟨31107196633527637469126243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20738131089018424979417495 31107196633527637469126243)
                  ·
                    refine ⟨46660794950291456203689365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31107196633527637469126243 46660794950291456203689365)
                    ·
                      refine ⟨2187224763294912009547939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46660794950291456203689365 2187224763294912009547939)
                      ·
                        rfl

theorem cell23_4259605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4259605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259605 prefixEnd_4259605 := by exact prefixLift 4259605
  have htrace : WordTrace (prefixWord ++ tailWord_4259605) baseStart_4259605 baseEnd_4259605 := by
    simpa [prefixWord, tailWord_4259605, baseEnd_4259605] using wordTrace_append hprefix tailTrace_4259605
  have hstable : (prefixWord ++ tailWord_4259605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259605).length < 2 ^ (prefixWord ++ tailWord_4259605).sum := by decide
  have hdescent : baseEnd_4259605 < baseStart_4259605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259669 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4259669 : Nat := 118140960795 + 4259669 * 2 ^ 59
def prefixEnd_4259669 : Nat := 4983230072969 + 3 ^ 40 * 4259669 * 2
def baseEnd_4259669 : Nat := 2187257626056799759147645

theorem tailTrace_4259669 : CollatzResearch.WordTrace tailWord_4259669 prefixEnd_4259669 2187257626056799759147645 := by
  unfold tailWord_4259669
  simp only [CollatzResearch.WordTrace]
  refine ⟨155362892004954181391590061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103575261336636120927726707 155362892004954181391590061)
  ·
    refine ⟨58261084501857818021846273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155362892004954181391590061 58261084501857818021846273)
    ·
      refine ⟨43695813376393363516384705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58261084501857818021846273 43695813376393363516384705)
      ·
        refine ⟨32771860032295022637288529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43695813376393363516384705 32771860032295022637288529)
        ·
          refine ⟨24578895024221266977966397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32771860032295022637288529 24578895024221266977966397)
          ·
            refine ⟨9217085634082975116737399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24578895024221266977966397 9217085634082975116737399)
            ·
              refine ⟨13825628451124462675106099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9217085634082975116737399 13825628451124462675106099)
              ·
                refine ⟨20738442676686694012659149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13825628451124462675106099 20738442676686694012659149)
                ·
                  refine ⟨7776916003757510254747181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20738442676686694012659149 7776916003757510254747181)
                  ·
                    refine ⟨2916343501409066345530193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7776916003757510254747181 2916343501409066345530193)
                    ·
                      refine ⟨2187257626056799759147645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916343501409066345530193 2187257626056799759147645)
                      ·
                        rfl

theorem cell23_4259669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4259669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259669 prefixEnd_4259669 := by exact prefixLift 4259669
  have htrace : WordTrace (prefixWord ++ tailWord_4259669) baseStart_4259669 baseEnd_4259669 := by
    simpa [prefixWord, tailWord_4259669, baseEnd_4259669] using wordTrace_append hprefix tailTrace_4259669
  have hstable : (prefixWord ++ tailWord_4259669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259669).length < 2 ^ (prefixWord ++ tailWord_4259669).sum := by decide
  have hdescent : baseEnd_4259669 < baseStart_4259669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259705 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 7]
def baseStart_4259705 : Nat := 118140960795 + 4259705 * 2 ^ 59
def prefixEnd_4259705 : Nat := 4983230072969 + 3 ^ 40 * 4259705 * 2
def baseEnd_4259705 : Nat := 243030679040040179810831

theorem tailTrace_4259705 : CollatzResearch.WordTrace tailWord_4259705 prefixEnd_4259705 243030679040040179810831 := by
  unfold tailWord_4259705
  simp only [CollatzResearch.WordTrace]
  refine ⟨155364205032823759539900569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103576136688549173026600379 155364205032823759539900569)
  ·
    refine ⟨116523153774617819654925427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155364205032823759539900569 116523153774617819654925427)
    ·
      refine ⟨174784730661926729482388141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116523153774617819654925427 174784730661926729482388141)
      ·
        refine ⟨65544273998222523555895553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174784730661926729482388141 65544273998222523555895553)
        ·
          refine ⟨49158205498666892666921665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65544273998222523555895553 49158205498666892666921665)
          ·
            refine ⟨36868654124000169500191249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49158205498666892666921665 36868654124000169500191249)
            ·
              refine ⟨27651490593000127125143437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36868654124000169500191249 27651490593000127125143437)
              ·
                refine ⟨10369308972375047671928789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27651490593000127125143437 10369308972375047671928789)
                ·
                  refine ⟨243030679040040179810831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10369308972375047671928789 243030679040040179810831)
                  ·
                    rfl

theorem cell23_4259705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_4259705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259705 prefixEnd_4259705 := by exact prefixLift 4259705
  have htrace : WordTrace (prefixWord ++ tailWord_4259705) baseStart_4259705 baseEnd_4259705 := by
    simpa [prefixWord, tailWord_4259705, baseEnd_4259705] using wordTrace_append hprefix tailTrace_4259705
  have hstable : (prefixWord ++ tailWord_4259705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259705).length < 2 ^ (prefixWord ++ tailWord_4259705).sum := by decide
  have hdescent : baseEnd_4259705 < baseStart_4259705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259716 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_4259716 : Nat := 118140960795 + 4259716 * 2 ^ 59
def prefixEnd_4259716 : Nat := 4983230072969 + 3 ^ 40 * 4259716 * 2
def baseEnd_4259716 : Nat := 2187281759647561075259929

theorem tailTrace_4259716 : CollatzResearch.WordTrace tailWord_4259716 prefixEnd_4259716 2187281759647561075259929 := by
  unfold tailWord_4259716
  simp only [CollatzResearch.WordTrace]
  refine ⟨77682303117891954209275501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103576404157189272279034001 77682303117891954209275501)
  ·
    refine ⟨29130863669209482828478313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77682303117891954209275501 29130863669209482828478313)
    ·
      refine ⟨21848147751907112121358735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29130863669209482828478313 21848147751907112121358735)
      ·
        refine ⟨32772221627860668182038103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21848147751907112121358735 32772221627860668182038103)
        ·
          refine ⟨49158332441791002273057155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32772221627860668182038103 49158332441791002273057155)
          ·
            refine ⟨73737498662686503409585733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49158332441791002273057155 73737498662686503409585733)
            ·
              refine ⟨13825780999253719389297325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73737498662686503409585733 13825780999253719389297325)
              ·
                refine ⟨5184667874720144770986497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13825780999253719389297325 5184667874720144770986497)
                ·
                  refine ⟨3888500906040108578239873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5184667874720144770986497 3888500906040108578239873)
                  ·
                    refine ⟨2916375679530081433679905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3888500906040108578239873 2916375679530081433679905)
                    ·
                      refine ⟨2187281759647561075259929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916375679530081433679905 2187281759647561075259929)
                      ·
                        rfl

theorem cell23_4259716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_4259716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259716 prefixEnd_4259716 := by exact prefixLift 4259716
  have htrace : WordTrace (prefixWord ++ tailWord_4259716) baseStart_4259716 baseEnd_4259716 := by
    simpa [prefixWord, tailWord_4259716, baseEnd_4259716] using wordTrace_append hprefix tailTrace_4259716
  have hstable : (prefixWord ++ tailWord_4259716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259716).length < 2 ^ (prefixWord ++ tailWord_4259716).sum := by decide
  have hdescent : baseEnd_4259716 < baseStart_4259716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_4259755 : Nat := 118140960795 + 4259755 * 2 ^ 59
def prefixEnd_4259755 : Nat := 4983230072969 + 3 ^ 40 * 4259755 * 2
def baseEnd_4259755 : Nat := 2187301785393086422672249

theorem tailTrace_4259755 : CollatzResearch.WordTrace tailWord_4259755 prefixEnd_4259755 2187301785393086422672249 := by
  unfold tailWord_4259755
  simp only [CollatzResearch.WordTrace]
  refine ⟨155366028682642618079220719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103577352455095078719480479 155366028682642618079220719)
  ·
    refine ⟨233049043023963927118831079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155366028682642618079220719 233049043023963927118831079)
    ·
      refine ⟨349573564535945890678246619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233049043023963927118831079 349573564535945890678246619)
      ·
        refine ⟨524360346803918836017369929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349573564535945890678246619 524360346803918836017369929)
        ·
          refine ⟨393270260102939127013027447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524360346803918836017369929 393270260102939127013027447)
          ·
            refine ⟨589905390154408690519541171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393270260102939127013027447 589905390154408690519541171)
            ·
              refine ⟨884858085231613035779311757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589905390154408690519541171 884858085231613035779311757)
              ·
                refine ⟨331821781961854888417241909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884858085231613035779311757 331821781961854888417241909)
                ·
                  refine ⟨31108292058923895789116429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331821781961854888417241909 31108292058923895789116429)
                  ·
                    refine ⟨11665609522096460920918661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31108292058923895789116429 11665609522096460920918661)
                    ·
                      refine ⟨2187301785393086422672249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11665609522096460920918661 2187301785393086422672249)
                      ·
                        rfl

theorem cell23_4259755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_4259755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259755 prefixEnd_4259755 := by exact prefixLift 4259755
  have htrace : WordTrace (prefixWord ++ tailWord_4259755) baseStart_4259755 baseEnd_4259755 := by
    simpa [prefixWord, tailWord_4259755, baseEnd_4259755] using wordTrace_append hprefix tailTrace_4259755
  have hstable : (prefixWord ++ tailWord_4259755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259755).length < 2 ^ (prefixWord ++ tailWord_4259755).sum := by decide
  have hdescent : baseEnd_4259755 < baseStart_4259755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259785 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_4259785 : Nat := 118140960795 + 4259785 * 2 ^ 59
def prefixEnd_4259785 : Nat := 4983230072969 + 3 ^ 40 * 4259785 * 2
def baseEnd_4259785 : Nat := 2187317189812721305297111

theorem tailTrace_4259785 : CollatzResearch.WordTrace tailWord_4259785 prefixEnd_4259785 2187317189812721305297111 := by
  unfold tailWord_4259785
  simp only [CollatzResearch.WordTrace]
  refine ⟨155367122872533933202812809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103578081915022622135208539 155367122872533933202812809)
  ·
    refine ⟨116525342154400449902109607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155367122872533933202812809 116525342154400449902109607)
    ·
      refine ⟨174788013231600674853164411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116525342154400449902109607 174788013231600674853164411)
      ·
        refine ⟨262182019847401012279746617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174788013231600674853164411 262182019847401012279746617)
        ·
          refine ⟨196636514885550759209809963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262182019847401012279746617 196636514885550759209809963)
          ·
            refine ⟨294954772328326138814714945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196636514885550759209809963 294954772328326138814714945)
            ·
              refine ⟨221216079246244604111036209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294954772328326138814714945 221216079246244604111036209)
              ·
                refine ⟨165912059434683453083277157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221216079246244604111036209 165912059434683453083277157)
                ·
                  refine ⟨31108511144003147453114467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165912059434683453083277157 31108511144003147453114467)
                  ·
                    refine ⟨46662766716004721179671701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31108511144003147453114467 46662766716004721179671701)
                    ·
                      refine ⟨2187317189812721305297111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46662766716004721179671701 2187317189812721305297111)
                      ·
                        rfl

theorem cell23_4259785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_4259785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259785 prefixEnd_4259785 := by exact prefixLift 4259785
  have htrace : WordTrace (prefixWord ++ tailWord_4259785) baseStart_4259785 baseEnd_4259785 := by
    simpa [prefixWord, tailWord_4259785, baseEnd_4259785] using wordTrace_append hprefix tailTrace_4259785
  have hstable : (prefixWord ++ tailWord_4259785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259785).length < 2 ^ (prefixWord ++ tailWord_4259785).sum := by decide
  have hdescent : baseEnd_4259785 < baseStart_4259785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259792 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_4259792 : Nat := 118140960795 + 4259792 * 2 ^ 59
def prefixEnd_4259792 : Nat := 4983230072969 + 3 ^ 40 * 4259792 * 2
def baseEnd_4259792 : Nat := 2187320784177302777909579

theorem tailTrace_4259792 : CollatzResearch.WordTrace tailWord_4259792 prefixEnd_4259792 2187320784177302777909579 := by
  unfold tailWord_4259792
  simp only [CollatzResearch.WordTrace]
  refine ⟨77683689091754286699158815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103578252122339048932211753 77683689091754286699158815)
  ·
    refine ⟨116525533637631430048738223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77683689091754286699158815 116525533637631430048738223)
    ·
      refine ⟨174788300456447145073107335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116525533637631430048738223 174788300456447145073107335)
      ·
        refine ⟨262182450684670717609661003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174788300456447145073107335 262182450684670717609661003)
        ·
          refine ⟨393273676027006076414491505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262182450684670717609661003 393273676027006076414491505)
          ·
            refine ⟨294955257020254557310868629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393273676027006076414491505 294955257020254557310868629)
            ·
              refine ⟨13826027672824432373946967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 294955257020254557310868629 13826027672824432373946967)
              ·
                refine ⟨20739041509236648560920451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13826027672824432373946967 20739041509236648560920451)
                ·
                  refine ⟨31108562263854972841380677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20739041509236648560920451 31108562263854972841380677)
                  ·
                    refine ⟨5832855424472807407758877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31108562263854972841380677 5832855424472807407758877)
                    ·
                      refine ⟨2187320784177302777909579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832855424472807407758877 2187320784177302777909579)
                      ·
                        rfl

theorem cell23_4259792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_4259792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259792 prefixEnd_4259792 := by exact prefixLift 4259792
  have htrace : WordTrace (prefixWord ++ tailWord_4259792) baseStart_4259792 baseEnd_4259792 := by
    simpa [prefixWord, tailWord_4259792, baseEnd_4259792] using wordTrace_append hprefix tailTrace_4259792
  have hstable : (prefixWord ++ tailWord_4259792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259792).length < 2 ^ (prefixWord ++ tailWord_4259792).sum := by decide
  have hdescent : baseEnd_4259792 < baseStart_4259792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259812 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 6]
def baseStart_4259812 : Nat := 118140960795 + 4259812 * 2 ^ 59
def prefixEnd_4259812 : Nat := 4983230072969 + 3 ^ 40 * 4259812 * 2
def baseEnd_4259812 : Nat := 243036783754488077739943

theorem tailTrace_4259812 : CollatzResearch.WordTrace tailWord_4259812 prefixEnd_4259812 243036783754488077739943 := by
  unfold tailWord_4259812
  simp only [CollatzResearch.WordTrace]
  refine ⟨77684053821718058407022845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103578738428957411209363793 77684053821718058407022845)
  ·
    refine ⟨29131520183144271902633567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77684053821718058407022845 29131520183144271902633567)
    ·
      refine ⟨43697280274716407853950351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29131520183144271902633567 43697280274716407853950351)
      ·
        refine ⟨65545920412074611780925527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43697280274716407853950351 65545920412074611780925527)
        ·
          refine ⟨98318880618111917671388291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65545920412074611780925527 98318880618111917671388291)
          ·
            refine ⟨147478320927167876507082437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98318880618111917671388291 147478320927167876507082437)
            ·
              refine ⟨27652185173843976845077957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147478320927167876507082437 27652185173843976845077957)
              ·
                refine ⟨5184784720095745658452117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27652185173843976845077957 5184784720095745658452117)
                ·
                  refine ⟨243036783754488077739943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5184784720095745658452117 243036783754488077739943)
                  ·
                    rfl

theorem cell23_4259812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_4259812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259812 prefixEnd_4259812 := by exact prefixLift 4259812
  have htrace : WordTrace (prefixWord ++ tailWord_4259812) baseStart_4259812 baseEnd_4259812 := by
    simpa [prefixWord, tailWord_4259812, baseEnd_4259812] using wordTrace_append hprefix tailTrace_4259812
  have hstable : (prefixWord ++ tailWord_4259812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259812).length < 2 ^ (prefixWord ++ tailWord_4259812).sum := by decide
  have hdescent : baseEnd_4259812 < baseStart_4259812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259839 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 3]
def baseStart_4259839 : Nat := 118140960795 + 4259839 * 2 ^ 59
def prefixEnd_4259839 : Nat := 4983230072969 + 3 ^ 40 * 4259839 * 2
def baseEnd_4259839 : Nat := 2187344917768064094021863

theorem tailTrace_4259839 : CollatzResearch.WordTrace tailWord_4259839 prefixEnd_4259839 2187344917768064094021863 := by
  unfold tailWord_4259839
  simp only [CollatzResearch.WordTrace]
  refine ⟨155369092414338300425278571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103579394942892200283519047 155369092414338300425278571)
  ·
    refine ⟨233053638621507450637917857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155369092414338300425278571 233053638621507450637917857)
    ·
      refine ⟨174790228966130587978438393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233053638621507450637917857 174790228966130587978438393)
      ·
        refine ⟨131092671724597940983828795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174790228966130587978438393 131092671724597940983828795)
        ·
          refine ⟨196639007586896911475743193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131092671724597940983828795 196639007586896911475743193)
          ·
            refine ⟨147479255690172683606807395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196639007586896911475743193 147479255690172683606807395)
            ·
              refine ⟨221218883535259025410211093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147479255690172683606807395 221218883535259025410211093)
              ·
                refine ⟨10369635165715266816103645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221218883535259025410211093 10369635165715266816103645)
                ·
                  refine ⟨3888613187143225056038867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10369635165715266816103645 3888613187143225056038867)
                  ·
                    refine ⟨5832919780714837584058301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3888613187143225056038867 5832919780714837584058301)
                    ·
                      refine ⟨2187344917768064094021863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5832919780714837584058301 2187344917768064094021863)
                      ·
                        rfl

theorem cell23_4259839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_4259839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259839 prefixEnd_4259839 := by exact prefixLift 4259839
  have htrace : WordTrace (prefixWord ++ tailWord_4259839) baseStart_4259839 baseEnd_4259839 := by
    simpa [prefixWord, tailWord_4259839, baseEnd_4259839] using wordTrace_append hprefix tailTrace_4259839
  have hstable : (prefixWord ++ tailWord_4259839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259839).length < 2 ^ (prefixWord ++ tailWord_4259839).sum := by decide
  have hdescent : baseEnd_4259839 < baseStart_4259839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259866 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_4259866 : Nat := 118140960795 + 4259866 * 2 ^ 59
def prefixEnd_4259866 : Nat := 4983230072969 + 3 ^ 40 * 4259866 * 2
def baseEnd_4259866 : Nat := 2187358781745735488384239

theorem tailTrace_4259866 : CollatzResearch.WordTrace tailWord_4259866 prefixEnd_4259866 2187358781745735488384239 := by
  unfold tailWord_4259866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38842519296310121009127863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103580051456826989357674301 38842519296310121009127863)
  ·
    refine ⟨58263778944465181513691795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38842519296310121009127863 58263778944465181513691795)
    ·
      refine ⟨87395668416697772270537693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58263778944465181513691795 87395668416697772270537693)
      ·
        refine ⟨32773375656261664601451635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87395668416697772270537693 32773375656261664601451635)
        ·
          refine ⟨49160063484392496902177453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32773375656261664601451635 49160063484392496902177453)
          ·
            refine ⟨18435023806647186338316545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49160063484392496902177453 18435023806647186338316545)
            ·
              refine ⟨13826267854985389753737409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18435023806647186338316545 13826267854985389753737409)
              ·
                refine ⟨10369700891239042315303057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13826267854985389753737409 10369700891239042315303057)
                ·
                  refine ⟨7777275668429281736477293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10369700891239042315303057 7777275668429281736477293)
                  ·
                    refine ⟨2916478375660980651178985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7777275668429281736477293 2916478375660980651178985)
                    ·
                      refine ⟨2187358781745735488384239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916478375660980651178985 2187358781745735488384239)
                      ·
                        rfl

theorem cell23_4259866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_4259866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259866 prefixEnd_4259866 := by exact prefixLift 4259866
  have htrace : WordTrace (prefixWord ++ tailWord_4259866) baseStart_4259866 baseEnd_4259866 := by
    simpa [prefixWord, tailWord_4259866, baseEnd_4259866] using wordTrace_append hprefix tailTrace_4259866
  have hstable : (prefixWord ++ tailWord_4259866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259866).length < 2 ^ (prefixWord ++ tailWord_4259866).sum := by decide
  have hdescent : baseEnd_4259866 < baseStart_4259866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259889 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_4259889 : Nat := 118140960795 + 4259889 * 2 ^ 59
def prefixEnd_4259889 : Nat := 4983230072969 + 3 ^ 40 * 4259889 * 2
def baseEnd_4259889 : Nat := 729123530600262966132211

theorem tailTrace_4259889 : CollatzResearch.WordTrace tailWord_4259889 prefixEnd_4259889 729123530600262966132211 := by
  unfold tailWord_4259889
  simp only [CollatzResearch.WordTrace]
  refine ⟨155370916064157158964598721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103580610709438105976399147 155370916064157158964598721)
  ·
    refine ⟨116528187048117869223449041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155370916064157158964598721 116528187048117869223449041)
    ·
      refine ⟨87396140286088401917586781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116528187048117869223449041 87396140286088401917586781)
      ·
        refine ⟨32773552607283150719095043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87396140286088401917586781 32773552607283150719095043)
        ·
          refine ⟨49160328910924726078642565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32773552607283150719095043 49160328910924726078642565)
          ·
            refine ⟨9217561670798386139745481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49160328910924726078642565 9217561670798386139745481)
            ·
              refine ⟨6913171253098789604809111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9217561670798386139745481 6913171253098789604809111)
              ·
                refine ⟨10369756879648184407213667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6913171253098789604809111 10369756879648184407213667)
                ·
                  refine ⟨15554635319472276610820501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10369756879648184407213667 15554635319472276610820501)
                  ·
                    refine ⟨729123530600262966132211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15554635319472276610820501 729123530600262966132211)
                    ·
                      rfl

theorem cell23_4259889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_4259889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259889 prefixEnd_4259889 := by exact prefixLift 4259889
  have htrace : WordTrace (prefixWord ++ tailWord_4259889) baseStart_4259889 baseEnd_4259889 := by
    simpa [prefixWord, tailWord_4259889, baseEnd_4259889] using wordTrace_append hprefix tailTrace_4259889
  have hstable : (prefixWord ++ tailWord_4259889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259889).length < 2 ^ (prefixWord ++ tailWord_4259889).sum := by decide
  have hdescent : baseEnd_4259889 < baseStart_4259889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259973 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_4259973 : Nat := 118140960795 + 4259973 * 2 ^ 59
def prefixEnd_4259973 : Nat := 4983230072969 + 3 ^ 40 * 4259973 * 2
def baseEnd_4259973 : Nat := 2187413724175766569746247

theorem tailTrace_4259973 : CollatzResearch.WordTrace tailWord_4259973 prefixEnd_4259973 2187413724175766569746247 := by
  unfold tailWord_4259973
  simp only [CollatzResearch.WordTrace]
  refine ⟨155373979795852841310656573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103582653197235227540437715 155373979795852841310656573)
  ·
    refine ⟨58265242423444815491496215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155373979795852841310656573 58265242423444815491496215)
    ·
      refine ⟨87397863635167223237244323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58265242423444815491496215 87397863635167223237244323)
      ·
        refine ⟨131096795452750834855866485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87397863635167223237244323 131096795452750834855866485)
        ·
          refine ⟨12290324573695390767737483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131096795452750834855866485 12290324573695390767737483)
          ·
            refine ⟨18435486860543086151606225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12290324573695390767737483 18435486860543086151606225)
            ·
              refine ⟨13826615145407314613704669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18435486860543086151606225 13826615145407314613704669)
              ·
                refine ⟨5184980679527742980139251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13826615145407314613704669 5184980679527742980139251)
                ·
                  refine ⟨7777471019291614470208877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5184980679527742980139251 7777471019291614470208877)
                  ·
                    refine ⟨2916551632234355426328329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7777471019291614470208877 2916551632234355426328329)
                    ·
                      refine ⟨2187413724175766569746247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916551632234355426328329 2187413724175766569746247)
                      ·
                        rfl

theorem cell23_4259973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_4259973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259973 prefixEnd_4259973 := by exact prefixLift 4259973
  have htrace : WordTrace (prefixWord ++ tailWord_4259973) baseStart_4259973 baseEnd_4259973 := by
    simpa [prefixWord, tailWord_4259973, baseEnd_4259973] using wordTrace_append hprefix tailTrace_4259973
  have hstable : (prefixWord ++ tailWord_4259973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259973).length < 2 ^ (prefixWord ++ tailWord_4259973).sum := by decide
  have hdescent : baseEnd_4259973 < baseStart_4259973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4259989 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_4259989 : Nat := 118140960795 + 4259989 * 2 ^ 59
def prefixEnd_4259989 : Nat := 4983230072969 + 3 ^ 40 * 4259989 * 2
def baseEnd_4259989 : Nat := 2187421939866238507146173

theorem tailTrace_4259989 : CollatzResearch.WordTrace tailWord_4259989 prefixEnd_4259989 2187421939866238507146173 := by
  unfold tailWord_4259989
  simp only [CollatzResearch.WordTrace]
  refine ⟨155374563363794876043239021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103583042242529917362159347 155374563363794876043239021)
  ·
    refine ⟨58265461261423078516214633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155374563363794876043239021 58265461261423078516214633)
    ·
      refine ⟨43699095946067308887160975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58265461261423078516214633 43699095946067308887160975)
      ·
        refine ⟨65548643919100963330741463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43699095946067308887160975 65548643919100963330741463)
        ·
          refine ⟨98322965878651444996112195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65548643919100963330741463 98322965878651444996112195)
          ·
            refine ⟨147484448817977167494168293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98322965878651444996112195 147484448817977167494168293)
            ·
              refine ⟨27653334153370718905156555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147484448817977167494168293 27653334153370718905156555)
              ·
                refine ⟨41480001230056078357734833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27653334153370718905156555 41480001230056078357734833)
                ·
                  refine ⟨31110000922542058768301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41480001230056078357734833 31110000922542058768301125)
                  ·
                    refine ⟨5833125172976636019056461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31110000922542058768301125 5833125172976636019056461)
                    ·
                      refine ⟨2187421939866238507146173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833125172976636019056461 2187421939866238507146173)
                      ·
                        rfl

theorem cell23_4259989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_4259989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4259989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4259989 prefixEnd_4259989 := by exact prefixLift 4259989
  have htrace : WordTrace (prefixWord ++ tailWord_4259989) baseStart_4259989 baseEnd_4259989 := by
    simpa [prefixWord, tailWord_4259989, baseEnd_4259989] using wordTrace_append hprefix tailTrace_4259989
  have hstable : (prefixWord ++ tailWord_4259989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4259989).length < 2 ^ (prefixWord ++ tailWord_4259989).sum := by decide
  have hdescent : baseEnd_4259989 < baseStart_4259989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4259989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260007 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_4260007 : Nat := 118140960795 + 4260007 * 2 ^ 59
def prefixEnd_4260007 : Nat := 4983230072969 + 3 ^ 40 * 4260007 * 2
def baseEnd_4260007 : Nat := 2187431182518019436721091

theorem tailTrace_4260007 : CollatzResearch.WordTrace tailWord_4260007 prefixEnd_4260007 2187431182518019436721091 := by
  unfold tailWord_4260007
  simp only [CollatzResearch.WordTrace]
  refine ⟨155375219877729665117394275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103583479918486443411596183 155375219877729665117394275)
  ·
    refine ⟨233062829816594497676091413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155375219877729665117394275 233062829816594497676091413)
    ·
      refine ⟨10924820147652867078566785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 233062829816594497676091413 10924820147652867078566785)
      ·
        refine ⟨8193615110739650308925089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10924820147652867078566785 8193615110739650308925089)
        ·
          refine ⟨6145211333054737731693817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8193615110739650308925089 6145211333054737731693817)
          ·
            refine ⟨4608908499791053298770363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6145211333054737731693817 4608908499791053298770363)
            ·
              refine ⟨6913362749686579948155545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4608908499791053298770363 6913362749686579948155545)
              ·
                refine ⟨5185022062264934961116659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6913362749686579948155545 5185022062264934961116659)
                ·
                  refine ⟨7777533093397402441674989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185022062264934961116659 7777533093397402441674989)
                  ·
                    refine ⟨2916574910024025915628121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7777533093397402441674989 2916574910024025915628121)
                    ·
                      refine ⟨2187431182518019436721091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916574910024025915628121 2187431182518019436721091)
                      ·
                        rfl

theorem cell23_4260007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_4260007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260007 prefixEnd_4260007 := by exact prefixLift 4260007
  have htrace : WordTrace (prefixWord ++ tailWord_4260007) baseStart_4260007 baseEnd_4260007 := by
    simpa [prefixWord, tailWord_4260007, baseEnd_4260007] using wordTrace_append hprefix tailTrace_4260007
  have hstable : (prefixWord ++ tailWord_4260007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260007).length < 2 ^ (prefixWord ++ tailWord_4260007).sum := by decide
  have hdescent : baseEnd_4260007 < baseStart_4260007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260019 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3]
def baseStart_4260019 : Nat := 118140960795 + 4260019 * 2 ^ 59
def prefixEnd_4260019 : Nat := 4983230072969 + 3 ^ 40 * 4260019 * 2
def baseEnd_4260019 : Nat := 2187437344285873389771035

theorem tailTrace_4260019 : CollatzResearch.WordTrace tailWord_4260019 prefixEnd_4260019 2187437344285873389771035 := by
  unfold tailWord_4260019
  simp only [CollatzResearch.WordTrace]
  refine ⟨155375657553686191166831111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103583771702457460777887407 155375657553686191166831111)
  ·
    refine ⟨233063486330529286750246667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155375657553686191166831111 233063486330529286750246667)
    ·
      refine ⟨349595229495793930125370001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233063486330529286750246667 349595229495793930125370001)
      ·
        refine ⟨262196422121845447594027501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349595229495793930125370001 262196422121845447594027501)
        ·
          refine ⟨98323658295692042847760313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262196422121845447594027501 98323658295692042847760313)
          ·
            refine ⟨73742743721769032135820235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98323658295692042847760313 73742743721769032135820235)
            ·
              refine ⟨110614115582653548203730353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73742743721769032135820235 110614115582653548203730353)
              ·
                refine ⟨82960586686990161152797765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110614115582653548203730353 82960586686990161152797765)
                ·
                  refine ⟨15555110003810655216149581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82960586686990161152797765 15555110003810655216149581)
                  ·
                    refine ⟨5833166251428995706056093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15555110003810655216149581 5833166251428995706056093)
                    ·
                      refine ⟨2187437344285873389771035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833166251428995706056093 2187437344285873389771035)
                      ·
                        rfl

theorem cell23_4260019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_4260019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260019 prefixEnd_4260019 := by exact prefixLift 4260019
  have htrace : WordTrace (prefixWord ++ tailWord_4260019) baseStart_4260019 baseEnd_4260019 := by
    simpa [prefixWord, tailWord_4260019, baseEnd_4260019] using wordTrace_append hprefix tailTrace_4260019
  have hstable : (prefixWord ++ tailWord_4260019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260019).length < 2 ^ (prefixWord ++ tailWord_4260019).sum := by decide
  have hdescent : baseEnd_4260019 < baseStart_4260019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260049 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_4260049 : Nat := 118140960795 + 4260049 * 2 ^ 59
def prefixEnd_4260049 : Nat := 4983230072969 + 3 ^ 40 * 4260049 * 2
def baseEnd_4260049 : Nat := 2187452748705508272395897

theorem tailTrace_4260049 : CollatzResearch.WordTrace tailWord_4260049 prefixEnd_4260049 2187452748705508272395897 := by
  unfold tailWord_4260049
  simp only [CollatzResearch.WordTrace]
  refine ⟨155376751743577506290423201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103584501162385004193615467 155376751743577506290423201)
  ·
    refine ⟨116532563807683129717817401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155376751743577506290423201 116532563807683129717817401)
    ·
      refine ⟨87399422855762347288363051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116532563807683129717817401 87399422855762347288363051)
      ·
        refine ⟨131099134283643520932544577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87399422855762347288363051 131099134283643520932544577)
        ·
          refine ⟨98324350712732640699408433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131099134283643520932544577 98324350712732640699408433)
          ·
            refine ⟨73743263034549480524556325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98324350712732640699408433 73743263034549480524556325)
            ·
              refine ⟨13826861818978027598354311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73743263034549480524556325 13826861818978027598354311)
              ·
                refine ⟨20740292728467041397531467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13826861818978027598354311 20740292728467041397531467)
                ·
                  refine ⟨31110439092700562096297201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20740292728467041397531467 31110439092700562096297201)
                  ·
                    refine ⟨23332829319525421572222901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31110439092700562096297201 23332829319525421572222901)
                    ·
                      refine ⟨2187452748705508272395897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23332829319525421572222901 2187452748705508272395897)
                      ·
                        rfl

theorem cell23_4260049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_4260049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260049 prefixEnd_4260049 := by exact prefixLift 4260049
  have htrace : WordTrace (prefixWord ++ tailWord_4260049) baseStart_4260049 baseEnd_4260049 := by
    simpa [prefixWord, tailWord_4260049, baseEnd_4260049] using wordTrace_append hprefix tailTrace_4260049
  have hstable : (prefixWord ++ tailWord_4260049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260049).length < 2 ^ (prefixWord ++ tailWord_4260049).sum := by decide
  have hdescent : baseEnd_4260049 < baseStart_4260049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260053 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4260053 : Nat := 118140960795 + 4260053 * 2 ^ 59
def prefixEnd_4260053 : Nat := 4983230072969 + 3 ^ 40 * 4260053 * 2
def baseEnd_4260053 : Nat := 2187454802628126256745879

theorem tailTrace_4260053 : CollatzResearch.WordTrace tailWord_4260053 prefixEnd_4260053 2187454802628126256745879 := by
  unfold tailWord_4260053
  simp only [CollatzResearch.WordTrace]
  refine ⟨155376897635563014973568813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103584598423708676649045875 155376897635563014973568813)
  ·
    refine ⟨58266336613336130615088305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155376897635563014973568813 58266336613336130615088305)
    ·
      refine ⟨43699752460002097961316229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58266336613336130615088305 43699752460002097961316229)
      ·
        refine ⟨8193703586250393367746793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43699752460002097961316229 8193703586250393367746793)
        ·
          refine ⟨6145277689687795025810095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8193703586250393367746793 6145277689687795025810095)
          ·
            refine ⟨9217916534531692538715143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145277689687795025810095 9217916534531692538715143)
            ·
              refine ⟨13826874801797538808072715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9217916534531692538715143 13826874801797538808072715)
              ·
                refine ⟨20740312202696308212109073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13826874801797538808072715 20740312202696308212109073)
                ·
                  refine ⟨15555234152022231159081805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20740312202696308212109073 15555234152022231159081805)
                  ·
                    refine ⟨5833212807008336684655677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15555234152022231159081805 5833212807008336684655677)
                    ·
                      refine ⟨2187454802628126256745879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833212807008336684655677 2187454802628126256745879)
                      ·
                        rfl

theorem cell23_4260053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4260053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260053 prefixEnd_4260053 := by exact prefixLift 4260053
  have htrace : WordTrace (prefixWord ++ tailWord_4260053) baseStart_4260053 baseEnd_4260053 := by
    simpa [prefixWord, tailWord_4260053, baseEnd_4260053] using wordTrace_append hprefix tailTrace_4260053
  have hstable : (prefixWord ++ tailWord_4260053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260053).length < 2 ^ (prefixWord ++ tailWord_4260053).sum := by decide
  have hdescent : baseEnd_4260053 < baseStart_4260053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260059 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4]
def baseStart_4260059 : Nat := 118140960795 + 4260059 * 2 ^ 59
def prefixEnd_4260059 : Nat := 4983230072969 + 3 ^ 40 * 4260059 * 2
def baseEnd_4260059 : Nat := 2187457883512053233270851

theorem tailTrace_4260059 : CollatzResearch.WordTrace tailWord_4260059 prefixEnd_4260059 2187457883512053233270851 := by
  unfold tailWord_4260059
  simp only [CollatzResearch.WordTrace]
  refine ⟨155377116473541277998287231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103584744315694185332191487 155377116473541277998287231)
  ·
    refine ⟨233065674710311916997430847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155377116473541277998287231 233065674710311916997430847)
    ·
      refine ⟨349598512065467875496146271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233065674710311916997430847 349598512065467875496146271)
      ·
        refine ⟨524397768098201813244219407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349598512065467875496146271 524397768098201813244219407)
        ·
          refine ⟨786596652147302719866329111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524397768098201813244219407 786596652147302719866329111)
          ·
            refine ⟨1179894978220954079799493667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786596652147302719866329111 1179894978220954079799493667)
            ·
              refine ⟨1769842467331431119699240501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179894978220954079799493667 1769842467331431119699240501)
              ·
                refine ⟨165922731312321667471803797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1769842467331431119699240501 165922731312321667471803797)
                ·
                  refine ⟨7777628030265078162740803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165922731312321667471803797 7777628030265078162740803)
                  ·
                    refine ⟨11666442045397617244111205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7777628030265078162740803 11666442045397617244111205)
                    ·
                      refine ⟨2187457883512053233270851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11666442045397617244111205 2187457883512053233270851)
                      ·
                        rfl

theorem cell23_4260059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4].length) (baseStart_4260059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260059 prefixEnd_4260059 := by exact prefixLift 4260059
  have htrace : WordTrace (prefixWord ++ tailWord_4260059) baseStart_4260059 baseEnd_4260059 := by
    simpa [prefixWord, tailWord_4260059, baseEnd_4260059] using wordTrace_append hprefix tailTrace_4260059
  have hstable : (prefixWord ++ tailWord_4260059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260059).length < 2 ^ (prefixWord ++ tailWord_4260059).sum := by decide
  have hdescent : baseEnd_4260059 < baseStart_4260059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260076 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_4260076 : Nat := 118140960795 + 4260076 * 2 ^ 59
def prefixEnd_4260076 : Nat := 4983230072969 + 3 ^ 40 * 4260076 * 2
def baseEnd_4260076 : Nat := 2187466612683179666758273

theorem tailTrace_4260076 : CollatzResearch.WordTrace tailWord_4260076 prefixEnd_4260076 2187466612683179666758273 := by
  unfold tailWord_4260076
  simp only [CollatzResearch.WordTrace]
  refine ⟨77688868257239844950828041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103585157676319793267770721 77688868257239844950828041)
  ·
    refine ⟨58266651192929883713121031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77688868257239844950828041 58266651192929883713121031)
    ·
      refine ⟨87399976789394825569681547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58266651192929883713121031 87399976789394825569681547)
      ·
        refine ⟨131099965184092238354522321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87399976789394825569681547 131099965184092238354522321)
        ·
          refine ⟨98324973888069178765891741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131099965184092238354522321 98324973888069178765891741)
          ·
            refine ⟨36871865208025942037209403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98324973888069178765891741 36871865208025942037209403)
            ·
              refine ⟨55307797812038913055814105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36871865208025942037209403 55307797812038913055814105)
              ·
                refine ⟨41480848359029184791860579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55307797812038913055814105 41480848359029184791860579)
                ·
                  refine ⟨62221272538543777187790869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41480848359029184791860579 62221272538543777187790869)
                  ·
                    refine ⟨2916622150244239555677697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62221272538543777187790869 2916622150244239555677697)
                    ·
                      refine ⟨2187466612683179666758273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916622150244239555677697 2187466612683179666758273)
                      ·
                        rfl

theorem cell23_4260076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_4260076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260076 prefixEnd_4260076 := by exact prefixLift 4260076
  have htrace : WordTrace (prefixWord ++ tailWord_4260076) baseStart_4260076 baseEnd_4260076 := by
    simpa [prefixWord, tailWord_4260076, baseEnd_4260076] using wordTrace_append hprefix tailTrace_4260076
  have hstable : (prefixWord ++ tailWord_4260076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260076).length < 2 ^ (prefixWord ++ tailWord_4260076).sum := by decide
  have hdescent : baseEnd_4260076 < baseStart_4260076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260096 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_4260096 : Nat := 118140960795 + 4260096 * 2 ^ 59
def prefixEnd_4260096 : Nat := 4983230072969 + 3 ^ 40 * 4260096 * 2
def baseEnd_4260096 : Nat := 2187476882296269588508181

theorem tailTrace_4260096 : CollatzResearch.WordTrace tailWord_4260096 prefixEnd_4260096 2187476882296269588508181 := by
  unfold tailWord_4260096
  simp only [CollatzResearch.WordTrace]
  refine ⟨77689232987203616658692071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103585643982938155544922761 77689232987203616658692071)
  ·
    refine ⟨116533849480805424988038107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77689232987203616658692071 116533849480805424988038107)
    ·
      refine ⟨174800774221208137482057161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116533849480805424988038107 174800774221208137482057161)
      ·
        refine ⟨131100580665906103111542871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174800774221208137482057161 131100580665906103111542871)
        ·
          refine ⟨196650870998859154667314307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131100580665906103111542871 196650870998859154667314307)
          ·
            refine ⟨294976306498288732000971461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196650870998859154667314307 294976306498288732000971461)
            ·
              refine ⟨55308057468429137250182149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294976306498288732000971461 55308057468429137250182149)
              ·
                refine ⟨10370260775330463234409153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55308057468429137250182149 10370260775330463234409153)
                ·
                  refine ⟨7777695581497847425806865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10370260775330463234409153 7777695581497847425806865)
                  ·
                    refine ⟨5833271686123385569355149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7777695581497847425806865 5833271686123385569355149)
                    ·
                      refine ⟨2187476882296269588508181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833271686123385569355149 2187476882296269588508181)
                      ·
                        rfl

theorem cell23_4260096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_4260096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260096 prefixEnd_4260096 := by exact prefixLift 4260096
  have htrace : WordTrace (prefixWord ++ tailWord_4260096) baseStart_4260096 baseEnd_4260096 := by
    simpa [prefixWord, tailWord_4260096, baseEnd_4260096] using wordTrace_append hprefix tailTrace_4260096
  have hstable : (prefixWord ++ tailWord_4260096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260096).length < 2 ^ (prefixWord ++ tailWord_4260096).sum := by decide
  have hdescent : baseEnd_4260096 < baseStart_4260096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260099 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 8]
def baseStart_4260099 : Nat := 118140960795 + 4260099 * 2 ^ 59
def prefixEnd_4260099 : Nat := 4983230072969 + 3 ^ 40 * 4260099 * 2
def baseEnd_4260099 : Nat := 243053158082025897418963

theorem tailTrace_4260099 : CollatzResearch.WordTrace tailWord_4260099 prefixEnd_4260099 243053158082025897418963 := by
  unfold tailWord_4260099
  simp only [CollatzResearch.WordTrace]
  refine ⟨155378575393396364829743351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103585716928930909886495567 155378575393396364829743351)
  ·
    refine ⟨233067863090094547244615027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155378575393396364829743351 233067863090094547244615027)
    ·
      refine ⟨349601794635141820866922541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233067863090094547244615027 349601794635141820866922541)
      ·
        refine ⟨131100672988178182825095953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349601794635141820866922541 131100672988178182825095953)
        ·
          refine ⟨98325504741133637118821965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131100672988178182825095953 98325504741133637118821965)
          ·
            refine ⟨36872064277925113919558237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98325504741133637118821965 36872064277925113919558237)
            ·
              refine ⟨13827024104221917719834339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36872064277925113919558237 13827024104221917719834339)
              ·
                refine ⟨20740536156332876579751509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13827024104221917719834339 20740536156332876579751509)
                ·
                  refine ⟨243053158082025897418963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20740536156332876579751509 243053158082025897418963)
                  ·
                    rfl

theorem cell23_4260099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 8].length) (baseStart_4260099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260099 prefixEnd_4260099 := by exact prefixLift 4260099
  have htrace : WordTrace (prefixWord ++ tailWord_4260099) baseStart_4260099 baseEnd_4260099 := by
    simpa [prefixWord, tailWord_4260099, baseEnd_4260099] using wordTrace_append hprefix tailTrace_4260099
  have hstable : (prefixWord ++ tailWord_4260099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260099).length < 2 ^ (prefixWord ++ tailWord_4260099).sum := by decide
  have hdescent : baseEnd_4260099 < baseStart_4260099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260180 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4260180 : Nat := 118140960795 + 4260180 * 2 ^ 59
def prefixEnd_4260180 : Nat := 4983230072969 + 3 ^ 40 * 4260180 * 2
def baseEnd_4260180 : Nat := 729173338223749086619265

theorem tailTrace_4260180 : CollatzResearch.WordTrace tailWord_4260180 prefixEnd_4260180 729173338223749086619265 := by
  unfold tailWord_4260180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77690764853051457831720997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103587686470735277108961329 77690764853051457831720997)
  ·
    refine ⟨14567018409947148343447687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77690764853051457831720997 14567018409947148343447687)
    ·
      refine ⟨21850527614920722515171531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14567018409947148343447687 21850527614920722515171531)
      ·
        refine ⟨32775791422381083772757297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21850527614920722515171531 32775791422381083772757297)
        ·
          refine ⟨24581843566785812829567973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32775791422381083772757297 24581843566785812829567973)
          ·
            refine ⟨4609095668772339905543995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24581843566785812829567973 4609095668772339905543995)
            ·
              refine ⟨6913643503158509858315993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609095668772339905543995 6913643503158509858315993)
              ·
                refine ⟨5185232627368882393736995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6913643503158509858315993 5185232627368882393736995)
                ·
                  refine ⟨7777848941053323590605493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185232627368882393736995 7777848941053323590605493)
                  ·
                    refine ⟨729173338223749086619265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7777848941053323590605493 729173338223749086619265)
                    ·
                      rfl

theorem cell23_4260180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4260180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260180 prefixEnd_4260180 := by exact prefixLift 4260180
  have htrace : WordTrace (prefixWord ++ tailWord_4260180) baseStart_4260180 baseEnd_4260180 := by
    simpa [prefixWord, tailWord_4260180, baseEnd_4260180] using wordTrace_append hprefix tailTrace_4260180
  have hstable : (prefixWord ++ tailWord_4260180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260180).length < 2 ^ (prefixWord ++ tailWord_4260180).sum := by decide
  have hdescent : baseEnd_4260180 < baseStart_4260180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260210 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_4260210 : Nat := 118140960795 + 4260210 * 2 ^ 59
def prefixEnd_4260210 : Nat := 4983230072969 + 3 ^ 40 * 4260210 * 2
def baseEnd_4260210 : Nat := 729178473030294047494219

theorem tailTrace_4260210 : CollatzResearch.WordTrace tailWord_4260210 prefixEnd_4260210 729178473030294047494219 := by
  unfold tailWord_4260210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38845655973998557696758521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103588415930662820524689389 38845655973998557696758521)
  ·
    refine ⟨29134241980498918272568891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38845655973998557696758521 29134241980498918272568891)
    ·
      refine ⟨43701362970748377408853337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29134241980498918272568891 43701362970748377408853337)
      ·
        refine ⟨32776022228061283056640003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43701362970748377408853337 32776022228061283056640003)
        ·
          refine ⟨49164033342091924584960005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32776022228061283056640003 49164033342091924584960005)
          ·
            refine ⟨9218256251642235859680001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49164033342091924584960005 9218256251642235859680001)
            ·
              refine ⟨6913692188731676894760001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9218256251642235859680001 6913692188731676894760001)
              ·
                refine ⟨5185269141548757671070001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6913692188731676894760001 5185269141548757671070001)
                ·
                  refine ⟨3888951856161568253302501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5185269141548757671070001 3888951856161568253302501)
                  ·
                    refine ⟨729178473030294047494219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888951856161568253302501 729178473030294047494219)
                    ·
                      rfl

theorem cell23_4260210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_4260210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260210 prefixEnd_4260210 := by exact prefixLift 4260210
  have htrace : WordTrace (prefixWord ++ tailWord_4260210) baseStart_4260210 baseEnd_4260210 := by
    simpa [prefixWord, tailWord_4260210, baseEnd_4260210] using wordTrace_append hprefix tailTrace_4260210
  have hstable : (prefixWord ++ tailWord_4260210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260210).length < 2 ^ (prefixWord ++ tailWord_4260210).sum := by decide
  have hdescent : baseEnd_4260210 < baseStart_4260210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260233 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_4260233 : Nat := 118140960795 + 4260233 * 2 ^ 59
def prefixEnd_4260233 : Nat := 4983230072969 + 3 ^ 40 * 4260233 * 2
def baseEnd_4260233 : Nat := 2187547229145935552495051

theorem tailTrace_4260233 : CollatzResearch.WordTrace tailWord_4260233 prefixEnd_4260233 2187547229145935552495051 := by
  unfold tailWord_4260233
  simp only [CollatzResearch.WordTrace]
  refine ⟨155383462774910905715121353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103588975183273937143414235 155383462774910905715121353)
  ·
    refine ⟨116537597081183179286341015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155383462774910905715121353 116537597081183179286341015)
    ·
      refine ⟨174806395621774768929511523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116537597081183179286341015 174806395621774768929511523)
      ·
        refine ⟨262209593432662153394267285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174806395621774768929511523 262209593432662153394267285)
        ·
          refine ⟨12291074692156038440356279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 262209593432662153394267285 12291074692156038440356279)
          ·
            refine ⟨18436612038234057660534419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12291074692156038440356279 18436612038234057660534419)
            ·
              refine ⟨27654918057351086490801629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18436612038234057660534419 27654918057351086490801629)
              ·
                refine ⟨10370594271506657434050611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27654918057351086490801629 10370594271506657434050611)
                ·
                  refine ⟨15555891407259986151075917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10370594271506657434050611 15555891407259986151075917)
                  ·
                    refine ⟨5833459277722494806653469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15555891407259986151075917 5833459277722494806653469)
                    ·
                      refine ⟨2187547229145935552495051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833459277722494806653469 2187547229145935552495051)
                      ·
                        rfl

theorem cell23_4260233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_4260233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260233 prefixEnd_4260233 := by exact prefixLift 4260233
  have htrace : WordTrace (prefixWord ++ tailWord_4260233) baseStart_4260233 baseEnd_4260233 := by
    simpa [prefixWord, tailWord_4260233, baseEnd_4260233] using wordTrace_append hprefix tailTrace_4260233
  have hstable : (prefixWord ++ tailWord_4260233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260233).length < 2 ^ (prefixWord ++ tailWord_4260233).sum := by decide
  have hdescent : baseEnd_4260233 < baseStart_4260233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260234 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4260234 : Nat := 118140960795 + 4260234 * 2 ^ 59
def prefixEnd_4260234 : Nat := 4983230072969 + 3 ^ 40 * 4260234 * 2
def baseEnd_4260234 : Nat := 2187547742626590048582547

theorem tailTrace_4260234 : CollatzResearch.WordTrace tailWord_4260234 prefixEnd_4260234 2187547742626590048582547 := by
  unfold tailWord_4260234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38845874811976820721476939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103588999498604855257271837 38845874811976820721476939)
  ·
    refine ⟨58268812217965231082215409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38845874811976820721476939 58268812217965231082215409)
    ·
      refine ⟨43701609163473923311661557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58268812217965231082215409 43701609163473923311661557)
      ·
        refine ⟨4097025859075680310468271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43701609163473923311661557 4097025859075680310468271)
        ·
          refine ⟨6145538788613520465702407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4097025859075680310468271 6145538788613520465702407)
          ·
            refine ⟨9218308182920280698553611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145538788613520465702407 9218308182920280698553611)
            ·
              refine ⟨13827462274380421047830417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9218308182920280698553611 13827462274380421047830417)
              ·
                refine ⟨10370596705785315785872813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13827462274380421047830417 10370596705785315785872813)
                ·
                  refine ⟨3888973764669493419702305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10370596705785315785872813 3888973764669493419702305)
                  ·
                    refine ⟨2916730323502120064776729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3888973764669493419702305 2916730323502120064776729)
                    ·
                      refine ⟨2187547742626590048582547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916730323502120064776729 2187547742626590048582547)
                      ·
                        rfl

theorem cell23_4260234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4260234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260234 prefixEnd_4260234 := by exact prefixLift 4260234
  have htrace : WordTrace (prefixWord ++ tailWord_4260234) baseStart_4260234 baseEnd_4260234 := by
    simpa [prefixWord, tailWord_4260234, baseEnd_4260234] using wordTrace_append hprefix tailTrace_4260234
  have hstable : (prefixWord ++ tailWord_4260234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260234).length < 2 ^ (prefixWord ++ tailWord_4260234).sum := by decide
  have hdescent : baseEnd_4260234 < baseStart_4260234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260254 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4260254 : Nat := 118140960795 + 4260254 * 2 ^ 59
def prefixEnd_4260254 : Nat := 4983230072969 + 3 ^ 40 * 4260254 * 2
def baseEnd_4260254 : Nat := 2187558012239679970332455

theorem tailTrace_4260254 : CollatzResearch.WordTrace tailWord_4260254 prefixEnd_4260254 2187558012239679970332455 := by
  unfold tailWord_4260254
  simp only [CollatzResearch.WordTrace]
  refine ⟨19423028588479353287704477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103589485805223217534423877 19423028588479353287704477)
  ·
    refine ⟨7283635720679757482889179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19423028588479353287704477 7283635720679757482889179)
    ·
      refine ⟨10925453581019636224333769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7283635720679757482889179 10925453581019636224333769)
      ·
        refine ⟨8194090185764727168250327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10925453581019636224333769 8194090185764727168250327)
        ·
          refine ⟨12291135278647090752375491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8194090185764727168250327 12291135278647090752375491)
          ·
            refine ⟨18436702917970636128563237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12291135278647090752375491 18436702917970636128563237)
            ·
              refine ⟨3456881797119494274105607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18436702917970636128563237 3456881797119494274105607)
              ·
                refine ⟨5185322695679241411158411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456881797119494274105607 5185322695679241411158411)
                ·
                  refine ⟨7777984043518862116737617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185322695679241411158411 7777984043518862116737617)
                  ·
                    refine ⟨5833488032639146587553213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7777984043518862116737617 5833488032639146587553213)
                    ·
                      refine ⟨2187558012239679970332455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833488032639146587553213 2187558012239679970332455)
                      ·
                        rfl

theorem cell23_4260254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4260254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260254 prefixEnd_4260254 := by exact prefixLift 4260254
  have htrace : WordTrace (prefixWord ++ tailWord_4260254) baseStart_4260254 baseEnd_4260254 := by
    simpa [prefixWord, tailWord_4260254, baseEnd_4260254] using wordTrace_append hprefix tailTrace_4260254
  have hstable : (prefixWord ++ tailWord_4260254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260254).length < 2 ^ (prefixWord ++ tailWord_4260254).sum := by decide
  have hdescent : baseEnd_4260254 < baseStart_4260254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260284 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4260284 : Nat := 118140960795 + 4260284 * 2 ^ 59
def prefixEnd_4260284 : Nat := 4983230072969 + 3 ^ 40 * 4260284 * 2
def baseEnd_4260284 : Nat := 2187573416659314852957317

theorem tailTrace_4260284 : CollatzResearch.WordTrace tailWord_4260284 prefixEnd_4260284 2187573416659314852957317 := by
  unfold tailWord_4260284
  simp only [CollatzResearch.WordTrace]
  refine ⟨77692661448863070712613953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103590215265150760950151937 77692661448863070712613953)
  ·
    refine ⟨58269496086647303034460465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77692661448863070712613953 58269496086647303034460465)
    ·
      refine ⟨43702122064985477275845349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58269496086647303034460465 43702122064985477275845349)
      ·
        refine ⟨8194147887184776989221003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43702122064985477275845349 8194147887184776989221003)
        ·
          refine ⟨12291221830777165483831505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8194147887184776989221003 12291221830777165483831505)
          ·
            refine ⟨9218416373082874112873629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12291221830777165483831505 9218416373082874112873629)
            ·
              refine ⟨3456906139906077792327611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9218416373082874112873629 3456906139906077792327611)
              ·
                refine ⟨5185359209859116688491417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456906139906077792327611 5185359209859116688491417)
                ·
                  refine ⟨3889019407394337516368563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5185359209859116688491417 3889019407394337516368563)
                  ·
                    refine ⟨5833529111091506274552845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3889019407394337516368563 5833529111091506274552845)
                    ·
                      refine ⟨2187573416659314852957317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833529111091506274552845 2187573416659314852957317)
                      ·
                        rfl

theorem cell23_4260284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4260284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260284 prefixEnd_4260284 := by exact prefixLift 4260284
  have htrace : WordTrace (prefixWord ++ tailWord_4260284) baseStart_4260284 baseEnd_4260284 := by
    simpa [prefixWord, tailWord_4260284, baseEnd_4260284] using wordTrace_append hprefix tailTrace_4260284
  have hstable : (prefixWord ++ tailWord_4260284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260284).length < 2 ^ (prefixWord ++ tailWord_4260284).sum := by decide
  have hdescent : baseEnd_4260284 < baseStart_4260284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260310 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4260310 : Nat := 118140960795 + 4260310 * 2 ^ 59
def prefixEnd_4260310 : Nat := 4983230072969 + 3 ^ 40 * 4260310 * 2
def baseEnd_4260310 : Nat := 2187586767156331751232197

theorem tailTrace_4260310 : CollatzResearch.WordTrace tailWord_4260310 prefixEnd_4260310 2187586767156331751232197 := by
  unfold tailWord_4260310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711641949726996741604649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103590847463754631910449589 9711641949726996741604649)
  ·
    refine ⟨7283731462295247556203487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9711641949726996741604649 7283731462295247556203487)
    ·
      refine ⟨10925597193442871334305231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7283731462295247556203487 10925597193442871334305231)
      ·
        refine ⟨16388395790164307001457847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10925597193442871334305231 16388395790164307001457847)
        ·
          refine ⟨24582593685246460502186771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16388395790164307001457847 24582593685246460502186771)
          ·
            refine ⟨36873890527869690753280157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24582593685246460502186771 36873890527869690753280157)
            ·
              refine ⟨13827708947951134032480059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36873890527869690753280157 13827708947951134032480059)
              ·
                refine ⟨20741563421926701048720089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13827708947951134032480059 20741563421926701048720089)
                ·
                  refine ⟨15556172566445025786540067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20741563421926701048720089 15556172566445025786540067)
                  ·
                    refine ⟨23334258849667538679810101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15556172566445025786540067 23334258849667538679810101)
                    ·
                      refine ⟨2187586767156331751232197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23334258849667538679810101 2187586767156331751232197)
                      ·
                        rfl

theorem cell23_4260310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4260310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260310 prefixEnd_4260310 := by exact prefixLift 4260310
  have htrace : WordTrace (prefixWord ++ tailWord_4260310) baseStart_4260310 baseEnd_4260310 := by
    simpa [prefixWord, tailWord_4260310, baseEnd_4260310] using wordTrace_append hprefix tailTrace_4260310
  have hstable : (prefixWord ++ tailWord_4260310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260310).length < 2 ^ (prefixWord ++ tailWord_4260310).sum := by decide
  have hdescent : baseEnd_4260310 < baseStart_4260310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260330 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_4260330 : Nat := 118140960795 + 4260330 * 2 ^ 59
def prefixEnd_4260330 : Nat := 4983230072969 + 3 ^ 40 * 4260330 * 2
def baseEnd_4260330 : Nat := 243066337418824630331345

theorem tailTrace_4260330 : CollatzResearch.WordTrace tailWord_4260330 prefixEnd_4260330 243066337418824630331345 := by
  unfold tailWord_4260330
  simp only [CollatzResearch.WordTrace]
  refine ⟨38846750163889872820350611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103591333770372994187601629 38846750163889872820350611)
  ·
    refine ⟨58270125245834809230525917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38846750163889872820350611 58270125245834809230525917)
    ·
      refine ⟨21851296967188053461447219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58270125245834809230525917 21851296967188053461447219)
      ·
        refine ⟨32776945450782080192170829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21851296967188053461447219 32776945450782080192170829)
        ·
          refine ⟨12291354544043280072064061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32776945450782080192170829 12291354544043280072064061)
          ·
            refine ⟨4609257954016230027024023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12291354544043280072064061 4609257954016230027024023)
            ·
              refine ⟨6913886931024345040536035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609257954016230027024023 6913886931024345040536035)
              ·
                refine ⟨10370830396536517560804053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6913886931024345040536035 10370830396536517560804053)
                ·
                  refine ⟨243066337418824630331345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10370830396536517560804053 243066337418824630331345)
                  ·
                    rfl

theorem cell23_4260330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_4260330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260330 prefixEnd_4260330 := by exact prefixLift 4260330
  have htrace : WordTrace (prefixWord ++ tailWord_4260330) baseStart_4260330 baseEnd_4260330 := by
    simpa [prefixWord, tailWord_4260330, baseEnd_4260330] using wordTrace_append hprefix tailTrace_4260330
  have hstable : (prefixWord ++ tailWord_4260330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260330).length < 2 ^ (prefixWord ++ tailWord_4260330).sum := by decide
  have hdescent : baseEnd_4260330 < baseStart_4260330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260341 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4260341 : Nat := 118140960795 + 4260341 * 2 ^ 59
def prefixEnd_4260341 : Nat := 4983230072969 + 3 ^ 40 * 4260341 * 2
def baseEnd_4260341 : Nat := 2187602685056621129944555

theorem tailTrace_4260341 : CollatzResearch.WordTrace tailWord_4260341 prefixEnd_4260341 2187602685056621129944555 := by
  unfold tailWord_4260341
  simp only [CollatzResearch.WordTrace]
  refine ⟨155387401858519640160052877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103591601239013093440035251 155387401858519640160052877)
  ·
    refine ⟨58270275696944865060019829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155387401858519640160052877 58270275696944865060019829)
    ·
      refine ⟨5462838346588581099376859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58270275696944865060019829 5462838346588581099376859)
      ·
        refine ⟨8194257519882871649065289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462838346588581099376859 8194257519882871649065289)
        ·
          refine ⟨6145693139912153736798967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8194257519882871649065289 6145693139912153736798967)
          ·
            refine ⟨9218539709868230605198451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145693139912153736798967 9218539709868230605198451)
            ·
              refine ⟨13827809564802345907797677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9218539709868230605198451 13827809564802345907797677)
              ·
                refine ⟨5185428586800879715424129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13827809564802345907797677 5185428586800879715424129)
                ·
                  refine ⟨3889071440100659786568097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5185428586800879715424129 3889071440100659786568097)
                  ·
                    refine ⟨2916803580075494839926073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3889071440100659786568097 2916803580075494839926073)
                    ·
                      refine ⟨2187602685056621129944555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916803580075494839926073 2187602685056621129944555)
                      ·
                        rfl

theorem cell23_4260341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4260341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260341 prefixEnd_4260341 := by exact prefixLift 4260341
  have htrace : WordTrace (prefixWord ++ tailWord_4260341) baseStart_4260341 baseEnd_4260341 := by
    simpa [prefixWord, tailWord_4260341, baseEnd_4260341] using wordTrace_append hprefix tailTrace_4260341
  have hstable : (prefixWord ++ tailWord_4260341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260341).length < 2 ^ (prefixWord ++ tailWord_4260341).sum := by decide
  have hdescent : baseEnd_4260341 < baseStart_4260341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260380 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4260380 : Nat := 118140960795 + 4260380 * 2 ^ 59
def prefixEnd_4260380 : Nat := 4983230072969 + 3 ^ 40 * 4260380 * 2
def baseEnd_4260380 : Nat := 2187622710802146477356875

theorem tailTrace_4260380 : CollatzResearch.WordTrace tailWord_4260380 prefixEnd_4260380 2187622710802146477356875 := by
  unfold tailWord_4260380
  simp only [CollatzResearch.WordTrace]
  refine ⟨77694412152689174910361297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103592549536918899880481729 77694412152689174910361297)
  ·
    refine ⟨58270809114516881182770973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77694412152689174910361297 58270809114516881182770973)
    ·
      refine ⟨21851553417943830443539115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58270809114516881182770973 21851553417943830443539115)
      ·
        refine ⟨32777330126915745665308673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21851553417943830443539115 32777330126915745665308673)
        ·
          refine ⟨24582997595186809248981505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32777330126915745665308673 24582997595186809248981505)
          ·
            refine ⟨18437248196390106936736129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24582997595186809248981505 18437248196390106936736129)
            ·
              refine ⟨13827936147292580202552097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18437248196390106936736129 13827936147292580202552097)
              ·
                refine ⟨10370952110469435151914073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13827936147292580202552097 10370952110469435151914073)
                ·
                  refine ⟨7778214082852076363935555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10370952110469435151914073 7778214082852076363935555)
                  ·
                    refine ⟨11667321124278114545903333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7778214082852076363935555 11667321124278114545903333)
                    ·
                      refine ⟨2187622710802146477356875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11667321124278114545903333 2187622710802146477356875)
                      ·
                        rfl

theorem cell23_4260380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4260380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260380 prefixEnd_4260380 := by exact prefixLift 4260380
  have htrace : WordTrace (prefixWord ++ tailWord_4260380) baseStart_4260380 baseEnd_4260380 := by
    simpa [prefixWord, tailWord_4260380, baseEnd_4260380] using wordTrace_append hprefix tailTrace_4260380
  have hstable : (prefixWord ++ tailWord_4260380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260380).length < 2 ^ (prefixWord ++ tailWord_4260380).sum := by decide
  have hdescent : baseEnd_4260380 < baseStart_4260380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260383 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_4260383 : Nat := 118140960795 + 4260383 * 2 ^ 59
def prefixEnd_4260383 : Nat := 4983230072969 + 3 ^ 40 * 4260383 * 2
def baseEnd_4260383 : Nat := 2187624251244109965619361

theorem tailTrace_4260383 : CollatzResearch.WordTrace tailWord_4260383 prefixEnd_4260383 2187624251244109965619361 := by
  unfold tailWord_4260383
  simp only [CollatzResearch.WordTrace]
  refine ⟨155388933724367481333081803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103592622482911654222054535 155388933724367481333081803)
  ·
    refine ⟨233083400586551221999622705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155388933724367481333081803 233083400586551221999622705)
    ·
      refine ⟨174812550439913416499717029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233083400586551221999622705 174812550439913416499717029)
      ·
        refine ⟨32777353207483765593696943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174812550439913416499717029 32777353207483765593696943)
        ·
          refine ⟨49166029811225648390545415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32777353207483765593696943 49166029811225648390545415)
          ·
            refine ⟨73749044716838472585818123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49166029811225648390545415 73749044716838472585818123)
            ·
              refine ⟨110623567075257708878727185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73749044716838472585818123 110623567075257708878727185)
              ·
                refine ⟨82967675306443281659045389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110623567075257708878727185 82967675306443281659045389)
                ·
                  refine ⟨31112878239916230622142021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82967675306443281659045389 31112878239916230622142021)
                  ·
                    refine ⟨5833664669984293241651629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31112878239916230622142021 5833664669984293241651629)
                    ·
                      refine ⟨2187624251244109965619361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833664669984293241651629 2187624251244109965619361)
                      ·
                        rfl

theorem cell23_4260383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_4260383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260383 prefixEnd_4260383 := by exact prefixLift 4260383
  have htrace : WordTrace (prefixWord ++ tailWord_4260383) baseStart_4260383 baseEnd_4260383 := by
    simpa [prefixWord, tailWord_4260383, baseEnd_4260383] using wordTrace_append hprefix tailTrace_4260383
  have hstable : (prefixWord ++ tailWord_4260383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260383).length < 2 ^ (prefixWord ++ tailWord_4260383).sum := by decide
  have hdescent : baseEnd_4260383 < baseStart_4260383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260403 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 6]
def baseStart_4260403 : Nat := 118140960795 + 4260403 * 2 ^ 59
def prefixEnd_4260403 : Nat := 4983230072969 + 3 ^ 40 * 4260403 * 2
def baseEnd_4260403 : Nat := 243070502317466654152141

theorem tailTrace_4260403 : CollatzResearch.WordTrace tailWord_4260403 prefixEnd_4260403 243070502317466654152141 := by
  unfold tailWord_4260403
  simp only [CollatzResearch.WordTrace]
  refine ⟨155389663184295024748809863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103593108789530016499206575 155389663184295024748809863)
  ·
    refine ⟨233084494776442537123214795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155389663184295024748809863 233084494776442537123214795)
    ·
      refine ⟨349626742164663805684822193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233084494776442537123214795 349626742164663805684822193)
      ·
        refine ⟨262220056623497854263616645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349626742164663805684822193 262220056623497854263616645)
        ·
          refine ⟨49166260616905847674428121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262220056623497854263616645 49166260616905847674428121)
          ·
            refine ⟨36874695462679385755821091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49166260616905847674428121 36874695462679385755821091)
            ·
              refine ⟨55312043194019078633731637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36874695462679385755821091 55312043194019078633731637)
              ·
                refine ⟨5185504049439288621912341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55312043194019078633731637 5185504049439288621912341)
                ·
                  refine ⟨243070502317466654152141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5185504049439288621912341 243070502317466654152141)
                  ·
                    rfl

theorem cell23_4260403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 6].length) (baseStart_4260403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260403 prefixEnd_4260403 := by exact prefixLift 4260403
  have htrace : WordTrace (prefixWord ++ tailWord_4260403) baseStart_4260403 baseEnd_4260403 := by
    simpa [prefixWord, tailWord_4260403, baseEnd_4260403] using wordTrace_append hprefix tailTrace_4260403
  have hstable : (prefixWord ++ tailWord_4260403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260403).length < 2 ^ (prefixWord ++ tailWord_4260403).sum := by decide
  have hdescent : baseEnd_4260403 < baseStart_4260403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260417 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4260417 : Nat := 118140960795 + 4260417 * 2 ^ 59
def prefixEnd_4260417 : Nat := 4983230072969 + 3 ^ 40 * 4260417 * 2
def baseEnd_4260417 : Nat := 2187641709586362832594205

theorem tailTrace_4260417 : CollatzResearch.WordTrace tailWord_4260417 prefixEnd_4260417 2187641709586362832594205 := by
  unfold tailWord_4260417
  simp only [CollatzResearch.WordTrace]
  refine ⟨155390173806244305139819505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103593449204162870093213003 155390173806244305139819505)
  ·
    refine ⟨116542630354683228854864629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155390173806244305139819505 116542630354683228854864629)
    ·
      refine ⟨10925871595751552705143559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116542630354683228854864629 10925871595751552705143559)
      ·
        refine ⟨16388807393627329057715339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10925871595751552705143559 16388807393627329057715339)
        ·
          refine ⟨24583211090440993586573009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16388807393627329057715339 24583211090440993586573009)
          ·
            refine ⟨18437408317830745189929757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24583211090440993586573009 18437408317830745189929757)
            ·
              refine ⟨6914028119186529446223659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18437408317830745189929757 6914028119186529446223659)
              ·
                refine ⟨10371042178779794169335489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6914028119186529446223659 10371042178779794169335489)
                ·
                  refine ⟨7778281634084845627001617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10371042178779794169335489 7778281634084845627001617)
                  ·
                    refine ⟨5833711225563634220251213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7778281634084845627001617 5833711225563634220251213)
                    ·
                      refine ⟨2187641709586362832594205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833711225563634220251213 2187641709586362832594205)
                      ·
                        rfl

theorem cell23_4260417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4260417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260417 prefixEnd_4260417 := by exact prefixLift 4260417
  have htrace : WordTrace (prefixWord ++ tailWord_4260417) baseStart_4260417 baseEnd_4260417 := by
    simpa [prefixWord, tailWord_4260417, baseEnd_4260417] using wordTrace_append hprefix tailTrace_4260417
  have hstable : (prefixWord ++ tailWord_4260417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260417).length < 2 ^ (prefixWord ++ tailWord_4260417).sum := by decide
  have hdescent : baseEnd_4260417 < baseStart_4260417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260480 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_4260480 : Nat := 118140960795 + 4260480 * 2 ^ 59
def prefixEnd_4260480 : Nat := 4983230072969 + 3 ^ 40 * 4260480 * 2
def baseEnd_4260480 : Nat := 729224686289198695368805

theorem tailTrace_4260480 : CollatzResearch.WordTrace tailWord_4260480 prefixEnd_4260480 729224686289198695368805 := by
  unfold tailWord_4260480
  simp only [CollatzResearch.WordTrace]
  refine ⟨77696235802508033449681447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103594981070010711266241929 77696235802508033449681447)
  ·
    refine ⟨116544353703762050174522171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77696235802508033449681447 116544353703762050174522171)
    ·
      refine ⟨174816530555643075261783257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116544353703762050174522171 174816530555643075261783257)
      ·
        refine ⟨131112397916732306446337443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174816530555643075261783257 131112397916732306446337443)
        ·
          refine ⟨196668596875098459669506165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131112397916732306446337443 196668596875098459669506165)
          ·
            refine ⟨18437680957040480594016203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196668596875098459669506165 18437680957040480594016203)
            ·
              refine ⟨27656521435560720891024305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18437680957040480594016203 27656521435560720891024305)
              ·
                refine ⟨20742391076670540668268229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27656521435560720891024305 20742391076670540668268229)
                ·
                  refine ⟨3889198326875726375300293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20742391076670540668268229 3889198326875726375300293)
                  ·
                    refine ⟨729224686289198695368805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889198326875726375300293 729224686289198695368805)
                    ·
                      rfl

theorem cell23_4260480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_4260480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260480 prefixEnd_4260480 := by exact prefixLift 4260480
  have htrace : WordTrace (prefixWord ++ tailWord_4260480) baseStart_4260480 baseEnd_4260480 := by
    simpa [prefixWord, tailWord_4260480, baseEnd_4260480] using wordTrace_append hprefix tailTrace_4260480
  have hstable : (prefixWord ++ tailWord_4260480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260480).length < 2 ^ (prefixWord ++ tailWord_4260480).sum := by decide
  have hdescent : baseEnd_4260480 < baseStart_4260480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260498 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_4260498 : Nat := 118140960795 + 4260498 * 2 ^ 59
def prefixEnd_4260498 : Nat := 4983230072969 + 3 ^ 40 * 4260498 * 2
def baseEnd_4260498 : Nat := 2187683301519377015681333

theorem tailTrace_4260498 : CollatzResearch.WordTrace tailWord_4260498 prefixEnd_4260498 2187683301519377015681333 := by
  unfold tailWord_4260498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38848282029737713993379537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103595418745967237315678765 38848282029737713993379537)
  ·
    refine ⟨29136211522303285495034653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38848282029737713993379537 29136211522303285495034653)
    ·
      refine ⟨10926079320863732060637995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29136211522303285495034653 10926079320863732060637995)
      ·
        refine ⟨16389118981295598090956993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926079320863732060637995 16389118981295598090956993)
        ·
          refine ⟨12291839235971698568217745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16389118981295598090956993 12291839235971698568217745)
          ·
            refine ⟨9218879426978773926163309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12291839235971698568217745 9218879426978773926163309)
            ·
              refine ⟨3457079785117040222311241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9218879426978773926163309 3457079785117040222311241)
              ·
                refine ⟨2592809838837780166733431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3457079785117040222311241 2592809838837780166733431)
                ·
                  refine ⟨3889214758256670250100147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592809838837780166733431 3889214758256670250100147)
                  ·
                    refine ⟨5833822137385005375150221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3889214758256670250100147 5833822137385005375150221)
                    ·
                      refine ⟨2187683301519377015681333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833822137385005375150221 2187683301519377015681333)
                      ·
                        rfl

theorem cell23_4260498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_4260498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260498 prefixEnd_4260498 := by exact prefixLift 4260498
  have htrace : WordTrace (prefixWord ++ tailWord_4260498) baseStart_4260498 baseEnd_4260498 := by
    simpa [prefixWord, tailWord_4260498, baseEnd_4260498] using wordTrace_append hprefix tailTrace_4260498
  have hstable : (prefixWord ++ tailWord_4260498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260498).length < 2 ^ (prefixWord ++ tailWord_4260498).sum := by decide
  have hdescent : baseEnd_4260498 < baseStart_4260498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260553 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_4260553 : Nat := 118140960795 + 4260553 * 2 ^ 59
def prefixEnd_4260553 : Nat := 4983230072969 + 3 ^ 40 * 4260553 * 2
def baseEnd_4260553 : Nat := 729237180985124766831193

theorem tailTrace_4260553 : CollatzResearch.WordTrace tailWord_4260553 prefixEnd_4260553 729237180985124766831193 := by
  unfold tailWord_4260553
  simp only [CollatzResearch.WordTrace]
  refine ⟨155395134133751600366770313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103596756089167733577846875 155395134133751600366770313)
  ·
    refine ⟨116546350600313700275077735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155395134133751600366770313 116546350600313700275077735)
    ·
      refine ⟨174819525900470550412616603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116546350600313700275077735 174819525900470550412616603)
      ·
        refine ⟨262229288850705825618924905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174819525900470550412616603 262229288850705825618924905)
        ·
          refine ⟨196671966638029369214193679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262229288850705825618924905 196671966638029369214193679)
          ·
            refine ⟨295007949957044053821290519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196671966638029369214193679 295007949957044053821290519)
            ·
              refine ⟨442511924935566080731935779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295007949957044053821290519 442511924935566080731935779)
              ·
                refine ⟨663767887403349121097903669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442511924935566080731935779 663767887403349121097903669)
                ·
                  refine ⟨62228239444063980102928469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 663767887403349121097903669 62228239444063980102928469)
                  ·
                    refine ⟨729237180985124766831193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62228239444063980102928469 729237180985124766831193)
                    ·
                      rfl

theorem cell23_4260553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_4260553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260553 prefixEnd_4260553 := by exact prefixLift 4260553
  have htrace : WordTrace (prefixWord ++ tailWord_4260553) baseStart_4260553 baseEnd_4260553 := by
    simpa [prefixWord, tailWord_4260553, baseEnd_4260553] using wordTrace_append hprefix tailTrace_4260553
  have hstable : (prefixWord ++ tailWord_4260553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260553).length < 2 ^ (prefixWord ++ tailWord_4260553).sum := by decide
  have hdescent : baseEnd_4260553 < baseStart_4260553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260554 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_4260554 : Nat := 118140960795 + 4260554 * 2 ^ 59
def prefixEnd_4260554 : Nat := 4983230072969 + 3 ^ 40 * 4260554 * 2
def baseEnd_4260554 : Nat := 2187712056436028796581075

theorem tailTrace_4260554 : CollatzResearch.WordTrace tailWord_4260554 prefixEnd_4260554 2187712056436028796581075 := by
  unfold tailWord_4260554
  simp only [CollatzResearch.WordTrace]
  refine ⟨38848792651686994384389179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103596780404498651691704477 38848792651686994384389179)
  ·
    refine ⟨58273188977530491576583769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38848792651686994384389179 58273188977530491576583769)
    ·
      refine ⟨43704891733147868682437827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58273188977530491576583769 43704891733147868682437827)
      ·
        refine ⟨65557337599721803023656741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43704891733147868682437827 65557337599721803023656741)
        ·
          refine ⟨12292000799947838066935639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65557337599721803023656741 12292000799947838066935639)
          ·
            refine ⟨18438001199921757100403459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12292000799947838066935639 18438001199921757100403459)
            ·
              refine ⟨27657001799882635650605189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18438001199921757100403459 27657001799882635650605189)
              ·
                refine ⟨5185687837477994184488473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27657001799882635650605189 5185687837477994184488473)
                ·
                  refine ⟨3889265878108495638366355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5185687837477994184488473 3889265878108495638366355)
                  ·
                    refine ⟨5833898817162743457549533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3889265878108495638366355 5833898817162743457549533)
                    ·
                      refine ⟨2187712056436028796581075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5833898817162743457549533 2187712056436028796581075)
                      ·
                        rfl

theorem cell23_4260554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_4260554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260554 prefixEnd_4260554 := by exact prefixLift 4260554
  have htrace : WordTrace (prefixWord ++ tailWord_4260554) baseStart_4260554 baseEnd_4260554 := by
    simpa [prefixWord, tailWord_4260554, baseEnd_4260554] using wordTrace_append hprefix tailTrace_4260554
  have hstable : (prefixWord ++ tailWord_4260554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260554).length < 2 ^ (prefixWord ++ tailWord_4260554).sum := by decide
  have hdescent : baseEnd_4260554 < baseStart_4260554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260570 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_4260570 : Nat := 118140960795 + 4260570 * 2 ^ 59
def prefixEnd_4260570 : Nat := 4983230072969 + 3 ^ 40 * 4260570 * 2
def baseEnd_4260570 : Nat := 729240090708833577993667

theorem tailTrace_4260570 : CollatzResearch.WordTrace tailWord_4260570 prefixEnd_4260570 729240090708833577993667 := by
  unfold tailWord_4260570
  simp only [CollatzResearch.WordTrace]
  refine ⟨38848938543672503067534791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103597169449793341513426109 38848938543672503067534791)
  ·
    refine ⟨58273407815508754601302187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38848938543672503067534791 58273407815508754601302187)
    ·
      refine ⟨87410111723263131901953281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58273407815508754601302187 87410111723263131901953281)
      ·
        refine ⟨65557583792447348926464961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87410111723263131901953281 65557583792447348926464961)
        ·
          refine ⟨49168187844335511694848721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65557583792447348926464961 49168187844335511694848721)
          ·
            refine ⟨36876140883251633771136541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49168187844335511694848721 36876140883251633771136541)
            ·
              refine ⟨13828552831219362664176203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36876140883251633771136541 13828552831219362664176203)
              ·
                refine ⟨20742829246829043996264305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13828552831219362664176203 20742829246829043996264305)
                ·
                  refine ⟨15557121935121782997198229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20742829246829043996264305 15557121935121782997198229)
                  ·
                    refine ⟨729240090708833577993667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15557121935121782997198229 729240090708833577993667)
                    ·
                      rfl

theorem cell23_4260570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_4260570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260570 prefixEnd_4260570 := by exact prefixLift 4260570
  have htrace : WordTrace (prefixWord ++ tailWord_4260570) baseStart_4260570 baseEnd_4260570 := by
    simpa [prefixWord, tailWord_4260570, baseEnd_4260570] using wordTrace_append hprefix tailTrace_4260570
  have hstable : (prefixWord ++ tailWord_4260570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260570).length < 2 ^ (prefixWord ++ tailWord_4260570).sum := by decide
  have hdescent : baseEnd_4260570 < baseStart_4260570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260594 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4260594 : Nat := 118140960795 + 4260594 * 2 ^ 59
def prefixEnd_4260594 : Nat := 4983230072969 + 3 ^ 40 * 4260594 * 2
def baseEnd_4260594 : Nat := 2187732595662208640080891

theorem tailTrace_4260594 : CollatzResearch.WordTrace tailWord_4260594 prefixEnd_4260594 2187732595662208640080891 := by
  unfold tailWord_4260594
  simp only [CollatzResearch.WordTrace]
  refine ⟨38849157381650766092253209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103597753017735376246008557 38849157381650766092253209)
  ·
    refine ⟨29136868036238074569189907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38849157381650766092253209 29136868036238074569189907)
    ·
      refine ⟨43705302054357111853784861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29136868036238074569189907 43705302054357111853784861)
      ·
        refine ⟨16389488270383916945169323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43705302054357111853784861 16389488270383916945169323)
        ·
          refine ⟨24584232405575875417753985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16389488270383916945169323 24584232405575875417753985)
          ·
            refine ⟨18438174304181906563315489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24584232405575875417753985 18438174304181906563315489)
            ·
              refine ⟨13828630728136429922486617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18438174304181906563315489 13828630728136429922486617)
              ·
                refine ⟨10371473046102322441864963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13828630728136429922486617 10371473046102322441864963)
                ·
                  refine ⟨15557209569153483662797445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10371473046102322441864963 15557209569153483662797445)
                  ·
                    refine ⟨2916976794216278186774521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15557209569153483662797445 2916976794216278186774521)
                    ·
                      refine ⟨2187732595662208640080891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2916976794216278186774521 2187732595662208640080891)
                      ·
                        rfl

theorem cell23_4260594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4260594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260594 prefixEnd_4260594 := by exact prefixLift 4260594
  have htrace : WordTrace (prefixWord ++ tailWord_4260594) baseStart_4260594 baseEnd_4260594 := by
    simpa [prefixWord, tailWord_4260594, baseEnd_4260594] using wordTrace_append hprefix tailTrace_4260594
  have hstable : (prefixWord ++ tailWord_4260594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260594).length < 2 ^ (prefixWord ++ tailWord_4260594).sum := by decide
  have hdescent : baseEnd_4260594 < baseStart_4260594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260617 : List Nat := [1, 2, 1, 1, 3, 2, 4, 4, 5]
def baseStart_4260617 : Nat := 118140960795 + 4260617 * 2 ^ 59
def prefixEnd_4260617 : Nat := 4983230072969 + 3 ^ 40 * 4260617 * 2
def baseEnd_4260617 : Nat := 243082711746362450010365

theorem tailTrace_4260617 : CollatzResearch.WordTrace tailWord_4260617 prefixEnd_4260617 243082711746362450010365 := by
  unfold tailWord_4260617
  simp only [CollatzResearch.WordTrace]
  refine ⟨155397468405519739297100105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103598312270346492864733403 155397468405519739297100105)
  ·
    refine ⟨116548101304139804472825079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155397468405519739297100105 116548101304139804472825079)
    ·
      refine ⟨174822151956209706709237619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116548101304139804472825079 174822151956209706709237619)
      ·
        refine ⟨262233227934314560063856429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174822151956209706709237619 262233227934314560063856429)
        ·
          refine ⟨98337460475367960023946161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262233227934314560063856429 98337460475367960023946161)
          ·
            refine ⟨73753095356525970017959621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98337460475367960023946161 73753095356525970017959621)
            ·
              refine ⟨13828705379348619378367429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73753095356525970017959621 13828705379348619378367429)
              ·
                refine ⟨2592882258627866133443893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13828705379348619378367429 2592882258627866133443893)
                ·
                  refine ⟨243082711746362450010365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2592882258627866133443893 243082711746362450010365)
                  ·
                    rfl

theorem cell23_4260617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 5].length) (baseStart_4260617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260617 prefixEnd_4260617 := by exact prefixLift 4260617
  have htrace : WordTrace (prefixWord ++ tailWord_4260617) baseStart_4260617 baseEnd_4260617 := by
    simpa [prefixWord, tailWord_4260617, baseEnd_4260617] using wordTrace_append hprefix tailTrace_4260617
  have hstable : (prefixWord ++ tailWord_4260617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260617).length < 2 ^ (prefixWord ++ tailWord_4260617).sum := by decide
  have hdescent : baseEnd_4260617 < baseStart_4260617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260677 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_4260677 : Nat := 118140960795 + 4260677 * 2 ^ 59
def prefixEnd_4260677 : Nat := 4983230072969 + 3 ^ 40 * 4260677 * 2
def baseEnd_4260677 : Nat := 729258404852177271781003

theorem tailTrace_4260677 : CollatzResearch.WordTrace tailWord_4260677 prefixEnd_4260677 729258404852177271781003 := by
  unfold tailWord_4260677
  simp only [CollatzResearch.WordTrace]
  refine ⟨155399656785302369544284285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103599771190201579696189523 155399656785302369544284285)
  ·
    refine ⟨58274871294488388579106607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155399656785302369544284285 58274871294488388579106607)
    ·
      refine ⟨87412306941732582868659911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58274871294488388579106607 87412306941732582868659911)
      ·
        refine ⟨131118460412598874302989867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87412306941732582868659911 131118460412598874302989867)
        ·
          refine ⟨196677690618898311454484801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131118460412598874302989867 196677690618898311454484801)
          ·
            refine ⟨147508267964173733590863601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196677690618898311454484801 147508267964173733590863601)
            ·
              refine ⟨110631200973130300193147701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147508267964173733590863601 110631200973130300193147701)
              ·
                refine ⟨10371675091230965643107597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110631200973130300193147701 10371675091230965643107597)
                ·
                  refine ⟨3889378159211612116165349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10371675091230965643107597 3889378159211612116165349)
                  ·
                    refine ⟨729258404852177271781003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889378159211612116165349 729258404852177271781003)
                    ·
                      rfl

theorem cell23_4260677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_4260677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260677 prefixEnd_4260677 := by exact prefixLift 4260677
  have htrace : WordTrace (prefixWord ++ tailWord_4260677) baseStart_4260677 baseEnd_4260677 := by
    simpa [prefixWord, tailWord_4260677, baseEnd_4260677] using wordTrace_append hprefix tailTrace_4260677
  have hstable : (prefixWord ++ tailWord_4260677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260677).length < 2 ^ (prefixWord ++ tailWord_4260677).sum := by decide
  have hdescent : baseEnd_4260677 < baseStart_4260677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260704 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_4260704 : Nat := 118140960795 + 4260704 * 2 ^ 59
def prefixEnd_4260704 : Nat := 4983230072969 + 3 ^ 40 * 4260704 * 2
def baseEnd_4260704 : Nat := 2187789078534203209705385

theorem tailTrace_4260704 : CollatzResearch.WordTrace tailWord_4260704 prefixEnd_4260704 2187789078534203209705385 := by
  unfold tailWord_4260704
  simp only [CollatzResearch.WordTrace]
  refine ⟨77700320778102276577758583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103600427704136368770344777 77700320778102276577758583)
  ·
    refine ⟨116550481167153414866637875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77700320778102276577758583 116550481167153414866637875)
    ·
      refine ⟨174825721750730122299956813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116550481167153414866637875 174825721750730122299956813)
      ·
        refine ⟨65559645656523795862483805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174825721750730122299956813 65559645656523795862483805)
        ·
          refine ⟨24584867121196423448431427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65559645656523795862483805 24584867121196423448431427)
          ·
            refine ⟨36877300681794635172647141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24584867121196423448431427 36877300681794635172647141)
            ·
              refine ⟨6914493877836494094871339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36877300681794635172647141 6914493877836494094871339)
              ·
                refine ⟨10371740816754741142307009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6914493877836494094871339 10371740816754741142307009)
                ·
                  refine ⟨7778805612566055856730257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10371740816754741142307009 7778805612566055856730257)
                  ·
                    refine ⟨5834104209424541892547693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7778805612566055856730257 5834104209424541892547693)
                    ·
                      refine ⟨2187789078534203209705385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5834104209424541892547693 2187789078534203209705385)
                      ·
                        rfl

theorem cell23_4260704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_4260704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260704 prefixEnd_4260704 := by exact prefixLift 4260704
  have htrace : WordTrace (prefixWord ++ tailWord_4260704) baseStart_4260704 baseEnd_4260704 := by
    simpa [prefixWord, tailWord_4260704, baseEnd_4260704] using wordTrace_append hprefix tailTrace_4260704
  have hstable : (prefixWord ++ tailWord_4260704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260704).length < 2 ^ (prefixWord ++ tailWord_4260704).sum := by decide
  have hdescent : baseEnd_4260704 < baseStart_4260704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260777 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_4260777 : Nat := 118140960795 + 4260777 * 2 ^ 59
def prefixEnd_4260777 : Nat := 4983230072969 + 3 ^ 40 * 4260777 * 2
def baseEnd_4260777 : Nat := 2187826562621981424092549

theorem tailTrace_4260777 : CollatzResearch.WordTrace tailWord_4260777 prefixEnd_4260777 2187826562621981424092549 := by
  unfold tailWord_4260777
  simp only [CollatzResearch.WordTrace]
  refine ⟨155403304084940086622924585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103602202723293391081949723 155403304084940086622924585)
  ·
    refine ⟨116552478063705064967193439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155403304084940086622924585 116552478063705064967193439)
    ·
      refine ⟨174828717095557597450790159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116552478063705064967193439 174828717095557597450790159)
      ·
        refine ⟨262243075643336396176185239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174828717095557597450790159 262243075643336396176185239)
        ·
          refine ⟨393364613465004594264277859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262243075643336396176185239 393364613465004594264277859)
          ·
            refine ⟨590046920197506891396416789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393364613465004594264277859 590046920197506891396416789)
            ·
              refine ⟨27658449384258135534207037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 590046920197506891396416789 27658449384258135534207037)
              ·
                refine ⟨10371918519096800825327639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27658449384258135534207037 10371918519096800825327639)
                ·
                  refine ⟨15557877778645201237991459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10371918519096800825327639 15557877778645201237991459)
                  ·
                    refine ⟨23336816667967801856987189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15557877778645201237991459 23336816667967801856987189)
                    ·
                      refine ⟨2187826562621981424092549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23336816667967801856987189 2187826562621981424092549)
                      ·
                        rfl

theorem cell23_4260777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_4260777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260777 prefixEnd_4260777 := by exact prefixLift 4260777
  have htrace : WordTrace (prefixWord ++ tailWord_4260777) baseStart_4260777 baseEnd_4260777 := by
    simpa [prefixWord, tailWord_4260777, baseEnd_4260777] using wordTrace_append hprefix tailTrace_4260777
  have hstable : (prefixWord ++ tailWord_4260777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260777).length < 2 ^ (prefixWord ++ tailWord_4260777).sum := by decide
  have hdescent : baseEnd_4260777 < baseStart_4260777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260791 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_4260791 : Nat := 118140960795 + 4260791 * 2 ^ 59
def prefixEnd_4260791 : Nat := 4983230072969 + 3 ^ 40 * 4260791 * 2
def baseEnd_4260791 : Nat := 2187833751351144369317485

theorem tailTrace_4260791 : CollatzResearch.WordTrace tailWord_4260791 prefixEnd_4260791 2187833751351144369317485 := by
  unfold tailWord_4260791
  simp only [CollatzResearch.WordTrace]
  refine ⟨155403814706889367013934227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103602543137926244675956151 155403814706889367013934227)
  ·
    refine ⟨233105722060334050520901341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155403814706889367013934227 233105722060334050520901341)
    ·
      refine ⟨87414645772625268945338003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233105722060334050520901341 87414645772625268945338003)
      ·
        refine ⟨131121968658937903418007005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87414645772625268945338003 131121968658937903418007005)
        ·
          refine ⟨49170738247101713781752627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131121968658937903418007005 49170738247101713781752627)
          ·
            refine ⟨73756107370652570672628941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49170738247101713781752627 73756107370652570672628941)
            ·
              refine ⟨27658540263994714002235853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73756107370652570672628941 27658540263994714002235853)
              ·
                refine ⟨10371952598998017750838445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27658540263994714002235853 10371952598998017750838445)
                ·
                  refine ⟨3889482224624256656564417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10371952598998017750838445 3889482224624256656564417)
                  ·
                    refine ⟨2917111668468192492423313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3889482224624256656564417 2917111668468192492423313)
                    ·
                      refine ⟨2187833751351144369317485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917111668468192492423313 2187833751351144369317485)
                      ·
                        rfl

theorem cell23_4260791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_4260791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260791 prefixEnd_4260791 := by exact prefixLift 4260791
  have htrace : WordTrace (prefixWord ++ tailWord_4260791) baseStart_4260791 baseEnd_4260791 := by
    simpa [prefixWord, tailWord_4260791, baseEnd_4260791] using wordTrace_append hprefix tailTrace_4260791
  have hstable : (prefixWord ++ tailWord_4260791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260791).length < 2 ^ (prefixWord ++ tailWord_4260791).sum := by decide
  have hdescent : baseEnd_4260791 < baseStart_4260791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260811 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 3]
def baseStart_4260811 : Nat := 118140960795 + 4260811 * 2 ^ 59
def prefixEnd_4260811 : Nat := 4983230072969 + 3 ^ 40 * 4260811 * 2
def baseEnd_4260811 : Nat := 2187844020964234291067393

theorem tailTrace_4260811 : CollatzResearch.WordTrace tailWord_4260811 prefixEnd_4260811 2187844020964234291067393 := by
  unfold tailWord_4260811
  simp only [CollatzResearch.WordTrace]
  refine ⟨155404544166816910429662287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103603029444544606953108191 155404544166816910429662287)
  ·
    refine ⟨233106816250225365644493431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155404544166816910429662287 233106816250225365644493431)
    ·
      refine ⟨349660224375338048466740147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233106816250225365644493431 349660224375338048466740147)
      ·
        refine ⟨524490336563007072700110221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349660224375338048466740147 524490336563007072700110221)
        ·
          refine ⟨196683876211127652262541333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 524490336563007072700110221 196683876211127652262541333)
          ·
            refine ⟨9219556697396608699806625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196683876211127652262541333 9219556697396608699806625)
            ·
              refine ⟨6914667523047456524854969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9219556697396608699806625 6914667523047456524854969)
              ·
                refine ⟨5186000642285592393641227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914667523047456524854969 5186000642285592393641227)
                ·
                  refine ⟨7779000963428388590461841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186000642285592393641227 7779000963428388590461841)
                  ·
                    refine ⟨5834250722571291442846381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7779000963428388590461841 5834250722571291442846381)
                    ·
                      refine ⟨2187844020964234291067393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5834250722571291442846381 2187844020964234291067393)
                      ·
                        rfl

theorem cell23_4260811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 3].length) (baseStart_4260811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260811 prefixEnd_4260811 := by exact prefixLift 4260811
  have htrace : WordTrace (prefixWord ++ tailWord_4260811) baseStart_4260811 baseEnd_4260811 := by
    simpa [prefixWord, tailWord_4260811, baseEnd_4260811] using wordTrace_append hprefix tailTrace_4260811
  have hstable : (prefixWord ++ tailWord_4260811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260811).length < 2 ^ (prefixWord ++ tailWord_4260811).sum := by decide
  have hdescent : baseEnd_4260811 < baseStart_4260811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260814 : List Nat := [4, 1, 1, 1, 2, 3, 4, 7]
def baseStart_4260814 : Nat := 118140960795 + 4260814 * 2 ^ 59
def prefixEnd_4260814 : Nat := 4983230072969 + 3 ^ 40 * 4260814 * 2
def baseEnd_4260814 : Nat := 81031317089118436271477

theorem tailTrace_4260814 : CollatzResearch.WordTrace tailWord_4260814 prefixEnd_4260814 81031317089118436271477 := by
  unfold tailWord_4260814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19425581698225755242752687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103603102390537361294680997 19425581698225755242752687)
  ·
    refine ⟨29138372547338632864129031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19425581698225755242752687 29138372547338632864129031)
    ·
      refine ⟨43707558821007949296193547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29138372547338632864129031 43707558821007949296193547)
      ·
        refine ⟨65561338231511923944290321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43707558821007949296193547 65561338231511923944290321)
        ·
          refine ⟨49171003673633942958217741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65561338231511923944290321 49171003673633942958217741)
          ·
            refine ⟨18439126377612728609331653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49171003673633942958217741 18439126377612728609331653)
            ·
              refine ⟨3457336195802386614249685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18439126377612728609331653 3457336195802386614249685)
              ·
                refine ⟨81031317089118436271477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3457336195802386614249685 81031317089118436271477)
                ·
                  rfl

theorem cell23_4260814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_4260814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260814 prefixEnd_4260814 := by exact prefixLift 4260814
  have htrace : WordTrace (prefixWord ++ tailWord_4260814) baseStart_4260814 baseEnd_4260814 := by
    simpa [prefixWord, tailWord_4260814, baseEnd_4260814] using wordTrace_append hprefix tailTrace_4260814
  have hstable : (prefixWord ++ tailWord_4260814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260814).length < 2 ^ (prefixWord ++ tailWord_4260814).sum := by decide
  have hdescent : baseEnd_4260814 < baseStart_4260814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260825 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 1, 2, 2]
def baseStart_4260825 : Nat := 118140960795 + 4260825 * 2 ^ 59
def prefixEnd_4260825 : Nat := 4983230072969 + 3 ^ 40 * 4260825 * 2
def baseEnd_4260825 : Nat := 2187851209693397236292329

theorem tailTrace_4260825 : CollatzResearch.WordTrace tailWord_4260825 prefixEnd_4260825 2187851209693397236292329 := by
  unfold tailWord_4260825
  simp only [CollatzResearch.WordTrace]
  refine ⟨155405054788766190820671929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103603369859177460547114619 155405054788766190820671929)
  ·
    refine ⟨116553791091574643115503947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155405054788766190820671929 116553791091574643115503947)
    ·
      refine ⟨174830686637361964673255921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116553791091574643115503947 174830686637361964673255921)
      ·
        refine ⟨131123014978021473504941941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174830686637361964673255921 131123014978021473504941941)
        ·
          refine ⟨12292782654189513141088307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131123014978021473504941941 12292782654189513141088307)
          ·
            refine ⟨18439173981284269711632461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12292782654189513141088307 18439173981284269711632461)
            ·
              refine ⟨6914690242981601141862173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18439173981284269711632461 6914690242981601141862173)
              ·
                refine ⟨2593008841118100428198315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6914690242981601141862173 2593008841118100428198315)
                ·
                  refine ⟨3889513261677150642297473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593008841118100428198315 3889513261677150642297473)
                  ·
                    refine ⟨2917134946257862981723105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3889513261677150642297473 2917134946257862981723105)
                    ·
                      refine ⟨2187851209693397236292329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917134946257862981723105 2187851209693397236292329)
                      ·
                        rfl

theorem cell23_4260825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_4260825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260825 prefixEnd_4260825 := by exact prefixLift 4260825
  have htrace : WordTrace (prefixWord ++ tailWord_4260825) baseStart_4260825 baseEnd_4260825 := by
    simpa [prefixWord, tailWord_4260825, baseEnd_4260825] using wordTrace_append hprefix tailTrace_4260825
  have hstable : (prefixWord ++ tailWord_4260825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260825).length < 2 ^ (prefixWord ++ tailWord_4260825).sum := by decide
  have hdescent : baseEnd_4260825 < baseStart_4260825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260842 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_4260842 : Nat := 118140960795 + 4260842 * 2 ^ 59
def prefixEnd_4260842 : Nat := 4983230072969 + 3 ^ 40 * 4260842 * 2
def baseEnd_4260842 : Nat := 2187859938864523669779751

theorem tailTrace_4260842 : CollatzResearch.WordTrace tailWord_4260842 prefixEnd_4260842 2187859938864523669779751 := by
  unfold tailWord_4260842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38851418707426150681010195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103603783219803068482693853 38851418707426150681010195)
  ·
    refine ⟨58277128061139226021515293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38851418707426150681010195 58277128061139226021515293)
    ·
      refine ⟨21853923022927209758068235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58277128061139226021515293 21853923022927209758068235)
      ·
        refine ⟨32780884534390814637102353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21853923022927209758068235 32780884534390814637102353)
        ·
          refine ⟨24585663400793110977826765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32780884534390814637102353 24585663400793110977826765)
          ·
            refine ⟨9219623775297416616685037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24585663400793110977826765 9219623775297416616685037)
            ·
              refine ⟨3457358915736531231256889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9219623775297416616685037 3457358915736531231256889)
              ·
                refine ⟨2593019186802398423442667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3457358915736531231256889 2593019186802398423442667)
                ·
                  refine ⟨3889528780203597635164001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593019186802398423442667 3889528780203597635164001)
                  ·
                    refine ⟨2917146585152698226373001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3889528780203597635164001 2917146585152698226373001)
                    ·
                      refine ⟨2187859938864523669779751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917146585152698226373001 2187859938864523669779751)
                      ·
                        rfl

theorem cell23_4260842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_4260842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260842 prefixEnd_4260842 := by exact prefixLift 4260842
  have htrace : WordTrace (prefixWord ++ tailWord_4260842) baseStart_4260842 baseEnd_4260842 := by
    simpa [prefixWord, tailWord_4260842, baseEnd_4260842] using wordTrace_append hprefix tailTrace_4260842
  have hstable : (prefixWord ++ tailWord_4260842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260842).length < 2 ^ (prefixWord ++ tailWord_4260842).sum := by decide
  have hdescent : baseEnd_4260842 < baseStart_4260842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260857 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_4260857 : Nat := 118140960795 + 4260857 * 2 ^ 59
def prefixEnd_4260857 : Nat := 4983230072969 + 3 ^ 40 * 4260857 * 2
def baseEnd_4260857 : Nat := 729289213691447037030727

theorem tailTrace_4260857 : CollatzResearch.WordTrace tailWord_4260857 prefixEnd_4260857 729289213691447037030727 := by
  unfold tailWord_4260857
  simp only [CollatzResearch.WordTrace]
  refine ⟨155406221924650260285836825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103604147949766840190557883 155406221924650260285836825)
  ·
    refine ⟨116554666443487695214377619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155406221924650260285836825 116554666443487695214377619)
    ·
      refine ⟨174831999665231542821566429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116554666443487695214377619 174831999665231542821566429)
      ·
        refine ⟨65561999874461828558087411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174831999665231542821566429 65561999874461828558087411)
        ·
          refine ⟨98342999811692742837131117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65561999874461828558087411 98342999811692742837131117)
          ·
            refine ⟨36878624929384778563924169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98342999811692742837131117 36878624929384778563924169)
            ·
              refine ⟨27658968697038583922943127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36878624929384778563924169 27658968697038583922943127)
              ·
                refine ⟨41488453045557875884414691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27658968697038583922943127 41488453045557875884414691)
                ·
                  refine ⟨62232679568336813826622037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41488453045557875884414691 62232679568336813826622037)
                  ·
                    refine ⟨729289213691447037030727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62232679568336813826622037 729289213691447037030727)
                    ·
                      rfl

theorem cell23_4260857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_4260857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260857 prefixEnd_4260857 := by exact prefixLift 4260857
  have htrace : WordTrace (prefixWord ++ tailWord_4260857) baseStart_4260857 baseEnd_4260857 := by
    simpa [prefixWord, tailWord_4260857, baseEnd_4260857] using wordTrace_append hprefix tailTrace_4260857
  have hstable : (prefixWord ++ tailWord_4260857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260857).length < 2 ^ (prefixWord ++ tailWord_4260857).sum := by decide
  have hdescent : baseEnd_4260857 < baseStart_4260857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260862 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4260862 : Nat := 118140960795 + 4260862 * 2 ^ 59
def prefixEnd_4260862 : Nat := 4983230072969 + 3 ^ 40 * 4260862 * 2
def baseEnd_4260862 : Nat := 2187870208477613591529659

theorem tailTrace_4260862 : CollatzResearch.WordTrace tailWord_4260862 prefixEnd_4260862 2187870208477613591529659 := by
  unfold tailWord_4260862
  simp only [CollatzResearch.WordTrace]
  refine ⟨19425800536204018267471105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103604269526421430759845893 19425800536204018267471105)
  ·
    refine ⟨14569350402153013700603329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19425800536204018267471105 14569350402153013700603329)
    ·
      refine ⟨10927012801614760275452497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14569350402153013700603329 10927012801614760275452497)
      ·
        refine ⟨8195259601211070206589373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10927012801614760275452497 8195259601211070206589373)
        ·
          refine ⟨3073222350454151327471015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8195259601211070206589373 3073222350454151327471015)
          ·
            refine ⟨4609833525681226991206523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073222350454151327471015 4609833525681226991206523)
            ·
              refine ⟨6914750288521840486809785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609833525681226991206523 6914750288521840486809785)
              ·
                refine ⟨5186062716391380365107339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914750288521840486809785 5186062716391380365107339)
                ·
                  refine ⟨7779094074587070547661009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186062716391380365107339 7779094074587070547661009)
                  ·
                    refine ⟨5834320555940302910745757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7779094074587070547661009 5834320555940302910745757)
                    ·
                      refine ⟨2187870208477613591529659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5834320555940302910745757 2187870208477613591529659)
                      ·
                        rfl

theorem cell23_4260862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4260862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260862 prefixEnd_4260862 := by exact prefixLift 4260862
  have htrace : WordTrace (prefixWord ++ tailWord_4260862) baseStart_4260862 baseEnd_4260862 := by
    simpa [prefixWord, tailWord_4260862, baseEnd_4260862] using wordTrace_append hprefix tailTrace_4260862
  have hstable : (prefixWord ++ tailWord_4260862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260862).length < 2 ^ (prefixWord ++ tailWord_4260862).sum := by decide
  have hdescent : baseEnd_4260862 < baseStart_4260862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260881 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_4260881 : Nat := 118140960795 + 4260881 * 2 ^ 59
def prefixEnd_4260881 : Nat := 4983230072969 + 3 ^ 40 * 4260881 * 2
def baseEnd_4260881 : Nat := 2187879964610049017192071

theorem tailTrace_4260881 : CollatzResearch.WordTrace tailWord_4260881 prefixEnd_4260881 2187879964610049017192071 := by
  unfold tailWord_4260881
  simp only [CollatzResearch.WordTrace]
  refine ⟨155407097276563312384710497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103604731517708874923140331 155407097276563312384710497)
  ·
    refine ⟨116555322957422484288532873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155407097276563312384710497 116555322957422484288532873)
    ·
      refine ⟨87416492218066863216399655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116555322957422484288532873 87416492218066863216399655)
      ·
        refine ⟨131124738327100294824599483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87416492218066863216399655 131124738327100294824599483)
        ·
          refine ⟨196687107490650442236899225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131124738327100294824599483 196687107490650442236899225)
          ·
            refine ⟨147515330617987831677674419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196687107490650442236899225 147515330617987831677674419)
            ·
              refine ⟨221272995926981747516511629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147515330617987831677674419 221272995926981747516511629)
              ·
                refine ⟨82977373472618155318691861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221272995926981747516511629 82977373472618155318691861)
                ·
                  refine ⟨3889564381528976030563681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82977373472618155318691861 3889564381528976030563681)
                  ·
                    refine ⟨2917173286146732022922761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3889564381528976030563681 2917173286146732022922761)
                    ·
                      refine ⟨2187879964610049017192071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917173286146732022922761 2187879964610049017192071)
                      ·
                        rfl

theorem cell23_4260881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_4260881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260881 prefixEnd_4260881 := by exact prefixLift 4260881
  have htrace : WordTrace (prefixWord ++ tailWord_4260881) baseStart_4260881 baseEnd_4260881 := by
    simpa [prefixWord, tailWord_4260881, baseEnd_4260881] using wordTrace_append hprefix tailTrace_4260881
  have hstable : (prefixWord ++ tailWord_4260881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260881).length < 2 ^ (prefixWord ++ tailWord_4260881).sum := by decide
  have hdescent : baseEnd_4260881 < baseStart_4260881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4260885 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_4260885 : Nat := 118140960795 + 4260885 * 2 ^ 59
def prefixEnd_4260885 : Nat := 4983230072969 + 3 ^ 40 * 4260885 * 2
def baseEnd_4260885 : Nat := 2187882018532667001542053

theorem tailTrace_4260885 : CollatzResearch.WordTrace tailWord_4260885 prefixEnd_4260885 2187882018532667001542053 := by
  unfold tailWord_4260885
  simp only [CollatzResearch.WordTrace]
  refine ⟨155407243168548821067856109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103604828779032547378570739 155407243168548821067856109)
  ·
    refine ⟨58277716188205807900446041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155407243168548821067856109 58277716188205807900446041)
    ·
      refine ⟨43708287141154355925334531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58277716188205807900446041 43708287141154355925334531)
      ·
        refine ⟨65562430711731533888001797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43708287141154355925334531 65562430711731533888001797)
        ·
          refine ⟨12292955758449662604000337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65562430711731533888001797 12292955758449662604000337)
          ·
            refine ⟨9219716818837246953000253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12292955758449662604000337 9219716818837246953000253)
            ·
              refine ⟨3457393807063967607375095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9219716818837246953000253 3457393807063967607375095)
              ·
                refine ⟨5186090710595951411062643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457393807063967607375095 5186090710595951411062643)
                ·
                  refine ⟨7779136065893927116593965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186090710595951411062643 7779136065893927116593965)
                  ·
                    refine ⟨2917176024710222668722737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7779136065893927116593965 2917176024710222668722737)
                    ·
                      refine ⟨2187882018532667001542053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917176024710222668722737 2187882018532667001542053)
                      ·
                        rfl

theorem cell23_4260885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_4260885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4260885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4260885 prefixEnd_4260885 := by exact prefixLift 4260885
  have htrace : WordTrace (prefixWord ++ tailWord_4260885) baseStart_4260885 baseEnd_4260885 := by
    simpa [prefixWord, tailWord_4260885, baseEnd_4260885] using wordTrace_append hprefix tailTrace_4260885
  have hstable : (prefixWord ++ tailWord_4260885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4260885).length < 2 ^ (prefixWord ++ tailWord_4260885).sum := by decide
  have hdescent : baseEnd_4260885 < baseStart_4260885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4260885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261028 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 6]
def baseStart_4261028 : Nat := 118140960795 + 4261028 * 2 ^ 59
def prefixEnd_4261028 : Nat := 4983230072969 + 3 ^ 40 * 4261028 * 2
def baseEnd_4261028 : Nat := 243106160696251104672655

theorem tailTrace_4261028 : CollatzResearch.WordTrace tailWord_4261028 prefixEnd_4261028 243106160696251104672655 := by
  unfold tailWord_4261028
  simp only [CollatzResearch.WordTrace]
  refine ⟨77706229403515378245155869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103608305871353837660207825 77706229403515378245155869)
  ·
    refine ⟨29139836026318266841933451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77706229403515378245155869 29139836026318266841933451)
    ·
      refine ⟨43709754039477400262900177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29139836026318266841933451 43709754039477400262900177)
      ·
        refine ⟨32782315529608050197175133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43709754039477400262900177 32782315529608050197175133)
        ·
          refine ⟨12293368323603018823940675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32782315529608050197175133 12293368323603018823940675)
          ·
            refine ⟨18440052485404528235911013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12293368323603018823940675 18440052485404528235911013)
            ·
              refine ⟨3457509841013349044233315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18440052485404528235911013 3457509841013349044233315)
              ·
                refine ⟨5186264761520023566349973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457509841013349044233315 5186264761520023566349973)
                ·
                  refine ⟨243106160696251104672655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5186264761520023566349973 243106160696251104672655)
                  ·
                    rfl

theorem cell23_4261028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_4261028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261028 prefixEnd_4261028 := by exact prefixLift 4261028
  have htrace : WordTrace (prefixWord ++ tailWord_4261028) baseStart_4261028 baseEnd_4261028 := by
    simpa [prefixWord, tailWord_4261028, baseEnd_4261028] using wordTrace_append hprefix tailTrace_4261028
  have hstable : (prefixWord ++ tailWord_4261028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261028).length < 2 ^ (prefixWord ++ tailWord_4261028).sum := by decide
  have hdescent : baseEnd_4261028 < baseStart_4261028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261088 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_4261088 : Nat := 118140960795 + 4261088 * 2 ^ 59
def prefixEnd_4261088 : Nat := 4983230072969 + 3 ^ 40 * 4261088 * 2
def baseEnd_4261088 : Nat := 729328751701843235767873

theorem tailTrace_4261088 : CollatzResearch.WordTrace tailWord_4261088 prefixEnd_4261088 729328751701843235767873 := by
  unfold tailWord_4261088
  simp only [CollatzResearch.WordTrace]
  refine ⟨77707323593406693368747959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103609764791208924491663945 77707323593406693368747959)
  ·
    refine ⟨116560985390110040053121939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77707323593406693368747959 116560985390110040053121939)
    ·
      refine ⟨174841478085165060079682909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116560985390110040053121939 174841478085165060079682909)
      ·
        refine ⟨65565554281936897529881091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174841478085165060079682909 65565554281936897529881091)
        ·
          refine ⟨98348331422905346294821637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65565554281936897529881091 98348331422905346294821637)
          ·
            refine ⟨18440312141794752430279057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98348331422905346294821637 18440312141794752430279057)
            ·
              refine ⟨13830234106346064322709293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18440312141794752430279057 13830234106346064322709293)
              ·
                refine ⟨5186337789879774121015985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13830234106346064322709293 5186337789879774121015985)
                ·
                  refine ⟨3889753342409830590761989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5186337789879774121015985 3889753342409830590761989)
                  ·
                    refine ⟨729328751701843235767873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3889753342409830590761989 729328751701843235767873)
                    ·
                      rfl

theorem cell23_4261088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_4261088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261088 prefixEnd_4261088 := by exact prefixLift 4261088
  have htrace : WordTrace (prefixWord ++ tailWord_4261088) baseStart_4261088 baseEnd_4261088 := by
    simpa [prefixWord, tailWord_4261088, baseEnd_4261088] using wordTrace_append hprefix tailTrace_4261088
  have hstable : (prefixWord ++ tailWord_4261088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261088).length < 2 ^ (prefixWord ++ tailWord_4261088).sum := by decide
  have hdescent : baseEnd_4261088 < baseStart_4261088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261098 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_4261098 : Nat := 118140960795 + 4261098 * 2 ^ 59
def prefixEnd_4261098 : Nat := 4983230072969 + 3 ^ 40 * 4261098 * 2
def baseEnd_4261098 : Nat := 2187991389912074668178573

theorem tailTrace_4261098 : CollatzResearch.WordTrace tailWord_4261098 prefixEnd_4261098 2187991389912074668178573 := by
  unfold tailWord_4261098
  simp only [CollatzResearch.WordTrace]
  refine ⟨38853752979194289611339987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103610007944518105630239965 38853752979194289611339987)
  ·
    refine ⟨58280629468791434417009981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38853752979194289611339987 58280629468791434417009981)
    ·
      refine ⟨21855236050796787906378743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58280629468791434417009981 21855236050796787906378743)
      ·
        refine ⟨32782854076195181859568115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21855236050796787906378743 32782854076195181859568115)
        ·
          refine ⟨49174281114292772789352173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32782854076195181859568115 49174281114292772789352173)
          ·
            refine ⟨18440355417859789796007065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49174281114292772789352173 18440355417859789796007065)
            ·
              refine ⟨13830266563394842347005299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18440355417859789796007065 13830266563394842347005299)
              ·
                refine ⟨20745399845092263520507949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13830266563394842347005299 20745399845092263520507949)
                ·
                  refine ⟨7779524941909598820190481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20745399845092263520507949 7779524941909598820190481)
                  ·
                    refine ⟨5834643706432199115142861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7779524941909598820190481 5834643706432199115142861)
                    ·
                      refine ⟨2187991389912074668178573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5834643706432199115142861 2187991389912074668178573)
                      ·
                        rfl

theorem cell23_4261098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_4261098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261098 prefixEnd_4261098 := by exact prefixLift 4261098
  have htrace : WordTrace (prefixWord ++ tailWord_4261098) baseStart_4261098 baseEnd_4261098 := by
    simpa [prefixWord, tailWord_4261098, baseEnd_4261098] using wordTrace_append hprefix tailTrace_4261098
  have hstable : (prefixWord ++ tailWord_4261098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261098).length < 2 ^ (prefixWord ++ tailWord_4261098).sum := by decide
  have hdescent : baseEnd_4261098 < baseStart_4261098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261155 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 1, 3, 2]
def baseStart_4261155 : Nat := 118140960795 + 4261155 * 2 ^ 59
def prefixEnd_4261155 : Nat := 4983230072969 + 3 ^ 40 * 4261155 * 2
def baseEnd_4261155 : Nat := 2188020658309380945165811

theorem tailTrace_4261155 : CollatzResearch.WordTrace tailWord_4261155 prefixEnd_4261155 2188020658309380945165811 := by
  unfold tailWord_4261155
  simp only [CollatzResearch.WordTrace]
  refine ⟨155417090877570657180184919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103611393918380438120123279 155417090877570657180184919)
  ·
    refine ⟨233125636316355985770277379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155417090877570657180184919 233125636316355985770277379)
    ·
      refine ⟨349688454474533978655416069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233125636316355985770277379 349688454474533978655416069)
      ·
        refine ⟨65566585213975120997890513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 349688454474533978655416069 65566585213975120997890513)
        ·
          refine ⟨49174938910481340748417885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65566585213975120997890513 49174938910481340748417885)
          ·
            refine ⟨18440602091430502780656707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49174938910481340748417885 18440602091430502780656707)
            ·
              refine ⟨27660903137145754170985061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18440602091430502780656707 27660903137145754170985061)
              ·
                refine ⟨5186419338214828907059699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27660903137145754170985061 5186419338214828907059699)
                ·
                  refine ⟨7779629007322243360589549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186419338214828907059699 7779629007322243360589549)
                  ·
                    refine ⟨2917360877745841260221081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7779629007322243360589549 2917360877745841260221081)
                    ·
                      refine ⟨2188020658309380945165811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917360877745841260221081 2188020658309380945165811)
                      ·
                        rfl

theorem cell23_4261155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_4261155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261155 prefixEnd_4261155 := by exact prefixLift 4261155
  have htrace : WordTrace (prefixWord ++ tailWord_4261155) baseStart_4261155 baseEnd_4261155 := by
    simpa [prefixWord, tailWord_4261155, baseEnd_4261155] using wordTrace_append hprefix tailTrace_4261155
  have hstable : (prefixWord ++ tailWord_4261155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261155).length < 2 ^ (prefixWord ++ tailWord_4261155).sum := by decide
  have hdescent : baseEnd_4261155 < baseStart_4261155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261168 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2]
def baseStart_4261168 : Nat := 118140960795 + 4261168 * 2 ^ 59
def prefixEnd_4261168 : Nat := 4983230072969 + 3 ^ 40 * 4261168 * 2
def baseEnd_4261168 : Nat := 2188027333557889394303251

theorem tailTrace_4261168 : CollatzResearch.WordTrace tailWord_4261168 prefixEnd_4261168 2188027333557889394303251 := by
  unfold tailWord_4261168
  simp only [CollatzResearch.WordTrace]
  refine ⟨77708782513261780200204079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103611710017682373600272105 77708782513261780200204079)
  ·
    refine ⟨116563173769892670300306119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77708782513261780200204079 116563173769892670300306119)
    ·
      refine ⟨174844760654839005450459179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116563173769892670300306119 174844760654839005450459179)
      ·
        refine ⟨262267140982258508175688769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174844760654839005450459179 262267140982258508175688769)
        ·
          refine ⟨196700355736693881131766577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262267140982258508175688769 196700355736693881131766577)
          ·
            refine ⟨147525266802520410848824933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196700355736693881131766577 147525266802520410848824933)
            ·
              refine ⟨27660987525472577034154675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147525266802520410848824933 27660987525472577034154675)
              ·
                refine ⟨41491481288208865551232013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27660987525472577034154675 41491481288208865551232013)
                ·
                  refine ⟨15559305483078324581712005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41491481288208865551232013 15559305483078324581712005)
                  ·
                    refine ⟨2917369778077185859071001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15559305483078324581712005 2917369778077185859071001)
                    ·
                      refine ⟨2188027333557889394303251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917369778077185859071001 2188027333557889394303251)
                      ·
                        rfl

theorem cell23_4261168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2].length) (baseStart_4261168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261168 prefixEnd_4261168 := by exact prefixLift 4261168
  have htrace : WordTrace (prefixWord ++ tailWord_4261168) baseStart_4261168 baseEnd_4261168 := by
    simpa [prefixWord, tailWord_4261168, baseEnd_4261168] using wordTrace_append hprefix tailTrace_4261168
  have hstable : (prefixWord ++ tailWord_4261168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261168).length < 2 ^ (prefixWord ++ tailWord_4261168).sum := by decide
  have hdescent : baseEnd_4261168 < baseStart_4261168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261171 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_4261171 : Nat := 118140960795 + 4261171 * 2 ^ 59
def prefixEnd_4261171 : Nat := 4983230072969 + 3 ^ 40 * 4261171 * 2
def baseEnd_4261171 : Nat := 2188028873999852882565737

theorem tailTrace_4261171 : CollatzResearch.WordTrace tailWord_4261171 prefixEnd_4261171 2188028873999852882565737 := by
  unfold tailWord_4261171
  simp only [CollatzResearch.WordTrace]
  refine ⟨155417674445512691912767367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103611782963675127941844911 155417674445512691912767367)
  ·
    refine ⟨233126511668269037869151051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155417674445512691912767367 233126511668269037869151051)
    ·
      refine ⟨349689767502403556803726577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233126511668269037869151051 349689767502403556803726577)
      ·
        refine ⟨262267325626802667602794933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349689767502403556803726577 262267325626802667602794933)
        ·
          refine ⟨24587561777512750087762025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 262267325626802667602794933 24587561777512750087762025)
          ·
            refine ⟨18440671333134562565821519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24587561777512750087762025 18440671333134562565821519)
            ·
              refine ⟨27661006999701843848732279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18440671333134562565821519 27661006999701843848732279)
              ·
                refine ⟨41491510499552765773098419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27661006999701843848732279 41491510499552765773098419)
                ·
                  refine ⟨62237265749329148659647629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41491510499552765773098419 62237265749329148659647629)
                  ·
                    refine ⟨23338974655998430747367861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62237265749329148659647629 23338974655998430747367861)
                    ·
                      refine ⟨2188028873999852882565737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23338974655998430747367861 2188028873999852882565737)
                      ·
                        rfl

theorem cell23_4261171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_4261171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261171 prefixEnd_4261171 := by exact prefixLift 4261171
  have htrace : WordTrace (prefixWord ++ tailWord_4261171) baseStart_4261171 baseEnd_4261171 := by
    simpa [prefixWord, tailWord_4261171, baseEnd_4261171] using wordTrace_append hprefix tailTrace_4261171
  have hstable : (prefixWord ++ tailWord_4261171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261171).length < 2 ^ (prefixWord ++ tailWord_4261171).sum := by decide
  have hdescent : baseEnd_4261171 < baseStart_4261171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261172 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4261172 : Nat := 118140960795 + 4261172 * 2 ^ 59
def prefixEnd_4261172 : Nat := 4983230072969 + 3 ^ 40 * 4261172 * 2
def baseEnd_4261172 : Nat := 2188029387480507378653233

theorem tailTrace_4261172 : CollatzResearch.WordTrace tailWord_4261172 prefixEnd_4261172 2188029387480507378653233 := by
  unfold tailWord_4261172
  simp only [CollatzResearch.WordTrace]
  refine ⟨77708855459254534541776885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103611807279006046055702513 77708855459254534541776885)
  ·
    refine ⟨7285205199305112613291583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77708855459254534541776885 7285205199305112613291583)
    ·
      refine ⟨10927807798957668919937375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285205199305112613291583 10927807798957668919937375)
      ·
        refine ⟨16391711698436503379906063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10927807798957668919937375 16391711698436503379906063)
        ·
          refine ⟨24587567547654755069859095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16391711698436503379906063 24587567547654755069859095)
          ·
            refine ⟨36881351321482132604788643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24587567547654755069859095 36881351321482132604788643)
            ·
              refine ⟨55322026982223198907182965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36881351321482132604788643 55322026982223198907182965)
              ·
                refine ⟨5186440029583424897548403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55322026982223198907182965 5186440029583424897548403)
                ·
                  refine ⟨7779660044375137346322605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186440029583424897548403 7779660044375137346322605)
                  ·
                    refine ⟨2917372516640676504870977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7779660044375137346322605 2917372516640676504870977)
                    ·
                      refine ⟨2188029387480507378653233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917372516640676504870977 2188029387480507378653233)
                      ·
                        rfl

theorem cell23_4261172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4261172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261172 prefixEnd_4261172 := by exact prefixLift 4261172
  have htrace : WordTrace (prefixWord ++ tailWord_4261172) baseStart_4261172 baseEnd_4261172 := by
    simpa [prefixWord, tailWord_4261172, baseEnd_4261172] using wordTrace_append hprefix tailTrace_4261172
  have hstable : (prefixWord ++ tailWord_4261172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261172).length < 2 ^ (prefixWord ++ tailWord_4261172).sum := by decide
  have hdescent : baseEnd_4261172 < baseStart_4261172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261231 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_4261231 : Nat := 118140960795 + 4261231 * 2 ^ 59
def prefixEnd_4261231 : Nat := 4983230072969 + 3 ^ 40 * 4261231 * 2
def baseEnd_4261231 : Nat := 2188059682839122647815461

theorem tailTrace_4261231 : CollatzResearch.WordTrace tailWord_4261231 prefixEnd_4261231 2188059682839122647815461 := by
  unfold tailWord_4261231
  simp only [CollatzResearch.WordTrace]
  refine ⟨155419862825295322159951547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103613241883530214773301031 155419862825295322159951547)
  ·
    refine ⟨233129794237942983239927321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155419862825295322159951547 233129794237942983239927321)
    ·
      refine ⟨174847345678457237429945491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233129794237942983239927321 174847345678457237429945491)
      ·
        refine ⟨262271018517685856144918237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174847345678457237429945491 262271018517685856144918237)
        ·
          refine ⟨98351631944132196054344339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262271018517685856144918237 98351631944132196054344339)
          ·
            refine ⟨147527447916198294081516509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98351631944132196054344339 147527447916198294081516509)
            ·
              refine ⟨55322792968574360280568691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147527447916198294081516509 55322792968574360280568691)
              ·
                refine ⟨82984189452861540420853037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55322792968574360280568691 82984189452861540420853037)
                ·
                  refine ⟨31119071044823077657819889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82984189452861540420853037 31119071044823077657819889)
                  ·
                    refine ⟨23339303283617308243364917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31119071044823077657819889 23339303283617308243364917)
                    ·
                      refine ⟨2188059682839122647815461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23339303283617308243364917 2188059682839122647815461)
                      ·
                        rfl

theorem cell23_4261231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_4261231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261231 prefixEnd_4261231 := by exact prefixLift 4261231
  have htrace : WordTrace (prefixWord ++ tailWord_4261231) baseStart_4261231 baseEnd_4261231 := by
    simpa [prefixWord, tailWord_4261231, baseEnd_4261231] using wordTrace_append hprefix tailTrace_4261231
  have hstable : (prefixWord ++ tailWord_4261231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261231).length < 2 ^ (prefixWord ++ tailWord_4261231).sum := by decide
  have hdescent : baseEnd_4261231 < baseStart_4261231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261272 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_4261272 : Nat := 118140960795 + 4261272 * 2 ^ 59
def prefixEnd_4261272 : Nat := 4983230072969 + 3 ^ 40 * 4261272 * 2
def baseEnd_4261272 : Nat := 729360245181985662467591

theorem tailTrace_4261272 : CollatzResearch.WordTrace tailWord_4261272 prefixEnd_4261272 729360245181985662467591 := by
  unfold tailWord_4261272
  simp only [CollatzResearch.WordTrace]
  refine ⟨77710679109073393081097035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103614238812097857441462713 77710679109073393081097035)
  ·
    refine ⟨116566018663610089621645553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77710679109073393081097035 116566018663610089621645553)
    ·
      refine ⟨87424513997707567216234165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116566018663610089621645553 87424513997707567216234165)
      ·
        refine ⟨8196048187285084426521953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87424513997707567216234165 8196048187285084426521953)
        ·
          refine ⟨6147036140463813319891465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8196048187285084426521953 6147036140463813319891465)
          ·
            refine ⟨4610277105347859989918599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147036140463813319891465 4610277105347859989918599)
            ·
              refine ⟨6915415658021789984877899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610277105347859989918599 6915415658021789984877899)
              ·
                refine ⟨10373123487032684977316849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6915415658021789984877899 10373123487032684977316849)
                ·
                  refine ⟨7779842615274513732987637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10373123487032684977316849 7779842615274513732987637)
                  ·
                    refine ⟨729360245181985662467591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7779842615274513732987637 729360245181985662467591)
                    ·
                      rfl

theorem cell23_4261272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_4261272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261272 prefixEnd_4261272 := by exact prefixLift 4261272
  have htrace : WordTrace (prefixWord ++ tailWord_4261272) baseStart_4261272 baseEnd_4261272 := by
    simpa [prefixWord, tailWord_4261272, baseEnd_4261272] using wordTrace_append hprefix tailTrace_4261272
  have hstable : (prefixWord ++ tailWord_4261272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261272).length < 2 ^ (prefixWord ++ tailWord_4261272).sum := by decide
  have hdescent : baseEnd_4261272 < baseStart_4261272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261298 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_4261298 : Nat := 118140960795 + 4261298 * 2 ^ 59
def prefixEnd_4261298 : Nat := 4983230072969 + 3 ^ 40 * 4261298 * 2
def baseEnd_4261298 : Nat := 243121565115885987297517

theorem tailTrace_4261298 : CollatzResearch.WordTrace tailWord_4261298 prefixEnd_4261298 243121565115885987297517 := by
  unfold tailWord_4261298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38855576629013148150660137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103614871010701728401760365 38855576629013148150660137)
  ·
    refine ⟨29141682471759861112995103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38855576629013148150660137 29141682471759861112995103)
    ·
      refine ⟨43712523707639791669492655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29141682471759861112995103 43712523707639791669492655)
      ·
        refine ⟨65568785561459687504238983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43712523707639791669492655 65568785561459687504238983)
        ·
          refine ⟨98353178342189531256358475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65568785561459687504238983 98353178342189531256358475)
          ·
            refine ⟨147529767513284296884537713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98353178342189531256358475 147529767513284296884537713)
            ·
              refine ⟨110647325634963222663403285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147529767513284296884537713 110647325634963222663403285)
              ·
                refine ⟨5186593389138901062347029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110647325634963222663403285 5186593389138901062347029)
                ·
                  refine ⟨243121565115885987297517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5186593389138901062347029 243121565115885987297517)
                  ·
                    rfl

theorem cell23_4261298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_4261298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261298 prefixEnd_4261298 := by exact prefixLift 4261298
  have htrace : WordTrace (prefixWord ++ tailWord_4261298) baseStart_4261298 baseEnd_4261298 := by
    simpa [prefixWord, tailWord_4261298, baseEnd_4261298] using wordTrace_append hprefix tailTrace_4261298
  have hstable : (prefixWord ++ tailWord_4261298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261298).length < 2 ^ (prefixWord ++ tailWord_4261298).sum := by decide
  have hdescent : baseEnd_4261298 < baseStart_4261298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261335 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_4261335 : Nat := 118140960795 + 4261335 * 2 ^ 59
def prefixEnd_4261335 : Nat := 4983230072969 + 3 ^ 40 * 4261335 * 2
def baseEnd_4261335 : Nat := 2188113084827190240914983

theorem tailTrace_4261335 : CollatzResearch.WordTrace tailWord_4261335 prefixEnd_4261335 2188113084827190240914983 := by
  unfold tailWord_4261335
  simp only [CollatzResearch.WordTrace]
  refine ⟨155423656016918547921737459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103615770677945698614491639 155423656016918547921737459)
  ·
    refine ⟨233135484025377821882606189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155423656016918547921737459 233135484025377821882606189)
    ·
      refine ⟨87425806509516683205977321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233135484025377821882606189 87425806509516683205977321)
      ·
        refine ⟨65569354882137512404482991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87425806509516683205977321 65569354882137512404482991)
        ·
          refine ⟨98354032323206268606724487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65569354882137512404482991 98354032323206268606724487)
          ·
            refine ⟨147531048484809402910086731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98354032323206268606724487 147531048484809402910086731)
            ·
              refine ⟨221296572727214104365130097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147531048484809402910086731 221296572727214104365130097)
              ·
                refine ⟨165972429545410578273847573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221296572727214104365130097 165972429545410578273847573)
                ·
                  refine ⟨7779957634941120856586605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165972429545410578273847573 7779957634941120856586605)
                  ·
                    refine ⟨2917484113102920321219977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7779957634941120856586605 2917484113102920321219977)
                    ·
                      refine ⟨2188113084827190240914983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917484113102920321219977 2188113084827190240914983)
                      ·
                        rfl

theorem cell23_4261335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_4261335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261335 prefixEnd_4261335 := by exact prefixLift 4261335
  have htrace : WordTrace (prefixWord ++ tailWord_4261335) baseStart_4261335 baseEnd_4261335 := by
    simpa [prefixWord, tailWord_4261335, baseEnd_4261335] using wordTrace_append hprefix tailTrace_4261335
  have hstable : (prefixWord ++ tailWord_4261335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261335).length < 2 ^ (prefixWord ++ tailWord_4261335).sum := by decide
  have hdescent : baseEnd_4261335 < baseStart_4261335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261345 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_4261345 : Nat := 118140960795 + 4261345 * 2 ^ 59
def prefixEnd_4261345 : Nat := 4983230072969 + 3 ^ 40 * 4261345 * 2
def baseEnd_4261345 : Nat := 729372739877911733929979

theorem tailTrace_4261345 : CollatzResearch.WordTrace tailWord_4261345 prefixEnd_4261345 729372739877911733929979 := by
  unfold tailWord_4261345
  simp only [CollatzResearch.WordTrace]
  refine ⟨155424020746882319629601489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103616013831254879753067659 155424020746882319629601489)
  ·
    refine ⟨116568015560161739722201117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155424020746882319629601489 116568015560161739722201117)
    ·
      refine ⟨43713005835060652395825419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116568015560161739722201117 43713005835060652395825419)
      ·
        refine ⟨65569508752590978593738129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43713005835060652395825419 65569508752590978593738129)
        ·
          refine ⟨49177131564443233945303597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65569508752590978593738129 49177131564443233945303597)
          ·
            refine ⟨18441424336666212729488849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49177131564443233945303597 18441424336666212729488849)
            ·
              refine ⟨13831068252499659547116637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18441424336666212729488849 13831068252499659547116637)
              ·
                refine ⟨5186650594687372330168739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13831068252499659547116637 5186650594687372330168739)
                ·
                  refine ⟨7779975892031058495253109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186650594687372330168739 7779975892031058495253109)
                  ·
                    refine ⟨729372739877911733929979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7779975892031058495253109 729372739877911733929979)
                    ·
                      rfl

theorem cell23_4261345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_4261345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261345 prefixEnd_4261345 := by exact prefixLift 4261345
  have htrace : WordTrace (prefixWord ++ tailWord_4261345) baseStart_4261345 baseEnd_4261345 := by
    simpa [prefixWord, tailWord_4261345, baseEnd_4261345] using wordTrace_append hprefix tailTrace_4261345
  have hstable : (prefixWord ++ tailWord_4261345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261345).length < 2 ^ (prefixWord ++ tailWord_4261345).sum := by decide
  have hdescent : baseEnd_4261345 < baseStart_4261345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261352 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4261352 : Nat := 118140960795 + 4261352 * 2 ^ 59
def prefixEnd_4261352 : Nat := 4983230072969 + 3 ^ 40 * 4261352 * 2
def baseEnd_4261352 : Nat := 2188121813998316674402405

theorem tailTrace_4261352 : CollatzResearch.WordTrace tailWord_4261352 prefixEnd_4261352 2188121813998316674402405 := by
  unfold tailWord_4261352
  simp only [CollatzResearch.WordTrace]
  refine ⟨77712138028928479912553155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103616184038571306550070873 77712138028928479912553155)
  ·
    refine ⟨116568207043392719868829733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77712138028928479912553155 116568207043392719868829733)
    ·
      refine ⟨21856538820636134975405575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116568207043392719868829733 21856538820636134975405575)
      ·
        refine ⟨32784808230954202463108363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21856538820636134975405575 32784808230954202463108363)
        ·
          refine ⟨49177212346431303694662545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32784808230954202463108363 49177212346431303694662545)
          ·
            refine ⟨36882909259823477770996909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49177212346431303694662545 36882909259823477770996909)
            ·
              refine ⟨13831090972433804164123841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36882909259823477770996909 13831090972433804164123841)
              ·
                refine ⟨10373318229325353123092881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13831090972433804164123841 10373318229325353123092881)
                ·
                  refine ⟨7779988671994014842319661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10373318229325353123092881 7779988671994014842319661)
                  ·
                    refine ⟨2917495751997755565869873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7779988671994014842319661 2917495751997755565869873)
                    ·
                      refine ⟨2188121813998316674402405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917495751997755565869873 2188121813998316674402405)
                      ·
                        rfl

theorem cell23_4261352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4261352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261352 prefixEnd_4261352 := by exact prefixLift 4261352
  have htrace : WordTrace (prefixWord ++ tailWord_4261352) baseStart_4261352 baseEnd_4261352 := by
    simpa [prefixWord, tailWord_4261352, baseEnd_4261352] using wordTrace_append hprefix tailTrace_4261352
  have hstable : (prefixWord ++ tailWord_4261352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261352).length < 2 ^ (prefixWord ++ tailWord_4261352).sum := by decide
  have hdescent : baseEnd_4261352 < baseStart_4261352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261385 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_4261385 : Nat := 118140960795 + 4261385 * 2 ^ 59
def prefixEnd_4261385 : Nat := 4983230072969 + 3 ^ 40 * 4261385 * 2
def baseEnd_4261385 : Nat := 2188138758859915045289753

theorem tailTrace_4261385 : CollatzResearch.WordTrace tailWord_4261385 prefixEnd_4261385 2188138758859915045289753 := by
  unfold tailWord_4261385
  simp only [CollatzResearch.WordTrace]
  refine ⟨155425479666737406461057609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103616986444491604307371739 155425479666737406461057609)
  ·
    refine ⟨116569109750053054845793207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155425479666737406461057609 116569109750053054845793207)
    ·
      refine ⟨174853664625079582268689811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116569109750053054845793207 174853664625079582268689811)
      ·
        refine ⟨262280496937619373403034717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174853664625079582268689811 262280496937619373403034717)
        ·
          refine ⟨98355186351607265026138019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262280496937619373403034717 98355186351607265026138019)
          ·
            refine ⟨147532779527410897539207029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98355186351607265026138019 147532779527410897539207029)
            ·
              refine ⟨13831198080694771644300659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147532779527410897539207029 13831198080694771644300659)
              ·
                refine ⟨20746797121042157466450989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13831198080694771644300659 20746797121042157466450989)
                ·
                  refine ⟨7780048920390809049919121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20746797121042157466450989 7780048920390809049919121)
                  ·
                    refine ⟨5835036690293106787439341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7780048920390809049919121 5835036690293106787439341)
                    ·
                      refine ⟨2188138758859915045289753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5835036690293106787439341 2188138758859915045289753)
                      ·
                        rfl

theorem cell23_4261385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_4261385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261385 prefixEnd_4261385 := by exact prefixLift 4261385
  have htrace : WordTrace (prefixWord ++ tailWord_4261385) baseStart_4261385 baseEnd_4261385 := by
    simpa [prefixWord, tailWord_4261385, baseEnd_4261385] using wordTrace_append hprefix tailTrace_4261385
  have hstable : (prefixWord ++ tailWord_4261385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261385).length < 2 ^ (prefixWord ++ tailWord_4261385).sum := by decide
  have hdescent : baseEnd_4261385 < baseStart_4261385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261395 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4]
def baseStart_4261395 : Nat := 118140960795 + 4261395 * 2 ^ 59
def prefixEnd_4261395 : Nat := 4983230072969 + 3 ^ 40 * 4261395 * 2
def baseEnd_4261395 : Nat := 2188143893666460006164707

theorem tailTrace_4261395 : CollatzResearch.WordTrace tailWord_4261395 prefixEnd_4261395 2188143893666460006164707 := by
  unfold tailWord_4261395
  simp only [CollatzResearch.WordTrace]
  refine ⟨155425844396701178168921639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103617229597800785445947759 155425844396701178168921639)
  ·
    refine ⟨233138766595051767253382459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155425844396701178168921639 233138766595051767253382459)
    ·
      refine ⟨349708149892577650880073689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233138766595051767253382459 349708149892577650880073689)
      ·
        refine ⟨262281112419433238160055267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349708149892577650880073689 262281112419433238160055267)
        ·
          refine ⟨393421668629149857240082901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262281112419433238160055267 393421668629149857240082901)
          ·
            refine ⟨9220820358495699779064443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 393421668629149857240082901 9220820358495699779064443)
            ·
              refine ⟨13831230537743549668596665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9220820358495699779064443 13831230537743549668596665)
              ·
                refine ⟨10373422903307662251447499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13831230537743549668596665 10373422903307662251447499)
                ·
                  refine ⟨15560134354961493377171249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10373422903307662251447499 15560134354961493377171249)
                  ·
                    refine ⟨11670100766221120032878437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15560134354961493377171249 11670100766221120032878437)
                    ·
                      refine ⟨2188143893666460006164707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11670100766221120032878437 2188143893666460006164707)
                      ·
                        rfl

theorem cell23_4261395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_4261395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261395 prefixEnd_4261395 := by exact prefixLift 4261395
  have htrace : WordTrace (prefixWord ++ tailWord_4261395) baseStart_4261395 baseEnd_4261395 := by
    simpa [prefixWord, tailWord_4261395, baseEnd_4261395] using wordTrace_append hprefix tailTrace_4261395
  have hstable : (prefixWord ++ tailWord_4261395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261395).length < 2 ^ (prefixWord ++ tailWord_4261395).sum := by decide
  have hdescent : baseEnd_4261395 < baseStart_4261395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261396 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4261396 : Nat := 118140960795 + 4261396 * 2 ^ 59
def prefixEnd_4261396 : Nat := 4983230072969 + 3 ^ 40 * 4261396 * 2
def baseEnd_4261396 : Nat := 729381469049038167417401

theorem tailTrace_4261396 : CollatzResearch.WordTrace tailWord_4261396 prefixEnd_4261396 729381469049038167417401 := by
  unfold tailWord_4261396
  simp only [CollatzResearch.WordTrace]
  refine ⟨77712940434848777669854021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103617253913131703559805361 77712940434848777669854021)
  ·
    refine ⟨14571176331534145813097629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77712940434848777669854021 14571176331534145813097629)
    ·
      refine ⟨5464191124325304679911611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14571176331534145813097629 5464191124325304679911611)
      ·
        refine ⟨8196286686487957019867417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464191124325304679911611 8196286686487957019867417)
        ·
          refine ⟨6147215014865967764900563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8196286686487957019867417 6147215014865967764900563)
          ·
            refine ⟨9220822522298951647350845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147215014865967764900563 9220822522298951647350845)
            ·
              refine ⟨3457808445862106867756567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9220822522298951647350845 3457808445862106867756567)
              ·
                refine ⟨5186712668793160301634851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457808445862106867756567 5186712668793160301634851)
                ·
                  refine ⟨7780069003189740452452277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186712668793160301634851 7780069003189740452452277)
                  ·
                    refine ⟨729381469049038167417401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7780069003189740452452277 729381469049038167417401)
                    ·
                      rfl

theorem cell23_4261396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4261396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261396 prefixEnd_4261396 := by exact prefixLift 4261396
  have htrace : WordTrace (prefixWord ++ tailWord_4261396) baseStart_4261396 baseEnd_4261396 := by
    simpa [prefixWord, tailWord_4261396, baseEnd_4261396] using wordTrace_append hprefix tailTrace_4261396
  have hstable : (prefixWord ++ tailWord_4261396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261396).length < 2 ^ (prefixWord ++ tailWord_4261396).sum := by decide
  have hdescent : baseEnd_4261396 < baseStart_4261396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261422 : List Nat := [4, 1, 3, 1, 2, 3, 1, 8]
def baseStart_4261422 : Nat := 118140960795 + 4261422 * 2 ^ 59
def prefixEnd_4261422 : Nat := 4983230072969 + 3 ^ 40 * 4261422 * 2
def baseEnd_4261422 : Nat := 81042879912745607426929

theorem tailTrace_4261422 : CollatzResearch.WordTrace tailWord_4261422 prefixEnd_4261422 81042879912745607426929 := by
  unfold tailWord_4261422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428353645950420222519315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103617886111735574520103013 19428353645950420222519315)
  ·
    refine ⟨29142530468925630333778973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19428353645950420222519315 29142530468925630333778973)
    ·
      refine ⟨10928448925847111375167115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29142530468925630333778973 10928448925847111375167115)
      ·
        refine ⟨16392673388770667062750673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928448925847111375167115 16392673388770667062750673)
        ·
          refine ⟨12294505041578000297063005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16392673388770667062750673 12294505041578000297063005)
          ·
            refine ⟨4610439390591750111398627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12294505041578000297063005 4610439390591750111398627)
            ·
              refine ⟨6915659085887625167097941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610439390591750111398627 6915659085887625167097941)
              ·
                refine ⟨81042879912745607426929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6915659085887625167097941 81042879912745607426929)
                ·
                  rfl

theorem cell23_4261422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_4261422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261422 prefixEnd_4261422 := by exact prefixLift 4261422
  have htrace : WordTrace (prefixWord ++ tailWord_4261422) baseStart_4261422 baseEnd_4261422 := by
    simpa [prefixWord, tailWord_4261422, baseEnd_4261422] using wordTrace_append hprefix tailTrace_4261422
  have hstable : (prefixWord ++ tailWord_4261422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261422).length < 2 ^ (prefixWord ++ tailWord_4261422).sum := by decide
  have hdescent : baseEnd_4261422 < baseStart_4261422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261432 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_4261432 : Nat := 118140960795 + 4261432 * 2 ^ 59
def prefixEnd_4261432 : Nat := 4983230072969 + 3 ^ 40 * 4261432 * 2
def baseEnd_4261432 : Nat := 2188162892450676361402037

theorem tailTrace_4261432 : CollatzResearch.WordTrace tailWord_4261432 prefixEnd_4261432 2188162892450676361402037 := by
  unfold tailWord_4261432
  simp only [CollatzResearch.WordTrace]
  refine ⟨77713596948783566744009275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103618129265044755658679033 77713596948783566744009275)
  ·
    refine ⟨116570395423175350116013913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77713596948783566744009275 116570395423175350116013913)
    ·
      refine ⟨87427796567381512587010435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116570395423175350116013913 87427796567381512587010435)
      ·
        refine ⟨131141694851072268880515653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87427796567381512587010435 131141694851072268880515653)
        ·
          refine ⟨24589067784576050415096685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131141694851072268880515653 24589067784576050415096685)
          ·
            refine ⟨9220900419216018905661257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24589067784576050415096685 9220900419216018905661257)
            ·
              refine ⟨6915675314412014179245943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9220900419216018905661257 6915675314412014179245943)
              ·
                refine ⟨10373512971618021268868915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6915675314412014179245943 10373512971618021268868915)
                ·
                  refine ⟨15560269457427031903303373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10373512971618021268868915 15560269457427031903303373)
                  ·
                    refine ⟨5835101046535136963738765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15560269457427031903303373 5835101046535136963738765)
                    ·
                      refine ⟨2188162892450676361402037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5835101046535136963738765 2188162892450676361402037)
                      ·
                        rfl

theorem cell23_4261432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_4261432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261432 prefixEnd_4261432 := by exact prefixLift 4261432
  have htrace : WordTrace (prefixWord ++ tailWord_4261432) baseStart_4261432 baseEnd_4261432 := by
    simpa [prefixWord, tailWord_4261432, baseEnd_4261432] using wordTrace_append hprefix tailTrace_4261432
  have hstable : (prefixWord ++ tailWord_4261432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261432).length < 2 ^ (prefixWord ++ tailWord_4261432).sum := by decide
  have hdescent : baseEnd_4261432 < baseStart_4261432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261453 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4261453 : Nat := 118140960795 + 4261453 * 2 ^ 59
def prefixEnd_4261453 : Nat := 4983230072969 + 3 ^ 40 * 4261453 * 2
def baseEnd_4261453 : Nat := 2188173675544420779239441

theorem tailTrace_4261453 : CollatzResearch.WordTrace tailWord_4261453 prefixEnd_4261453 2188173675544420779239441 := by
  unfold tailWord_4261453
  simp only [CollatzResearch.WordTrace]
  refine ⟨155427959830491054074533013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103618639886994036049688675 155427959830491054074533013)
  ·
    refine ⟨7285685617054268159743735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155427959830491054074533013 7285685617054268159743735)
    ·
      refine ⟨10928528425581402239615603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285685617054268159743735 10928528425581402239615603)
      ·
        refine ⟨16392792638372103359423405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928528425581402239615603 16392792638372103359423405)
        ·
          refine ⟨6147297239389538759783777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16392792638372103359423405 6147297239389538759783777)
          ·
            refine ⟨4610472929542154069837833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147297239389538759783777 4610472929542154069837833)
            ·
              refine ⟨3457854697156615552378375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610472929542154069837833 3457854697156615552378375)
              ·
                refine ⟨5186782045734923328567563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457854697156615552378375 5186782045734923328567563)
                ·
                  refine ⟨7780173068602384992851345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186782045734923328567563 7780173068602384992851345)
                  ·
                    refine ⟨5835129801451788744638509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7780173068602384992851345 5835129801451788744638509)
                    ·
                      refine ⟨2188173675544420779239441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5835129801451788744638509 2188173675544420779239441)
                      ·
                        rfl

theorem cell23_4261453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4261453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261453 prefixEnd_4261453 := by exact prefixLift 4261453
  have htrace : WordTrace (prefixWord ++ tailWord_4261453) baseStart_4261453 baseEnd_4261453 := by
    simpa [prefixWord, tailWord_4261453, baseEnd_4261453] using wordTrace_append hprefix tailTrace_4261453
  have hstable : (prefixWord ++ tailWord_4261453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261453).length < 2 ^ (prefixWord ++ tailWord_4261453).sum := by decide
  have hdescent : baseEnd_4261453 < baseStart_4261453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261489 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_4261489 : Nat := 118140960795 + 4261489 * 2 ^ 59
def prefixEnd_4261489 : Nat := 4983230072969 + 3 ^ 40 * 4261489 * 2
def baseEnd_4261489 : Nat := 2188192160847982638389275

theorem tailTrace_4261489 : CollatzResearch.WordTrace tailWord_4261489 prefixEnd_4261489 2188192160847982638389275 := by
  unfold tailWord_4261489
  simp only [CollatzResearch.WordTrace]
  refine ⟨155429272858360632222843521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103619515238907088148562347 155429272858360632222843521)
  ·
    refine ⟨116571954643770474167132641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155429272858360632222843521 116571954643770474167132641)
    ·
      refine ⟨87428965982827855625349481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116571954643770474167132641 87428965982827855625349481)
      ·
        refine ⟨65571724487120891719012111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87428965982827855625349481 65571724487120891719012111)
        ·
          refine ⟨98357586730681337578518167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65571724487120891719012111 98357586730681337578518167)
          ·
            refine ⟨147536380096022006367777251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98357586730681337578518167 147536380096022006367777251)
            ·
              refine ⟨221304570144033009551665877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147536380096022006367777251 221304570144033009551665877)
              ·
                refine ⟨5186825862750773661367169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 221304570144033009551665877 5186825862750773661367169)
                ·
                  refine ⟨3890119397063080246025377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5186825862750773661367169 3890119397063080246025377)
                  ·
                    refine ⟨2917589547797310184519033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890119397063080246025377 2917589547797310184519033)
                    ·
                      refine ⟨2188192160847982638389275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917589547797310184519033 2188192160847982638389275)
                      ·
                        rfl

theorem cell23_4261489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_4261489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261489 prefixEnd_4261489 := by exact prefixLift 4261489
  have htrace : WordTrace (prefixWord ++ tailWord_4261489) baseStart_4261489 baseEnd_4261489 := by
    simpa [prefixWord, tailWord_4261489, baseEnd_4261489] using wordTrace_append hprefix tailTrace_4261489
  have hstable : (prefixWord ++ tailWord_4261489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261489).length < 2 ^ (prefixWord ++ tailWord_4261489).sum := by decide
  have hdescent : baseEnd_4261489 < baseStart_4261489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261562 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_4261562 : Nat := 118140960795 + 4261562 * 2 ^ 59
def prefixEnd_4261562 : Nat := 4983230072969 + 3 ^ 40 * 4261562 * 2
def baseEnd_4261562 : Nat := 2188229644935760852776439

theorem tailTrace_4261562 : CollatzResearch.WordTrace tailWord_4261562 prefixEnd_4261562 2188229644935760852776439 := by
  unfold tailWord_4261562
  simp only [CollatzResearch.WordTrace]
  refine ⟨38857983846774041422562735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103621290258064110460167293 38857983846774041422562735)
  ·
    refine ⟨58286975770161062133844103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38857983846774041422562735 58286975770161062133844103)
    ·
      refine ⟨87430463655241593200766155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58286975770161062133844103 87430463655241593200766155)
      ·
        refine ⟨131145695482862389801149233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87430463655241593200766155 131145695482862389801149233)
        ·
          refine ⟨98359271612146792350861925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131145695482862389801149233 98359271612146792350861925)
          ·
            refine ⟨18442363427277523565786611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98359271612146792350861925 18442363427277523565786611)
            ·
              refine ⟨27663545140916285348679917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18442363427277523565786611 27663545140916285348679917)
              ·
                refine ⟨10373829427843607005754969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27663545140916285348679917 10373829427843607005754969)
                ·
                  refine ⟨7780372070882705254316227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10373829427843607005754969 7780372070882705254316227)
                  ·
                    refine ⟨11670558106324057881474341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7780372070882705254316227 11670558106324057881474341)
                    ·
                      refine ⟨2188229644935760852776439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11670558106324057881474341 2188229644935760852776439)
                      ·
                        rfl

theorem cell23_4261562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_4261562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261562 prefixEnd_4261562 := by exact prefixLift 4261562
  have htrace : WordTrace (prefixWord ++ tailWord_4261562) baseStart_4261562 baseEnd_4261562 := by
    simpa [prefixWord, tailWord_4261562, baseEnd_4261562] using wordTrace_append hprefix tailTrace_4261562
  have hstable : (prefixWord ++ tailWord_4261562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261562).length < 2 ^ (prefixWord ++ tailWord_4261562).sum := by decide
  have hdescent : baseEnd_4261562 < baseStart_4261562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261575 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_4261575 : Nat := 118140960795 + 4261575 * 2 ^ 59
def prefixEnd_4261575 : Nat := 4983230072969 + 3 ^ 40 * 4261575 * 2
def baseEnd_4261575 : Nat := 2188236320184269301913879

theorem tailTrace_4261575 : CollatzResearch.WordTrace tailWord_4261575 prefixEnd_4261575 2188236320184269301913879 := by
  unfold tailWord_4261575
  simp only [CollatzResearch.WordTrace]
  refine ⟨155432409536049068910474179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103621606357366045940316119 155432409536049068910474179)
  ·
    refine ⟨233148614304073603365711269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155432409536049068910474179 233148614304073603365711269)
    ·
      refine ⟨43715365182013800631070863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233148614304073603365711269 43715365182013800631070863)
      ·
        refine ⟨65573047773020700946606295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43715365182013800631070863 65573047773020700946606295)
        ·
          refine ⟨98359571659531051419909443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65573047773020700946606295 98359571659531051419909443)
          ·
            refine ⟨147539357489296577129864165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98359571659531051419909443 147539357489296577129864165)
            ·
              refine ⟨27663629529243108211849531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147539357489296577129864165 27663629529243108211849531)
              ·
                refine ⟨41495444293864662317774297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27663629529243108211849531 41495444293864662317774297)
                ·
                  refine ⟨31121583220398496738330723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41495444293864662317774297 31121583220398496738330723)
                  ·
                    refine ⟨46682374830597745107496085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31121583220398496738330723 46682374830597745107496085)
                    ·
                      refine ⟨2188236320184269301913879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46682374830597745107496085 2188236320184269301913879)
                      ·
                        rfl

theorem cell23_4261575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_4261575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261575 prefixEnd_4261575 := by exact prefixLift 4261575
  have htrace : WordTrace (prefixWord ++ tailWord_4261575) baseStart_4261575 baseEnd_4261575 := by
    simpa [prefixWord, tailWord_4261575, baseEnd_4261575] using wordTrace_append hprefix tailTrace_4261575
  have hstable : (prefixWord ++ tailWord_4261575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261575).length < 2 ^ (prefixWord ++ tailWord_4261575).sum := by decide
  have hdescent : baseEnd_4261575 < baseStart_4261575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261625 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4261625 : Nat := 118140960795 + 4261625 * 2 ^ 59
def prefixEnd_4261625 : Nat := 4983230072969 + 3 ^ 40 * 4261625 * 2
def baseEnd_4261625 : Nat := 2188261994216994106288649

theorem tailTrace_4261625 : CollatzResearch.WordTrace tailWord_4261625 prefixEnd_4261625 2188261994216994106288649 := by
  unfold tailWord_4261625
  simp only [CollatzResearch.WordTrace]
  refine ⟨155434233185867927449794329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103622822123911951633196219 155434233185867927449794329)
  ·
    refine ⟨116575674889400945587345747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155434233185867927449794329 116575674889400945587345747)
    ·
      refine ⟨174863512334101418381018621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116575674889400945587345747 174863512334101418381018621)
      ·
        refine ⟨65573817125288031892881983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174863512334101418381018621 65573817125288031892881983)
        ·
          refine ⟨98360725687932047839322975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65573817125288031892881983 98360725687932047839322975)
          ·
            refine ⟨147541088531898071758984463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98360725687932047839322975 147541088531898071758984463)
            ·
              refine ⟨221311632797847107638476695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147541088531898071758984463 221311632797847107638476695)
              ·
                refine ⟨331967449196770661457715043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221311632797847107638476695 331967449196770661457715043)
                ·
                  refine ⟨497951173795155992186572565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331967449196770661457715043 497951173795155992186572565)
                  ·
                    refine ⟨23341461271647937133745589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 497951173795155992186572565 23341461271647937133745589)
                    ·
                      refine ⟨2188261994216994106288649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23341461271647937133745589 2188261994216994106288649)
                      ·
                        rfl

theorem cell23_4261625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4261625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261625 prefixEnd_4261625 := by exact prefixLift 4261625
  have htrace : WordTrace (prefixWord ++ tailWord_4261625) baseStart_4261625 baseEnd_4261625 := by
    simpa [prefixWord, tailWord_4261625, baseEnd_4261625] using wordTrace_append hprefix tailTrace_4261625
  have hstable : (prefixWord ++ tailWord_4261625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261625).length < 2 ^ (prefixWord ++ tailWord_4261625).sum := by decide
  have hdescent : baseEnd_4261625 < baseStart_4261625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261632 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_4261632 : Nat := 118140960795 + 4261632 * 2 ^ 59
def prefixEnd_4261632 : Nat := 4983230072969 + 3 ^ 40 * 4261632 * 2
def baseEnd_4261632 : Nat := 729421862860525192967039

theorem tailTrace_4261632 : CollatzResearch.WordTrace tailWord_4261632 prefixEnd_4261632 729421862860525192967039 := by
  unfold tailWord_4261632
  simp only [CollatzResearch.WordTrace]
  refine ⟨77717244248421283822649575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103622992331228378430199433 77717244248421283822649575)
  ·
    refine ⟨116575866372631925733974363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77717244248421283822649575 116575866372631925733974363)
    ·
      refine ⟨174863799558947888600961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116575866372631925733974363 174863799558947888600961545)
      ·
        refine ⟨131147849669210916450721159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174863799558947888600961545 131147849669210916450721159)
        ·
          refine ⟨196721774503816374676081739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131147849669210916450721159 196721774503816374676081739)
          ·
            refine ⟨295082661755724562014122609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196721774503816374676081739 295082661755724562014122609)
            ·
              refine ⟨221311996316793421510591957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295082661755724562014122609 221311996316793421510591957)
              ·
                refine ⟨5186999913674845816654499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 221311996316793421510591957 5186999913674845816654499)
                ·
                  refine ⟨7780499870512268724981749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5186999913674845816654499 7780499870512268724981749)
                  ·
                    refine ⟨729421862860525192967039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7780499870512268724981749 729421862860525192967039)
                    ·
                      rfl

theorem cell23_4261632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_4261632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261632 prefixEnd_4261632 := by exact prefixLift 4261632
  have htrace : WordTrace (prefixWord ++ tailWord_4261632) baseStart_4261632 baseEnd_4261632 := by
    simpa [prefixWord, tailWord_4261632, baseEnd_4261632] using wordTrace_append hprefix tailTrace_4261632
  have hstable : (prefixWord ++ tailWord_4261632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261632).length < 2 ^ (prefixWord ++ tailWord_4261632).sum := by decide
  have hdescent : baseEnd_4261632 < baseStart_4261632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261669 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_4261669 : Nat := 118140960795 + 4261669 * 2 ^ 59
def prefixEnd_4261669 : Nat := 4983230072969 + 3 ^ 40 * 4261669 * 2
def baseEnd_4261669 : Nat := 2188284587365791934138447

theorem tailTrace_4261669 : CollatzResearch.WordTrace tailWord_4261669 prefixEnd_4261669 2188284587365791934138447 := by
  unfold tailWord_4261669
  simp only [CollatzResearch.WordTrace]
  refine ⟨155435837997708522964396061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103623891998472348642930707 155435837997708522964396061)
  ·
    refine ⟨58288439249140696111648523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155435837997708522964396061 58288439249140696111648523)
    ·
      refine ⟨87432658873711044167472785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58288439249140696111648523 87432658873711044167472785)
      ·
        refine ⟨65574494155283283125604589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87432658873711044167472785 65574494155283283125604589)
        ·
          refine ⟨24590435308231231172101721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65574494155283283125604589 24590435308231231172101721)
          ·
            refine ⟨18442826481173423379076291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24590435308231231172101721 18442826481173423379076291)
            ·
              refine ⟨27664239721760135068614437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18442826481173423379076291 27664239721760135068614437)
              ·
                refine ⟨5187044947830025325365207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27664239721760135068614437 5187044947830025325365207)
                ·
                  refine ⟨7780567421745037988047811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187044947830025325365207 7780567421745037988047811)
                  ·
                    refine ⟨11670851132617556982071717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7780567421745037988047811 11670851132617556982071717)
                    ·
                      refine ⟨2188284587365791934138447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11670851132617556982071717 2188284587365791934138447)
                      ·
                        rfl

theorem cell23_4261669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_4261669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261669 prefixEnd_4261669 := by exact prefixLift 4261669
  have htrace : WordTrace (prefixWord ++ tailWord_4261669) baseStart_4261669 baseEnd_4261669 := by
    simpa [prefixWord, tailWord_4261669, baseEnd_4261669] using wordTrace_append hprefix tailTrace_4261669
  have hstable : (prefixWord ++ tailWord_4261669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261669).length < 2 ^ (prefixWord ++ tailWord_4261669).sum := by decide
  have hdescent : baseEnd_4261669 < baseStart_4261669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261703 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_4261703 : Nat := 118140960795 + 4261703 * 2 ^ 59
def prefixEnd_4261703 : Nat := 4983230072969 + 3 ^ 40 * 4261703 * 2
def baseEnd_4261703 : Nat := 2188302045708044801113291

theorem tailTrace_4261703 : CollatzResearch.WordTrace tailWord_4261703 prefixEnd_4261703 2188302045708044801113291 := by
  unfold tailWord_4261703
  simp only [CollatzResearch.WordTrace]
  refine ⟨155437078079585346771133763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103624718719723564514089175 155437078079585346771133763)
  ·
    refine ⟨233155617119378020156700645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155437078079585346771133763 233155617119378020156700645)
    ·
      refine ⟨43716678209883378779381371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233155617119378020156700645 43716678209883378779381371)
      ·
        refine ⟨65575017314825068169072057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43716678209883378779381371 65575017314825068169072057)
        ·
          refine ⟨49181262986118801126804043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65575017314825068169072057 49181262986118801126804043)
          ·
            refine ⟨73771894479178201690206065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49181262986118801126804043 73771894479178201690206065)
            ·
              refine ⟨55328920859383651267654549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73771894479178201690206065 55328920859383651267654549)
              ·
                refine ⟨2593543165283608653171307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55328920859383651267654549 2593543165283608653171307)
                ·
                  refine ⟨3890314747925412979756961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593543165283608653171307 3890314747925412979756961)
                  ·
                    refine ⟨2917736060944059734817721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890314747925412979756961 2917736060944059734817721)
                    ·
                      refine ⟨2188302045708044801113291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917736060944059734817721 2188302045708044801113291)
                      ·
                        rfl

theorem cell23_4261703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_4261703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261703 prefixEnd_4261703 := by exact prefixLift 4261703
  have htrace : WordTrace (prefixWord ++ tailWord_4261703) baseStart_4261703 baseEnd_4261703 := by
    simpa [prefixWord, tailWord_4261703, baseEnd_4261703] using wordTrace_append hprefix tailTrace_4261703
  have hstable : (prefixWord ++ tailWord_4261703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261703).length < 2 ^ (prefixWord ++ tailWord_4261703).sum := by decide
  have hdescent : baseEnd_4261703 < baseStart_4261703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261709 : List Nat := [1, 6, 1, 2, 1, 1, 1, 10]
def baseStart_4261709 : Nat := 118140960795 + 4261709 * 2 ^ 59
def prefixEnd_4261709 : Nat := 4983230072969 + 3 ^ 40 * 4261709 * 2
def baseEnd_4261709 : Nat := 81048338021924880653269

theorem tailTrace_4261709 : CollatzResearch.WordTrace tailWord_4261709 prefixEnd_4261709 81048338021924880653269 := by
  unfold tailWord_4261709
  simp only [CollatzResearch.WordTrace]
  refine ⟨155437296917563609795852181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103624864611709073197234787 155437296917563609795852181)
  ·
    refine ⟨7286123293010794209180571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 155437296917563609795852181 7286123293010794209180571)
    ·
      refine ⟨10929184939516191313770857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7286123293010794209180571 10929184939516191313770857)
      ·
        refine ⟨8196888704637143485328143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10929184939516191313770857 8196888704637143485328143)
        ·
          refine ⟨12295333056955715227992215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196888704637143485328143 12295333056955715227992215)
          ·
            refine ⟨18442999585433572841988323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12295333056955715227992215 18442999585433572841988323)
            ·
              refine ⟨27664499378150359262982485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18442999585433572841988323 27664499378150359262982485)
              ·
                refine ⟨81048338021924880653269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27664499378150359262982485 81048338021924880653269)
                ·
                  rfl

theorem cell23_4261709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 10].length) (baseStart_4261709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261709 prefixEnd_4261709 := by exact prefixLift 4261709
  have htrace : WordTrace (prefixWord ++ tailWord_4261709) baseStart_4261709 baseEnd_4261709 := by
    simpa [prefixWord, tailWord_4261709, baseEnd_4261709] using wordTrace_append hprefix tailTrace_4261709
  have hstable : (prefixWord ++ tailWord_4261709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261709).length < 2 ^ (prefixWord ++ tailWord_4261709).sum := by decide
  have hdescent : baseEnd_4261709 < baseStart_4261709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261713 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 2, 4]
def baseStart_4261713 : Nat := 118140960795 + 4261713 * 2 ^ 59
def prefixEnd_4261713 : Nat := 4983230072969 + 3 ^ 40 * 4261713 * 2
def baseEnd_4261713 : Nat := 729435726838196587329415

theorem tailTrace_4261713 : CollatzResearch.WordTrace tailWord_4261713 prefixEnd_4261713 729435726838196587329415 := by
  unfold tailWord_4261713
  simp only [CollatzResearch.WordTrace]
  refine ⟨155437442809549118478997793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103624961873032745652665195 155437442809549118478997793)
  ·
    refine ⟨116578082107161838859248345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155437442809549118478997793 116578082107161838859248345)
    ·
      refine ⟨87433561580371379144436259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116578082107161838859248345 87433561580371379144436259)
      ·
        refine ⟨131150342370557068716654389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87433561580371379144436259 131150342370557068716654389)
        ·
          refine ⟨12295344597239725192186349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131150342370557068716654389 12295344597239725192186349)
          ·
            refine ⟨4610754223964896947069881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12295344597239725192186349 4610754223964896947069881)
            ·
              refine ⟨3458065667973672710302411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610754223964896947069881 3458065667973672710302411)
              ·
                refine ⟨5187098501960509065453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458065667973672710302411 5187098501960509065453617)
                ·
                  refine ⟨3890323876470381799090213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5187098501960509065453617 3890323876470381799090213)
                  ·
                    refine ⟨729435726838196587329415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890323876470381799090213 729435726838196587329415)
                    ·
                      rfl

theorem cell23_4261713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_4261713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261713 prefixEnd_4261713 := by exact prefixLift 4261713
  have htrace : WordTrace (prefixWord ++ tailWord_4261713) baseStart_4261713 baseEnd_4261713 := by
    simpa [prefixWord, tailWord_4261713, baseEnd_4261713] using wordTrace_append hprefix tailTrace_4261713
  have hstable : (prefixWord ++ tailWord_4261713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261713).length < 2 ^ (prefixWord ++ tailWord_4261713).sum := by decide
  have hdescent : baseEnd_4261713 < baseStart_4261713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261759 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 5, 4, 2]
def baseStart_4261759 : Nat := 118140960795 + 4261759 * 2 ^ 59
def prefixEnd_4261759 : Nat := 4983230072969 + 3 ^ 40 * 4261759 * 2
def baseEnd_4261759 : Nat := 2188330800624696582013033

theorem tailTrace_4261759 : CollatzResearch.WordTrace tailWord_4261759 prefixEnd_4261759 2188330800624696582013033 := by
  unfold tailWord_4261759
  simp only [CollatzResearch.WordTrace]
  refine ⟨155439120567382468335172331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103626080378254978890114887 155439120567382468335172331)
  ·
    refine ⟨233158680851073702502758497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155439120567382468335172331 233158680851073702502758497)
    ·
      refine ⟨174869010638305276877068873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233158680851073702502758497 174869010638305276877068873)
      ·
        refine ⟨131151757978728957657801655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174869010638305276877068873 131151757978728957657801655)
        ·
          refine ⟨196727636968093436486702483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131151757978728957657801655 196727636968093436486702483)
          ·
            refine ⟨295091455452140154730053725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196727636968093436486702483 295091455452140154730053725)
            ·
              refine ⟨110659295794552558023770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295091455452140154730053725 110659295794552558023770147)
              ·
                refine ⟨165988943691828837035655221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110659295794552558023770147 165988943691828837035655221)
                ·
                  refine ⟨15561463471108953472092677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165988943691828837035655221 15561463471108953472092677)
                  ·
                    refine ⟨2917774400832928776017377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15561463471108953472092677 2917774400832928776017377)
                    ·
                      refine ⟨2188330800624696582013033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917774400832928776017377 2188330800624696582013033)
                      ·
                        rfl

theorem cell23_4261759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_4261759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261759 prefixEnd_4261759 := by exact prefixLift 4261759
  have htrace : WordTrace (prefixWord ++ tailWord_4261759) baseStart_4261759 baseEnd_4261759 := by
    simpa [prefixWord, tailWord_4261759, baseEnd_4261759] using wordTrace_append hprefix tailTrace_4261759
  have hstable : (prefixWord ++ tailWord_4261759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261759).length < 2 ^ (prefixWord ++ tailWord_4261759).sum := by decide
  have hdescent : baseEnd_4261759 < baseStart_4261759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261792 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4261792 : Nat := 118140960795 + 4261792 * 2 ^ 59
def prefixEnd_4261792 : Nat := 4983230072969 + 3 ^ 40 * 4261792 * 2
def baseEnd_4261792 : Nat := 2188347745486294952900381

theorem tailTrace_4261792 : CollatzResearch.WordTrace tailWord_4261792 prefixEnd_4261792 2188347745486294952900381 := by
  unfold tailWord_4261792
  simp only [CollatzResearch.WordTrace]
  refine ⟨77720162088131457485561815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103626882784175276647415753 77720162088131457485561815)
  ·
    refine ⟨116580243132197186228342723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77720162088131457485561815 116580243132197186228342723)
    ·
      refine ⟨174870364698295779342514085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116580243132197186228342723 174870364698295779342514085)
      ·
        refine ⟨32788193380930458626721391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174870364698295779342514085 32788193380930458626721391)
        ·
          refine ⟨49182290071395687940082087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32788193380930458626721391 49182290071395687940082087)
          ·
            refine ⟨73773435107093531910123131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49182290071395687940082087 73773435107093531910123131)
            ·
              refine ⟨110660152660640297865184697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73773435107093531910123131 110660152660640297865184697)
              ·
                refine ⟨82995114495480223398888523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110660152660640297865184697 82995114495480223398888523)
                ·
                  refine ⟨124492671743220335098332785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82995114495480223398888523 124492671743220335098332785)
                  ·
                    refine ⟨93369503807415251323749589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124492671743220335098332785 93369503807415251323749589)
                    ·
                      refine ⟨2188347745486294952900381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93369503807415251323749589 2188347745486294952900381)
                      ·
                        rfl

theorem cell23_4261792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4261792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261792 prefixEnd_4261792 := by exact prefixLift 4261792
  have htrace : WordTrace (prefixWord ++ tailWord_4261792) baseStart_4261792 baseEnd_4261792 := by
    simpa [prefixWord, tailWord_4261792, baseEnd_4261792] using wordTrace_append hprefix tailTrace_4261792
  have hstable : (prefixWord ++ tailWord_4261792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261792).length < 2 ^ (prefixWord ++ tailWord_4261792).sum := by decide
  have hdescent : baseEnd_4261792 < baseStart_4261792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261850 : List Nat := [3, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_4261850 : Nat := 118140960795 + 4261850 * 2 ^ 59
def prefixEnd_4261850 : Nat := 4983230072969 + 3 ^ 40 * 4261850 * 2
def baseEnd_4261850 : Nat := 243153058596028413997235

theorem tailTrace_4261850 : CollatzResearch.WordTrace tailWord_4261850 prefixEnd_4261850 243153058596028413997235 := by
  unfold tailWord_4261850
  simp only [CollatzResearch.WordTrace]
  refine ⟨38860609902513197719183751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103628293073368527251156669 38860609902513197719183751)
  ·
    refine ⟨58290914853769796578775627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38860609902513197719183751 58290914853769796578775627)
    ·
      refine ⟨87436372280654694868163441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58290914853769796578775627 87436372280654694868163441)
      ·
        refine ⟨65577279210491021151122581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87436372280654694868163441 65577279210491021151122581)
        ·
          refine ⟨3073934962991766616458871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65577279210491021151122581 3073934962991766616458871)
          ·
            refine ⟨4610902444487649924688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073934962991766616458871 4610902444487649924688307)
            ·
              refine ⟨6916353666731474887032461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610902444487649924688307 6916353666731474887032461)
              ·
                refine ⟨2593632625024303082637173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6916353666731474887032461 2593632625024303082637173)
                ·
                  refine ⟨243153058596028413997235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2593632625024303082637173 243153058596028413997235)
                  ·
                    rfl

theorem cell23_4261850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_4261850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261850 prefixEnd_4261850 := by exact prefixLift 4261850
  have htrace : WordTrace (prefixWord ++ tailWord_4261850) baseStart_4261850 baseEnd_4261850 := by
    simpa [prefixWord, tailWord_4261850, baseEnd_4261850] using wordTrace_append hprefix tailTrace_4261850
  have hstable : (prefixWord ++ tailWord_4261850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261850).length < 2 ^ (prefixWord ++ tailWord_4261850).sum := by decide
  have hdescent : baseEnd_4261850 < baseStart_4261850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261866 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_4261866 : Nat := 118140960795 + 4261866 * 2 ^ 59
def prefixEnd_4261866 : Nat := 4983230072969 + 3 ^ 40 * 4261866 * 2
def baseEnd_4261866 : Nat := 2188385743054727663375041

theorem tailTrace_4261866 : CollatzResearch.WordTrace tailWord_4261866 prefixEnd_4261866 2188385743054727663375041 := by
  unfold tailWord_4261866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38860755794498706402329363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103628682118663217072878301 38860755794498706402329363)
  ·
    refine ⟨58291133691748059603494045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38860755794498706402329363 58291133691748059603494045)
    ·
      refine ⟨21859175134405522351310267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58291133691748059603494045 21859175134405522351310267)
      ·
        refine ⟨32788762701608283526965401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21859175134405522351310267 32788762701608283526965401)
        ·
          refine ⟨24591572026206212645224051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32788762701608283526965401 24591572026206212645224051)
          ·
            refine ⟨36887358039309318967836077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24591572026206212645224051 36887358039309318967836077)
            ·
              refine ⟨13832759264740994612938529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36887358039309318967836077 13832759264740994612938529)
              ·
                refine ⟨10374569448555745959703897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13832759264740994612938529 10374569448555745959703897)
                ·
                  refine ⟨7780927086416809469777923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10374569448555745959703897 7780927086416809469777923)
                  ·
                    refine ⟨11671390629625214204666885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7780927086416809469777923 11671390629625214204666885)
                    ·
                      refine ⟨2188385743054727663375041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11671390629625214204666885 2188385743054727663375041)
                      ·
                        rfl

theorem cell23_4261866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_4261866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261866 prefixEnd_4261866 := by exact prefixLift 4261866
  have htrace : WordTrace (prefixWord ++ tailWord_4261866) baseStart_4261866 baseEnd_4261866 := by
    simpa [prefixWord, tailWord_4261866, baseEnd_4261866] using wordTrace_append hprefix tailTrace_4261866
  have hstable : (prefixWord ++ tailWord_4261866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261866).length < 2 ^ (prefixWord ++ tailWord_4261866).sum := by decide
  have hdescent : baseEnd_4261866 < baseStart_4261866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261927 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4261927 : Nat := 118140960795 + 4261927 * 2 ^ 59
def prefixEnd_4261927 : Nat := 4983230072969 + 3 ^ 40 * 4261927 * 2
def baseEnd_4261927 : Nat := 729472355124883974904087

theorem tailTrace_4261927 : CollatzResearch.WordTrace tailWord_4261927 prefixEnd_4261927 729472355124883974904087 := by
  unfold tailWord_4261927
  simp only [CollatzResearch.WordTrace]
  refine ⟨155445248030773833027288035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103630165353849222018192023 155445248030773833027288035)
  ·
    refine ⟨233167872046160749540932053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155445248030773833027288035 233167872046160749540932053)
    ·
      refine ⟨5464872001081892567365595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 233167872046160749540932053 5464872001081892567365595)
      ·
        refine ⟨8197308001622838851048393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464872001081892567365595 8197308001622838851048393)
        ·
          refine ⟨6147981001217129138286295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8197308001622838851048393 6147981001217129138286295)
          ·
            refine ⟨9221971501825693707429443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147981001217129138286295 9221971501825693707429443)
            ·
              refine ⟨13832957252738540561144165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9221971501825693707429443 13832957252738540561144165)
              ·
                refine ⟨2593679484888476355214531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13832957252738540561144165 2593679484888476355214531)
                ·
                  refine ⟨3890519227332714532821797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593679484888476355214531 3890519227332714532821797)
                  ·
                    refine ⟨729472355124883974904087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890519227332714532821797 729472355124883974904087)
                    ·
                      rfl

theorem cell23_4261927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4261927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261927 prefixEnd_4261927 := by exact prefixLift 4261927
  have htrace : WordTrace (prefixWord ++ tailWord_4261927) baseStart_4261927 baseEnd_4261927 := by
    simpa [prefixWord, tailWord_4261927, baseEnd_4261927] using wordTrace_append hprefix tailTrace_4261927
  have hstable : (prefixWord ++ tailWord_4261927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261927).length < 2 ^ (prefixWord ++ tailWord_4261927).sum := by decide
  have hdescent : baseEnd_4261927 < baseStart_4261927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261966 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_4261966 : Nat := 118140960795 + 4261966 * 2 ^ 59
def prefixEnd_4261966 : Nat := 4983230072969 + 3 ^ 40 * 4261966 * 2
def baseEnd_4261966 : Nat := 729479030373392424041527

theorem tailTrace_4261966 : CollatzResearch.WordTrace tailWord_4261966 prefixEnd_4261966 729479030373392424041527 := by
  unfold tailWord_4261966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19430833809704067835994719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103631113651755028458638501 19430833809704067835994719)
  ·
    refine ⟨29146250714556101753992079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19430833809704067835994719 29146250714556101753992079)
    ·
      refine ⟨43719376071834152630988119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29146250714556101753992079 43719376071834152630988119)
      ·
        refine ⟨65579064107751228946482179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43719376071834152630988119 65579064107751228946482179)
        ·
          refine ⟨98368596161626843419723269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65579064107751228946482179 98368596161626843419723269)
          ·
            refine ⟨18444111780305033141198113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98368596161626843419723269 18444111780305033141198113)
            ·
              refine ⟨13833083835228774855898585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18444111780305033141198113 13833083835228774855898585)
              ·
                refine ⟨10374812876421581141923939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13833083835228774855898585 10374812876421581141923939)
                ·
                  refine ⟨15562219314632371712885909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10374812876421581141923939 15562219314632371712885909)
                  ·
                    refine ⟨729479030373392424041527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15562219314632371712885909 729479030373392424041527)
                    ·
                      rfl

theorem cell23_4261966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_4261966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261966 prefixEnd_4261966 := by exact prefixLift 4261966
  have htrace : WordTrace (prefixWord ++ tailWord_4261966) baseStart_4261966 baseEnd_4261966 := by
    simpa [prefixWord, tailWord_4261966, baseEnd_4261966] using wordTrace_append hprefix tailTrace_4261966
  have hstable : (prefixWord ++ tailWord_4261966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261966).length < 2 ^ (prefixWord ++ tailWord_4261966).sum := by decide
  have hdescent : baseEnd_4261966 < baseStart_4261966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261969 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_4261969 : Nat := 118140960795 + 4261969 * 2 ^ 59
def prefixEnd_4261969 : Nat := 4983230072969 + 3 ^ 40 * 4261969 * 2
def baseEnd_4261969 : Nat := 2188438631562140760387067

theorem tailTrace_4261969 : CollatzResearch.WordTrace tailWord_4261969 prefixEnd_4261969 2188438631562140760387067 := by
  unfold tailWord_4261969
  simp only [CollatzResearch.WordTrace]
  refine ⟨155446779896621674200316961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103631186597747782800211307 155446779896621674200316961)
  ·
    refine ⟨116585084922466255650237721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155446779896621674200316961 116585084922466255650237721)
    ·
      refine ⟨87438813691849691737678291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116585084922466255650237721 87438813691849691737678291)
      ·
        refine ⟨131158220537774537606517437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87438813691849691737678291 131158220537774537606517437)
        ·
          refine ⟨49184332701665451602444039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131158220537774537606517437 49184332701665451602444039)
          ·
            refine ⟨73776499052498177403666059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49184332701665451602444039 73776499052498177403666059)
            ·
              refine ⟨110664748578747266105499089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73776499052498177403666059 110664748578747266105499089)
              ·
                refine ⟨82998561434060449579124317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110664748578747266105499089 82998561434060449579124317)
                ·
                  refine ⟨31124460537772668592171619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82998561434060449579124317 31124460537772668592171619)
                  ·
                    refine ⟨46686690806659002888257429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31124460537772668592171619 46686690806659002888257429)
                    ·
                      refine ⟨2188438631562140760387067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46686690806659002888257429 2188438631562140760387067)
                      ·
                        rfl

theorem cell23_4261969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_4261969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261969 prefixEnd_4261969 := by exact prefixLift 4261969
  have htrace : WordTrace (prefixWord ++ tailWord_4261969) baseStart_4261969 baseEnd_4261969 := by
    simpa [prefixWord, tailWord_4261969, baseEnd_4261969] using wordTrace_append hprefix tailTrace_4261969
  have hstable : (prefixWord ++ tailWord_4261969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261969).length < 2 ^ (prefixWord ++ tailWord_4261969).sum := by decide
  have hdescent : baseEnd_4261969 < baseStart_4261969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4261973 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4261973 : Nat := 118140960795 + 4261973 * 2 ^ 59
def prefixEnd_4261973 : Nat := 4983230072969 + 3 ^ 40 * 4261973 * 2
def baseEnd_4261973 : Nat := 2188440685484758744737049

theorem tailTrace_4261973 : CollatzResearch.WordTrace tailWord_4261973 prefixEnd_4261973 2188440685484758744737049 := by
  unfold tailWord_4261973
  simp only [CollatzResearch.WordTrace]
  refine ⟨155446925788607182883462573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103631283859071455255641715 155446925788607182883462573)
  ·
    refine ⟨58292597170727693581298465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155446925788607182883462573 58292597170727693581298465)
    ·
      refine ⟨43719447878045770185973849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58292597170727693581298465 43719447878045770185973849)
      ·
        refine ⟨32789585908534327639480387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43719447878045770185973849 32789585908534327639480387)
        ·
          refine ⟨49184378862801491459220581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32789585908534327639480387 49184378862801491459220581)
          ·
            refine ⟨9222071036775279648603859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49184378862801491459220581 9222071036775279648603859)
            ·
              refine ⟨13833106555162919472905789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222071036775279648603859 13833106555162919472905789)
              ·
                refine ⟨5187414958186094802339671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13833106555162919472905789 5187414958186094802339671)
                ·
                  refine ⟨7781122437279142203509507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187414958186094802339671 7781122437279142203509507)
                  ·
                    refine ⟨11671683655918713305264261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7781122437279142203509507 11671683655918713305264261)
                    ·
                      refine ⟨2188440685484758744737049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11671683655918713305264261 2188440685484758744737049)
                      ·
                        rfl

theorem cell23_4261973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4261973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4261973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4261973 prefixEnd_4261973 := by exact prefixLift 4261973
  have htrace : WordTrace (prefixWord ++ tailWord_4261973) baseStart_4261973 baseEnd_4261973 := by
    simpa [prefixWord, tailWord_4261973, baseEnd_4261973] using wordTrace_append hprefix tailTrace_4261973
  have hstable : (prefixWord ++ tailWord_4261973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4261973).length < 2 ^ (prefixWord ++ tailWord_4261973).sum := by decide
  have hdescent : baseEnd_4261973 < baseStart_4261973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4261973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262000 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 2, 4]
def baseStart_4262000 : Nat := 118140960795 + 4262000 * 2 ^ 59
def prefixEnd_4262000 : Nat := 4983230072969 + 3 ^ 40 * 4262000 * 2
def baseEnd_4262000 : Nat := 729484849820810046366475

theorem tailTrace_4262000 : CollatzResearch.WordTrace tailWord_4262000 prefixEnd_4262000 729484849820810046366475 := by
  unfold tailWord_4262000
  simp only [CollatzResearch.WordTrace]
  refine ⟨77723955279754683247347727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103631940373006244329796969 77723955279754683247347727)
  ·
    refine ⟨116585932919632024871021591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77723955279754683247347727 116585932919632024871021591)
    ·
      refine ⟨174878899379448037306532387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116585932919632024871021591 174878899379448037306532387)
      ·
        refine ⟨262318349069172055959798581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174878899379448037306532387 262318349069172055959798581)
        ·
          refine ⟨24592345225234880246231117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 262318349069172055959798581 24592345225234880246231117)
          ·
            refine ⟨9222129459463080092336669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24592345225234880246231117 9222129459463080092336669)
            ·
              refine ⟨3458298547298655034626251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9222129459463080092336669 3458298547298655034626251)
              ·
                refine ⟨5187447820947982551939377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458298547298655034626251 5187447820947982551939377)
                ·
                  refine ⟨3890585865710986913954533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5187447820947982551939377 3890585865710986913954533)
                  ·
                    refine ⟨729484849820810046366475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890585865710986913954533 729484849820810046366475)
                    ·
                      rfl

theorem cell23_4262000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_4262000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262000 prefixEnd_4262000 := by exact prefixLift 4262000
  have htrace : WordTrace (prefixWord ++ tailWord_4262000) baseStart_4262000 baseEnd_4262000 := by
    simpa [prefixWord, tailWord_4262000, baseEnd_4262000] using wordTrace_append hprefix tailTrace_4262000
  have hstable : (prefixWord ++ tailWord_4262000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262000).length < 2 ^ (prefixWord ++ tailWord_4262000).sum := by decide
  have hdescent : baseEnd_4262000 < baseStart_4262000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262013 : List Nat := [1, 4, 1, 1, 3, 4, 2, 7]
def baseStart_4262013 : Nat := 118140960795 + 4262013 * 2 ^ 59
def prefixEnd_4262013 : Nat := 4983230072969 + 3 ^ 40 * 4262013 * 2
def baseEnd_4262013 : Nat := 81054119433738466230995

theorem tailTrace_4262013 : CollatzResearch.WordTrace tailWord_4262013 prefixEnd_4262013 81054119433738466230995 := by
  unfold tailWord_4262013
  simp only [CollatzResearch.WordTrace]
  refine ⟨155448384708462269714918693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103632256472308179809945795 155448384708462269714918693)
  ·
    refine ⟨29146572132836675571547255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155448384708462269714918693 29146572132836675571547255)
    ·
      refine ⟨43719858199255013357320883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29146572132836675571547255 43719858199255013357320883)
      ·
        refine ⟨65579787298882520035981325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43719858199255013357320883 65579787298882520035981325)
        ·
          refine ⟨24592420237080945013492997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65579787298882520035981325 24592420237080945013492997)
          ·
            refine ⟨4611078794452677190029937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24592420237080945013492997 4611078794452677190029937)
            ·
              refine ⟨3458309095839507892522453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4611078794452677190029937 3458309095839507892522453)
              ·
                refine ⟨81054119433738466230995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3458309095839507892522453 81054119433738466230995)
                ·
                  rfl

theorem cell23_4262013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 7].length) (baseStart_4262013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262013 prefixEnd_4262013 := by exact prefixLift 4262013
  have htrace : WordTrace (prefixWord ++ tailWord_4262013) baseStart_4262013 baseEnd_4262013 := by
    simpa [prefixWord, tailWord_4262013, baseEnd_4262013] using wordTrace_append hprefix tailTrace_4262013
  have hstable : (prefixWord ++ tailWord_4262013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262013).length < 2 ^ (prefixWord ++ tailWord_4262013).sum := by decide
  have hdescent : baseEnd_4262013 < baseStart_4262013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262023 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_4262023 : Nat := 118140960795 + 4262023 * 2 ^ 59
def prefixEnd_4262023 : Nat := 4983230072969 + 3 ^ 40 * 4262023 * 2
def baseEnd_4262023 : Nat := 2188466359517483549111819

theorem tailTrace_4262023 : CollatzResearch.WordTrace tailWord_4262023 prefixEnd_4262023 2188466359517483549111819 := by
  unfold tailWord_4262023
  simp only [CollatzResearch.WordTrace]
  refine ⟨155448749438426041422782723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103632499625617360948521815 155448749438426041422782723)
  ·
    refine ⟨233173124157639062134174085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155448749438426041422782723 233173124157639062134174085)
    ·
      refine ⟨43719960779557324150157641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233173124157639062134174085 43719960779557324150157641)
      ·
        refine ⟨32789970584667993112618231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43719960779557324150157641 32789970584667993112618231)
        ·
          refine ⟨49184955877001989668927347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32789970584667993112618231 49184955877001989668927347)
          ·
            refine ⟨73777433815502984503391021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49184955877001989668927347 73777433815502984503391021)
            ·
              refine ⟨27666537680813619188771633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73777433815502984503391021 27666537680813619188771633)
              ·
                refine ⟨20749903260610214391578725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27666537680813619188771633 20749903260610214391578725)
                ·
                  refine ⟨3890606861364415198421011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20749903260610214391578725 3890606861364415198421011)
                  ·
                    refine ⟨5835910292046622797631517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3890606861364415198421011 5835910292046622797631517)
                    ·
                      refine ⟨2188466359517483549111819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5835910292046622797631517 2188466359517483549111819)
                      ·
                        rfl

theorem cell23_4262023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_4262023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262023 prefixEnd_4262023 := by exact prefixLift 4262023
  have htrace : WordTrace (prefixWord ++ tailWord_4262023) baseStart_4262023 baseEnd_4262023 := by
    simpa [prefixWord, tailWord_4262023, baseEnd_4262023] using wordTrace_append hprefix tailTrace_4262023
  have hstable : (prefixWord ++ tailWord_4262023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262023).length < 2 ^ (prefixWord ++ tailWord_4262023).sum := by decide
  have hdescent : baseEnd_4262023 < baseStart_4262023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262024 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4262024 : Nat := 118140960795 + 4262024 * 2 ^ 59
def prefixEnd_4262024 : Nat := 4983230072969 + 3 ^ 40 * 4262024 * 2
def baseEnd_4262024 : Nat := 2188466872998138045199315

theorem tailTrace_4262024 : CollatzResearch.WordTrace tailWord_4262024 prefixEnd_4262024 2188466872998138045199315 := by
  unfold tailWord_4262024
  simp only [CollatzResearch.WordTrace]
  refine ⟨77724392955711209296784563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103632523940948279062379417 77724392955711209296784563)
  ·
    refine ⟨116586589433566813945176845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77724392955711209296784563 116586589433566813945176845)
    ·
      refine ⟨43719971037587555229441317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116586589433566813945176845 43719971037587555229441317)
      ·
        refine ⟨8197494569547666605520247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43719971037587555229441317 8197494569547666605520247)
        ·
          refine ⟨12296241854321499908280371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8197494569547666605520247 12296241854321499908280371)
          ·
            refine ⟨18444362781482249862420557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12296241854321499908280371 18444362781482249862420557)
            ·
              refine ⟨6916636043055843698407709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18444362781482249862420557 6916636043055843698407709)
              ·
                refine ⟨2593738516145941386902891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6916636043055843698407709 2593738516145941386902891)
                ·
                  refine ⟨3890607774218912080354337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593738516145941386902891 3890607774218912080354337)
                  ·
                    refine ⟨2917955830664184060265753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890607774218912080354337 2917955830664184060265753)
                    ·
                      refine ⟨2188466872998138045199315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917955830664184060265753 2188466872998138045199315)
                      ·
                        rfl

theorem cell23_4262024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4262024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262024 prefixEnd_4262024 := by exact prefixLift 4262024
  have htrace : WordTrace (prefixWord ++ tailWord_4262024) baseStart_4262024 baseEnd_4262024 := by
    simpa [prefixWord, tailWord_4262024, baseEnd_4262024] using wordTrace_append hprefix tailTrace_4262024
  have hstable : (prefixWord ++ tailWord_4262024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262024).length < 2 ^ (prefixWord ++ tailWord_4262024).sum := by decide
  have hdescent : baseEnd_4262024 < baseStart_4262024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262063 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 1, 4, 2]
def baseStart_4262063 : Nat := 118140960795 + 4262063 * 2 ^ 59
def prefixEnd_4262063 : Nat := 4983230072969 + 3 ^ 40 * 4262063 * 2
def baseEnd_4262063 : Nat := 2188486898743663392611635

theorem tailTrace_4262063 : CollatzResearch.WordTrace tailWord_4262063 prefixEnd_4262063 2188486898743663392611635 := by
  unfold tailWord_4262063
  simp only [CollatzResearch.WordTrace]
  refine ⟨155450208358281128254238843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103633472238854085502825895 155450208358281128254238843)
  ·
    refine ⟨233175312537421692381358265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155450208358281128254238843 233175312537421692381358265)
    ·
      refine ⟨174881484403066269286018699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233175312537421692381358265 174881484403066269286018699)
      ·
        refine ⟨262322226604599403929028049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174881484403066269286018699 262322226604599403929028049)
        ·
          refine ⟨196741669953449552946771037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262322226604599403929028049 196741669953449552946771037)
          ·
            refine ⟨73778126232543582355039139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196741669953449552946771037 73778126232543582355039139)
            ·
              refine ⟨110667189348815373532558709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73778126232543582355039139 110667189348815373532558709)
              ·
                refine ⟨10375049001451441268677379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110667189348815373532558709 10375049001451441268677379)
                ·
                  refine ⟨15562573502177161903016069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10375049001451441268677379 15562573502177161903016069)
                  ·
                    refine ⟨2917982531658217856815513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15562573502177161903016069 2917982531658217856815513)
                    ·
                      refine ⟨2188486898743663392611635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917982531658217856815513 2188486898743663392611635)
                      ·
                        rfl

theorem cell23_4262063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4, 2].length) (baseStart_4262063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262063 prefixEnd_4262063 := by exact prefixLift 4262063
  have htrace : WordTrace (prefixWord ++ tailWord_4262063) baseStart_4262063 baseEnd_4262063 := by
    simpa [prefixWord, tailWord_4262063, baseEnd_4262063] using wordTrace_append hprefix tailTrace_4262063
  have hstable : (prefixWord ++ tailWord_4262063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262063).length < 2 ^ (prefixWord ++ tailWord_4262063).sum := by decide
  have hdescent : baseEnd_4262063 < baseStart_4262063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262066 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_4262066 : Nat := 118140960795 + 4262066 * 2 ^ 59
def prefixEnd_4262066 : Nat := 4983230072969 + 3 ^ 40 * 4262066 * 2
def baseEnd_4262066 : Nat := 2188488439185626880874121

theorem tailTrace_4262066 : CollatzResearch.WordTrace tailWord_4262066 prefixEnd_4262066 2188488439185626880874121 := by
  unfold tailWord_4262066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38862579444317564941649513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103633545184846839844398701 38862579444317564941649513)
  ·
    refine ⟨29146934583238173706237135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38862579444317564941649513 29146934583238173706237135)
    ·
      refine ⟨43720401874857260559355703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29146934583238173706237135 43720401874857260559355703)
      ·
        refine ⟨65580602812285890839033555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43720401874857260559355703 65580602812285890839033555)
        ·
          refine ⟨98370904218428836258550333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65580602812285890839033555 98370904218428836258550333)
          ·
            refine ⟨36889089081910813596956375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98370904218428836258550333 36889089081910813596956375)
            ·
              refine ⟨55333633622866220395434563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36889089081910813596956375 55333633622866220395434563)
              ·
                refine ⟨83000450434299330593151845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55333633622866220395434563 83000450434299330593151845)
                ·
                  refine ⟨15562584456431124486215971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83000450434299330593151845 15562584456431124486215971)
                  ·
                    refine ⟨23343876684646686729323957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15562584456431124486215971 23343876684646686729323957)
                    ·
                      refine ⟨2188488439185626880874121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23343876684646686729323957 2188488439185626880874121)
                      ·
                        rfl

theorem cell23_4262066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_4262066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262066 prefixEnd_4262066 := by exact prefixLift 4262066
  have htrace : WordTrace (prefixWord ++ tailWord_4262066) baseStart_4262066 baseEnd_4262066 := by
    simpa [prefixWord, tailWord_4262066, baseEnd_4262066] using wordTrace_append hprefix tailTrace_4262066
  have hstable : (prefixWord ++ tailWord_4262066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262066).length < 2 ^ (prefixWord ++ tailWord_4262066).sum := by decide
  have hdescent : baseEnd_4262066 < baseStart_4262066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262080 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2]
def baseStart_4262080 : Nat := 118140960795 + 4262080 * 2 ^ 59
def prefixEnd_4262080 : Nat := 4983230072969 + 3 ^ 40 * 4262080 * 2
def baseEnd_4262080 : Nat := 2188495627914789826099057

theorem tailTrace_4262080 : CollatzResearch.WordTrace tailWord_4262080 prefixEnd_4262080 2188495627914789826099057 := by
  unfold tailWord_4262080
  simp only [CollatzResearch.WordTrace]
  refine ⟨77725414199609770078803847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103633885599479693438405129 77725414199609770078803847)
  ·
    refine ⟨116588121299414655118205771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77725414199609770078803847 116588121299414655118205771)
    ·
      refine ⟨174882181949121982677308657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116588121299414655118205771 174882181949121982677308657)
      ·
        refine ⟨131161636461841487007981493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174882181949121982677308657 131161636461841487007981493)
        ·
          refine ⟨12296403418297639406998265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131161636461841487007981493 12296403418297639406998265)
          ·
            refine ⟨9222302563723229555248699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12296403418297639406998265 9222302563723229555248699)
            ·
              refine ⟨13833453845584844332873049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222302563723229555248699 13833453845584844332873049)
              ·
                refine ⟨10375090384188633249654787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13833453845584844332873049 10375090384188633249654787)
                ·
                  refine ⟨15562635576282949874482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10375090384188633249654787 15562635576282949874482181)
                  ·
                    refine ⟨2917994170553053101465409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15562635576282949874482181 2917994170553053101465409)
                    ·
                      refine ⟨2188495627914789826099057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917994170553053101465409 2188495627914789826099057)
                      ·
                        rfl

theorem cell23_4262080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_4262080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262080 prefixEnd_4262080 := by exact prefixLift 4262080
  have htrace : WordTrace (prefixWord ++ tailWord_4262080) baseStart_4262080 baseEnd_4262080 := by
    simpa [prefixWord, tailWord_4262080, baseEnd_4262080] using wordTrace_append hprefix tailTrace_4262080
  have hstable : (prefixWord ++ tailWord_4262080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262080).length < 2 ^ (prefixWord ++ tailWord_4262080).sum := by decide
  have hdescent : baseEnd_4262080 < baseStart_4262080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262084 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_4262084 : Nat := 118140960795 + 4262084 * 2 ^ 59
def prefixEnd_4262084 : Nat := 4983230072969 + 3 ^ 40 * 4262084 * 2
def baseEnd_4262084 : Nat := 2188497681837407810449039

theorem tailTrace_4262084 : CollatzResearch.WordTrace tailWord_4262084 prefixEnd_4262084 2188497681837407810449039 := by
  unfold tailWord_4262084
  simp only [CollatzResearch.WordTrace]
  refine ⟨77725487145602524420376653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103633982860803365893835537 77725487145602524420376653)
  ·
    refine ⟨29147057679600946657641245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77725487145602524420376653 29147057679600946657641245)
    ·
      refine ⟨10930146629850354996615467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29147057679600946657641245 10930146629850354996615467)
      ·
        refine ⟨16395219944775532494923201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930146629850354996615467 16395219944775532494923201)
        ·
          refine ⟨12296414958581649371192401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16395219944775532494923201 12296414958581649371192401)
          ·
            refine ⟨9222311218936237028394301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12296414958581649371192401 9222311218936237028394301)
            ·
              refine ⟨3458366707101088885647863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9222311218936237028394301 3458366707101088885647863)
              ·
                refine ⟨5187550060651633328471795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458366707101088885647863 5187550060651633328471795)
                ·
                  refine ⟨7781325090977449992707693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187550060651633328471795 7781325090977449992707693)
                  ·
                    refine ⟨2917996909116543747265385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7781325090977449992707693 2917996909116543747265385)
                    ·
                      refine ⟨2188497681837407810449039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2917996909116543747265385 2188497681837407810449039)
                      ·
                        rfl

theorem cell23_4262084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_4262084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262084 prefixEnd_4262084 := by exact prefixLift 4262084
  have htrace : WordTrace (prefixWord ++ tailWord_4262084) baseStart_4262084 baseEnd_4262084 := by
    simpa [prefixWord, tailWord_4262084, baseEnd_4262084] using wordTrace_append hprefix tailTrace_4262084
  have hstable : (prefixWord ++ tailWord_4262084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262084).length < 2 ^ (prefixWord ++ tailWord_4262084).sum := by decide
  have hdescent : baseEnd_4262084 < baseStart_4262084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262096 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_4262096 : Nat := 118140960795 + 4262096 * 2 ^ 59
def prefixEnd_4262096 : Nat := 4983230072969 + 3 ^ 40 * 4262096 * 2
def baseEnd_4262096 : Nat := 2188503843605261763498983

theorem tailTrace_4262096 : CollatzResearch.WordTrace tailWord_4262096 prefixEnd_4262096 2188503843605261763498983 := by
  unfold tailWord_4262096
  simp only [CollatzResearch.WordTrace]
  refine ⟨77725705983580787445095071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103634274644774383260126761 77725705983580787445095071)
  ·
    refine ⟨116588558975371181167642607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77725705983580787445095071 116588558975371181167642607)
    ·
      refine ⟨174882838463056771751463911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116588558975371181167642607 174882838463056771751463911)
      ·
        refine ⟨262324257694585157627195867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174882838463056771751463911 262324257694585157627195867)
        ·
          refine ⟨393486386541877736440793801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262324257694585157627195867 393486386541877736440793801)
          ·
            refine ⟨295114789906408302330595351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393486386541877736440793801 295114789906408302330595351)
            ·
              refine ⟨442672184859612453495893027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295114789906408302330595351 442672184859612453495893027)
              ·
                refine ⟨664008277289418680243839541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442672184859612453495893027 664008277289418680243839541)
                ·
                  refine ⟨62250775995883001272859957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 664008277289418680243839541 62250775995883001272859957)
                  ·
                    refine ⟨5836010249614031369330621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62250775995883001272859957 5836010249614031369330621)
                    ·
                      refine ⟨2188503843605261763498983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5836010249614031369330621 2188503843605261763498983)
                      ·
                        rfl

theorem cell23_4262096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_4262096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262096 prefixEnd_4262096 := by exact prefixLift 4262096
  have htrace : WordTrace (prefixWord ++ tailWord_4262096) baseStart_4262096 baseEnd_4262096 := by
    simpa [prefixWord, tailWord_4262096, baseEnd_4262096] using wordTrace_append hprefix tailTrace_4262096
  have hstable : (prefixWord ++ tailWord_4262096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262096).length < 2 ^ (prefixWord ++ tailWord_4262096).sum := by decide
  have hdescent : baseEnd_4262096 < baseStart_4262096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262113 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_4262113 : Nat := 118140960795 + 4262113 * 2 ^ 59
def prefixEnd_4262113 : Nat := 4983230072969 + 3 ^ 40 * 4262113 * 2
def baseEnd_4262113 : Nat := 2188512572776388196986405

theorem tailTrace_4262113 : CollatzResearch.WordTrace tailWord_4262113 prefixEnd_4262113 2188512572776388196986405 := by
  unfold tailWord_4262113
  simp only [CollatzResearch.WordTrace]
  refine ⟨155452032008099986793558993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103634688005399991195705995 155452032008099986793558993)
  ·
    refine ⟨116589024006074990095169245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155452032008099986793558993 116589024006074990095169245)
    ·
      refine ⟨43720884002278121285688467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116589024006074990095169245 43720884002278121285688467)
      ·
        refine ⟨65581326003417181928532701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43720884002278121285688467 65581326003417181928532701)
        ·
          refine ⟨24592997251281443223199763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65581326003417181928532701 24592997251281443223199763)
          ·
            refine ⟨36889495876922164834799645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24592997251281443223199763 36889495876922164834799645)
            ·
              refine ⟨13833560953845811813049867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36889495876922164834799645 13833560953845811813049867)
              ·
                refine ⟨20750341430768717719574801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13833560953845811813049867 20750341430768717719574801)
                ·
                  refine ⟨15562756073076538289681101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20750341430768717719574801 15562756073076538289681101)
                  ·
                    refine ⟨5836033527403701858630413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15562756073076538289681101 5836033527403701858630413)
                    ·
                      refine ⟨2188512572776388196986405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5836033527403701858630413 2188512572776388196986405)
                      ·
                        rfl

theorem cell23_4262113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_4262113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262113 prefixEnd_4262113 := by exact prefixLift 4262113
  have htrace : WordTrace (prefixWord ++ tailWord_4262113) baseStart_4262113 baseEnd_4262113 := by
    simpa [prefixWord, tailWord_4262113, baseEnd_4262113] using wordTrace_append hprefix tailTrace_4262113
  have hstable : (prefixWord ++ tailWord_4262113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262113).length < 2 ^ (prefixWord ++ tailWord_4262113).sum := by decide
  have hdescent : baseEnd_4262113 < baseStart_4262113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262116 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_4262116 : Nat := 118140960795 + 4262116 * 2 ^ 59
def prefixEnd_4262116 : Nat := 4983230072969 + 3 ^ 40 * 4262116 * 2
def baseEnd_4262116 : Nat := 729504704406117228416297

theorem tailTrace_4262116 : CollatzResearch.WordTrace tailWord_4262116 prefixEnd_4262116 729504704406117228416297 := by
  unfold tailWord_4262116
  simp only [CollatzResearch.WordTrace]
  refine ⟨77726070713544559152959101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103634760951392745537278801 77726070713544559152959101)
  ·
    refine ⟨29147276517579209682359663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77726070713544559152959101 29147276517579209682359663)
    ·
      refine ⟨43720914776368814523539495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29147276517579209682359663 43720914776368814523539495)
      ·
        refine ⟨65581372164553221785309243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43720914776368814523539495 65581372164553221785309243)
        ·
          refine ⟨98372058246829832677963865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65581372164553221785309243 98372058246829832677963865)
          ·
            refine ⟨73779043685122374508472899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98372058246829832677963865 73779043685122374508472899)
            ·
              refine ⟨110668565527683561762709349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73779043685122374508472899 110668565527683561762709349)
              ·
                refine ⟨20750356036440667830508003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110668565527683561762709349 20750356036440667830508003)
                ·
                  refine ⟨31125534054661001745762005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20750356036440667830508003 31125534054661001745762005)
                  ·
                    refine ⟨729504704406117228416297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31125534054661001745762005 729504704406117228416297)
                    ·
                      rfl

theorem cell23_4262116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_4262116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262116 prefixEnd_4262116 := by exact prefixLift 4262116
  have htrace : WordTrace (prefixWord ++ tailWord_4262116) baseStart_4262116 baseEnd_4262116 := by
    simpa [prefixWord, tailWord_4262116, baseEnd_4262116] using wordTrace_append hprefix tailTrace_4262116
  have hstable : (prefixWord ++ tailWord_4262116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262116).length < 2 ^ (prefixWord ++ tailWord_4262116).sum := by decide
  have hdescent : baseEnd_4262116 < baseStart_4262116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262123 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 5, 2]
def baseStart_4262123 : Nat := 118140960795 + 4262123 * 2 ^ 59
def prefixEnd_4262123 : Nat := 4983230072969 + 3 ^ 40 * 4262123 * 2
def baseEnd_4262123 : Nat := 2188517707582933157861359

theorem tailTrace_4262123 : CollatzResearch.WordTrace tailWord_4262123 prefixEnd_4262123 2188517707582933157861359 := by
  unfold tailWord_4262123
  simp only [CollatzResearch.WordTrace]
  refine ⟨155452396738063758501423023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103634931158709172334282015 155452396738063758501423023)
  ·
    refine ⟨233178595107095637752134535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155452396738063758501423023 233178595107095637752134535)
    ·
      refine ⟨349767892660643456628201803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233178595107095637752134535 349767892660643456628201803)
      ·
        refine ⟨524651838990965184942302705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349767892660643456628201803 524651838990965184942302705)
        ·
          refine ⟨393488879243223888706727029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524651838990965184942302705 393488879243223888706727029)
          ·
            refine ⟨36889582429052239566255659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 393488879243223888706727029 36889582429052239566255659)
            ·
              refine ⟨55334373643578359349383489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36889582429052239566255659 55334373643578359349383489)
              ·
                refine ⟨41500780232683769512037617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55334373643578359349383489 41500780232683769512037617)
                ·
                  refine ⟨31125585174512827134028213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41500780232683769512037617 31125585174512827134028213)
                  ·
                    refine ⟨2918023610110577543815145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31125585174512827134028213 2918023610110577543815145)
                    ·
                      refine ⟨2188517707582933157861359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918023610110577543815145 2188517707582933157861359)
                      ·
                        rfl

theorem cell23_4262123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5, 2].length) (baseStart_4262123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262123 prefixEnd_4262123 := by exact prefixLift 4262123
  have htrace : WordTrace (prefixWord ++ tailWord_4262123) baseStart_4262123 baseEnd_4262123 := by
    simpa [prefixWord, tailWord_4262123, baseEnd_4262123] using wordTrace_append hprefix tailTrace_4262123
  have hstable : (prefixWord ++ tailWord_4262123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262123).length < 2 ^ (prefixWord ++ tailWord_4262123).sum := by decide
  have hdescent : baseEnd_4262123 < baseStart_4262123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262180 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_4262180 : Nat := 118140960795 + 4262180 * 2 ^ 59
def prefixEnd_4262180 : Nat := 4983230072969 + 3 ^ 40 * 4262180 * 2
def baseEnd_4262180 : Nat := 729515658660079811616199

theorem tailTrace_4262180 : CollatzResearch.WordTrace tailWord_4262180 prefixEnd_4262180 729515658660079811616199 := by
  unfold tailWord_4262180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77727237849428628618123997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103636317132571504824165329 77727237849428628618123997)
  ·
    refine ⟨29147714193535735731796499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77727237849428628618123997 29147714193535735731796499)
    ·
      refine ⟨43721571290303603597694749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29147714193535735731796499 43721571290303603597694749)
      ·
        refine ⟨16395589233863851349135531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43721571290303603597694749 16395589233863851349135531)
        ·
          refine ⟨24593383850795777023703297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16395589233863851349135531 24593383850795777023703297)
          ·
            refine ⟨18445037888096832767777473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24593383850795777023703297 18445037888096832767777473)
            ·
              refine ⟨13833778416072624575833105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18445037888096832767777473 13833778416072624575833105)
              ·
                refine ⟨10375333812054468431874829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13833778416072624575833105 10375333812054468431874829)
                ·
                  refine ⟨3890750179520425661953061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10375333812054468431874829 3890750179520425661953061)
                  ·
                    refine ⟨729515658660079811616199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3890750179520425661953061 729515658660079811616199)
                    ·
                      rfl

theorem cell23_4262180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_4262180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262180 prefixEnd_4262180 := by exact prefixLift 4262180
  have htrace : WordTrace (prefixWord ++ tailWord_4262180) baseStart_4262180 baseEnd_4262180 := by
    simpa [prefixWord, tailWord_4262180, baseEnd_4262180] using wordTrace_append hprefix tailTrace_4262180
  have hstable : (prefixWord ++ tailWord_4262180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262180).length < 2 ^ (prefixWord ++ tailWord_4262180).sum := by decide
  have hdescent : baseEnd_4262180 < baseStart_4262180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262238 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4262238 : Nat := 118140960795 + 4262238 * 2 ^ 59
def prefixEnd_4262238 : Nat := 4983230072969 + 3 ^ 40 * 4262238 * 2
def baseEnd_4262238 : Nat := 2188576757858200207923331

theorem tailTrace_4262238 : CollatzResearch.WordTrace tailWord_4262238 prefixEnd_4262238 2188576757858200207923331 := by
  unfold tailWord_4262238
  simp only [CollatzResearch.WordTrace]
  refine ⟨19432073891580891642732421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103637727421764755427906245 19432073891580891642732421)
  ·
    refine ⟨3643513854671417183012329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19432073891580891642732421 3643513854671417183012329)
    ·
      refine ⟨2732635391003562887259247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3643513854671417183012329 2732635391003562887259247)
      ·
        refine ⟨4098953086505344330888871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732635391003562887259247 4098953086505344330888871)
        ·
          refine ⟨6148429629758016496333307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098953086505344330888871 6148429629758016496333307)
          ·
            refine ⟨9222644444637024744499961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148429629758016496333307 9222644444637024744499961)
            ·
              refine ⟨6916983333477768558374971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9222644444637024744499961 6916983333477768558374971)
              ·
                refine ⟨10375475000216652837562457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6916983333477768558374971 10375475000216652837562457)
                ·
                  refine ⟨7781606250162489628171843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10375475000216652837562457 7781606250162489628171843)
                  ·
                    refine ⟨11672409375243734442257765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7781606250162489628171843 11672409375243734442257765)
                    ·
                      refine ⟨2188576757858200207923331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11672409375243734442257765 2188576757858200207923331)
                      ·
                        rfl

theorem cell23_4262238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4262238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262238 prefixEnd_4262238 := by exact prefixLift 4262238
  have htrace : WordTrace (prefixWord ++ tailWord_4262238) baseStart_4262238 baseEnd_4262238 := by
    simpa [prefixWord, tailWord_4262238, baseEnd_4262238] using wordTrace_append hprefix tailTrace_4262238
  have hstable : (prefixWord ++ tailWord_4262238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262238).length < 2 ^ (prefixWord ++ tailWord_4262238).sum := by decide
  have hdescent : baseEnd_4262238 < baseStart_4262238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262240 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_4262240 : Nat := 118140960795 + 4262240 * 2 ^ 59
def prefixEnd_4262240 : Nat := 4983230072969 + 3 ^ 40 * 4262240 * 2
def baseEnd_4262240 : Nat := 729525928273169733366107

theorem tailTrace_4262240 : CollatzResearch.WordTrace tailWord_4262240 prefixEnd_4262240 729525928273169733366107 := by
  unfold tailWord_4262240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77728332039319943741716087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103637776052426591655621449 77728332039319943741716087)
  ·
    refine ⟨116592498058979915612574131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77728332039319943741716087 116592498058979915612574131)
    ·
      refine ⟨174888747088469873418861197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116592498058979915612574131 174888747088469873418861197)
      ·
        refine ⟨65583280158176202532072949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174888747088469873418861197 65583280158176202532072949)
        ·
          refine ⟨6148432514829018987381839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65583280158176202532072949 6148432514829018987381839)
          ·
            refine ⟨9222648772243528481072759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148432514829018987381839 9222648772243528481072759)
            ·
              refine ⟨13833973158365292721609139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222648772243528481072759 13833973158365292721609139)
              ·
                refine ⟨20750959737547939082413709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13833973158365292721609139 20750959737547939082413709)
                ·
                  refine ⟨7781609901580477155905141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20750959737547939082413709 7781609901580477155905141)
                  ·
                    refine ⟨729525928273169733366107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7781609901580477155905141 729525928273169733366107)
                    ·
                      rfl

theorem cell23_4262240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_4262240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262240 prefixEnd_4262240 := by exact prefixLift 4262240
  have htrace : WordTrace (prefixWord ++ tailWord_4262240) baseStart_4262240 baseEnd_4262240 := by
    simpa [prefixWord, tailWord_4262240, baseEnd_4262240] using wordTrace_append hprefix tailTrace_4262240
  have hstable : (prefixWord ++ tailWord_4262240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262240).length < 2 ^ (prefixWord ++ tailWord_4262240).sum := by decide
  have hdescent : baseEnd_4262240 < baseStart_4262240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262247 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_4262247 : Nat := 118140960795 + 4262247 * 2 ^ 59
def prefixEnd_4262247 : Nat := 4983230072969 + 3 ^ 40 * 4262247 * 2
def baseEnd_4262247 : Nat := 2188581379184090672710789

theorem tailTrace_4262247 : CollatzResearch.WordTrace tailWord_4262247 prefixEnd_4262247 2188581379184090672710789 := by
  unfold tailWord_4262247
  simp only [CollatzResearch.WordTrace]
  refine ⟨155456919389614527678936995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103637946259743018452624663 155456919389614527678936995)
  ·
    refine ⟨233185379084421791518405493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155456919389614527678936995 233185379084421791518405493)
    ·
      refine ⟨21861129289164542954850515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 233185379084421791518405493 21861129289164542954850515)
      ·
        refine ⟨32791693933746814432275773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21861129289164542954850515 32791693933746814432275773)
        ·
          refine ⟨12296885225155055412103415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32791693933746814432275773 12296885225155055412103415)
          ·
            refine ⟨18445327837732583118155123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12296885225155055412103415 18445327837732583118155123)
            ·
              refine ⟨27667991756598874677232685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18445327837732583118155123 27667991756598874677232685)
              ·
                refine ⟨10375496908724578003962257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27667991756598874677232685 10375496908724578003962257)
                ·
                  refine ⟨7781622681543433502971693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10375496908724578003962257 7781622681543433502971693)
                  ·
                    refine ⟨2918108505578787563614385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7781622681543433502971693 2918108505578787563614385)
                    ·
                      refine ⟨2188581379184090672710789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918108505578787563614385 2188581379184090672710789)
                      ·
                        rfl

theorem cell23_4262247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_4262247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262247 prefixEnd_4262247 := by exact prefixLift 4262247
  have htrace : WordTrace (prefixWord ++ tailWord_4262247) baseStart_4262247 baseEnd_4262247 := by
    simpa [prefixWord, tailWord_4262247, baseEnd_4262247] using wordTrace_append hprefix tailTrace_4262247
  have hstable : (prefixWord ++ tailWord_4262247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262247).length < 2 ^ (prefixWord ++ tailWord_4262247).sum := by decide
  have hdescent : baseEnd_4262247 < baseStart_4262247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262263 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_4262263 : Nat := 118140960795 + 4262263 * 2 ^ 59
def prefixEnd_4262263 : Nat := 4983230072969 + 3 ^ 40 * 4262263 * 2
def baseEnd_4262263 : Nat := 2188589594874562610110715

theorem tailTrace_4262263 : CollatzResearch.WordTrace tailWord_4262263 prefixEnd_4262263 2188589594874562610110715 := by
  unfold tailWord_4262263
  simp only [CollatzResearch.WordTrace]
  refine ⟨155457502957556562411519443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103638335305037708274346295 155457502957556562411519443)
  ·
    refine ⟨233186254436334843617279165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155457502957556562411519443 233186254436334843617279165)
    ·
      refine ⟨87444845413625566356479687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233186254436334843617279165 87444845413625566356479687)
      ·
        refine ⟨131167268120438349534719531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87444845413625566356479687 131167268120438349534719531)
        ·
          refine ⟨196750902180657524302079297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131167268120438349534719531 196750902180657524302079297)
          ·
            refine ⟨147563176635493143226559473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196750902180657524302079297 147563176635493143226559473)
            ·
              refine ⟨110672382476619857419919605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147563176635493143226559473 110672382476619857419919605)
              ·
                refine ⟨10375535857183111633117463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110672382476619857419919605 10375535857183111633117463)
                ·
                  refine ⟨15563303785774667449676195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10375535857183111633117463 15563303785774667449676195)
                  ·
                    refine ⟨23344955678662001174514293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15563303785774667449676195 23344955678662001174514293)
                    ·
                      refine ⟨2188589594874562610110715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23344955678662001174514293 2188589594874562610110715)
                      ·
                        rfl

theorem cell23_4262263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_4262263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262263 prefixEnd_4262263 := by exact prefixLift 4262263
  have htrace : WordTrace (prefixWord ++ tailWord_4262263) baseStart_4262263 baseEnd_4262263 := by
    simpa [prefixWord, tailWord_4262263, baseEnd_4262263] using wordTrace_append hprefix tailTrace_4262263
  have hstable : (prefixWord ++ tailWord_4262263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262263).length < 2 ^ (prefixWord ++ tailWord_4262263).sum := by decide
  have hdescent : baseEnd_4262263 < baseStart_4262263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262277 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 3, 2, 2]
def baseStart_4262277 : Nat := 118140960795 + 4262277 * 2 ^ 59
def prefixEnd_4262277 : Nat := 4983230072969 + 3 ^ 40 * 4262277 * 2
def baseEnd_4262277 : Nat := 2188596783603725555335651

theorem tailTrace_4262277 : CollatzResearch.WordTrace tailWord_4262277 prefixEnd_4262277 2188596783603725555335651 := by
  unfold tailWord_4262277
  simp only [CollatzResearch.WordTrace]
  refine ⟨155458013579505842802529085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103638675719670561868352723 155458013579505842802529085)
  ·
    refine ⟨58296755092314691050948407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155458013579505842802529085 58296755092314691050948407)
    ·
      refine ⟨87445132638472036576422611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58296755092314691050948407 87445132638472036576422611)
      ·
        refine ⟨131167698957708054864633917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87445132638472036576422611 131167698957708054864633917)
        ·
          refine ⟨49187887109140520574237719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131167698957708054864633917 49187887109140520574237719)
          ·
            refine ⟨73781830663710780861356579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49187887109140520574237719 73781830663710780861356579)
            ·
              refine ⟨110672745995566171292034869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73781830663710780861356579 110672745995566171292034869)
              ·
                refine ⟨10375569937084328558628269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110672745995566171292034869 10375569937084328558628269)
                ·
                  refine ⟨3890838726406623209485601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10375569937084328558628269 3890838726406623209485601)
                  ·
                    refine ⟨2918129044804967407114201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890838726406623209485601 2918129044804967407114201)
                    ·
                      refine ⟨2188596783603725555335651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918129044804967407114201 2188596783603725555335651)
                      ·
                        rfl

theorem cell23_4262277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_4262277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262277 prefixEnd_4262277 := by exact prefixLift 4262277
  have htrace : WordTrace (prefixWord ++ tailWord_4262277) baseStart_4262277 baseEnd_4262277 := by
    simpa [prefixWord, tailWord_4262277, baseEnd_4262277] using wordTrace_append hprefix tailTrace_4262277
  have hstable : (prefixWord ++ tailWord_4262277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262277).length < 2 ^ (prefixWord ++ tailWord_4262277).sum := by decide
  have hdescent : baseEnd_4262277 < baseStart_4262277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262280 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_4262280 : Nat := 118140960795 + 4262280 * 2 ^ 59
def prefixEnd_4262280 : Nat := 4983230072969 + 3 ^ 40 * 4262280 * 2
def baseEnd_4262280 : Nat := 2188598324045689043598137

theorem tailTrace_4262280 : CollatzResearch.WordTrace tailWord_4262280 prefixEnd_4262280 2188598324045689043598137 := by
  unfold tailWord_4262280
  simp only [CollatzResearch.WordTrace]
  refine ⟨77729061499247487157444147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103638748665663316209925529 77729061499247487157444147)
  ·
    refine ⟨116593592248871230736166221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77729061499247487157444147 116593592248871230736166221)
    ·
      refine ⟨43722597093326711526062333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116593592248871230736166221 43722597093326711526062333)
      ·
        refine ⟨16395973909997516822273375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43722597093326711526062333 16395973909997516822273375)
        ·
          refine ⟨24593960864996275233410063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16395973909997516822273375 24593960864996275233410063)
          ·
            refine ⟨36890941297494412850115095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24593960864996275233410063 36890941297494412850115095)
            ·
              refine ⟨55336411946241619275172643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36890941297494412850115095 55336411946241619275172643)
              ·
                refine ⟨83004617919362428912758965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55336411946241619275172643 83004617919362428912758965)
                ·
                  refine ⟨7781682929940227710571153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83004617919362428912758965 7781682929940227710571153)
                  ·
                    refine ⟨5836262197455170782928365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7781682929940227710571153 5836262197455170782928365)
                    ·
                      refine ⟨2188598324045689043598137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5836262197455170782928365 2188598324045689043598137)
                      ·
                        rfl

theorem cell23_4262280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_4262280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262280 prefixEnd_4262280 := by exact prefixLift 4262280
  have htrace : WordTrace (prefixWord ++ tailWord_4262280) baseStart_4262280 baseEnd_4262280 := by
    simpa [prefixWord, tailWord_4262280, baseEnd_4262280] using wordTrace_append hprefix tailTrace_4262280
  have hstable : (prefixWord ++ tailWord_4262280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262280).length < 2 ^ (prefixWord ++ tailWord_4262280).sum := by decide
  have hdescent : baseEnd_4262280 < baseStart_4262280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262283 : List Nat := [1, 1, 1, 1, 4, 4, 3, 8]
def baseStart_4262283 : Nat := 118140960795 + 4262283 * 2 ^ 59
def prefixEnd_4262283 : Nat := 4983230072969 + 3 ^ 40 * 4262283 * 2
def baseEnd_4262283 : Nat := 81059254240283427105949

theorem tailTrace_4262283 : CollatzResearch.WordTrace tailWord_4262283 prefixEnd_4262283 81059254240283427105949 := by
  unfold tailWord_4262283
  simp only [CollatzResearch.WordTrace]
  refine ⟨155458232417484105827247503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103638821611656070551498335 155458232417484105827247503)
  ·
    refine ⟨233187348626226158740871255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155458232417484105827247503 233187348626226158740871255)
    ·
      refine ⟨349781022939339238111306883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233187348626226158740871255 349781022939339238111306883)
      ·
        refine ⟨524671534409008857166960325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349781022939339238111306883 524671534409008857166960325)
        ·
          refine ⟨98375912701689160718805061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 524671534409008857166960325 98375912701689160718805061)
          ·
            refine ⟨18445483631566717634775949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98375912701689160718805061 18445483631566717634775949)
            ·
              refine ⟨6917056361837519113040981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18445483631566717634775949 6917056361837519113040981)
              ·
                refine ⟨81059254240283427105949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6917056361837519113040981 81059254240283427105949)
                ·
                  rfl

theorem cell23_4262283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 8].length) (baseStart_4262283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262283 prefixEnd_4262283 := by exact prefixLift 4262283
  have htrace : WordTrace (prefixWord ++ tailWord_4262283) baseStart_4262283 baseEnd_4262283 := by
    simpa [prefixWord, tailWord_4262283, baseEnd_4262283] using wordTrace_append hprefix tailTrace_4262283
  have hstable : (prefixWord ++ tailWord_4262283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262283).length < 2 ^ (prefixWord ++ tailWord_4262283).sum := by decide
  have hdescent : baseEnd_4262283 < baseStart_4262283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262311 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_4262311 : Nat := 118140960795 + 4262311 * 2 ^ 59
def prefixEnd_4262311 : Nat := 4983230072969 + 3 ^ 40 * 4262311 * 2
def baseEnd_4262311 : Nat := 2188614241945978422310495

theorem tailTrace_4262311 : CollatzResearch.WordTrace tailWord_4262311 prefixEnd_4262311 2188614241945978422310495 := by
  unfold tailWord_4262311
  simp only [CollatzResearch.WordTrace]
  refine ⟨155459253661382666609266787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103639502440921777739511191 155459253661382666609266787)
  ·
    refine ⟨233188880492073999913900181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155459253661382666609266787 233188880492073999913900181)
    ·
      refine ⟨10930728773065968745964071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 233188880492073999913900181 10930728773065968745964071)
      ·
        refine ⟨16396093159598953118946107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930728773065968745964071 16396093159598953118946107)
        ·
          refine ⟨24594139739398429678419161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16396093159598953118946107 24594139739398429678419161)
          ·
            refine ⟨18445604804548822258814371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24594139739398429678419161 18445604804548822258814371)
            ·
              refine ⟨27668407206823233388221557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18445604804548822258814371 27668407206823233388221557)
              ·
                refine ⟨2593913175639678130145771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27668407206823233388221557 2593913175639678130145771)
                ·
                  refine ⟨3890869763459517195218657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2593913175639678130145771 3890869763459517195218657)
                  ·
                    refine ⟨2918152322594637896413993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890869763459517195218657 2918152322594637896413993)
                    ·
                      refine ⟨2188614241945978422310495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918152322594637896413993 2188614241945978422310495)
                      ·
                        rfl

theorem cell23_4262311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_4262311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262311 prefixEnd_4262311 := by exact prefixLift 4262311
  have htrace : WordTrace (prefixWord ++ tailWord_4262311) baseStart_4262311 baseEnd_4262311 := by
    simpa [prefixWord, tailWord_4262311, baseEnd_4262311] using wordTrace_append hprefix tailTrace_4262311
  have hstable : (prefixWord ++ tailWord_4262311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262311).length < 2 ^ (prefixWord ++ tailWord_4262311).sum := by decide
  have hdescent : baseEnd_4262311 < baseStart_4262311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262327 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_4262327 : Nat := 118140960795 + 4262327 * 2 ^ 59
def prefixEnd_4262327 : Nat := 4983230072969 + 3 ^ 40 * 4262327 * 2
def baseEnd_4262327 : Nat := 2188622457636450359710421

theorem tailTrace_4262327 : CollatzResearch.WordTrace tailWord_4262327 prefixEnd_4262327 2188622457636450359710421 := by
  unfold tailWord_4262327
  simp only [CollatzResearch.WordTrace]
  refine ⟨155459837229324701341849235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103639891486216467561232823 155459837229324701341849235)
  ·
    refine ⟨233189755843987052012773853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155459837229324701341849235 233189755843987052012773853)
    ·
      refine ⟨87446158441495144504790195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233189755843987052012773853 87446158441495144504790195)
      ·
        refine ⟨131169237662242716757185293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87446158441495144504790195 131169237662242716757185293)
        ·
          refine ⟨49188464123341018783944485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131169237662242716757185293 49188464123341018783944485)
          ·
            refine ⟨9222837023126441021989591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49188464123341018783944485 9222837023126441021989591)
            ·
              refine ⟨13834255534689661532984387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222837023126441021989591 13834255534689661532984387)
              ·
                refine ⟨20751383302034492299476581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13834255534689661532984387 20751383302034492299476581)
                ·
                  refine ⟨3890884369131467306151859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20751383302034492299476581 3890884369131467306151859)
                  ·
                    refine ⟨5836326553697200959227789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3890884369131467306151859 5836326553697200959227789)
                    ·
                      refine ⟨2188622457636450359710421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5836326553697200959227789 2188622457636450359710421)
                      ·
                        rfl

theorem cell23_4262327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_4262327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262327 prefixEnd_4262327 := by exact prefixLift 4262327
  have htrace : WordTrace (prefixWord ++ tailWord_4262327) baseStart_4262327 baseEnd_4262327 := by
    simpa [prefixWord, tailWord_4262327, baseEnd_4262327] using wordTrace_append hprefix tailTrace_4262327
  have hstable : (prefixWord ++ tailWord_4262327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262327).length < 2 ^ (prefixWord ++ tailWord_4262327).sum := by decide
  have hdescent : baseEnd_4262327 < baseStart_4262327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262353 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_4262353 : Nat := 118140960795 + 4262353 * 2 ^ 59
def prefixEnd_4262353 : Nat := 4983230072969 + 3 ^ 40 * 4262353 * 2
def baseEnd_4262353 : Nat := 2188635808133467257985301

theorem tailTrace_4262353 : CollatzResearch.WordTrace tailWord_4262353 prefixEnd_4262353 2188635808133467257985301 := by
  unfold tailWord_4262353
  simp only [CollatzResearch.WordTrace]
  refine ⟨155460785527230507782295713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103640523684820338521530475 155460785527230507782295713)
  ·
    refine ⟨116595589145422880836721785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155460785527230507782295713 116595589145422880836721785)
    ·
      refine ⟨87446691859067160627541339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116595589145422880836721785 87446691859067160627541339)
      ·
        refine ⟨131170037788600740941312009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87446691859067160627541339 131170037788600740941312009)
        ·
          refine ⟨98377528341450555705984007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131170037788600740941312009 98377528341450555705984007)
          ·
            refine ⟨147566292512175833558976011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98377528341450555705984007 147566292512175833558976011)
            ·
              refine ⟨221349438768263750338464017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147566292512175833558976011 221349438768263750338464017)
              ·
                refine ⟨166012079076197812753848013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221349438768263750338464017 166012079076197812753848013)
                ·
                  refine ⟨62254529653574179782693005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166012079076197812753848013 62254529653574179782693005)
                  ·
                    refine ⟨23345448620090317418509877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62254529653574179782693005 23345448620090317418509877)
                    ·
                      refine ⟨2188635808133467257985301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23345448620090317418509877 2188635808133467257985301)
                      ·
                        rfl

theorem cell23_4262353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_4262353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262353 prefixEnd_4262353 := by exact prefixLift 4262353
  have htrace : WordTrace (prefixWord ++ tailWord_4262353) baseStart_4262353 baseEnd_4262353 := by
    simpa [prefixWord, tailWord_4262353, baseEnd_4262353] using wordTrace_append hprefix tailTrace_4262353
  have hstable : (prefixWord ++ tailWord_4262353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262353).length < 2 ^ (prefixWord ++ tailWord_4262353).sum := by decide
  have hdescent : baseEnd_4262353 < baseStart_4262353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262363 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_4262363 : Nat := 118140960795 + 4262363 * 2 ^ 59
def prefixEnd_4262363 : Nat := 4983230072969 + 3 ^ 40 * 4262363 * 2
def baseEnd_4262363 : Nat := 2188640942940012218860255

theorem tailTrace_4262363 : CollatzResearch.WordTrace tailWord_4262363 prefixEnd_4262363 2188640942940012218860255 := by
  unfold tailWord_4262363
  simp only [CollatzResearch.WordTrace]
  refine ⟨155461150257194279490159743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103640766838129519660106495 155461150257194279490159743)
  ·
    refine ⟨233191725385791419235239615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155461150257194279490159743 233191725385791419235239615)
    ·
      refine ⟨349787588078687128852859423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233191725385791419235239615 349787588078687128852859423)
      ·
        refine ⟨524681382118030693279289135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349787588078687128852859423 524681382118030693279289135)
        ·
          refine ⟨787022073177046039918933703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524681382118030693279289135 787022073177046039918933703)
          ·
            refine ⟨1180533109765569059878400555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787022073177046039918933703 1180533109765569059878400555)
            ·
              refine ⟨1770799664648353589817600833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180533109765569059878400555 1770799664648353589817600833)
              ·
                refine ⟨1328099748486265192363200625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770799664648353589817600833 1328099748486265192363200625)
                ·
                  refine ⟨996074811364698894272400469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328099748486265192363200625 996074811364698894272400469)
                  ·
                    refine ⟨11672751695680065167254693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 996074811364698894272400469 11672751695680065167254693)
                    ·
                      refine ⟨2188640942940012218860255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11672751695680065167254693 2188640942940012218860255)
                      ·
                        rfl

theorem cell23_4262363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_4262363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262363 prefixEnd_4262363 := by exact prefixLift 4262363
  have htrace : WordTrace (prefixWord ++ tailWord_4262363) baseStart_4262363 baseEnd_4262363 := by
    simpa [prefixWord, tailWord_4262363, baseEnd_4262363] using wordTrace_append hprefix tailTrace_4262363
  have hstable : (prefixWord ++ tailWord_4262363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262363).length < 2 ^ (prefixWord ++ tailWord_4262363).sum := by decide
  have hdescent : baseEnd_4262363 < baseStart_4262363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262383 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_4262383 : Nat := 118140960795 + 4262383 * 2 ^ 59
def prefixEnd_4262383 : Nat := 4983230072969 + 3 ^ 40 * 4262383 * 2
def baseEnd_4262383 : Nat := 2188651212553102140610163

theorem tailTrace_4262383 : CollatzResearch.WordTrace tailWord_4262383 prefixEnd_4262383 2188651212553102140610163 := by
  unfold tailWord_4262383
  simp only [CollatzResearch.WordTrace]
  refine ⟨155461879717121822905887803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103641253144747881937258535 155461879717121822905887803)
  ·
    refine ⟨233192819575682734358831705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155461879717121822905887803 233192819575682734358831705)
    ·
      refine ⟨174894614681762050769123779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233192819575682734358831705 174894614681762050769123779)
      ·
        refine ⟨262341922022643076153685669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174894614681762050769123779 262341922022643076153685669)
        ·
          refine ⟨49189110379245576778816063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262341922022643076153685669 49189110379245576778816063)
          ·
            refine ⟨73783665568868365168224095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49189110379245576778816063 73783665568868365168224095)
            ·
              refine ⟨110675498353302547752336143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73783665568868365168224095 110675498353302547752336143)
              ·
                refine ⟨166013247529953821628504215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110675498353302547752336143 166013247529953821628504215)
                ·
                  refine ⟨249019871294930732442756323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166013247529953821628504215 249019871294930732442756323)
                  ·
                    refine ⟨373529806942396098664134485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249019871294930732442756323 373529806942396098664134485)
                    ·
                      refine ⟨2188651212553102140610163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 373529806942396098664134485 2188651212553102140610163)
                      ·
                        rfl

theorem cell23_4262383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_4262383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262383 prefixEnd_4262383 := by exact prefixLift 4262383
  have htrace : WordTrace (prefixWord ++ tailWord_4262383) baseStart_4262383 baseEnd_4262383 := by
    simpa [prefixWord, tailWord_4262383, baseEnd_4262383] using wordTrace_append hprefix tailTrace_4262383
  have hstable : (prefixWord ++ tailWord_4262383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262383).length < 2 ^ (prefixWord ++ tailWord_4262383).sum := by decide
  have hdescent : baseEnd_4262383 < baseStart_4262383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262384 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2]
def baseStart_4262384 : Nat := 118140960795 + 4262384 * 2 ^ 59
def prefixEnd_4262384 : Nat := 4983230072969 + 3 ^ 40 * 4262384 * 2
def baseEnd_4262384 : Nat := 2188651726033756636697659

theorem tailTrace_4262384 : CollatzResearch.WordTrace tailWord_4262384 prefixEnd_4262384 2188651726033756636697659 := by
  unfold tailWord_4262384
  simp only [CollatzResearch.WordTrace]
  refine ⟨77730958095059100038337103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103641277460078800051116137 77730958095059100038337103)
  ·
    refine ⟨116596437142588650057505655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77730958095059100038337103 116596437142588650057505655)
    ·
      refine ⟨174894655713882975086258483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116596437142588650057505655 174894655713882975086258483)
      ·
        refine ⟨262341983570824462629387725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174894655713882975086258483 262341983570824462629387725)
        ·
          refine ⟨98378243839059173486020397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262341983570824462629387725 98378243839059173486020397)
          ·
            refine ⟨36891841439647190057257649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98378243839059173486020397 36891841439647190057257649)
            ·
              refine ⟨27668881079735392542943237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36891841439647190057257649 27668881079735392542943237)
              ·
                refine ⟨5187915202450386101801857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27668881079735392542943237 5187915202450386101801857)
                ·
                  refine ⟨3890936401837789576351393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5187915202450386101801857 3890936401837789576351393)
                  ·
                    refine ⟨2918202301378342182263545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890936401837789576351393 2918202301378342182263545)
                    ·
                      refine ⟨2188651726033756636697659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918202301378342182263545 2188651726033756636697659)
                      ·
                        rfl

theorem cell23_4262384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2].length) (baseStart_4262384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262384 prefixEnd_4262384 := by exact prefixLift 4262384
  have htrace : WordTrace (prefixWord ++ tailWord_4262384) baseStart_4262384 baseEnd_4262384 := by
    simpa [prefixWord, tailWord_4262384, baseEnd_4262384] using wordTrace_append hprefix tailTrace_4262384
  have hstable : (prefixWord ++ tailWord_4262384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262384).length < 2 ^ (prefixWord ++ tailWord_4262384).sum := by decide
  have hdescent : baseEnd_4262384 < baseStart_4262384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262401 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_4262401 : Nat := 118140960795 + 4262401 * 2 ^ 59
def prefixEnd_4262401 : Nat := 4983230072969 + 3 ^ 40 * 4262401 * 2
def baseEnd_4262401 : Nat := 2188660455204883070185081

theorem tailTrace_4262401 : CollatzResearch.WordTrace tailWord_4262401 prefixEnd_4262401 2188660455204883070185081 := by
  unfold tailWord_4262401
  simp only [CollatzResearch.WordTrace]
  refine ⟨155462536231056611980043057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103641690820704407986695371 155462536231056611980043057)
  ·
    refine ⟨116596902173292458985032293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155462536231056611980043057 116596902173292458985032293)
    ·
      refine ⟨21861919157492336059693555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116596902173292458985032293 21861919157492336059693555)
      ·
        refine ⟨32792878736238504089540333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21861919157492336059693555 32792878736238504089540333)
        ·
          refine ⟨12297329526089439033577625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32792878736238504089540333 12297329526089439033577625)
          ·
            refine ⟨9222997144567079275183219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12297329526089439033577625 9222997144567079275183219)
            ·
              refine ⟨13834495716850618912774829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9222997144567079275183219 13834495716850618912774829)
              ·
                refine ⟨5187935893818982092290561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13834495716850618912774829 5187935893818982092290561)
                ·
                  refine ⟨3890951920364236569217921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5187935893818982092290561 3890951920364236569217921)
                  ·
                    refine ⟨2918213940273177426913441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3890951920364236569217921 2918213940273177426913441)
                    ·
                      refine ⟨2188660455204883070185081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918213940273177426913441 2188660455204883070185081)
                      ·
                        rfl

theorem cell23_4262401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_4262401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262401 prefixEnd_4262401 := by exact prefixLift 4262401
  have htrace : WordTrace (prefixWord ++ tailWord_4262401) baseStart_4262401 baseEnd_4262401 := by
    simpa [prefixWord, tailWord_4262401, baseEnd_4262401] using wordTrace_append hprefix tailTrace_4262401
  have hstable : (prefixWord ++ tailWord_4262401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262401).length < 2 ^ (prefixWord ++ tailWord_4262401).sum := by decide
  have hdescent : baseEnd_4262401 < baseStart_4262401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262474 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_4262474 : Nat := 118140960795 + 4262474 * 2 ^ 59
def prefixEnd_4262474 : Nat := 4983230072969 + 3 ^ 40 * 4262474 * 2
def baseEnd_4262474 : Nat := 2188697939292661284572245

theorem tailTrace_4262474 : CollatzResearch.WordTrace tailWord_4262474 prefixEnd_4262474 2188697939292661284572245 := by
  unfold tailWord_4262474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38866299689948036361862619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103643465839861430298300317 38866299689948036361862619)
  ·
    refine ⟨58299449534922054542793929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38866299689948036361862619 58299449534922054542793929)
    ·
      refine ⟨43724587151191540907095447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58299449534922054542793929 43724587151191540907095447)
      ·
        refine ⟨65586880726787311360643171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43724587151191540907095447 65586880726787311360643171)
        ·
          refine ⟨98380321090180967040964757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65586880726787311360643171 98380321090180967040964757)
          ·
            refine ⟨4611577551102232830045223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98380321090180967040964757 4611577551102232830045223)
            ·
              refine ⟨6917366326653349245067835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4611577551102232830045223 6917366326653349245067835)
              ·
                refine ⟨10376049489980023867601753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6917366326653349245067835 10376049489980023867601753)
                ·
                  refine ⟨7782037117485017900701315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10376049489980023867601753 7782037117485017900701315)
                  ·
                    refine ⟨11673055676227526851051973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7782037117485017900701315 11673055676227526851051973)
                    ·
                      refine ⟨2188697939292661284572245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11673055676227526851051973 2188697939292661284572245)
                      ·
                        rfl

theorem cell23_4262474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_4262474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262474 prefixEnd_4262474 := by exact prefixLift 4262474
  have htrace : WordTrace (prefixWord ++ tailWord_4262474) baseStart_4262474 baseEnd_4262474 := by
    simpa [prefixWord, tailWord_4262474, baseEnd_4262474] using wordTrace_append hprefix tailTrace_4262474
  have hstable : (prefixWord ++ tailWord_4262474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262474).length < 2 ^ (prefixWord ++ tailWord_4262474).sum := by decide
  have hdescent : baseEnd_4262474 < baseStart_4262474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262497 : List Nat := [1, 2, 3, 1, 1, 4, 3, 2, 6]
def baseStart_4262497 : Nat := 118140960795 + 4262497 * 2 ^ 59
def prefixEnd_4262497 : Nat := 4983230072969 + 3 ^ 40 * 4262497 * 2
def baseEnd_4262497 : Nat := 243189972149746077176071

theorem tailTrace_4262497 : CollatzResearch.WordTrace tailWord_4262497 prefixEnd_4262497 243189972149746077176071 := by
  unfold tailWord_4262497
  simp only [CollatzResearch.WordTrace]
  refine ⟨155466037638708820375537745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103644025092472546917025163 155466037638708820375537745)
  ·
    refine ⟨116599528229031615281653309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155466037638708820375537745 116599528229031615281653309)
    ·
      refine ⟨43724823085886855730619991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116599528229031615281653309 43724823085886855730619991)
      ·
        refine ⟨65587234628830283595929987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43724823085886855730619991 65587234628830283595929987)
        ·
          refine ⟨98380851943245425393894981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65587234628830283595929987 98380851943245425393894981)
          ·
            refine ⟨18446409739358517261355309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98380851943245425393894981 18446409739358517261355309)
            ·
              refine ⟨6917403652259443973008241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18446409739358517261355309 6917403652259443973008241)
              ·
                refine ⟨5188052739194582979756181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6917403652259443973008241 5188052739194582979756181)
                ·
                  refine ⟨243189972149746077176071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5188052739194582979756181 243189972149746077176071)
                  ·
                    rfl

theorem cell23_4262497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_4262497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262497 prefixEnd_4262497 := by exact prefixLift 4262497
  have htrace : WordTrace (prefixWord ++ tailWord_4262497) baseStart_4262497 baseEnd_4262497 := by
    simpa [prefixWord, tailWord_4262497, baseEnd_4262497] using wordTrace_append hprefix tailTrace_4262497
  have hstable : (prefixWord ++ tailWord_4262497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262497).length < 2 ^ (prefixWord ++ tailWord_4262497).sum := by decide
  have hdescent : baseEnd_4262497 < baseStart_4262497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262500 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_4262500 : Nat := 118140960795 + 4262500 * 2 ^ 59
def prefixEnd_4262500 : Nat := 4983230072969 + 3 ^ 40 * 4262500 * 2
def baseEnd_4262500 : Nat := 2188711289789678182847125

theorem tailTrace_4262500 : CollatzResearch.WordTrace tailWord_4262500 prefixEnd_4262500 2188711289789678182847125 := by
  unfold tailWord_4262500
  simp only [CollatzResearch.WordTrace]
  refine ⟨77733073528848975943948477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103644098038465301258597969 77733073528848975943948477)
  ·
    refine ⟨29149902573318365978980679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77733073528848975943948477 29149902573318365978980679)
    ·
      refine ⟨43724853859977548968471019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29149902573318365978980679 43724853859977548968471019)
      ·
        refine ⟨65587280789966323452706529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43724853859977548968471019 65587280789966323452706529)
        ·
          refine ⟨49190460592474742589529897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65587280789966323452706529 49190460592474742589529897)
          ·
            refine ⟨36892845444356056942147423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49190460592474742589529897 36892845444356056942147423)
            ·
              refine ⟨55339268166534085413221135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36892845444356056942147423 55339268166534085413221135)
              ·
                refine ⟨83008902249801128119831703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55339268166534085413221135 83008902249801128119831703)
                ·
                  refine ⟨124513353374701692179747555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83008902249801128119831703 124513353374701692179747555)
                  ·
                    refine ⟨186770030062052538269621333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124513353374701692179747555 186770030062052538269621333)
                    ·
                      refine ⟨2188711289789678182847125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 186770030062052538269621333 2188711289789678182847125)
                      ·
                        rfl

theorem cell23_4262500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_4262500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262500 prefixEnd_4262500 := by exact prefixLift 4262500
  have htrace : WordTrace (prefixWord ++ tailWord_4262500) baseStart_4262500 baseEnd_4262500 := by
    simpa [prefixWord, tailWord_4262500, baseEnd_4262500] using wordTrace_append hprefix tailTrace_4262500
  have hstable : (prefixWord ++ tailWord_4262500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262500).length < 2 ^ (prefixWord ++ tailWord_4262500).sum := by decide
  have hdescent : baseEnd_4262500 < baseStart_4262500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262524 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_4262524 : Nat := 118140960795 + 4262524 * 2 ^ 59
def prefixEnd_4262524 : Nat := 4983230072969 + 3 ^ 40 * 4262524 * 2
def baseEnd_4262524 : Nat := 2188723613325386088947015

theorem tailTrace_4262524 : CollatzResearch.WordTrace tailWord_4262524 prefixEnd_4262524 2188723613325386088947015 := by
  unfold tailWord_4262524
  simp only [CollatzResearch.WordTrace]
  refine ⟨77733511204805501993385313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103644681606407335991180417 77733511204805501993385313)
  ·
    refine ⟨58300133403604126495038985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77733511204805501993385313 58300133403604126495038985)
    ·
      refine ⟨43725100052703094871279239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58300133403604126495038985 43725100052703094871279239)
      ·
        refine ⟨65587650079054642306918859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43725100052703094871279239 65587650079054642306918859)
        ·
          refine ⟨98381475118581963460378289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65587650079054642306918859 98381475118581963460378289)
          ·
            refine ⟨73786106338936472595283717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98381475118581963460378289 73786106338936472595283717)
            ·
              refine ⟨13834894938550588611615697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73786106338936472595283717 13834894938550588611615697)
              ·
                refine ⟨10376171203912941458711773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13834894938550588611615697 10376171203912941458711773)
                ·
                  refine ⟨3891064201467353047016915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10376171203912941458711773 3891064201467353047016915)
                  ·
                    refine ⟨5836596302201029570525373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891064201467353047016915 5836596302201029570525373)
                    ·
                      refine ⟨2188723613325386088947015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5836596302201029570525373 2188723613325386088947015)
                      ·
                        rfl

theorem cell23_4262524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_4262524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262524 prefixEnd_4262524 := by exact prefixLift 4262524
  have htrace : WordTrace (prefixWord ++ tailWord_4262524) baseStart_4262524 baseEnd_4262524 := by
    simpa [prefixWord, tailWord_4262524, baseEnd_4262524] using wordTrace_append hprefix tailTrace_4262524
  have hstable : (prefixWord ++ tailWord_4262524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262524).length < 2 ^ (prefixWord ++ tailWord_4262524).sum := by decide
  have hdescent : baseEnd_4262524 < baseStart_4262524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262547 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 8, 2]
def baseStart_4262547 : Nat := 118140960795 + 4262547 * 2 ^ 59
def prefixEnd_4262547 : Nat := 4983230072969 + 3 ^ 40 * 4262547 * 2
def baseEnd_4262547 : Nat := 2188735423380439498959409

theorem tailTrace_4262547 : CollatzResearch.WordTrace tailWord_4262547 prefixEnd_4262547 2188735423380439498959409 := by
  unfold tailWord_4262547
  simp only [CollatzResearch.WordTrace]
  refine ⟨155467861288527678914857895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103645240859018452609905263 155467861288527678914857895)
  ·
    refine ⟨233201791932791518372286843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155467861288527678914857895 233201791932791518372286843)
    ·
      refine ⟨349802687899187277558430265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233201791932791518372286843 349802687899187277558430265)
      ·
        refine ⟨262352015924390458168822699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349802687899187277558430265 262352015924390458168822699)
        ·
          refine ⟨393528023886585687253234049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262352015924390458168822699 393528023886585687253234049)
          ·
            refine ⟨295146017914939265439925537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393528023886585687253234049 295146017914939265439925537)
            ·
              refine ⟨221359513436204449079944153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295146017914939265439925537 221359513436204449079944153)
              ·
                refine ⟨166019635077153336809958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221359513436204449079944153 166019635077153336809958115)
                ·
                  refine ⟨249029452615730005214937173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166019635077153336809958115 249029452615730005214937173)
                  ·
                    refine ⟨2918313897840585998612545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 249029452615730005214937173 2918313897840585998612545)
                    ·
                      refine ⟨2188735423380439498959409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918313897840585998612545 2188735423380439498959409)
                      ·
                        rfl

theorem cell23_4262547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8, 2].length) (baseStart_4262547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262547 prefixEnd_4262547 := by exact prefixLift 4262547
  have htrace : WordTrace (prefixWord ++ tailWord_4262547) baseStart_4262547 baseEnd_4262547 := by
    simpa [prefixWord, tailWord_4262547, baseEnd_4262547] using wordTrace_append hprefix tailTrace_4262547
  have hstable : (prefixWord ++ tailWord_4262547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262547).length < 2 ^ (prefixWord ++ tailWord_4262547).sum := by decide
  have hdescent : baseEnd_4262547 < baseStart_4262547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262581 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4262581 : Nat := 118140960795 + 4262581 * 2 ^ 59
def prefixEnd_4262581 : Nat := 4983230072969 + 3 ^ 40 * 4262581 * 2
def baseEnd_4262581 : Nat := 2188752881722692365934253

theorem tailTrace_4262581 : CollatzResearch.WordTrace tailWord_4262581 prefixEnd_4262581 2188752881722692365934253 := by
  unfold tailWord_4262581
  simp only [CollatzResearch.WordTrace]
  refine ⟨155469101370404502721595597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103646067580269668481063731 155469101370404502721595597)
  ·
    refine ⟨58300913013901688520598349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155469101370404502721595597 58300913013901688520598349)
    ·
      refine ⟨21862842380213133195224381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58300913013901688520598349 21862842380213133195224381)
      ·
        refine ⟨8198565892579924948209143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21862842380213133195224381 8198565892579924948209143)
        ·
          refine ⟨12297848838869887422313715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8198565892579924948209143 12297848838869887422313715)
          ·
            refine ⟨18446773258304831133470573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12297848838869887422313715 18446773258304831133470573)
            ·
              refine ⟨6917539971864311675051465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18446773258304831133470573 6917539971864311675051465)
              ·
                refine ⟨5188154978898233756288599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6917539971864311675051465 5188154978898233756288599)
                ·
                  refine ⟨7782232468347350634432899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188154978898233756288599 7782232468347350634432899)
                  ·
                    refine ⟨11673348702521025951649349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7782232468347350634432899 11673348702521025951649349)
                    ·
                      refine ⟨2188752881722692365934253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11673348702521025951649349 2188752881722692365934253)
                      ·
                        rfl

theorem cell23_4262581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4262581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262581 prefixEnd_4262581 := by exact prefixLift 4262581
  have htrace : WordTrace (prefixWord ++ tailWord_4262581) baseStart_4262581 baseEnd_4262581 := by
    simpa [prefixWord, tailWord_4262581, baseEnd_4262581] using wordTrace_append hprefix tailTrace_4262581
  have hstable : (prefixWord ++ tailWord_4262581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262581).length < 2 ^ (prefixWord ++ tailWord_4262581).sum := by decide
  have hdescent : baseEnd_4262581 < baseStart_4262581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262615 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 1, 2, 2]
def baseStart_4262615 : Nat := 118140960795 + 4262615 * 2 ^ 59
def prefixEnd_4262615 : Nat := 4983230072969 + 3 ^ 40 * 4262615 * 2
def baseEnd_4262615 : Nat := 2188770340064945232909097

theorem tailTrace_4262615 : CollatzResearch.WordTrace tailWord_4262615 prefixEnd_4262615 2188770340064945232909097 := by
  unfold tailWord_4262615
  simp only [CollatzResearch.WordTrace]
  refine ⟨155470341452281326528333299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103646894301520884352222199 155470341452281326528333299)
  ·
    refine ⟨233205512178421989792499949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155470341452281326528333299 233205512178421989792499949)
    ·
      refine ⟨87452067066908246172187481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233205512178421989792499949 87452067066908246172187481)
      ·
        refine ⟨65589050300181184629140611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87452067066908246172187481 65589050300181184629140611)
        ·
          refine ⟨98383575450271776943710917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65589050300181184629140611 98383575450271776943710917)
          ·
            refine ⟨18446920396925958176945797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98383575450271776943710917 18446920396925958176945797)
            ·
              refine ⟨3458797574423617158177337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18446920396925958176945797 3458797574423617158177337)
              ·
                refine ⟨2594098180817712868633003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3458797574423617158177337 2594098180817712868633003)
                ·
                  refine ⟨3891147271226569302949505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594098180817712868633003 3891147271226569302949505)
                  ·
                    refine ⟨2918360453419926977212129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3891147271226569302949505 2918360453419926977212129)
                    ·
                      refine ⟨2188770340064945232909097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918360453419926977212129 2188770340064945232909097)
                      ·
                        rfl

theorem cell23_4262615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_4262615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262615 prefixEnd_4262615 := by exact prefixLift 4262615
  have htrace : WordTrace (prefixWord ++ tailWord_4262615) baseStart_4262615 baseEnd_4262615 := by
    simpa [prefixWord, tailWord_4262615, baseEnd_4262615] using wordTrace_append hprefix tailTrace_4262615
  have hstable : (prefixWord ++ tailWord_4262615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262615).length < 2 ^ (prefixWord ++ tailWord_4262615).sum := by decide
  have hdescent : baseEnd_4262615 < baseStart_4262615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262641 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_4262641 : Nat := 118140960795 + 4262641 * 2 ^ 59
def prefixEnd_4262641 : Nat := 4983230072969 + 3 ^ 40 * 4262641 * 2
def baseEnd_4262641 : Nat := 2188783690561962131183977

theorem tailTrace_4262641 : CollatzResearch.WordTrace tailWord_4262641 prefixEnd_4262641 2188783690561962131183977 := by
  unfold tailWord_4262641
  simp only [CollatzResearch.WordTrace]
  refine ⟨155471289750187132968779777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103647526500124755312519851 155471289750187132968779777)
  ·
    refine ⟨116603467312640349726584833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155471289750187132968779777 116603467312640349726584833)
    ·
      refine ⟨87452600484480262294938625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116603467312640349726584833 87452600484480262294938625)
      ·
        refine ⟨65589450363360196721203969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87452600484480262294938625 65589450363360196721203969)
        ·
          refine ⟨49192087772520147540902977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65589450363360196721203969 49192087772520147540902977)
          ·
            refine ⟨36894065829390110655677233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49192087772520147540902977 36894065829390110655677233)
            ·
              refine ⟨27670549372042582991757925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36894065829390110655677233 27670549372042582991757925)
              ·
                refine ⟨5188228007257984310954611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27670549372042582991757925 5188228007257984310954611)
                ·
                  refine ⟨7782342010886976466431917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188228007257984310954611 7782342010886976466431917)
                  ·
                    refine ⟨2918378254082616174911969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7782342010886976466431917 2918378254082616174911969)
                    ·
                      refine ⟨2188783690561962131183977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918378254082616174911969 2188783690561962131183977)
                      ·
                        rfl

theorem cell23_4262641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_4262641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262641 prefixEnd_4262641 := by exact prefixLift 4262641
  have htrace : WordTrace (prefixWord ++ tailWord_4262641) baseStart_4262641 baseEnd_4262641 := by
    simpa [prefixWord, tailWord_4262641, baseEnd_4262641] using wordTrace_append hprefix tailTrace_4262641
  have hstable : (prefixWord ++ tailWord_4262641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262641).length < 2 ^ (prefixWord ++ tailWord_4262641).sum := by decide
  have hdescent : baseEnd_4262641 < baseStart_4262641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262657 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4262657 : Nat := 118140960795 + 4262657 * 2 ^ 59
def prefixEnd_4262657 : Nat := 4983230072969 + 3 ^ 40 * 4262657 * 2
def baseEnd_4262657 : Nat := 2188791906252434068583903

theorem tailTrace_4262657 : CollatzResearch.WordTrace tailWord_4262657 prefixEnd_4262657 2188791906252434068583903 := by
  unfold tailWord_4262657
  simp only [CollatzResearch.WordTrace]
  refine ⟨155471873318129167701362225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103647915545419445134241483 155471873318129167701362225)
  ·
    refine ⟨116603904988596875776021669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155471873318129167701362225 116603904988596875776021669)
    ·
      refine ⟨21863232185361914208004063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116603904988596875776021669 21863232185361914208004063)
      ·
        refine ⟨32794848278042871312006095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21863232185361914208004063 32794848278042871312006095)
        ·
          refine ⟨49192272417064306968009143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32794848278042871312006095 49192272417064306968009143)
          ·
            refine ⟨73788408625596460452013715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49192272417064306968009143 73788408625596460452013715)
            ·
              refine ⟨110682612938394690678020573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73788408625596460452013715 110682612938394690678020573)
              ·
                refine ⟨41505979851898009004257715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110682612938394690678020573 41505979851898009004257715)
                ·
                  refine ⟨62258969777847013506386573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41505979851898009004257715 62258969777847013506386573)
                  ·
                    refine ⟨23347113666692630064894965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62258969777847013506386573 23347113666692630064894965)
                    ·
                      refine ⟨2188791906252434068583903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23347113666692630064894965 2188791906252434068583903)
                      ·
                        rfl

theorem cell23_4262657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4262657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262657 prefixEnd_4262657 := by exact prefixLift 4262657
  have htrace : WordTrace (prefixWord ++ tailWord_4262657) baseStart_4262657 baseEnd_4262657 := by
    simpa [prefixWord, tailWord_4262657, baseEnd_4262657] using wordTrace_append hprefix tailTrace_4262657
  have hstable : (prefixWord ++ tailWord_4262657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262657).length < 2 ^ (prefixWord ++ tailWord_4262657).sum := by decide
  have hdescent : baseEnd_4262657 < baseStart_4262657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262671 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 4, 2, 2]
def baseStart_4262671 : Nat := 118140960795 + 4262671 * 2 ^ 59
def prefixEnd_4262671 : Nat := 4983230072969 + 3 ^ 40 * 4262671 * 2
def baseEnd_4262671 : Nat := 2188799094981597013808839

theorem tailTrace_4262671 : CollatzResearch.WordTrace tailWord_4262671 prefixEnd_4262671 2188799094981597013808839 := by
  unfold tailWord_4262671
  simp only [CollatzResearch.WordTrace]
  refine ⟨155472383940078448092371867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103648255960052298728247911 155472383940078448092371867)
  ·
    refine ⟨233208575910117672138557801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155472383940078448092371867 233208575910117672138557801)
    ·
      refine ⟨174906431932588254103918351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233208575910117672138557801 174906431932588254103918351)
      ·
        refine ⟨262359647898882381155877527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174906431932588254103918351 262359647898882381155877527)
        ·
          refine ⟨393539471848323571733816291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262359647898882381155877527 393539471848323571733816291)
          ·
            refine ⟨590309207772485357600724437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393539471848323571733816291 590309207772485357600724437)
            ·
              refine ⟨13835372057167625568766979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 590309207772485357600724437 13835372057167625568766979)
              ·
                refine ⟨20753058085751438353150469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13835372057167625568766979 20753058085751438353150469)
                ·
                  refine ⟨3891198391078394691215713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20753058085751438353150469 3891198391078394691215713)
                  ·
                    refine ⟨2918398793308796018411785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3891198391078394691215713 2918398793308796018411785)
                    ·
                      refine ⟨2188799094981597013808839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918398793308796018411785 2188799094981597013808839)
                      ·
                        rfl

theorem cell23_4262671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2, 2].length) (baseStart_4262671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262671 prefixEnd_4262671 := by exact prefixLift 4262671
  have htrace : WordTrace (prefixWord ++ tailWord_4262671) baseStart_4262671 baseEnd_4262671 := by
    simpa [prefixWord, tailWord_4262671, baseEnd_4262671] using wordTrace_append hprefix tailTrace_4262671
  have hstable : (prefixWord ++ tailWord_4262671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262671).length < 2 ^ (prefixWord ++ tailWord_4262671).sum := by decide
  have hdescent : baseEnd_4262671 < baseStart_4262671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262684 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4262684 : Nat := 118140960795 + 4262684 * 2 ^ 59
def prefixEnd_4262684 : Nat := 4983230072969 + 3 ^ 40 * 4262684 * 2
def baseEnd_4262684 : Nat := 2188805770230105462946279

theorem tailTrace_4262684 : CollatzResearch.WordTrace tailWord_4262684 prefixEnd_4262684 2188805770230105462946279 := by
  unfold tailWord_4262684
  simp only [CollatzResearch.WordTrace]
  refine ⟨77736429044515675656297553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103648572059354234208396737 77736429044515675656297553)
  ·
    refine ⟨58302321783386756742223165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77736429044515675656297553 58302321783386756742223165)
    ·
      refine ⟨21863370668770033778333687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58302321783386756742223165 21863370668770033778333687)
      ·
        refine ⟨32795056003155050667500531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21863370668770033778333687 32795056003155050667500531)
        ·
          refine ⟨49192584004732576001250797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32795056003155050667500531 49192584004732576001250797)
          ·
            refine ⟨18447219001774716000469049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49192584004732576001250797 18447219001774716000469049)
            ·
              refine ⟨13835414251331037000351787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18447219001774716000469049 13835414251331037000351787)
              ·
                refine ⟨20753121376996555500527681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13835414251331037000351787 20753121376996555500527681)
                ·
                  refine ⟨15564841032747416625395761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20753121376996555500527681 15564841032747416625395761)
                  ·
                    refine ⟨11673630774560562469046821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15564841032747416625395761 11673630774560562469046821)
                    ·
                      refine ⟨2188805770230105462946279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11673630774560562469046821 2188805770230105462946279)
                      ·
                        rfl

theorem cell23_4262684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4262684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262684 prefixEnd_4262684 := by exact prefixLift 4262684
  have htrace : WordTrace (prefixWord ++ tailWord_4262684) baseStart_4262684 baseEnd_4262684 := by
    simpa [prefixWord, tailWord_4262684, baseEnd_4262684] using wordTrace_append hprefix tailTrace_4262684
  have hstable : (prefixWord ++ tailWord_4262684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262684).length < 2 ^ (prefixWord ++ tailWord_4262684).sum := by decide
  have hdescent : baseEnd_4262684 < baseStart_4262684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262688 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2]
def baseStart_4262688 : Nat := 118140960795 + 4262688 * 2 ^ 59
def prefixEnd_4262688 : Nat := 4983230072969 + 3 ^ 40 * 4262688 * 2
def baseEnd_4262688 : Nat := 2188807824152723447296261

theorem tailTrace_4262688 : CollatzResearch.WordTrace tailWord_4262688 prefixEnd_4262688 2188807824152723447296261 := by
  unfold tailWord_4262688
  simp only [CollatzResearch.WordTrace]
  refine ⟨77736501990508429997870359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103648669320677906663827145 77736501990508429997870359)
  ·
    refine ⟨116604752985762644996805539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77736501990508429997870359 116604752985762644996805539)
    ·
      refine ⟨174907129478643967495208309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116604752985762644996805539 174907129478643967495208309)
      ·
        refine ⟨16397543388622871952675779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174907129478643967495208309 16397543388622871952675779)
        ·
          refine ⟨24596315082934307929013669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16397543388622871952675779 24596315082934307929013669)
          ·
            refine ⟨4611809078050182736690063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24596315082934307929013669 4611809078050182736690063)
            ·
              refine ⟨6917713617075274105035095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4611809078050182736690063 6917713617075274105035095)
              ·
                refine ⟨10376570425612911157552643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6917713617075274105035095 10376570425612911157552643)
                ·
                  refine ⟨15564855638419366736328965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10376570425612911157552643 15564855638419366736328965)
                  ·
                    refine ⟨2918410432203631263061681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15564855638419366736328965 2918410432203631263061681)
                    ·
                      refine ⟨2188807824152723447296261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918410432203631263061681 2188807824152723447296261)
                      ·
                        rfl

theorem cell23_4262688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_4262688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262688 prefixEnd_4262688 := by exact prefixLift 4262688
  have htrace : WordTrace (prefixWord ++ tailWord_4262688) baseStart_4262688 baseEnd_4262688 := by
    simpa [prefixWord, tailWord_4262688, baseEnd_4262688] using wordTrace_append hprefix tailTrace_4262688
  have hstable : (prefixWord ++ tailWord_4262688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262688).length < 2 ^ (prefixWord ++ tailWord_4262688).sum := by decide
  have hdescent : baseEnd_4262688 < baseStart_4262688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262767 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 10]
def baseStart_4262767 : Nat := 118140960795 + 4262767 * 2 ^ 59
def prefixEnd_4262767 : Nat := 4983230072969 + 3 ^ 40 * 4262767 * 2
def baseEnd_4262767 : Nat := 243205376569380959800933

theorem tailTrace_4262767 : CollatzResearch.WordTrace tailWord_4262767 prefixEnd_4262767 243205376569380959800933 := by
  unfold tailWord_4262767
  simp only [CollatzResearch.WordTrace]
  refine ⟨155475885347730656487866555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103650590231820437658577703 155475885347730656487866555)
  ·
    refine ⟨233213828021595984731799833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155475885347730656487866555 233213828021595984731799833)
    ·
      refine ⟨174910371016196988548849875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233213828021595984731799833 174910371016196988548849875)
      ·
        refine ⟨262365556524295482823274813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174910371016196988548849875 262365556524295482823274813)
        ·
          refine ⟨98387083696610806058728055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262365556524295482823274813 98387083696610806058728055)
          ·
            refine ⟨147580625544916209088092083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98387083696610806058728055 147580625544916209088092083)
            ·
              refine ⟨221370938317374313632138125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147580625544916209088092083 221370938317374313632138125)
              ·
                refine ⟨83014101869015367612051797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221370938317374313632138125 83014101869015367612051797)
                ·
                  refine ⟨243205376569380959800933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 83014101869015367612051797 243205376569380959800933)
                  ·
                    rfl

theorem cell23_4262767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 10].length) (baseStart_4262767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262767 prefixEnd_4262767 := by exact prefixLift 4262767
  have htrace : WordTrace (prefixWord ++ tailWord_4262767) baseStart_4262767 baseEnd_4262767 := by
    simpa [prefixWord, tailWord_4262767, baseEnd_4262767] using wordTrace_append hprefix tailTrace_4262767
  have hstable : (prefixWord ++ tailWord_4262767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262767).length < 2 ^ (prefixWord ++ tailWord_4262767).sum := by decide
  have hdescent : baseEnd_4262767 < baseStart_4262767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262781 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_4262781 : Nat := 118140960795 + 4262781 * 2 ^ 59
def prefixEnd_4262781 : Nat := 4983230072969 + 3 ^ 40 * 4262781 * 2
def baseEnd_4262781 : Nat := 2188855577853591583433333

theorem tailTrace_4262781 : CollatzResearch.WordTrace tailWord_4262781 prefixEnd_4262781 2188855577853591583433333 := by
  unfold tailWord_4262781
  simp only [CollatzResearch.WordTrace]
  refine ⟨155476395969679936878876197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103650930646453291252584131 155476395969679936878876197)
  ·
    refine ⟨29151824244314988164789287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155476395969679936878876197 29151824244314988164789287)
    ·
      refine ⟨43727736366472482247183931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29151824244314988164789287 43727736366472482247183931)
      ·
        refine ⟨65591604549708723370775897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43727736366472482247183931 65591604549708723370775897)
        ·
          refine ⟨49193703412281542528081923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65591604549708723370775897 49193703412281542528081923)
          ·
            refine ⟨73790555118422313792122885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49193703412281542528081923 73790555118422313792122885)
            ·
              refine ⟨13835729084704183836023041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73790555118422313792122885 13835729084704183836023041)
              ·
                refine ⟨10376796813528137877017281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13835729084704183836023041 10376796813528137877017281)
                ·
                  refine ⟨7782597610146103407762961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10376796813528137877017281 7782597610146103407762961)
                  ·
                    refine ⟨5836948207609577555822221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7782597610146103407762961 5836948207609577555822221)
                    ·
                      refine ⟨2188855577853591583433333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5836948207609577555822221 2188855577853591583433333)
                      ·
                        rfl

theorem cell23_4262781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_4262781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262781 prefixEnd_4262781 := by exact prefixLift 4262781
  have htrace : WordTrace (prefixWord ++ tailWord_4262781) baseStart_4262781 baseEnd_4262781 := by
    simpa [prefixWord, tailWord_4262781, baseEnd_4262781] using wordTrace_append hprefix tailTrace_4262781
  have hstable : (prefixWord ++ tailWord_4262781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262781).length < 2 ^ (prefixWord ++ tailWord_4262781).sum := by decide
  have hdescent : baseEnd_4262781 < baseStart_4262781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262845 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_4262845 : Nat := 118140960795 + 4262845 * 2 ^ 59
def prefixEnd_4262845 : Nat := 4983230072969 + 3 ^ 40 * 4262845 * 2
def baseEnd_4262845 : Nat := 2188888440615479333033039

theorem tailTrace_4262845 : CollatzResearch.WordTrace tailWord_4262845 prefixEnd_4262845 2188888440615479333033039 := by
  unfold tailWord_4262845
  simp only [CollatzResearch.WordTrace]
  refine ⟨155478730241448075809205989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103652486827632050539470659 155478730241448075809205989)
  ·
    refine ⟨29152261920271514214226123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 155478730241448075809205989 29152261920271514214226123)
    ·
      refine ⟨43728392880407271321339185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29152261920271514214226123 43728392880407271321339185)
      ·
        refine ⟨32796294660305453491004389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43728392880407271321339185 32796294660305453491004389)
        ·
          refine ⟨6149305248807272529563323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32796294660305453491004389 6149305248807272529563323)
          ·
            refine ⟨9223957873210908794344985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6149305248807272529563323 9223957873210908794344985)
            ·
              refine ⟨6917968404908181595758739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9223957873210908794344985 6917968404908181595758739)
              ·
                refine ⟨10376952607362272393638109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6917968404908181595758739 10376952607362272393638109)
                ·
                  refine ⟨3891357227760852147614291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10376952607362272393638109 3891357227760852147614291)
                  ·
                    refine ⟨5837035841641278221421437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891357227760852147614291 5837035841641278221421437)
                    ·
                      refine ⟨2188888440615479333033039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837035841641278221421437 2188888440615479333033039)
                      ·
                        rfl

theorem cell23_4262845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_4262845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262845 prefixEnd_4262845 := by exact prefixLift 4262845
  have htrace : WordTrace (prefixWord ++ tailWord_4262845) baseStart_4262845 baseEnd_4262845 := by
    simpa [prefixWord, tailWord_4262845, baseEnd_4262845] using wordTrace_append hprefix tailTrace_4262845
  have hstable : (prefixWord ++ tailWord_4262845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262845).length < 2 ^ (prefixWord ++ tailWord_4262845).sum := by decide
  have hdescent : baseEnd_4262845 < baseStart_4262845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262868 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4262868 : Nat := 118140960795 + 4262868 * 2 ^ 59
def prefixEnd_4262868 : Nat := 4983230072969 + 3 ^ 40 * 4262868 * 2
def baseEnd_4262868 : Nat := 2188900250670532743045433

theorem tailTrace_4262868 : CollatzResearch.WordTrace tailWord_4262868 prefixEnd_4262868 2188900250670532743045433 := by
  unfold tailWord_4262868
  simp only [CollatzResearch.WordTrace]
  refine ⟨77739784560182375368646629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103653046080243167158195505 77739784560182375368646629)
  ·
    refine ⟨14576209605034195381621243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77739784560182375368646629 14576209605034195381621243)
    ·
      refine ⟨21864314407551293072431865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14576209605034195381621243 21864314407551293072431865)
      ·
        refine ⟨16398235805663469804323899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21864314407551293072431865 16398235805663469804323899)
        ·
          refine ⟨24597353708495204706485849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16398235805663469804323899 24597353708495204706485849)
          ·
            refine ⟨18448015281371403529864387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24597353708495204706485849 18448015281371403529864387)
            ·
              refine ⟨27672022922057105294796581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18448015281371403529864387 27672022922057105294796581)
              ·
                refine ⟨5188504297885707242774359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27672022922057105294796581 5188504297885707242774359)
                ·
                  refine ⟨7782756446828560864161539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188504297885707242774359 7782756446828560864161539)
                  ·
                    refine ⟨11674134670242841296242309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7782756446828560864161539 11674134670242841296242309)
                    ·
                      refine ⟨2188900250670532743045433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11674134670242841296242309 2188900250670532743045433)
                      ·
                        rfl

theorem cell23_4262868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4262868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262868 prefixEnd_4262868 := by exact prefixLift 4262868
  have htrace : WordTrace (prefixWord ++ tailWord_4262868) baseStart_4262868 baseEnd_4262868 := by
    simpa [prefixWord, tailWord_4262868, baseEnd_4262868] using wordTrace_append hprefix tailTrace_4262868
  have hstable : (prefixWord ++ tailWord_4262868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262868).length < 2 ^ (prefixWord ++ tailWord_4262868).sum := by decide
  have hdescent : baseEnd_4262868 < baseStart_4262868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262879 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 1, 1, 3]
def baseStart_4262879 : Nat := 118140960795 + 4262879 * 2 ^ 59
def prefixEnd_4262879 : Nat := 4983230072969 + 3 ^ 40 * 4262879 * 2
def baseEnd_4262879 : Nat := 2188905898957732200007883

theorem tailTrace_4262879 : CollatzResearch.WordTrace tailWord_4262879 prefixEnd_4262879 2188905898957732200007883 := by
  unfold tailWord_4262879
  simp only [CollatzResearch.WordTrace]
  refine ⟨155479970323324899615943691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103653313548883266410629127 155479970323324899615943691)
  ·
    refine ⟨233219955484987349423915537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155479970323324899615943691 233219955484987349423915537)
    ·
      refine ⟨174914966613740512067936653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233219955484987349423915537 174914966613740512067936653)
      ·
        refine ⟨65593112480152692025476245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174914966613740512067936653 65593112480152692025476245)
        ·
          refine ⟨3074677147507157438694199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65593112480152692025476245 3074677147507157438694199)
          ·
            refine ⟨4612015721260736158041299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074677147507157438694199 4612015721260736158041299)
            ·
              refine ⟨6918023581891104237061949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4612015721260736158041299 6918023581891104237061949)
              ·
                refine ⟨2594258843209164088898231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6918023581891104237061949 2594258843209164088898231)
                ·
                  refine ⟨3891388264813746133347347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594258843209164088898231 3891388264813746133347347)
                  ·
                    refine ⟨5837082397220619200021021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891388264813746133347347 5837082397220619200021021)
                    ·
                      refine ⟨2188905898957732200007883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837082397220619200021021 2188905898957732200007883)
                      ·
                        rfl

theorem cell23_4262879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_4262879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262879 prefixEnd_4262879 := by exact prefixLift 4262879
  have htrace : WordTrace (prefixWord ++ tailWord_4262879) baseStart_4262879 baseEnd_4262879 := by
    simpa [prefixWord, tailWord_4262879, baseEnd_4262879] using wordTrace_append hprefix tailTrace_4262879
  have hstable : (prefixWord ++ tailWord_4262879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262879).length < 2 ^ (prefixWord ++ tailWord_4262879).sum := by decide
  have hdescent : baseEnd_4262879 < baseStart_4262879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262888 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4262888 : Nat := 118140960795 + 4262888 * 2 ^ 59
def prefixEnd_4262888 : Nat := 4983230072969 + 3 ^ 40 * 4262888 * 2
def baseEnd_4262888 : Nat := 2188910520283622664795341

theorem tailTrace_4262888 : CollatzResearch.WordTrace tailWord_4262888 prefixEnd_4262888 2188910520283622664795341 := by
  unfold tailWord_4262888
  simp only [CollatzResearch.WordTrace]
  refine ⟨77740149290146147076510659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103653532386861529435347545 77740149290146147076510659)
  ·
    refine ⟨116610223935219220614765989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77740149290146147076510659 116610223935219220614765989)
    ·
      refine ⟨21864416987853603865268623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116610223935219220614765989 21864416987853603865268623)
      ·
        refine ⟨32796625481780405797902935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21864416987853603865268623 32796625481780405797902935)
        ·
          refine ⟨49194938222670608696854403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32796625481780405797902935 49194938222670608696854403)
          ·
            refine ⟨73792407334005913045281605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49194938222670608696854403 73792407334005913045281605)
            ·
              refine ⟨13836076375126108695990301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73792407334005913045281605 13836076375126108695990301)
              ·
                refine ⟨5188528640672290760996363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13836076375126108695990301 5188528640672290760996363)
                ·
                  refine ⟨7782792961008436141494545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188528640672290760996363 7782792961008436141494545)
                  ·
                    refine ⟨5837094720756327106120909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7782792961008436141494545 5837094720756327106120909)
                    ·
                      refine ⟨2188910520283622664795341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837094720756327106120909 2188910520283622664795341)
                      ·
                        rfl

theorem cell23_4262888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4262888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262888 prefixEnd_4262888 := by exact prefixLift 4262888
  have htrace : WordTrace (prefixWord ++ tailWord_4262888) baseStart_4262888 baseEnd_4262888 := by
    simpa [prefixWord, tailWord_4262888, baseEnd_4262888] using wordTrace_append hprefix tailTrace_4262888
  have hstable : (prefixWord ++ tailWord_4262888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262888).length < 2 ^ (prefixWord ++ tailWord_4262888).sum := by decide
  have hdescent : baseEnd_4262888 < baseStart_4262888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262902 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4262902 : Nat := 118140960795 + 4262902 * 2 ^ 59
def prefixEnd_4262902 : Nat := 4983230072969 + 3 ^ 40 * 4262902 * 2
def baseEnd_4262902 : Nat := 2188917709012785610020277

theorem tailTrace_4262902 : CollatzResearch.WordTrace tailWord_4262902 prefixEnd_4262902 2188917709012785610020277 := by
  unfold tailWord_4262902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717550575140098409001935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103653872801494383029353973 9717550575140098409001935)
  ·
    refine ⟨14576325862710147613502903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9717550575140098409001935 14576325862710147613502903)
    ·
      refine ⟨21864488794065221420254355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14576325862710147613502903 21864488794065221420254355)
      ·
        refine ⟨32796733191097832130381533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21864488794065221420254355 32796733191097832130381533)
        ·
          refine ⟨12298774946661687048893075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32796733191097832130381533 12298774946661687048893075)
          ·
            refine ⟨18448162419992530573339613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12298774946661687048893075 18448162419992530573339613)
            ·
              refine ⟨6918060907497198965002355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18448162419992530573339613 6918060907497198965002355)
              ·
                refine ⟨10377091361245798447503533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6918060907497198965002355 10377091361245798447503533)
                ·
                  refine ⟨3891409260467174417813825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10377091361245798447503533 3891409260467174417813825)
                  ·
                    refine ⟨2918556945350380813360369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3891409260467174417813825 2918556945350380813360369)
                    ·
                      refine ⟨2188917709012785610020277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918556945350380813360369 2188917709012785610020277)
                      ·
                        rfl

theorem cell23_4262902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4262902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262902 prefixEnd_4262902 := by exact prefixLift 4262902
  have htrace : WordTrace (prefixWord ++ tailWord_4262902) baseStart_4262902 baseEnd_4262902 := by
    simpa [prefixWord, tailWord_4262902, baseEnd_4262902] using wordTrace_append hprefix tailTrace_4262902
  have hstable : (prefixWord ++ tailWord_4262902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262902).length < 2 ^ (prefixWord ++ tailWord_4262902).sum := by decide
  have hdescent : baseEnd_4262902 < baseStart_4262902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262904 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_4262904 : Nat := 118140960795 + 4262904 * 2 ^ 59
def prefixEnd_4262904 : Nat := 4983230072969 + 3 ^ 40 * 4262904 * 2
def baseEnd_4262904 : Nat := 729639578658031534065089

theorem tailTrace_4262904 : CollatzResearch.WordTrace tailWord_4262904 prefixEnd_4262904 729639578658031534065089 := by
  unfold tailWord_4262904
  simp only [CollatzResearch.WordTrace]
  refine ⟨77740441074117164442801883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103653921432156219257069177 77740441074117164442801883)
  ·
    refine ⟨116610661611175746664202825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77740441074117164442801883 116610661611175746664202825)
    ·
      refine ⟨87457996208381809998152119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116610661611175746664202825 87457996208381809998152119)
      ·
        refine ⟨131186994312572714997228179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87457996208381809998152119 131186994312572714997228179)
        ·
          refine ⟨196780491468859072495842269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131186994312572714997228179 196780491468859072495842269)
          ·
            refine ⟨73792684300822152185940851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196780491468859072495842269 73792684300822152185940851)
            ·
              refine ⟨110689026451233228278911277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73792684300822152185940851 110689026451233228278911277)
              ·
                refine ⟨41508384919212460604591729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110689026451233228278911277 41508384919212460604591729)
                ·
                  refine ⟨31131288689409345453443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41508384919212460604591729 31131288689409345453443797)
                  ·
                    refine ⟨729639578658031534065089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31131288689409345453443797 729639578658031534065089)
                    ·
                      rfl

theorem cell23_4262904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_4262904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262904 prefixEnd_4262904 := by exact prefixLift 4262904
  have htrace : WordTrace (prefixWord ++ tailWord_4262904) baseStart_4262904 baseEnd_4262904 := by
    simpa [prefixWord, tailWord_4262904, baseEnd_4262904] using wordTrace_append hprefix tailTrace_4262904
  have hstable : (prefixWord ++ tailWord_4262904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262904).length < 2 ^ (prefixWord ++ tailWord_4262904).sum := by decide
  have hdescent : baseEnd_4262904 < baseStart_4262904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262911 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 9, 2]
def baseStart_4262911 : Nat := 118140960795 + 4262911 * 2 ^ 59
def prefixEnd_4262911 : Nat := 4983230072969 + 3 ^ 40 * 4262911 * 2
def baseEnd_4262911 : Nat := 2188922330338676074807735

theorem tailTrace_4262911 : CollatzResearch.WordTrace tailWord_4262911 prefixEnd_4262911 2188922330338676074807735 := by
  unfold tailWord_4262911
  simp only [CollatzResearch.WordTrace]
  refine ⟨155481137459208969081108587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103654091639472646054072391 155481137459208969081108587)
  ·
    refine ⟨233221706188813453621662881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155481137459208969081108587 233221706188813453621662881)
    ·
      refine ⟨174916279641610090216247161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233221706188813453621662881 174916279641610090216247161)
      ·
        refine ⟨131187209731207567662185371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174916279641610090216247161 131187209731207567662185371)
        ·
          refine ⟨196780814596811351493278057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131187209731207567662185371 196780814596811351493278057)
          ·
            refine ⟨147585610947608513619958543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196780814596811351493278057 147585610947608513619958543)
            ·
              refine ⟨221378416421412770429937815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147585610947608513619958543 221378416421412770429937815)
              ·
                refine ⟨332067624632119155644906723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221378416421412770429937815 332067624632119155644906723)
                ·
                  refine ⟨498101436948178733467360085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332067624632119155644906723 498101436948178733467360085)
                  ·
                    refine ⟨2918563107118234766410313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 498101436948178733467360085 2918563107118234766410313)
                    ·
                      refine ⟨2188922330338676074807735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918563107118234766410313 2188922330338676074807735)
                      ·
                        rfl

theorem cell23_4262911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_4262911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262911 prefixEnd_4262911 := by exact prefixLift 4262911
  have htrace : WordTrace (prefixWord ++ tailWord_4262911) baseStart_4262911 baseEnd_4262911 := by
    simpa [prefixWord, tailWord_4262911, baseEnd_4262911] using wordTrace_append hprefix tailTrace_4262911
  have hstable : (prefixWord ++ tailWord_4262911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262911).length < 2 ^ (prefixWord ++ tailWord_4262911).sum := by decide
  have hdescent : baseEnd_4262911 < baseStart_4262911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262961 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_4262961 : Nat := 118140960795 + 4262961 * 2 ^ 59
def prefixEnd_4262961 : Nat := 4983230072969 + 3 ^ 40 * 4262961 * 2
def baseEnd_4262961 : Nat := 2188948004371400879182505

theorem tailTrace_4262961 : CollatzResearch.WordTrace tailWord_4262961 prefixEnd_4262961 2188948004371400879182505 := by
  unfold tailWord_4262961
  simp only [CollatzResearch.WordTrace]
  refine ⟨155482961109027827620428737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103655307406018551746952491 155482961109027827620428737)
  ·
    refine ⟨116612220831770870715321553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155482961109027827620428737 116612220831770870715321553)
    ·
      refine ⟨87459165623828153036491165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116612220831770870715321553 87459165623828153036491165)
      ·
        refine ⟨32797187108935557388684187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87459165623828153036491165 32797187108935557388684187)
        ·
          refine ⟨49195780663403336083026281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32797187108935557388684187 49195780663403336083026281)
          ·
            refine ⟨36896835497552502062269711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49195780663403336083026281 36896835497552502062269711)
            ·
              refine ⟨55345253246328753093404567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36896835497552502062269711 55345253246328753093404567)
              ·
                refine ⟨83017879869493129640106851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55345253246328753093404567 83017879869493129640106851)
                ·
                  refine ⟨124526819804239694460160277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83017879869493129640106851 124526819804239694460160277)
                  ·
                    refine ⟨5837194678323735677820013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124526819804239694460160277 5837194678323735677820013)
                    ·
                      refine ⟨2188948004371400879182505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837194678323735677820013 2188948004371400879182505)
                      ·
                        rfl

theorem cell23_4262961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_4262961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262961 prefixEnd_4262961 := by exact prefixLift 4262961
  have htrace : WordTrace (prefixWord ++ tailWord_4262961) baseStart_4262961 baseEnd_4262961 := by
    simpa [prefixWord, tailWord_4262961, baseEnd_4262961] using wordTrace_append hprefix tailTrace_4262961
  have hstable : (prefixWord ++ tailWord_4262961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262961).length < 2 ^ (prefixWord ++ tailWord_4262961).sum := by decide
  have hdescent : baseEnd_4262961 < baseStart_4262961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4262991 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_4262991 : Nat := 118140960795 + 4262991 * 2 ^ 59
def prefixEnd_4262991 : Nat := 4983230072969 + 3 ^ 40 * 4262991 * 2
def baseEnd_4262991 : Nat := 2188963408791035761807367

theorem tailTrace_4262991 : CollatzResearch.WordTrace tailWord_4262991 prefixEnd_4262991 2188963408791035761807367 := by
  unfold tailWord_4262991
  simp only [CollatzResearch.WordTrace]
  refine ⟨155484055298919142744020827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103656036865946095162680551 155484055298919142744020827)
  ·
    refine ⟨233226082948378714116031241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155484055298919142744020827 233226082948378714116031241)
    ·
      refine ⟨174919562211284035587023431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233226082948378714116031241 174919562211284035587023431)
      ·
        refine ⟨262379343316926053380535147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174919562211284035587023431 262379343316926053380535147)
        ·
          refine ⟨393569014975389080070802721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262379343316926053380535147 393569014975389080070802721)
          ·
            refine ⟨295176761231541810053102041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393569014975389080070802721 295176761231541810053102041)
            ·
              refine ⟨221382570923656357539826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295176761231541810053102041 221382570923656357539826531)
              ·
                refine ⟨332073856385484536309739797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221382570923656357539826531 332073856385484536309739797)
                ·
                  refine ⟨15565962018069587639519053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 332073856385484536309739797 15565962018069587639519053)
                  ·
                    refine ⟨5837235756776095364819645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15565962018069587639519053 5837235756776095364819645)
                    ·
                      refine ⟨2188963408791035761807367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837235756776095364819645 2188963408791035761807367)
                      ·
                        rfl

theorem cell23_4262991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_4262991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4262991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4262991 prefixEnd_4262991 := by exact prefixLift 4262991
  have htrace : WordTrace (prefixWord ++ tailWord_4262991) baseStart_4262991 baseEnd_4262991 := by
    simpa [prefixWord, tailWord_4262991, baseEnd_4262991] using wordTrace_append hprefix tailTrace_4262991
  have hstable : (prefixWord ++ tailWord_4262991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4262991).length < 2 ^ (prefixWord ++ tailWord_4262991).sum := by decide
  have hdescent : baseEnd_4262991 < baseStart_4262991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4262991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263011 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 4, 5]
def baseStart_4263011 : Nat := 118140960795 + 4263011 * 2 ^ 59
def prefixEnd_4263011 : Nat := 4983230072969 + 3 ^ 40 * 4263011 * 2
def baseEnd_4263011 : Nat := 729657892801375227852425

theorem tailTrace_4263011 : CollatzResearch.WordTrace tailWord_4263011 prefixEnd_4263011 729657892801375227852425 := by
  unfold tailWord_4263011
  simp only [CollatzResearch.WordTrace]
  refine ⟨155484784758846686159748887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103656523172564457439832591 155484784758846686159748887)
  ·
    refine ⟨233227177138270029239623331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155484784758846686159748887 233227177138270029239623331)
    ·
      refine ⟨349840765707405043859434997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233227177138270029239623331 349840765707405043859434997)
      ·
        refine ⟨32797571785069222861822031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 349840765707405043859434997 32797571785069222861822031)
        ·
          refine ⟨49196357677603834292733047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32797571785069222861822031 49196357677603834292733047)
          ·
            refine ⟨73794536516405751439099571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49196357677603834292733047 73794536516405751439099571)
            ·
              refine ⟨110691804774608627158649357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73794536516405751439099571 110691804774608627158649357)
              ·
                refine ⟨41509426790478235184493509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110691804774608627158649357 41509426790478235184493509)
                ·
                  refine ⟨7783017523214669097092533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41509426790478235184493509 7783017523214669097092533)
                  ·
                    refine ⟨729657892801375227852425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7783017523214669097092533 729657892801375227852425)
                    ·
                      rfl

theorem cell23_4263011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 5].length) (baseStart_4263011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263011 prefixEnd_4263011 := by exact prefixLift 4263011
  have htrace : WordTrace (prefixWord ++ tailWord_4263011) baseStart_4263011 baseEnd_4263011 := by
    simpa [prefixWord, tailWord_4263011, baseEnd_4263011] using wordTrace_append hprefix tailTrace_4263011
  have hstable : (prefixWord ++ tailWord_4263011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263011).length < 2 ^ (prefixWord ++ tailWord_4263011).sum := by decide
  have hdescent : baseEnd_4263011 < baseStart_4263011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263031 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_4263031 : Nat := 118140960795 + 4263031 * 2 ^ 59
def prefixEnd_4263031 : Nat := 4983230072969 + 3 ^ 40 * 4263031 * 2
def baseEnd_4263031 : Nat := 2188983948017215605307183

theorem tailTrace_4263031 : CollatzResearch.WordTrace tailWord_4263031 prefixEnd_4263031 2188983948017215605307183 := by
  unfold tailWord_4263031
  simp only [CollatzResearch.WordTrace]
  refine ⟨155485514218774229575476947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103657009479182819716984631 155485514218774229575476947)
  ·
    refine ⟨233228271328161344363215421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155485514218774229575476947 233228271328161344363215421)
    ·
      refine ⟨87460601748060504136205783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233228271328161344363215421 87460601748060504136205783)
      ·
        refine ⟨131190902622090756204308675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87460601748060504136205783 131190902622090756204308675)
        ·
          refine ⟨196786353933136134306463013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131190902622090756204308675 196786353933136134306463013)
          ·
            refine ⟨36897441362463025182461815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196786353933136134306463013 36897441362463025182461815)
            ·
              refine ⟨55346162043694537773692723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36897441362463025182461815 55346162043694537773692723)
              ·
                refine ⟨83019243065541806660539085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55346162043694537773692723 83019243065541806660539085)
                ·
                  refine ⟨31132216149578177497702157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83019243065541806660539085 31132216149578177497702157)
                  ·
                    refine ⟨11674581056091816561638309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31132216149578177497702157 11674581056091816561638309)
                    ·
                      refine ⟨2188983948017215605307183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11674581056091816561638309 2188983948017215605307183)
                      ·
                        rfl

theorem cell23_4263031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_4263031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263031 prefixEnd_4263031 := by exact prefixLift 4263031
  have htrace : WordTrace (prefixWord ++ tailWord_4263031) baseStart_4263031 baseEnd_4263031 := by
    simpa [prefixWord, tailWord_4263031, baseEnd_4263031] using wordTrace_append hprefix tailTrace_4263031
  have hstable : (prefixWord ++ tailWord_4263031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263031).length < 2 ^ (prefixWord ++ tailWord_4263031).sum := by decide
  have hdescent : baseEnd_4263031 < baseStart_4263031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263061 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4263061 : Nat := 118140960795 + 4263061 * 2 ^ 59
def prefixEnd_4263061 : Nat := 4983230072969 + 3 ^ 40 * 4263061 * 2
def baseEnd_4263061 : Nat := 2188999352436850487932045

theorem tailTrace_4263061 : CollatzResearch.WordTrace tailWord_4263061 prefixEnd_4263061 2188999352436850487932045 := by
  unfold tailWord_4263061
  simp only [CollatzResearch.WordTrace]
  refine ⟨155486608408665544699069037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103657738939110363132712691 155486608408665544699069037)
  ·
    refine ⟨58307478153249579262150889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 155486608408665544699069037 58307478153249579262150889)
    ·
      refine ⟨43730608614937184446613167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58307478153249579262150889 43730608614937184446613167)
      ·
        refine ⟨65595912922405776669919751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43730608614937184446613167 65595912922405776669919751)
        ·
          refine ⟨98393869383608665004879627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65595912922405776669919751 98393869383608665004879627)
          ·
            refine ⟨147590804075412997507319441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98393869383608665004879627 147590804075412997507319441)
            ·
              refine ⟨110693103056559748130489581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147590804075412997507319441 110693103056559748130489581)
              ·
                refine ⟨41509913646209905548933593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110693103056559748130489581 41509913646209905548933593)
                ·
                  refine ⟨31132435234657429161700195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41509913646209905548933593 31132435234657429161700195)
                  ·
                    refine ⟨46698652851986143742550293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31132435234657429161700195 46698652851986143742550293)
                    ·
                      refine ⟨2188999352436850487932045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46698652851986143742550293 2188999352436850487932045)
                      ·
                        rfl

theorem cell23_4263061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4263061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263061 prefixEnd_4263061 := by exact prefixLift 4263061
  have htrace : WordTrace (prefixWord ++ tailWord_4263061) baseStart_4263061 baseEnd_4263061 := by
    simpa [prefixWord, tailWord_4263061, baseEnd_4263061] using wordTrace_append hprefix tailTrace_4263061
  have hstable : (prefixWord ++ tailWord_4263061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263061).length < 2 ^ (prefixWord ++ tailWord_4263061).sum := by decide
  have hdescent : baseEnd_4263061 < baseStart_4263061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263075 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 1, 4]
def baseStart_4263075 : Nat := 118140960795 + 4263075 * 2 ^ 59
def prefixEnd_4263075 : Nat := 4983230072969 + 3 ^ 40 * 4263075 * 2
def baseEnd_4263075 : Nat := 729668847055337811052327

theorem tailTrace_4263075 : CollatzResearch.WordTrace tailWord_4263075 prefixEnd_4263075 729668847055337811052327 := by
  unfold tailWord_4263075
  simp only [CollatzResearch.WordTrace]
  refine ⟨155487119030614825090078679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103658079353743216726719119 155487119030614825090078679)
  ·
    refine ⟨233230678545922237635118019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155487119030614825090078679 233230678545922237635118019)
    ·
      refine ⟨349846017818883356452677029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233230678545922237635118019 349846017818883356452677029)
      ·
        refine ⟨65596128341040629334876943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 349846017818883356452677029 65596128341040629334876943)
        ·
          refine ⟨98394192511560944002315415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65596128341040629334876943 98394192511560944002315415)
          ·
            refine ⟨147591288767341416003473123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98394192511560944002315415 147591288767341416003473123)
            ·
              refine ⟨221386933151012124005209685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147591288767341416003473123 221386933151012124005209685)
              ·
                refine ⟨2594378122863423328186051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 221386933151012124005209685 2594378122863423328186051)
                ·
                  refine ⟨3891567184295134992279077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594378122863423328186051 3891567184295134992279077)
                  ·
                    refine ⟨729668847055337811052327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3891567184295134992279077 729668847055337811052327)
                    ·
                      rfl

theorem cell23_4263075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 4].length) (baseStart_4263075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263075 prefixEnd_4263075 := by exact prefixLift 4263075
  have htrace : WordTrace (prefixWord ++ tailWord_4263075) baseStart_4263075 baseEnd_4263075 := by
    simpa [prefixWord, tailWord_4263075, baseEnd_4263075] using wordTrace_append hprefix tailTrace_4263075
  have hstable : (prefixWord ++ tailWord_4263075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263075).length < 2 ^ (prefixWord ++ tailWord_4263075).sum := by decide
  have hdescent : baseEnd_4263075 < baseStart_4263075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263091 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_4263091 : Nat := 118140960795 + 4263091 * 2 ^ 59
def prefixEnd_4263091 : Nat := 4983230072969 + 3 ^ 40 * 4263091 * 2
def baseEnd_4263091 : Nat := 2189014756856485370556907

theorem tailTrace_4263091 : CollatzResearch.WordTrace tailWord_4263091 prefixEnd_4263091 2189014756856485370556907 := by
  unfold tailWord_4263091
  simp only [CollatzResearch.WordTrace]
  refine ⟨155487702598556859822661127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103658468399037906548440751 155487702598556859822661127)
  ·
    refine ⟨233231553897835289733991691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155487702598556859822661127 233231553897835289733991691)
    ·
      refine ⟨349847330846752934600987537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233231553897835289733991691 349847330846752934600987537)
      ·
        refine ⟨262385498135064700950740653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349847330846752934600987537 262385498135064700950740653)
        ·
          refine ⟨98394561800649262856527745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262385498135064700950740653 98394561800649262856527745)
          ·
            refine ⟨73795921350486947142395809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98394561800649262856527745 73795921350486947142395809)
            ·
              refine ⟨55346941012865210356796857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73795921350486947142395809 55346941012865210356796857)
              ·
                refine ⟨41510205759648907767597643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55346941012865210356796857 41510205759648907767597643)
                ·
                  refine ⟨62265308639473361651396465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41510205759648907767597643 62265308639473361651396465)
                  ·
                    refine ⟨46698981479605021238547349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62265308639473361651396465 46698981479605021238547349)
                    ·
                      refine ⟨2189014756856485370556907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46698981479605021238547349 2189014756856485370556907)
                      ·
                        rfl

theorem cell23_4263091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_4263091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263091 prefixEnd_4263091 := by exact prefixLift 4263091
  have htrace : WordTrace (prefixWord ++ tailWord_4263091) baseStart_4263091 baseEnd_4263091 := by
    simpa [prefixWord, tailWord_4263091, baseEnd_4263091] using wordTrace_append hprefix tailTrace_4263091
  have hstable : (prefixWord ++ tailWord_4263091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263091).length < 2 ^ (prefixWord ++ tailWord_4263091).sum := by decide
  have hdescent : baseEnd_4263091 < baseStart_4263091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263102 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_4263102 : Nat := 118140960795 + 4263102 * 2 ^ 59
def prefixEnd_4263102 : Nat := 4983230072969 + 3 ^ 40 * 4263102 * 2
def baseEnd_4263102 : Nat := 2189020405143684827519357

theorem tailTrace_4263102 : CollatzResearch.WordTrace tailWord_4263102 prefixEnd_4263102 2189020405143684827519357 := by
  unfold tailWord_4263102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436012975189626087663945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103658735867678005800874373 19436012975189626087663945)
  ·
    refine ⟨14577009731392219565747959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19436012975189626087663945 14577009731392219565747959)
    ·
      refine ⟨21865514597088329348621939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14577009731392219565747959 21865514597088329348621939)
      ·
        refine ⟨32798271895632494022932909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21865514597088329348621939 32798271895632494022932909)
        ·
          refine ⟨12299351960862185258599841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32798271895632494022932909 12299351960862185258599841)
          ·
            refine ⟨9224513970646638943949881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12299351960862185258599841 9224513970646638943949881)
            ·
              refine ⟨6918385477984979207962411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9224513970646638943949881 6918385477984979207962411)
              ·
                refine ⟨10377578216977468811943617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6918385477984979207962411 10377578216977468811943617)
                ·
                  refine ⟨7783183662733101608957713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10377578216977468811943617 7783183662733101608957713)
                  ·
                    refine ⟨5837387747049826206718285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7783183662733101608957713 5837387747049826206718285)
                    ·
                      refine ⟨2189020405143684827519357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837387747049826206718285 2189020405143684827519357)
                      ·
                        rfl

theorem cell23_4263102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_4263102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263102 prefixEnd_4263102 := by exact prefixLift 4263102
  have htrace : WordTrace (prefixWord ++ tailWord_4263102) baseStart_4263102 baseEnd_4263102 := by
    simpa [prefixWord, tailWord_4263102, baseEnd_4263102] using wordTrace_append hprefix tailTrace_4263102
  have hstable : (prefixWord ++ tailWord_4263102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263102).length < 2 ^ (prefixWord ++ tailWord_4263102).sum := by decide
  have hdescent : baseEnd_4263102 < baseStart_4263102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263111 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_4263111 : Nat := 118140960795 + 4263111 * 2 ^ 59
def prefixEnd_4263111 : Nat := 4983230072969 + 3 ^ 40 * 4263111 * 2
def baseEnd_4263111 : Nat := 2189025026469575292306815

theorem tailTrace_4263111 : CollatzResearch.WordTrace tailWord_4263111 prefixEnd_4263111 2189025026469575292306815 := by
  unfold tailWord_4263111
  simp only [CollatzResearch.WordTrace]
  refine ⟨155488432058484403238389187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103658954705656268825592791 155488432058484403238389187)
  ·
    refine ⟨233232648087726604857583781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155488432058484403238389187 233232648087726604857583781)
    ·
      refine ⟨43731121516448738410796959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 233232648087726604857583781 43731121516448738410796959)
      ·
        refine ⟨65596682274673107616195439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43731121516448738410796959 65596682274673107616195439)
        ·
          refine ⟨98395023412009661424293159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65596682274673107616195439 98395023412009661424293159)
          ·
            refine ⟨147592535118014492136439739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98395023412009661424293159 147592535118014492136439739)
            ·
              refine ⟨221388802677021738204659609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147592535118014492136439739 221388802677021738204659609)
              ·
                refine ⟨166041602007766303653494707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221388802677021738204659609 166041602007766303653494707)
                ·
                  refine ⟨249062403011649455480242061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166041602007766303653494707 249062403011649455480242061)
                  ·
                    refine ⟨93398401129368545805090773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 249062403011649455480242061 93398401129368545805090773)
                    ·
                      refine ⟨2189025026469575292306815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 93398401129368545805090773 2189025026469575292306815)
                      ·
                        rfl

theorem cell23_4263111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_4263111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263111 prefixEnd_4263111 := by exact prefixLift 4263111
  have htrace : WordTrace (prefixWord ++ tailWord_4263111) baseStart_4263111 baseEnd_4263111 := by
    simpa [prefixWord, tailWord_4263111, baseEnd_4263111] using wordTrace_append hprefix tailTrace_4263111
  have hstable : (prefixWord ++ tailWord_4263111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263111).length < 2 ^ (prefixWord ++ tailWord_4263111).sum := by decide
  have hdescent : baseEnd_4263111 < baseStart_4263111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263126 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4263126 : Nat := 118140960795 + 4263126 * 2 ^ 59
def prefixEnd_4263126 : Nat := 4983230072969 + 3 ^ 40 * 4263126 * 2
def baseEnd_4263126 : Nat := 729677576226464244539749

theorem tailTrace_4263126 : CollatzResearch.WordTrace tailWord_4263126 prefixEnd_4263126 729677576226464244539749 := by
  unfold tailWord_4263126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718061197089378800011577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103659319435620040533456821 9718061197089378800011577)
  ·
    refine ⟨7288545897817034100008683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9718061197089378800011577 7288545897817034100008683)
    ·
      refine ⟨10932818846725551150013025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7288545897817034100008683 10932818846725551150013025)
      ·
        refine ⟨8199614135044163362509769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10932818846725551150013025 8199614135044163362509769)
        ·
          refine ⟨6149710601283122521882327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8199614135044163362509769 6149710601283122521882327)
          ·
            refine ⟨9224565901924683782823491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6149710601283122521882327 9224565901924683782823491)
            ·
              refine ⟨13836848852887025674235237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9224565901924683782823491 13836848852887025674235237)
              ·
                refine ⟨2594409159916317313919107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13836848852887025674235237 2594409159916317313919107)
                ·
                  refine ⟨3891613739874475970878661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594409159916317313919107 3891613739874475970878661)
                  ·
                    refine ⟨729677576226464244539749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3891613739874475970878661 729677576226464244539749)
                    ·
                      rfl

theorem cell23_4263126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4263126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263126 prefixEnd_4263126 := by exact prefixLift 4263126
  have htrace : WordTrace (prefixWord ++ tailWord_4263126) baseStart_4263126 baseEnd_4263126 := by
    simpa [prefixWord, tailWord_4263126, baseEnd_4263126] using wordTrace_append hprefix tailTrace_4263126
  have hstable : (prefixWord ++ tailWord_4263126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263126).length < 2 ^ (prefixWord ++ tailWord_4263126).sum := by decide
  have hdescent : baseEnd_4263126 < baseStart_4263126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263148 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_4263148 : Nat := 118140960795 + 4263148 * 2 ^ 59
def prefixEnd_4263148 : Nat := 4983230072969 + 3 ^ 40 * 4263148 * 2
def baseEnd_4263148 : Nat := 729681341751263882514715

theorem tailTrace_4263148 : CollatzResearch.WordTrace tailWord_4263148 prefixEnd_4263148 729681341751263882514715 := by
  unfold tailWord_4263148
  simp only [CollatzResearch.WordTrace]
  refine ⟨77744890779675179278743049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103659854372900239038324065 77744890779675179278743049)
  ·
    refine ⟨58308668084756384459057287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77744890779675179278743049 58308668084756384459057287)
    ·
      refine ⟨87463002127134576688585931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58308668084756384459057287 87463002127134576688585931)
      ·
        refine ⟨131194503190701865032878897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87463002127134576688585931 131194503190701865032878897)
        ·
          refine ⟨98395877393026398774659173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131194503190701865032878897 98395877393026398774659173)
          ·
            refine ⟨18449227011192449770248595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98395877393026398774659173 18449227011192449770248595)
            ·
              refine ⟨27673840516788674655372893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18449227011192449770248595 27673840516788674655372893)
              ·
                refine ⟨10377690193795752995764835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27673840516788674655372893 10377690193795752995764835)
                ·
                  refine ⟨15566535290693629493647253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10377690193795752995764835 15566535290693629493647253)
                  ·
                    refine ⟨729681341751263882514715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15566535290693629493647253 729681341751263882514715)
                    ·
                      rfl

theorem cell23_4263148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_4263148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263148 prefixEnd_4263148 := by exact prefixLift 4263148
  have htrace : WordTrace (prefixWord ++ tailWord_4263148) baseStart_4263148 baseEnd_4263148 := by
    simpa [prefixWord, tailWord_4263148, baseEnd_4263148] using wordTrace_append hprefix tailTrace_4263148
  have hstable : (prefixWord ++ tailWord_4263148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263148).length < 2 ^ (prefixWord ++ tailWord_4263148).sum := by decide
  have hdescent : baseEnd_4263148 < baseStart_4263148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263166 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_4263166 : Nat := 118140960795 + 4263166 * 2 ^ 59
def prefixEnd_4263166 : Nat := 4983230072969 + 3 ^ 40 * 4263166 * 2
def baseEnd_4263166 : Nat := 2189053267905572577119063

theorem tailTrace_4263166 : CollatzResearch.WordTrace tailWord_4263166 prefixEnd_4263166 2189053267905572577119063 := by
  unfold tailWord_4263166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436304759160643453955169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103660292048856765087760901 19436304759160643453955169)
  ·
    refine ⟨14577228569370482590466377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19436304759160643453955169 14577228569370482590466377)
    ·
      refine ⟨10932921427027861942849783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14577228569370482590466377 10932921427027861942849783)
      ·
        refine ⟨16399382140541792914274675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10932921427027861942849783 16399382140541792914274675)
        ·
          refine ⟨24599073210812689371412013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16399382140541792914274675 24599073210812689371412013)
          ·
            refine ⟨9224652454054758514279505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24599073210812689371412013 9224652454054758514279505)
            ·
              refine ⟨6918489340541068885709629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9224652454054758514279505 6918489340541068885709629)
              ·
                refine ⟨2594433502702900832141111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6918489340541068885709629 2594433502702900832141111)
                ·
                  refine ⟨3891650254054351248211667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594433502702900832141111 3891650254054351248211667)
                  ·
                    refine ⟨5837475381081526872317501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891650254054351248211667 5837475381081526872317501)
                    ·
                      refine ⟨2189053267905572577119063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837475381081526872317501 2189053267905572577119063)
                      ·
                        rfl

theorem cell23_4263166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_4263166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263166 prefixEnd_4263166 := by exact prefixLift 4263166
  have htrace : WordTrace (prefixWord ++ tailWord_4263166) baseStart_4263166 baseEnd_4263166 := by
    simpa [prefixWord, tailWord_4263166, baseEnd_4263166] using wordTrace_append hprefix tailTrace_4263166
  have hstable : (prefixWord ++ tailWord_4263166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263166).length < 2 ^ (prefixWord ++ tailWord_4263166).sum := by decide
  have hdescent : baseEnd_4263166 < baseStart_4263166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263172 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_4263172 : Nat := 118140960795 + 4263172 * 2 ^ 59
def prefixEnd_4263172 : Nat := 4983230072969 + 3 ^ 40 * 4263172 * 2
def baseEnd_4263172 : Nat := 2189056348789499553644035

theorem tailTrace_4263172 : CollatzResearch.WordTrace tailWord_4263172 prefixEnd_4263172 2189056348789499553644035 := by
  unfold tailWord_4263172
  simp only [CollatzResearch.WordTrace]
  refine ⟨77745328455631705328179885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103660437940842273770906513 77745328455631705328179885)
  ·
    refine ⟨29154498170861889498067457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77745328455631705328179885 29154498170861889498067457)
    ·
      refine ⟨21865873628146417123550593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29154498170861889498067457 21865873628146417123550593)
      ·
        refine ⟨16399405221109812842662945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21865873628146417123550593 16399405221109812842662945)
        ·
          refine ⟨12299553915832359631997209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16399405221109812842662945 12299553915832359631997209)
          ·
            refine ⟨9224665436874269723997907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12299553915832359631997209 9224665436874269723997907)
            ·
              refine ⟨13836998155311404585996861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9224665436874269723997907 13836998155311404585996861)
              ·
                refine ⟨5188874308241776719748823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13836998155311404585996861 5188874308241776719748823)
                ·
                  refine ⟨7783311462362665079623235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188874308241776719748823 7783311462362665079623235)
                  ·
                    refine ⟨11674967193543997619434853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7783311462362665079623235 11674967193543997619434853)
                    ·
                      refine ⟨2189056348789499553644035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11674967193543997619434853 2189056348789499553644035)
                      ·
                        rfl

theorem cell23_4263172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_4263172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263172 prefixEnd_4263172 := by exact prefixLift 4263172
  have htrace : WordTrace (prefixWord ++ tailWord_4263172) baseStart_4263172 baseEnd_4263172 := by
    simpa [prefixWord, tailWord_4263172, baseEnd_4263172] using wordTrace_append hprefix tailTrace_4263172
  have hstable : (prefixWord ++ tailWord_4263172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263172).length < 2 ^ (prefixWord ++ tailWord_4263172).sum := by decide
  have hdescent : baseEnd_4263172 < baseStart_4263172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263182 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_4263182 : Nat := 118140960795 + 4263182 * 2 ^ 59
def prefixEnd_4263182 : Nat := 4983230072969 + 3 ^ 40 * 4263182 * 2
def baseEnd_4263182 : Nat := 729687161198681504839663

theorem tailTrace_4263182 : CollatzResearch.WordTrace tailWord_4263182 prefixEnd_4263182 729687161198681504839663 := by
  unfold tailWord_4263182
  simp only [CollatzResearch.WordTrace]
  refine ⟨19436377705153397795527975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103660681094151454909482533 19436377705153397795527975)
  ·
    refine ⟨29154566557730096693291963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19436377705153397795527975 29154566557730096693291963)
    ·
      refine ⟨43731849836595145039937945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29154566557730096693291963 43731849836595145039937945)
      ·
        refine ⟨32798887377446358779953459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43731849836595145039937945 32798887377446358779953459)
        ·
          refine ⟨49198331066169538169930189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32798887377446358779953459 49198331066169538169930189)
          ·
            refine ⟨18449374149813576813723821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49198331066169538169930189 18449374149813576813723821)
            ·
              refine ⟨6918515306180091305146433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18449374149813576813723821 6918515306180091305146433)
              ·
                refine ⟨5188886479635068478859825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6918515306180091305146433 5188886479635068478859825)
                ·
                  refine ⟨3891664859726301359144869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5188886479635068478859825 3891664859726301359144869)
                  ·
                    refine ⟨729687161198681504839663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3891664859726301359144869 729687161198681504839663)
                    ·
                      rfl

theorem cell23_4263182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_4263182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263182 prefixEnd_4263182 := by exact prefixLift 4263182
  have htrace : WordTrace (prefixWord ++ tailWord_4263182) baseStart_4263182 baseEnd_4263182 := by
    simpa [prefixWord, tailWord_4263182, baseEnd_4263182] using wordTrace_append hprefix tailTrace_4263182
  have hstable : (prefixWord ++ tailWord_4263182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263182).length < 2 ^ (prefixWord ++ tailWord_4263182).sum := by decide
  have hdescent : baseEnd_4263182 < baseStart_4263182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263199 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 2, 4]
def baseStart_4263199 : Nat := 118140960795 + 4263199 * 2 ^ 59
def prefixEnd_4263199 : Nat := 4983230072969 + 3 ^ 40 * 4263199 * 2
def baseEnd_4263199 : Nat := 729690070922390316002137

theorem tailTrace_4263199 : CollatzResearch.WordTrace tailWord_4263199 prefixEnd_4263199 729690070922390316002137 := by
  unfold tailWord_4263199
  simp only [CollatzResearch.WordTrace]
  refine ⟨155491641682165594267592651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103661094454777062845061767 155491641682165594267592651)
  ·
    refine ⟨233237462523248391401388977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155491641682165594267592651 233237462523248391401388977)
    ·
      refine ⟨174928096892436293551041733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233237462523248391401388977 174928096892436293551041733)
      ·
        refine ⟨32799018167331805040820325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174928096892436293551041733 32799018167331805040820325)
        ·
          refine ⟨6149815906374713445153811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32799018167331805040820325 6149815906374713445153811)
          ·
            refine ⟨9224723859562070167730717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6149815906374713445153811 9224723859562070167730717)
            ·
              refine ⟨3459271447335776312899019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9224723859562070167730717 3459271447335776312899019)
              ·
                refine ⟨5188907171003664469348529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459271447335776312899019 5188907171003664469348529)
                ·
                  refine ⟨3891680378252748352011397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5188907171003664469348529 3891680378252748352011397)
                  ·
                    refine ⟨729690070922390316002137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3891680378252748352011397 729690070922390316002137)
                    ·
                      rfl

theorem cell23_4263199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_4263199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263199 prefixEnd_4263199 := by exact prefixLift 4263199
  have htrace : WordTrace (prefixWord ++ tailWord_4263199) baseStart_4263199 baseEnd_4263199 := by
    simpa [prefixWord, tailWord_4263199, baseEnd_4263199] using wordTrace_append hprefix tailTrace_4263199
  have hstable : (prefixWord ++ tailWord_4263199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263199).length < 2 ^ (prefixWord ++ tailWord_4263199).sum := by decide
  have hdescent : baseEnd_4263199 < baseStart_4263199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263232 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2]
def baseStart_4263232 : Nat := 118140960795 + 4263232 * 2 ^ 59
def prefixEnd_4263232 : Nat := 4983230072969 + 3 ^ 40 * 4263232 * 2
def baseEnd_4263232 : Nat := 2189087157628769318893759

theorem tailTrace_4263232 : CollatzResearch.WordTrace tailWord_4263232 prefixEnd_4263232 2189087157628769318893759 := by
  unfold tailWord_4263232
  simp only [CollatzResearch.WordTrace]
  refine ⟨77746422645523020451771975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103661896860697360602362633 77746422645523020451771975)
  ·
    refine ⟨116619633968284530677657963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77746422645523020451771975 116619633968284530677657963)
    ·
      refine ⟨174929450952426796016486945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116619633968284530677657963 174929450952426796016486945)
      ·
        refine ⟨131197088214320097012365209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174929450952426796016486945 131197088214320097012365209)
        ·
          refine ⟨98397816160740072759273907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131197088214320097012365209 98397816160740072759273907)
          ·
            refine ⟨147596724241110109138910861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98397816160740072759273907 147596724241110109138910861)
            ·
              refine ⟨55348771590416290927091573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147596724241110109138910861 55348771590416290927091573)
              ·
                refine ⟨5188947336601527274414835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55348771590416290927091573 5188947336601527274414835)
                ·
                  refine ⟨7783421004902290911622253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5188947336601527274414835 7783421004902290911622253)
                  ·
                    refine ⟨2918782876838359091858345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7783421004902290911622253 2918782876838359091858345)
                    ·
                      refine ⟨2189087157628769318893759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918782876838359091858345 2189087157628769318893759)
                      ·
                        rfl

theorem cell23_4263232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_4263232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263232 prefixEnd_4263232 := by exact prefixLift 4263232
  have htrace : WordTrace (prefixWord ++ tailWord_4263232) baseStart_4263232 baseEnd_4263232 := by
    simpa [prefixWord, tailWord_4263232, baseEnd_4263232] using wordTrace_append hprefix tailTrace_4263232
  have hstable : (prefixWord ++ tailWord_4263232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263232).length < 2 ^ (prefixWord ++ tailWord_4263232).sum := by decide
  have hdescent : baseEnd_4263232 < baseStart_4263232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263248 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_4263248 : Nat := 118140960795 + 4263248 * 2 ^ 59
def prefixEnd_4263248 : Nat := 4983230072969 + 3 ^ 40 * 4263248 * 2
def baseEnd_4263248 : Nat := 2189095373319241256293685

theorem tailTrace_4263248 : CollatzResearch.WordTrace tailWord_4263248 prefixEnd_4263248 2189095373319241256293685 := by
  unfold tailWord_4263248
  simp only [CollatzResearch.WordTrace]
  refine ⟨77746714429494037818063199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103662285905992050424084265 77746714429494037818063199)
  ·
    refine ⟨116620071644241056727094799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77746714429494037818063199 116620071644241056727094799)
    ·
      refine ⟨174930107466361585090642199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116620071644241056727094799 174930107466361585090642199)
      ·
        refine ⟨262395161199542377635963299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174930107466361585090642199 262395161199542377635963299)
        ·
          refine ⟨393592741799313566453944949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262395161199542377635963299 393592741799313566453944949)
          ·
            refine ⟨36899319543685646855057339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 393592741799313566453944949 36899319543685646855057339)
            ·
              refine ⟨55348979315528470282586009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36899319543685646855057339 55348979315528470282586009)
              ·
                refine ⟨41511734486646352711939507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55348979315528470282586009 41511734486646352711939507)
                ·
                  refine ⟨62267601729969529067909261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41511734486646352711939507 62267601729969529067909261)
                  ·
                    refine ⟨23350350648738573400465973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62267601729969529067909261 23350350648738573400465973)
                    ·
                      refine ⟨2189095373319241256293685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23350350648738573400465973 2189095373319241256293685)
                      ·
                        rfl

theorem cell23_4263248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_4263248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263248 prefixEnd_4263248 := by exact prefixLift 4263248
  have htrace : WordTrace (prefixWord ++ tailWord_4263248) baseStart_4263248 baseEnd_4263248 := by
    simpa [prefixWord, tailWord_4263248, baseEnd_4263248] using wordTrace_append hprefix tailTrace_4263248
  have hstable : (prefixWord ++ tailWord_4263248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263248).length < 2 ^ (prefixWord ++ tailWord_4263248).sum := by decide
  have hdescent : baseEnd_4263248 < baseStart_4263248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263322 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_4263322 : Nat := 118140960795 + 4263322 * 2 ^ 59
def prefixEnd_4263322 : Nat := 4983230072969 + 3 ^ 40 * 4263322 * 2
def baseEnd_4263322 : Nat := 2189133370887673966768345

theorem tailTrace_4263322 : CollatzResearch.WordTrace tailWord_4263322 prefixEnd_4263322 2189133370887673966768345 := by
  unfold tailWord_4263322
  simp only [CollatzResearch.WordTrace]
  refine ⟨38874031965179996568580055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103664085240479990849546813 38874031965179996568580055)
  ·
    refine ⟨58311047947769994852870083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38874031965179996568580055 58311047947769994852870083)
    ·
      refine ⟨87466571921654992279305125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58311047947769994852870083 87466571921654992279305125)
      ·
        refine ⟨16399982235310311052369711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87466571921654992279305125 16399982235310311052369711)
        ·
          refine ⟨24599973352965466578554567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16399982235310311052369711 24599973352965466578554567)
          ·
            refine ⟨36899960029448199867831851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24599973352965466578554567 36899960029448199867831851)
            ·
              refine ⟨55349940044172299801747777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36899960029448199867831851 55349940044172299801747777)
              ·
                refine ⟨41512455033129224851310833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55349940044172299801747777 41512455033129224851310833)
                ·
                  refine ⟨31134341274846918638483125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41512455033129224851310833 31134341274846918638483125)
                  ·
                    refine ⟨2918844494516898622357793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31134341274846918638483125 2918844494516898622357793)
                    ·
                      refine ⟨2189133370887673966768345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918844494516898622357793 2189133370887673966768345)
                      ·
                        rfl

theorem cell23_4263322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_4263322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263322 prefixEnd_4263322 := by exact prefixLift 4263322
  have htrace : WordTrace (prefixWord ++ tailWord_4263322) baseStart_4263322 baseEnd_4263322 := by
    simpa [prefixWord, tailWord_4263322, baseEnd_4263322] using wordTrace_append hprefix tailTrace_4263322
  have hstable : (prefixWord ++ tailWord_4263322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263322).length < 2 ^ (prefixWord ++ tailWord_4263322).sum := by decide
  have hdescent : baseEnd_4263322 < baseStart_4263322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263336 : List Nat := [2, 1, 6, 1, 2, 1, 2, 3, 5]
def baseStart_4263336 : Nat := 118140960795 + 4263336 * 2 ^ 59
def prefixEnd_4263336 : Nat := 4983230072969 + 3 ^ 40 * 4263336 * 2
def baseEnd_4263336 : Nat := 243237839957426323554809

theorem tailTrace_4263336 : CollatzResearch.WordTrace tailWord_4263336 prefixEnd_4263336 243237839957426323554809 := by
  unfold tailWord_4263336
  simp only [CollatzResearch.WordTrace]
  refine ⟨77748319241334633332664931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103664425655112844443553241 77748319241334633332664931)
  ·
    refine ⟨116622478862001949998997397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77748319241334633332664931 116622478862001949998997397)
    ·
      refine ⟨5466678696656341406203003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 116622478862001949998997397 5466678696656341406203003)
      ·
        refine ⟨8200018044984512109304505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5466678696656341406203003 8200018044984512109304505)
        ·
          refine ⟨6150013533738384081978379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8200018044984512109304505 6150013533738384081978379)
          ·
            refine ⟨9225020300607576122967569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6150013533738384081978379 9225020300607576122967569)
            ·
              refine ⟨6918765225455682092225677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9225020300607576122967569 6918765225455682092225677)
              ·
                refine ⟨2594536959545880784584629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6918765225455682092225677 2594536959545880784584629)
                ·
                  refine ⟨243237839957426323554809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2594536959545880784584629 243237839957426323554809)
                  ·
                    rfl

theorem cell23_4263336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 3, 5].length) (baseStart_4263336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263336 prefixEnd_4263336 := by exact prefixLift 4263336
  have htrace : WordTrace (prefixWord ++ tailWord_4263336) baseStart_4263336 baseEnd_4263336 := by
    simpa [prefixWord, tailWord_4263336, baseEnd_4263336] using wordTrace_append hprefix tailTrace_4263336
  have hstable : (prefixWord ++ tailWord_4263336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263336).length < 2 ^ (prefixWord ++ tailWord_4263336).sum := by decide
  have hdescent : baseEnd_4263336 < baseStart_4263336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263352 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_4263352 : Nat := 118140960795 + 4263352 * 2 ^ 59
def prefixEnd_4263352 : Nat := 4983230072969 + 3 ^ 40 * 4263352 * 2
def baseEnd_4263352 : Nat := 2189148775307308849393207

theorem tailTrace_4263352 : CollatzResearch.WordTrace tailWord_4263352 prefixEnd_4263352 2189148775307308849393207 := by
  unfold tailWord_4263352
  simp only [CollatzResearch.WordTrace]
  refine ⟨77748611025305650698956155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103664814700407534265274873 77748611025305650698956155)
  ·
    refine ⟨116622916537958476048434233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77748611025305650698956155 116622916537958476048434233)
    ·
      refine ⟨87467187403468857036325675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116622916537958476048434233 87467187403468857036325675)
      ·
        refine ⟨131200781105203285554488513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87467187403468857036325675 131200781105203285554488513)
        ·
          refine ⟨98400585828902464165866385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131200781105203285554488513 98400585828902464165866385)
          ·
            refine ⟨73800439371676848124399789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98400585828902464165866385 73800439371676848124399789)
            ·
              refine ⟨27675164764378818046649921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73800439371676848124399789 27675164764378818046649921)
              ·
                refine ⟨20756373573284113534987441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27675164764378818046649921 20756373573284113534987441)
                ·
                  refine ⟨15567280179963085151240581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20756373573284113534987441 15567280179963085151240581)
                  ·
                    refine ⟨2918865033743078465857609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15567280179963085151240581 2918865033743078465857609)
                    ·
                      refine ⟨2189148775307308849393207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2918865033743078465857609 2189148775307308849393207)
                      ·
                        rfl

theorem cell23_4263352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_4263352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263352 prefixEnd_4263352 := by exact prefixLift 4263352
  have htrace : WordTrace (prefixWord ++ tailWord_4263352) baseStart_4263352 baseEnd_4263352 := by
    simpa [prefixWord, tailWord_4263352, baseEnd_4263352] using wordTrace_append hprefix tailTrace_4263352
  have hstable : (prefixWord ++ tailWord_4263352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263352).length < 2 ^ (prefixWord ++ tailWord_4263352).sum := by decide
  have hdescent : baseEnd_4263352 < baseStart_4263352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263372 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4263372 : Nat := 118140960795 + 4263372 * 2 ^ 59
def prefixEnd_4263372 : Nat := 4983230072969 + 3 ^ 40 * 4263372 * 2
def baseEnd_4263372 : Nat := 2189159044920398771143115

theorem tailTrace_4263372 : CollatzResearch.WordTrace tailWord_4263372 prefixEnd_4263372 2189159044920398771143115 := by
  unfold tailWord_4263372
  simp only [CollatzResearch.WordTrace]
  refine ⟨77748975755269422406820185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103665301007025896542426913 77748975755269422406820185)
  ·
    refine ⟨58311731816452066805115139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77748975755269422406820185 58311731816452066805115139)
    ·
      refine ⟨87467597724678100207672709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58311731816452066805115139 87467597724678100207672709)
      ·
        refine ⟨16400174573377143788938633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87467597724678100207672709 16400174573377143788938633)
        ·
          refine ⟨12300130930032857841703975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16400174573377143788938633 12300130930032857841703975)
          ·
            refine ⟨18450196395049286762555963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300130930032857841703975 18450196395049286762555963)
            ·
              refine ⟨27675294592573930143833945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18450196395049286762555963 27675294592573930143833945)
              ·
                refine ⟨20756470944430447607875459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27675294592573930143833945 20756470944430447607875459)
                ·
                  refine ⟨31134706416645671411813189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20756470944430447607875459 31134706416645671411813189)
                  ·
                    refine ⟨5837757453121063389714973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31134706416645671411813189 5837757453121063389714973)
                    ·
                      refine ⟨2189159044920398771143115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5837757453121063389714973 2189159044920398771143115)
                      ·
                        rfl

theorem cell23_4263372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4263372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263372 prefixEnd_4263372 := by exact prefixLift 4263372
  have htrace : WordTrace (prefixWord ++ tailWord_4263372) baseStart_4263372 baseEnd_4263372 := by
    simpa [prefixWord, tailWord_4263372, baseEnd_4263372] using wordTrace_append hprefix tailTrace_4263372
  have hstable : (prefixWord ++ tailWord_4263372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263372).length < 2 ^ (prefixWord ++ tailWord_4263372).sum := by decide
  have hdescent : baseEnd_4263372 < baseStart_4263372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263375 : List Nat := [1, 1, 2, 1, 1, 4, 2, 5, 6]
def baseStart_4263375 : Nat := 118140960795 + 4263375 * 2 ^ 59
def prefixEnd_4263375 : Nat := 4983230072969 + 3 ^ 40 * 4263375 * 2
def baseEnd_4263375 : Nat := 243240065040262473267289

theorem tailTrace_4263375 : CollatzResearch.WordTrace tailWord_4263375 prefixEnd_4263375 243240065040262473267289 := by
  unfold tailWord_4263375
  simp only [CollatzResearch.WordTrace]
  refine ⟨155498060929527976325999579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103665373953018650883999719 155498060929527976325999579)
  ·
    refine ⟨233247091394291964488999369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155498060929527976325999579 233247091394291964488999369)
    ·
      refine ⟨174935318545718973366749527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233247091394291964488999369 174935318545718973366749527)
      ·
        refine ⟨262402977818578460050124291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174935318545718973366749527 262402977818578460050124291)
        ·
          refine ⟨393604466727867690075186437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262402977818578460050124291 393604466727867690075186437)
          ·
            refine ⟨73800837511475191889097457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 393604466727867690075186437 73800837511475191889097457)
            ·
              refine ⟨55350628133606393916823093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73800837511475191889097457 55350628133606393916823093)
              ·
                refine ⟨5189121387525599429702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55350628133606393916823093 5189121387525599429702165)
                ·
                  refine ⟨243240065040262473267289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5189121387525599429702165 243240065040262473267289)
                  ·
                    rfl

theorem cell23_4263375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 6].length) (baseStart_4263375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263375 prefixEnd_4263375 := by exact prefixLift 4263375
  have htrace : WordTrace (prefixWord ++ tailWord_4263375) baseStart_4263375 baseEnd_4263375 := by
    simpa [prefixWord, tailWord_4263375, baseEnd_4263375] using wordTrace_append hprefix tailTrace_4263375
  have hstable : (prefixWord ++ tailWord_4263375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263375).length < 2 ^ (prefixWord ++ tailWord_4263375).sum := by decide
  have hdescent : baseEnd_4263375 < baseStart_4263375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4263426 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_4263426 : Nat := 118140960795 + 4263426 * 2 ^ 59
def prefixEnd_4263426 : Nat := 4983230072969 + 3 ^ 40 * 4263426 * 2
def baseEnd_4263426 : Nat := 243242974763971284429763

theorem tailTrace_4263426 : CollatzResearch.WordTrace tailWord_4263426 prefixEnd_4263426 243242974763971284429763 := by
  unfold tailWord_4263426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38874980263085803009026533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103666614034895474690737421 38874980263085803009026533)
  ·
    refine ⟨7289058799328588064192475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38874980263085803009026533 7289058799328588064192475)
    ·
      refine ⟨10933588198992882096288713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7289058799328588064192475 10933588198992882096288713)
      ·
        refine ⟨8200191149244661572216535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10933588198992882096288713 8200191149244661572216535)
        ·
          refine ⟨12300286723866992358324803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200191149244661572216535 12300286723866992358324803)
          ·
            refine ⟨18450430085800488537487205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12300286723866992358324803 18450430085800488537487205)
            ·
              refine ⟨3459455641087591600778851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18450430085800488537487205 3459455641087591600778851)
              ·
                refine ⟨5189183461631387401168277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3459455641087591600778851 5189183461631387401168277)
                ·
                  refine ⟨243242974763971284429763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5189183461631387401168277 243242974763971284429763)
                  ·
                    rfl

theorem cell23_4263426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_4263426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4263426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4263426 prefixEnd_4263426 := by exact prefixLift 4263426
  have htrace : WordTrace (prefixWord ++ tailWord_4263426) baseStart_4263426 baseEnd_4263426 := by
    simpa [prefixWord, tailWord_4263426, baseEnd_4263426] using wordTrace_append hprefix tailTrace_4263426
  have hstable : (prefixWord ++ tailWord_4263426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4263426).length < 2 ^ (prefixWord ++ tailWord_4263426).sum := by decide
  have hdescent : baseEnd_4263426 < baseStart_4263426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4263426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
